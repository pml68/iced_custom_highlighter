//! A custom syntax highlighter for iced.
//!
//! It uses the colors from your app's Theme, based on the current [`Scope`]
use iced_core::font::Font;
use iced_core::text::highlighter::{self, Format};
use iced_core::Theme;

use once_cell::sync::Lazy;
use std::collections::HashSet;
use std::ops::Range;
use std::str::FromStr;
use syntect::highlighting;
use syntect::parsing;

static SYNTAXES: Lazy<parsing::SyntaxSet> = Lazy::new(parsing::SyntaxSet::load_defaults_nonewlines);

const LINES_PER_SNAPSHOT: usize = 50;

type ScopeSelectorsResult =
    core::result::Result<highlighting::ScopeSelectors, parsing::ParseScopeError>;

/// A syntax highlighter.
#[derive(Debug)]
pub struct Highlighter {
    syntax: &'static parsing::SyntaxReference,
    custom_scopes: Vec<Scope>,
    style: Option<fn(&Theme, Scope) -> Format<Font>>,
    caches: Vec<(parsing::ParseState, parsing::ScopeStack)>,
    current_line: usize,
}

impl highlighter::Highlighter for Highlighter {
    type Settings = Settings;
    type Highlight = Highlight;

    type Iterator<'a> = Box<dyn Iterator<Item = (Range<usize>, Self::Highlight)> + 'a>;

    fn new(settings: &Self::Settings) -> Self {
        let syntax = SYNTAXES
            .find_syntax_by_token(&settings.token)
            .unwrap_or_else(|| SYNTAXES.find_syntax_plain_text());

        let style = settings.style.clone();
        let custom_scopes = settings.custom_scopes.clone();

        let parser = parsing::ParseState::new(syntax);
        let stack = parsing::ScopeStack::new();

        Highlighter {
            syntax,
            custom_scopes,
            style,
            caches: vec![(parser, stack)],
            current_line: 0,
        }
    }

    fn update(&mut self, new_settings: &Self::Settings) {
        self.syntax = SYNTAXES
            .find_syntax_by_token(&new_settings.token)
            .unwrap_or_else(|| SYNTAXES.find_syntax_plain_text());

        self.custom_scopes = new_settings.custom_scopes.clone();

        self.style = new_settings.style.clone();

        // Restart the highlighter
        self.change_line(0);
    }

    fn change_line(&mut self, line: usize) {
        let snapshot = line / LINES_PER_SNAPSHOT;

        if snapshot <= self.caches.len() {
            self.caches.truncate(snapshot);
            self.current_line = snapshot * LINES_PER_SNAPSHOT;
        } else {
            self.caches.truncate(1);
            self.current_line = 0;
        }

        let (parser, stack) = self.caches.last().cloned().unwrap_or_else(|| {
            (
                parsing::ParseState::new(self.syntax),
                parsing::ScopeStack::new(),
            )
        });

        self.caches.push((parser, stack));
    }

    fn highlight_line(&mut self, line: &str) -> Self::Iterator<'_> {
        if self.current_line / LINES_PER_SNAPSHOT >= self.caches.len() {
            let (parser, stack) = self.caches.last().expect("Caches must not be empty");

            self.caches.push((parser.clone(), stack.clone()));
        }

        self.current_line += 1;

        let (parser, stack) = self.caches.last_mut().expect("Caches must not be empty");

        let ops = parser.parse_line(line, &SYNTAXES).unwrap_or_default();

        let style = &self.style;
        let custom_scopes = &self.custom_scopes;

        Box::new(
            ScopeRangeIterator {
                ops,
                line_length: line.len(),
                index: 0,
                last_str_index: 0,
            }
            .filter_map(move |(range, scope)| {
                let _ = stack.apply(&scope);

                if range.is_empty() {
                    None
                } else {
                    Some((
                        range,
                        Highlight {
                            scope: Scope::from_scopestack(stack.clone(), custom_scopes.clone()),
                            style: style.clone(),
                        },
                    ))
                }
            }),
        )
    }

    fn current_line(&self) -> usize {
        self.current_line
    }
}

/// The settings of a [`Highlighter`].
#[derive(Debug, Clone, PartialEq)]
pub struct Settings {
    /// Custom scopes used for parsing the code.
    ///
    /// It extends [`Scope::ALL`].
    pub custom_scopes: Vec<Scope>,

    /// The styling method of the [`Highlighter`].
    ///
    /// It dictates how text matching a certain scope will be highlighted.
    /// If set to None, [`default_style`] will be used.
    ///
    /// [`default_style`]: Highlight::default_style
    pub style: Option<fn(&Theme, Scope) -> Format<Font>>,

    /// The extension of the file or the name of the language to highlight.
    ///
    /// The [`Highlighter`] will use the token to automatically determine the grammar to use for highlighting.
    pub token: String,
}

impl Settings {
    /// Creates a new [`Settings`] struct with the given values.
    pub fn new(
        custom_scopes: Vec<Scope>,
        style: Option<fn(&Theme, Scope) -> Format<Font>>,
        token: impl Into<String>,
    ) -> Self {
        Self {
            custom_scopes,
            style,
            token: token.into(),
        }
    }
}

/// A highlight produced by a [`Highlighter`].
#[derive(Debug)]
pub struct Highlight {
    scope: Scope,
    style: Option<fn(&Theme, Scope) -> Format<Font>>,
}

impl Highlight {
    /// Returns the [`Format`] of the [`Highlight`].
    ///
    /// It contains both the [`color`] and the [`font`].
    ///
    /// [`color`]: iced_core::Color
    /// [`font`]: iced_core::Font
    pub fn to_format(&self, theme: &Theme) -> Format<Font> {
        match self.style {
            Some(style) => style(theme, self.scope.clone()),
            None => Self::default_style(theme, self.scope.clone()),
        }
    }

    /// The defalt styling function of a [`Highlight`].
    pub fn default_style(theme: &Theme, scope: Scope) -> Format<Font> {
        let color = match scope {
            Scope::Comment | Scope::TagStart => theme.extended_palette().background.weak.color,
            Scope::String | Scope::RegExp | Scope::QuotedString => {
                theme.extended_palette().primary.base.color
            }
            Scope::EscapeSequence | Scope::SupportConstruct | Scope::Continuation => {
                theme.extended_palette().danger.base.color
            }
            Scope::Number => theme.extended_palette().secondary.weak.color,
            Scope::Variable | Scope::VariableStart | Scope::TagName | Scope::Brackets => {
                theme.extended_palette().primary.weak.color
            }
            Scope::VariableFunction | Scope::FunctionName => {
                theme.extended_palette().success.base.color
            }
            Scope::Keyword | Scope::KeywordOperator | Scope::Operator => {
                theme.extended_palette().background.strong.color
            }
            Scope::KeywordOther => theme.extended_palette().danger.strong.color,
            Scope::Storage
            | Scope::StorageModifier
            | Scope::StorageType
            | Scope::Class
            | Scope::LibraryClass
            | Scope::LibraryFunction => theme.extended_palette().success.base.color,
            Scope::QuotedSingle => theme.palette().text,
            Scope::BuiltinConstant | Scope::UserDefinedConstant => {
                theme.extended_palette().danger.base.color
            }
            Scope::Invalid => theme.extended_palette().danger.weak.color,
            Scope::Special => theme.extended_palette().danger.strong.color,
            Scope::Import => theme.extended_palette().primary.weak.color,
            Scope::Exception => theme.extended_palette().danger.base.color,
            Scope::Parantheses | Scope::Braces => theme.extended_palette().background.strong.color,
            Scope::Other | Scope::Custom { .. } => theme.extended_palette().primary.strong.color,
        };

        Format {
            color: Some(color),
            font: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Hash)]
pub enum Scope {
    Comment,
    String,
    RegExp,
    EscapeSequence,
    Number,
    Variable,
    VariableFunction,
    Keyword,
    KeywordOperator,
    KeywordOther,
    Import,
    Operator,
    Storage,
    StorageModifier,
    Class,
    LibraryClass,
    FunctionName,
    VariableStart,
    BuiltinConstant,
    UserDefinedConstant,
    SupportConstruct,
    TagName,
    TagStart,
    LibraryFunction,
    Continuation,
    StorageType,
    Exception,
    Special,
    Invalid,
    QuotedString,
    QuotedSingle,
    Brackets,
    Parantheses,
    Braces,
    #[default]
    Other,
    /// A custom scope.
    Custom {
        /// The name of the scope, letting you identify it in match statements easily.
        name: String,
        /// A series of selectors separated by commas or pipes.
        scope_string: String,
    },
}

impl Scope {
    /// A list with all the defined scopes.
    pub const ALL: &'static [Self] = &[
        Self::Comment,
        Self::String,
        Self::RegExp,
        Self::EscapeSequence,
        Self::Number,
        Self::Variable,
        Self::VariableFunction,
        Self::Keyword,
        Self::KeywordOperator,
        Self::KeywordOther,
        Self::Import,
        Self::Operator,
        Self::Storage,
        Self::StorageModifier,
        Self::Class,
        Self::LibraryClass,
        Self::FunctionName,
        Self::VariableStart,
        Self::BuiltinConstant,
        Self::UserDefinedConstant,
        Self::SupportConstruct,
        Self::TagName,
        Self::TagStart,
        Self::LibraryFunction,
        Self::Continuation,
        Self::StorageType,
        Self::Exception,
        Self::Special,
        Self::Invalid,
        Self::QuotedString,
        Self::QuotedSingle,
        Self::Brackets,
        Self::Parantheses,
        Self::Braces,
    ];

    /// Creates a new custom [`Scope`].
    pub fn custom(name: impl Into<String>, scope_string: impl Into<String>) -> Self {
        Self::Custom {
            name: name.into(),
            scope_string: scope_string.into(),
        }
    }

    /// Retuns the scope string of the [`Scope`].
    pub fn scope_str(&self) -> &str {
        match self {
            Self::Comment => "comment, meta.documentation",
            Self::String => "string",
            Self::RegExp => "string.regexp",
            Self::EscapeSequence => "constant.character.escape",
            Self::Number => "constant.numeric",
            Self::Variable => "variable",
            Self::VariableFunction => "variable.function",
            Self::Keyword => "keyword",
            Self::KeywordOperator => "keyword.operator",
            Self::KeywordOther => "keyword.other",
            Self::Import => "meta.import keyword, keyword.control.import, keyword.control.import.from, keyword.other.import, keyword.control.at-rule.include, keyword.control.at-rule.import",
            Self::Operator => "keyword.operator.comparison, keyword.operator.assignment, keyword.operator.arithmetic",
            Self::Storage => "storage",
            Self::StorageModifier => "storage.modifier",
            Self::Class => "keyword.control.class, meta.class, entity.name.class, entity.name.type.class",
            Self::LibraryClass => "support, support.type, support.class",
            Self::FunctionName => "entity.name.function",
            Self::VariableStart => "punctuation.definition.variable",
            Self::BuiltinConstant => "constant.language, meta.preprocessor",
            Self::UserDefinedConstant => "constant.character, constant.other",
            Self::SupportConstruct => "support.function.construct, keyword.other.new",
            Self::TagName => "entity.name.tag",
            Self::TagStart => "punctuation.definition.tag.html, punctuation.definition.tag.begin, punctuation.definition.tag.end",
            Self::LibraryFunction => "support.function",
            Self::Continuation => "punctuation.separator.continuation",
            Self::StorageType => "storage.type",
            Self::Exception => "support.type.exception",
            Self::Special => "keyword.other.special-method",
            Self::Invalid => "invalid",
            Self::QuotedString => "string.quoted.double, string.quoted.single",
            Self::QuotedSingle => "punctuation.definition.string.begin, punctuation.definition.string.end",
            Self::Brackets => "meta.brace.squares",
            Self::Parantheses => "meta.brace.round, punctuation.definition.parameters.begin, punctuation.definition.parameters.end",
            Self::Braces => "meta.brace.curly",
            Self::Other => "",
            Self::Custom {scope_string,..} => &scope_string
        }
    }

    fn from_scopestack(stack: parsing::ScopeStack, custom_scopes: Vec<Self>) -> Self {
        let scopes: Vec<Self>;

        if custom_scopes.len() > 0 {
            let mut hashset: HashSet<Self> = (*Self::ALL).to_vec().into_iter().collect();
            hashset.extend(custom_scopes);
            scopes = hashset.into_iter().collect();
        } else {
            scopes = Self::ALL.to_vec();
        }

        let selectors: Vec<(Self, highlighting::ScopeSelectors)> = scopes
            .iter()
            .filter_map(|scope| {
                let selector: ScopeSelectorsResult = scope.clone().into();
                match selector {
                    Ok(selector) => Some((scope.clone(), selector)),
                    Err(_) => None,
                }
            })
            .collect();

        let mut matching_scopes: Vec<(parsing::MatchPower, Self)> = selectors
            .iter()
            .filter_map(|(scope, selector)| {
                selector
                    .does_match(&stack.scopes)
                    .map(|score| (score, scope.clone()))
            })
            .collect();
        matching_scopes.sort_by_key(|&(score, _)| score);
        match matching_scopes.last() {
            Some(scope) => scope.1.clone(),
            None => Self::Other,
        }
    }
}

impl From<Scope> for Result<highlighting::ScopeSelectors, parsing::ParseScopeError> {
    fn from(value: Scope) -> Self {
        highlighting::ScopeSelectors::from_str(value.scope_str())
    }
}

struct ScopeRangeIterator {
    ops: Vec<(usize, parsing::ScopeStackOp)>,
    line_length: usize,
    index: usize,
    last_str_index: usize,
}

impl Iterator for ScopeRangeIterator {
    type Item = (std::ops::Range<usize>, parsing::ScopeStackOp);

    fn next(&mut self) -> Option<Self::Item> {
        if self.index > self.ops.len() {
            return None;
        }

        let next_str_i = if self.index == self.ops.len() {
            self.line_length
        } else {
            self.ops[self.index].0
        };

        let range = self.last_str_index..next_str_i;
        self.last_str_index = next_str_i;

        let op = if self.index == 0 {
            parsing::ScopeStackOp::Noop
        } else {
            self.ops[self.index - 1].1.clone()
        };

        self.index += 1;
        Some((range, op))
    }
}