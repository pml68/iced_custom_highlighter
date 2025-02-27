# iced_custom_highlighter

A custom syntax highlighter for iced.

It uses the colors from your app's Theme, based on a styling method (like `default_style`)

# Example

```rust
use iced::widget::{Column, pick_list, text_editor};
use iced::{Element, Theme};
use iced_custom_highlighter::{Highlight, Highlighter, Settings};

#[derive(Default)]
struct State {
    content: text_editor::Content,
    theme: Theme,
}

#[derive(Debug, Clone)]
enum Message {
    Edit(text_editor::Action),
    ChangeTheme(Theme),
}

fn view(state: &State) -> Element<'_, Message> {
Column::new()
    .push(
        text_editor(&state.content)
            .placeholder("Type something here...")
            .highlight_with::<Highlighter>(
                Settings::new(vec![], Highlight::default_style, "rs"),
                Highlight::to_format,
            )
            .on_action(Message::Edit),
    )
    .push(pick_list(
        Theme::ALL,
        Some(state.theme),
        Message::ChangeTheme,
    ))
    .into()
}

fn update(state: &mut State, message: Message) {
    match message {
        Message::Edit(action) => {
            state.content.perform(action);
        }

        Message::ChangeTheme(theme) => {
            state.theme = theme;
        }
    }
}
```
