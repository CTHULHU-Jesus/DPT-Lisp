use anyhow::{anyhow, Result};
use dpt_lisp::Parse::Value;
use dpt_lisp::{parse_expr, repl_to_span, run, run1, State};
use wasm_bindgen::{JsCast, UnwrapThrowExt};
use web_sys::{console::log_1, Event, HtmlInputElement, HtmlTextAreaElement, InputEvent};
use yew::prelude::*;
use yew::{html, html::Scope, Component, Context, Html};

/// Update Message
pub enum Msg {
  /// Input from user
  Input(String),
  /// Load file from user
  Load,
}

/// Website Model
pub struct Model {
  log: Vec<Html>,
  input: String,
  state: State,
  context: dpt_lisp::Context,
}

/// Returns true if i could be parsed as an expression
fn complete_input(i: &str) -> bool {
  if i.chars().last() == Some('\n') {
    parse_expr(&repl_to_span(i)).is_ok()
  } else {
    false
  }
}

fn info_window() -> Html {
  let blockquote = |x: &str| html!(<blockquote><pre>{place_linebreaks(x)}</pre></blockquote>);
  let function_example = "(lambda (x [Int])\n        (+ x 1))";
  let let_example = "(let ((x 2)\n      (y [String] \"two\"))\n     (+ x x)\n     y)";

  html!(
      <div class="helplist">
          <h3>{blockquote("Examples")}</h3>
          <p>{"Function:"}</p>
          <p>{blockquote(function_example)}</p>
          <p>{"let:"}</p>
          <p>{blockquote(let_example)}</p>
      </div>
  )
}

fn place_linebreaks(s: &str) -> Vec<Html> {
  let mut v: Vec<Html> = Vec::new();
  for s in s.split("\n") {
    if s != "" {
      v.push(html!(<>{s}<br/></>));
    }
  }
  v
}

fn value_to_html(v: Result<Value>) -> Html {
  let (class, val) = match v {
    Ok(x) => ("value", format!("> {x}")),
    Err(e) => ("error", format!("{e}")),
  };
  let val = place_linebreaks(&val);
  html!(<blockquote class={class}><p>{val}</p></blockquote>)
}

impl Component for Model {
  type Message = Msg;
  type Properties = ();

  fn create(ctx: &Context<Self>) -> Self {
    Self {
      log: Vec::new(),
      input: "".to_owned(),
      state: State::default(),
      context: dpt_lisp::Context::default(),
    }
  }
  fn update(&mut self, ctx: &Context<Self>, msg: Self::Message) -> bool {
    match msg {
      Msg::Input(i) => {
        if complete_input(&i) {
          self.input = "".to_owned();
          let out = run1(&repl_to_span(&i), &mut self.state, &mut self.context);
          self.log.push(value_to_html(out));
        } else {
          self.input = i;
        }
      }
      Msg::Load => (),
    };
    true
  }

  fn changed(&mut self, ctx: &Context<Self>) -> bool {
    true
  }

  fn rendered(&mut self, ctx: &Context<Self>, first_render: bool) {}

  fn destroy(&mut self, ctx: &Context<Self>) {}

  fn view(&self, ctx: &Context<Self>) -> Html {
    let oninput = ctx.link().callback(move |e: InputEvent| {
      let input: HtmlTextAreaElement = e.target_unchecked_into();
      Msg::Input(input.value())
    });
    html! {
        <>
            <div class="infowindow">
        {info_window()}
        </div>
            <div class="term">
        // term input
            <div class="input-area">
            <textarea value={self.input.clone()} oninput={oninput}></textarea>
            <a href="https://github.com/CTHULHU-Jesus/DPT-Lisp">{"Github"}</a>
            </div>
        // term log
            <div class="log">
        {self.log.clone()}
        </div>
            </div>
            </>
    }
  }
}

fn main() {
  yew::start_app::<Model>();
}
