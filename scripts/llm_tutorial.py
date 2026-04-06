"""
LiteLLM Tutorial for proyecto-isabelle
======================================

This script demonstrates how to use the LLM router submodule to interact
with various LLM providers through a unified interface.

Environment Variables
---------------------
Create a `.env` file in the project root with the API keys you need:

    # OpenAI (for GPT models)
    OPENAI_API_KEY=sk-...

    # Anthropic (for Claude models)
    ANTHROPIC_API_KEY=sk-ant-...

    # Google (for Gemini models)
    GOOGLE_API_KEY=AI...

    # Local model endpoints (optional, these are the defaults)
    OLLAMA_BASE_URL=http://localhost:11434
    LM_STUDIO_BASE_URL=http://localhost:1234/v1

    # Default settings (optional)
    LLM_DEFAULT_MODEL=gpt-4o-mini
    LLM_DEFAULT_TIMEOUT=60

You only need to set the API keys for the providers you want to use.
For local models (Ollama, LM Studio), no API key is needed.
"""

from enum import Enum
from typing import Annotated, Optional

import typer
from rich.console import Console
from rich.markdown import Markdown
from rich.panel import Panel
from rich.syntax import Syntax
from rich.table import Table

from proyecto_isabelle.query import llm
from proyecto_isabelle.query.llm import LLMClient, LLMConfig, LLMResponse, Message

app = typer.Typer(
    name="llm-tutorial",
    help="Tutorial and examples for the proyecto-isabelle LLM module.",
    rich_markup_mode="rich",
)
console = Console()


class Provider(str, Enum):
    openai = "openai"
    anthropic = "anthropic"
    gemini = "gemini"
    ollama = "ollama"
    lm_studio = "lm-studio"


PROVIDER_MODELS = {
    Provider.openai: "gpt-4o-mini",
    Provider.anthropic: "claude-3-5-sonnet-20241022",
    Provider.gemini: "gemini/gemini-1.5-flash",
    Provider.ollama: "ollama/llama3.2",
    Provider.lm_studio: "lm-studio/local-model",
}


def display_response(response: LLMResponse, title: str = "Response") -> None:
    """Display an LLM response with rich formatting."""
    if response.success:
        content = response.content or "(empty response)"
        panel = Panel(
            Markdown(content),
            title=f"[green]{title}[/green]",
            border_style="green",
            subtitle=f"[dim]Model: {response.model}[/dim]",
        )
        console.print(panel)

        if response.usage:
            console.print(
                f"  [dim]Tokens: {response.usage.prompt_tokens} prompt + "
                f"{response.usage.completion_tokens} completion = "
                f"{response.usage.total_tokens} total[/dim]"
            )
    else:
        panel = Panel(
            f"[red]{response.error}[/red]",
            title="[red]Error[/red]",
            border_style="red",
        )
        console.print(panel)


def show_code(code: str, title: str = "Code") -> None:
    """Display code with syntax highlighting."""
    syntax = Syntax(code, "python", theme="monokai", line_numbers=True)
    console.print(Panel(syntax, title=f"[blue]{title}[/blue]", border_style="blue"))


@app.command()
def info():
    """Show environment setup information and model conventions."""
    # Environment variables table
    env_table = Table(title="Environment Variables", show_header=True)
    env_table.add_column("Variable", style="cyan")
    env_table.add_column("Description", style="white")
    env_table.add_column("Required", style="yellow")

    env_table.add_row("OPENAI_API_KEY", "OpenAI API key (sk-...)", "For OpenAI models")
    env_table.add_row(
        "ANTHROPIC_API_KEY", "Anthropic API key (sk-ant-...)", "For Claude models"
    )
    env_table.add_row("GOOGLE_API_KEY", "Google API key", "For Gemini models")
    env_table.add_row(
        "OLLAMA_BASE_URL", "Ollama endpoint (default: localhost:11434)", "Optional"
    )
    env_table.add_row(
        "LM_STUDIO_BASE_URL", "LM Studio endpoint (default: localhost:1234)", "Optional"
    )
    env_table.add_row("LLM_DEFAULT_MODEL", "Default model to use", "Optional")
    env_table.add_row("LLM_DEFAULT_TIMEOUT", "Request timeout in seconds", "Optional")

    console.print(env_table)
    console.print()

    # Model conventions table
    model_table = Table(title="Model Name Conventions", show_header=True)
    model_table.add_column("Provider", style="cyan")
    model_table.add_column("Format", style="yellow")
    model_table.add_column("Examples", style="green")

    model_table.add_row("OpenAI", "Direct", "gpt-4, gpt-4o, gpt-4o-mini")
    model_table.add_row(
        "Anthropic", "Direct", "claude-3-opus-20240229, claude-3-5-sonnet-20241022"
    )
    model_table.add_row(
        "Gemini", "gemini/ prefix", "gemini/gemini-pro, gemini/gemini-1.5-flash"
    )
    model_table.add_row(
        "Ollama", "ollama/ prefix", "ollama/llama2, ollama/mistral, ollama/codellama"
    )
    model_table.add_row("LM Studio", "lm-studio/ prefix", "lm-studio/local-model")

    console.print(model_table)


@app.command()
def test(
    provider: Annotated[
        Provider,
        typer.Argument(help="The provider to test"),
    ],
):
    """Test a specific LLM provider with a simple prompt."""
    model = PROVIDER_MODELS[provider]

    console.print(
        Panel(
            f"Testing [cyan]{provider.value}[/cyan] with model [yellow]{model}[/yellow]",
            title="Provider Test",
        )
    )

    with console.status(f"[bold green]Querying {provider.value}...[/bold green]"):
        response = llm.ask(
            prompt="Say 'Hello!' and nothing else.",
            model=model,
        )

    display_response(response, title=f"{provider.value} Response")


@app.command()
def ask(
    prompt: Annotated[str, typer.Argument(help="The prompt to send to the LLM")],
    model: Annotated[
        Optional[str],
        typer.Option("--model", "-m", help="Model to use (default: gpt-4o-mini)"),
    ] = None,
    system: Annotated[
        Optional[str],
        typer.Option("--system", "-s", help="System prompt"),
    ] = None,
    temperature: Annotated[
        float,
        typer.Option("--temperature", "-t", help="Sampling temperature (0.0-2.0)"),
    ] = 0.7,
):
    """Send a prompt to an LLM and display the response."""
    model_display = model or "default"
    console.print(f"[dim]Model: {model_display} | Temperature: {temperature}[/dim]")

    if system:
        console.print(f"[dim]System: {system}[/dim]")

    console.print()

    with console.status("[bold green]Thinking...[/bold green]"):
        response = llm.ask(
            prompt=prompt,
            model=model,
            system=system,
            temperature=temperature,
        )

    display_response(response)


@app.command()
def example(
    number: Annotated[
        int,
        typer.Argument(help="Example number to run (1-6)", min=1, max=6),
    ] = 1,
):
    """Run a specific tutorial example."""
    examples = {
        1: ("Simple ask()", _example_simple_ask),
        2: ("ask() with system prompt", _example_with_system_prompt),
        3: ("Multi-turn conversation", _example_multi_turn),
        4: ("Specific model selection", _example_specific_model),
        5: ("Custom client configuration", _example_custom_client),
        6: ("Error handling", _example_error_handling),
    }

    title, func = examples[number]
    console.print(
        Panel(f"[bold]{title}[/bold]", title=f"Example {number}", border_style="blue")
    )
    func()


@app.command()
def examples():
    """Run all tutorial examples."""
    console.print(
        Panel(
            "[bold]Running all examples[/bold]\n\n"
            "[dim]Make sure you have set up your API keys in .env[/dim]",
            title="Tutorial Examples",
            border_style="blue",
        )
    )

    example_list = [
        ("Simple ask()", _example_simple_ask),
        ("ask() with system prompt", _example_with_system_prompt),
        ("Multi-turn conversation", _example_multi_turn),
        ("Specific model selection", _example_specific_model),
        ("Custom client configuration", _example_custom_client),
        ("Error handling", _example_error_handling),
    ]

    for i, (title, func) in enumerate(example_list, 1):
        console.print()
        console.rule(f"[bold blue]Example {i}: {title}[/bold blue]")
        try:
            func()
        except Exception as e:
            console.print(f"[red]Failed: {e}[/red]")
            console.print(
                "[dim](This may be expected if API keys are not configured)[/dim]"
            )


def _example_simple_ask():
    """Example 1: Basic usage."""
    code = """response = llm.ask("What is 2 + 2? Answer in one word.")
print(response.content)"""
    show_code(code, "Simple ask()")

    with console.status("[bold green]Running...[/bold green]"):
        response = llm.ask("What is 2 + 2? Answer in one word.")

    display_response(response)


def _example_with_system_prompt():
    """Example 2: Using a system prompt."""
    code = """response = llm.ask(
    prompt="What is the capital of France?",
    system="You are a helpful assistant. Answer concisely.",
    temperature=0.3,
)"""
    show_code(code, "ask() with system prompt")

    with console.status("[bold green]Running...[/bold green]"):
        response = llm.ask(
            prompt="What is the capital of France?",
            system="You are a helpful assistant. Answer concisely in one sentence.",
            temperature=0.3,
        )

    display_response(response)


def _example_multi_turn():
    """Example 3: Multi-turn conversation."""
    code = """messages = [
    Message(role="system", content="You are a math tutor."),
    Message(role="user", content="I want to learn about prime numbers."),
    Message(role="assistant", content="Great choice! Prime numbers are..."),
    Message(role="user", content="Why is 2 special?"),
]
response = llm.complete(messages)"""
    show_code(code, "Multi-turn conversation")

    messages = [
        Message(role="system", content="You are a math tutor. Be encouraging."),
        Message(role="user", content="I want to learn about prime numbers."),
        Message(
            role="assistant",
            content="Great choice! Prime numbers are fascinating. A prime number is a natural number greater than 1 that has no positive divisors other than 1 and itself.",
        ),
        Message(role="user", content="Why is 2 special?"),
    ]

    # Show the conversation
    console.print("[dim]Conversation history:[/dim]")
    for msg in messages:
        style = {"system": "yellow", "user": "cyan", "assistant": "green"}[msg.role]
        console.print(f"  [{style}]{msg.role}:[/{style}] {msg.content[:60]}...")

    console.print()

    with console.status("[bold green]Running...[/bold green]"):
        response = llm.complete(messages, temperature=0.7, max_tokens=150)

    display_response(response)


def _example_specific_model():
    """Example 4: Using a specific model."""
    code = """response = llm.ask(
    prompt="Say 'Hello from' followed by your model name.",
    model="gpt-4o-mini",
)"""
    show_code(code, "Specific model selection")

    with console.status("[bold green]Running...[/bold green]"):
        response = llm.ask(
            prompt="Say 'Hello from' followed by your model name.",
            model="gpt-4o-mini",
        )

    display_response(response)


def _example_custom_client():
    """Example 5: Custom client configuration."""
    code = """config = LLMConfig(
    llm_default_model="gpt-4o-mini",
    llm_default_timeout=30,
)
client = LLMClient(config=config)
response = client.ask("What's the weather like?")"""
    show_code(code, "Custom client configuration")

    config = LLMConfig(
        llm_default_model="gpt-4o-mini",
        llm_default_timeout=30,
    )
    client = LLMClient(config=config)

    with console.status("[bold green]Running...[/bold green]"):
        response = client.ask("What's the weather like? (Just say you don't know)")

    display_response(response)


def _example_error_handling():
    """Example 6: Error handling."""
    code = """response = llm.ask(
    prompt="Hello",
    model="non-existent-model-12345",
)
if not response.success:
    print(f"Error: {response.error}")"""
    show_code(code, "Error handling")

    console.print("[dim]Trying to use a non-existent model...[/dim]")

    with console.status("[bold green]Running...[/bold green]"):
        response = llm.ask(
            prompt="Hello",
            model="non-existent-model-12345",
        )

    display_response(response, title="Expected Error")
    if not response.success:
        console.print("[green]Error was handled gracefully![/green]")


if __name__ == "__main__":
    app()
