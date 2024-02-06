use dap::requests::Command;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AdapterError {
    #[error("Unhandled command")]
    UnhandledCommand { command: Command },

    #[error("Missing command")]
    MissingCommand,

    #[error("Missing configuration")]
    MissingConfiguration,

    #[error("Missing source path argument")]
    MissingSourcePathArgument,

    #[error("Missing breakpoint location")]
    MissingBreakpointLocation,

    #[error("Missing source map")]
    MissingSourceMap { pc: u64 },

    #[error("Unknown breakpoint")]
    UnknownBreakpoint { pc: u64 },

    #[error("Build failed")]
    BuildFailed { reason: String },

    #[error("No active test executor")]
    NoActiveTestExecutor,

    #[error("Test execution failed")]
    TestExecutionFailed {
        #[from]
        source: anyhow::Error,
    },
}