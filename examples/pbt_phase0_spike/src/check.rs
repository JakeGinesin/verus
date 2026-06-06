pub struct NotProvided {
    pub x: u32,
}

pub fn fail_strategy() {
    let _ = verus_pbt_runtime::pbt_strategy::<NotProvided>();
}

pub fn fail_to_exec() {
    // IMPORTANT: invoke via fully-qualified trait syntax, not method syntax,
    // so the trait-bound `on_unimplemented` diagnostic fires instead of a
    // generic E0599 "no method found".
    let v = NotProvided { x: 0 };
    let _ = <NotProvided as verus_pbt_runtime::ToExecModel>::to_exec_model(&v);
}
