import NccCert.Unconditional
import NccCert.UnboundedGap

/-! Axiom audit: every theorem below should depend only on `propext`, `Classical.choice`, and
`Quot.sound` (the axioms OpenAI's Comparator challenge permits). -/

#print axioms NccCert.not_NCC_rate_one_of_exactFourier
#print axioms OAI.ExactFourier.main_theorem
#print axioms NccCert.not_NCC_rate_one
#print axioms NccCert.not_NCC_rate_of_exactFourier
#print axioms NccCert.not_NCC_rate

-- The statements, for the record.
#check @NccCert.not_NCC_rate_one_of_exactFourier
#check @NccCert.not_NCC_rate_one
#check @NccCert.not_NCC_rate_of_exactFourier
#check @NccCert.not_NCC_rate
#print NccCert.NCC_rate_one
#print NccCert.NCC_rate
#print NccCert.LinearCode
#print NccCert.ConcurrentFlow
#print NccCert.netOut
#print NccCert.tailOf
#print NccCert.headOf
