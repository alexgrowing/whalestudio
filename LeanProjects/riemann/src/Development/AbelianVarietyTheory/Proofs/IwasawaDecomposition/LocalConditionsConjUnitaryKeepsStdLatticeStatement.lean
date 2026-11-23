import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConditionsConjUnitaryKeepsStdLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalCondMoveDecoratedLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localConditions_conj_unitary_keepsStdLattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (n : ℕ) (t s : GA B n)
    (x : ∀ w : (B.primes X).vGs, GL (Fin n) (𝓞 B.fields.E ⧸ w.1.asIdeal)) (h : GLG B.fields.E n (B.primes X).vGs),
    (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf t p ∧ p.deco.1.N = stdLat B.fields.E n) →
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∈ v.asIdeal → bc (prV (E := B.host.E) v) t = 1) →
    (∀ (w : (B.primes X).vGs) (r j : Fin n), HasRes w.1 (adAt B.host.F w.1 ((t : Matrix (Fin n) (Fin n) _) r j)) ((x w).1 r j)) →
    (LocalCondMoveDecoratedLattice u n (t⁻¹ * s * t) h ↔ LocalCondMoveDecoratedLattice u n s (fun w => x w * h w * (x w)⁻¹)) := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.conj_unitary_preserves_stdLat_of_ptOf | exact GlobalTheory.Mem.Col2.TC.ChTw.Match.conj_unitary_preserves_stdLat_of_ptOf | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.Match.conj_unitary_preserves_stdLat_of_ptOf <;> assumption)
