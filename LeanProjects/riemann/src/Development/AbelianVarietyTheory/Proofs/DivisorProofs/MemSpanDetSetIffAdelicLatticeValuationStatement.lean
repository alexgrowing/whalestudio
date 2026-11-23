import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanDetSetIffAdelicLatticeValuation
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_detSet_iff_adelicLattice_valuation : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (L : Submodule (𝓞 E) (Fin n → E)), (∀ x : Fin n → E, x ∈ L ↔ ∀ (i : Fin n) (Q : HeightOneSpectrum (𝓞 E)), Valued.v (((g⁻¹).1.mulVec (fun j => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x j)) i) Q) ≤ 1) → ∀ x : E, x ∈ Submodule.span (𝓞 E) (detSet L) ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ Valued.v (g.1.det Q) := by
  first | exact @GlobalTheory.AdelicDetSpan.mem_span_detSet_iff | exact GlobalTheory.AdelicDetSpan.mem_span_detSet_iff | (intros; apply GlobalTheory.AdelicDetSpan.mem_span_detSet_iff <;> assumption)
