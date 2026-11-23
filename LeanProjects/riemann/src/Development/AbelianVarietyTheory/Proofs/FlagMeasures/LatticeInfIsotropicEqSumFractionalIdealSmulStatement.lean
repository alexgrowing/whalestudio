import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeInfIsotropicEqSumFractionalIdealSmul
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Ia
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_inf_isotropic_eq_sum_fractionalIdeal_smul : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (T : E) (G : Formalism.MainNotions.S.Lat.LFlag S r T) (Λ : Submodule (𝓞 E) S.V) (J : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E), (∀ a, J a ≠ 0) → (∀ (a : Fin r) (x : S.V), x ∈ Λ → x ∈ G.fl.Xa (a.val + 1) → G.fl.coefX x a ∈ J a) → (∀ (a : Fin r) (t : E), t ∈ J a → ∃ x ∈ Λ, x ∈ G.fl.Xa (a.val + 1) ∧ G.fl.coefX x a = t) → ∃ e' : Fin r → S.V, (∀ a, e' a - G.fl.e a ∈ G.fl.Xa a.val) ∧ Formalism.MainNotions.S.Lat.XLam Λ G = Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ J a ∧ y = x • e' a} := by
  first | exact @GlobalTheory.RowLatAssembly.xLam_eq_span | exact GlobalTheory.RowLatAssembly.xLam_eq_span | (intros; apply GlobalTheory.RowLatAssembly.xLam_eq_span <;> assumption)
