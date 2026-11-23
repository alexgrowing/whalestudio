import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExactFunctorPhiGammaOfFrames
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exact_functor_phiGamma_of_frames : ∀ {k G : Type} [Field k] [Group G] {Rk : Type} [CommRing Rk] [Algebra k Rk] {l n : ℕ} [NeZero n] (R : RingPG k l) (κ : k⸨X⸩ →+* Rk) (φ : Rk →ₐ[k] Rk) (a : G → (Rk →ₐ[k] Rk)) (g₀ : G) (ε : ZMod n → Rk) (Obj : Ob k G → Prop) (β : ∀ A : Ob k G, ZMod n → (Vc k A.m →+ Rk ⊗[k] (Fin A.m → k))), IsFrames R κ φ a g₀ ε Obj β → ∃ F : DFun R n G, F.Obj = Obj ∧ (∀ A, Obj A → ∀ i x, β A i ((F.D A).φ i x) = Phi φ A.m (β A (i - 1) x)) ∧ (∀ A, Obj A → ∀ i x, β A i ((F.D A).γ i x) = Act a A g₀ (β A i x)) ∧ (∀ A B f, Obj A → Obj B → IsHom A B f → ∀ i x, β B i (F.map A B f i x) = f.baseChange Rk (β A i x)) ∧ ∀ i, β (chr 1) i (F.unit i) = ε i ⊗ₜ[k] (fun _ => 1) := by
  first | exact @GlobalTheory.RedFun.exists_dfun_of_frames | exact GlobalTheory.RedFun.exists_dfun_of_frames | (intros; apply GlobalTheory.RedFun.exists_dfun_of_frames <;> assumption)
