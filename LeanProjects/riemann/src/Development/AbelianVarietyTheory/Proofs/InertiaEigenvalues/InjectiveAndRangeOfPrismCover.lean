import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteProjectiveModuleElementDescentEqualizerStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

noncomputable def matCoordMap {A B : Type} [CommRing A] [CommRing B] {d : ℕ} (q : A →+* B)
    (M : Matrix (Fin d) (Fin d) B) : (Fin d → A) →ₛₗ[q] (Fin d → B) where
  toFun z := M.mulVec fun i => q (z i)
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp
  map_smul' a x := by
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp

theorem Eval.effective_of_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C), Cover h → Function.Injective (V.v h f) ∧ ∀ z : Fin d → C.A, (∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → (fun i => p.f (z i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (z i)) → ∃ y, V.v h f y = z := by
  intro l _ K bk d S B C N _ _ V h f hc
  obtain ⟨D, p, q, hpo⟩ := hc.stable.po C h
  obtain ⟨hinj, hrange⟩ := GlobalTheory.T.prism_cover_injective_and_descent l _ B C h hc
  haveI := V.fin
  haveI := V.proj
  have hcomm : p.f.comp h.f = q.f.comp h.f := congrArg Hom.f hpo.comm
  have key := GlobalTheory.T.finite_projective_module_element_descent_equalizer B.A C.A D.A h.f p.f q.f hcomm hinj (hrange D p q hpo) N (Fin d → C.A) (Fin d → D.A)
    (V.v h f) (matCoordMap p.f 1) (matCoordMap q.f (S.ε (p.comp f) (q.comp f))) (V.v (p.comp h) (p.comp f))
    (V.bc h f) (V.bc (p.comp h) (p.comp f))
    (fun x => by
      change V.v (p.comp h) (p.comp f) x = (1 : Matrix (Fin d) (Fin d) D.A).mulVec fun i => p.f (V.v h f x i)
      rw [Matrix.one_mulVec]
      funext i
      exact V.v_nat p h f x i)
    (fun x => by
      change V.v (p.comp h) (p.comp f) x = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (V.v h f x i)
      have e : ∀ a a' : Hom B D, a = a' → V.v a (q.comp f) x = V.v a' (q.comp f) x := by
        intro a a' e; subst e; rfl
      rw [V.v_ε (p.comp h) (p.comp f) (q.comp f) x, e _ _ hpo.comm]
      congr 1
      funext i
      exact V.v_nat q h f x i)
  refine ⟨key.1, fun z hz => key.2 z ?_⟩
  change (1 : Matrix (Fin d) (Fin d) D.A).mulVec (fun i => p.f (z i)) =
    (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (z i)
  rw [Matrix.one_mulVec]
  exact hz D p q hpo.comm

end GlobalTheory.BSP
