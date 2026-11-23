import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveAndRangeOfPrismCoverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomEisensteinSpanAndNonZeroDivisorStatement
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.BSP.psi_nat : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B B' : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (N' : Type) [AddCommGroup N'] [Module B'.A N'] (V : Eval S B N) (V' : Eval S B' N') (k : Hom B B') (τ : N →ₛₗ[k.f] N'), (∀ (Q : Obj l ↥(OL K)) (a : Hom B' Q) (g : Hom bk.prism Q) (x : N), V'.v a g (τ x) = V.v (a.comp k) g x) → ∀ (t : B.A) (t' : B'.A) (Ψ : N →ₛₗ[B.D.φ] N) (Ψ' : N' →ₛₗ[B'.D.φ] N'), IsPsi V t Ψ → IsPsi V' t' Ψ' → ∀ x, t' ^ S.a • τ (Ψ x) = k.f t ^ S.a • Ψ' (τ x) := by
  intro l _ K bk d S B B' N _ _ N' _ _ V V' k τ hτ t t' Ψ Ψ' hΨ hΨ' x
  obtain ⟨C, h, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B'
  have hinj := (GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B' C N' V' h f hc).1
  have hE : BK.hf f bk.E ^ S.a ∈ nonZeroDivisors C.A := pow_mem (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C f).2 _
  apply hinj
  have L : V'.v h f (t' ^ S.a • τ (Ψ x)) = h.f t' ^ S.a • V.v (h.comp k) f (Ψ x) := by
    rw [map_smulₛₗ, map_pow, hτ]
  have R : V'.v h f (k.f t ^ S.a • Ψ' (τ x)) = h.f (k.f t) ^ S.a • V'.v h f (Ψ' (τ x)) := by
    rw [map_smulₛₗ, map_pow]
  have hkt : (h.comp k).f t = h.f (k.f t) := rfl
  have key : BK.hf f bk.E ^ S.a • V'.v h f (t' ^ S.a • τ (Ψ x)) =
      BK.hf f bk.E ^ S.a • V'.v h f (k.f t ^ S.a • Ψ' (τ x)) := by
    rw [L, R, smul_comm (BK.hf f bk.E ^ S.a) (h.f t' ^ S.a), smul_comm (BK.hf f bk.E ^ S.a) (h.f (k.f t) ^ S.a),
      hΨ (h.comp k) f x, hΨ' h f (τ x), hτ C h f x, smul_smul, smul_smul, hkt, mul_comm]
  funext i
  have hi := congrFun key i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact (mul_cancel_left_mem_nonZeroDivisors hE).1 hi
