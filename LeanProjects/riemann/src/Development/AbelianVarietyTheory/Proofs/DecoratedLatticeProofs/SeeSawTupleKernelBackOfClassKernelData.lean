import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftsAllChartsEqClassSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactEntriesLeOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem castP_surjective {D : D7} {p q a b : ℕ} (hp : p = a) (hq : q = b) (Q : FP D.what₂.Tau a b) :
    ∃ P : PolF D q p, castP hp hq P = Q := by
  subst hp; subst hq
  refine ⟨Q, ?_⟩
  show MvPolynomial.rename _ Q = Q
  have : (fun v : D.what₂.Tau × Fin q × Fin p => (v.1, Fin.cast rfl v.2.1, Fin.cast rfl v.2.2)) = id := by
    funext v; simp
  rw [this, MvPolynomial.rename_id_apply]

theorem kBack_of_classData : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsK ρ t), c.Is → t.Is → ρ.Is → A.Is →
    (∀ j, j < D.R.m → t.cK j ≠ 0) → t.KBack := by
  intro D c t ρ A hc ht hρ hA hK j hj
  refine ⟨hK j hj, fun w => ?_⟩
  have hj1 : j + 1 ≤ D.R.m := hj
  have hab : ρ.N j ≤ ρ.N (j + 1) := (hρ.rk j hj).2
  obtain ⟨hB, ν, hν, -, hL⟩ := GlobalTheory.T.thetaLifts_all_charts_eq_classSum D c ρ hc hρ j hj1 hab
  haveI := hB
  haveI := hν
  set z : D.what₂.Tau → Matrix (Fin (ρ.N (j + 1))) (Fin (ρ.N (j + 1))) ℂ :=
    fun τ => (ρ.sc j τ)⁻¹ • (ρ.fr (j + 1) w).1 τ with hz
  obtain ⟨m, ys, Ps, hinv, havg⟩ := GlobalTheory.KJInf.subY_eq_sum_averages D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) hab (ρ.lam j)
    (ρ.n j) (GinfC (c.X j)) ν (fun k => ρ.r j (Nat.le_of_succ_le hj1) k.1) (hρ.uni j _) z
  set s0 : ℂ := (∏ τ, ((ρ.fr (j + 1) w).1 τ).det ^ ρ.sD j τ)⁻¹ with hs0
  let y : Fin m → c.Fr j := fun i => (ρ.fr j).symm ⟨ys i, hinv i⟩
  have hy : ∀ i, (ρ.fr j (y i)).1 = ys i := fun i => congrArg Subtype.val ((ρ.fr j).apply_symm_apply ⟨ys i, hinv i⟩)
  have hP : ∀ i, ∃ P : PolF D (c.X (j + 1)).rank (c.X j).rank,
      castP (ρ.hN j (Nat.le_of_succ_le hj1)) (ρ.hN (j + 1) hj1) P = (s0 * ∏ τ, (ys i τ).det ^ ρ.sS j τ) • Ps i :=
    fun i => castP_surjective _ _ _
  choose P hP using hP
  refine ⟨m, y, P, fun ψ hψ γ => ?_⟩
  have hsc : ∀ (i : Fin 1) τ, (ρ.fr (j + 1) ((fun _ => w) i)).1 τ = ρ.sc j τ • (fun _ => z) i τ := by
    intro i τ
    simp only [hz]
    rw [smul_smul, mul_inv_cancel₀ (hρ.sc j τ), one_smul]
  have hav : ∀ F ∈ Vn (ρ.lam j) (ρ.n j), ∀ Λ : FP D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) →ₗ[ℂ] ℂ,
      ∑ i, (∏ τ, ((ρ.fr j (y i)).1 τ).det ^ (-ρ.sS j τ)) *
        ∫ k, Λ (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj1) k.1 τ)⁻¹) (fun _ => 1)
          (castP (ρ.hN j (Nat.le_of_succ_le hj1)) (ρ.hN (j + 1) hj1) (P i))) *
          evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj1) k.1 τ * (ρ.fr j (y i)).1 τ) F ∂ν =
      ∑ i : Fin 1, (fun _ => s0) i * Λ (subY hab ((fun _ => z) i) F) := by
    intro F hF Λ
    clear hL
    have h0 := havg F hF Λ
    rw [Fin.sum_univ_one, ← h0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (∏ τ, (ys i τ).det ^ (-ρ.sS j τ)) * ∏ τ, (ys i τ).det ^ ρ.sS j τ = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [_root_.zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hinv i τ).ne_zero)]
    beta_reduce
    simp only [hy, hP, map_smul, smul_eq_mul, mul_assoc, integral_const_mul]
    linear_combination (s0 * ∫ k, Λ (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj1) k.1 τ)⁻¹) (fun _ => 1) (Ps i)) *
          evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj1) k.1 τ * ys i τ) F ∂ν) * e
  have hmain := hL m y P 1 (fun _ => z) (fun _ => w) (fun _ => s0) hsc hav t A ht hA ψ hψ γ
  have hs1 : s0 * ∏ τ, ((ρ.fr (j + 1) w).1 τ).det ^ ρ.sD j τ = 1 := by
    rw [hs0]
    refine inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ ((ρ.fr (j + 1) w).2 τ).ne_zero)
  rw [hmain, Fin.sum_univ_one]
  simp only [hs1, one_smul]

end GlobalTheory.SeeSaw

end
