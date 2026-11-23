import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingleMemLocalLatticeCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBoundAbsLocalLatticeCompletionEntriesStatement

open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.Core.Rk.HgtFin

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.Doubling Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem absNorm_le_one_of_absFin_le_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E), absFin F v x ≤ 1 → ‖Algebra.norm (Fv F v) x‖₊ ≤ 1 := by
  intro F E _ _ _ _ _ σ hσ v x hx
  have hN := GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := Fv F v) x
  have e1 : absFin F v (algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.norm (Fv F v) x)) =
      ‖Algebra.norm (Fv F v) x‖₊ := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact absFin_tmul_one F v _
  have hs : absFin F v (sigR (Fv F v) σ x) ≤ absFin F v x := by
    refine (absFin_le_iff F v).2 fun τ => ?_
    have e2 : ∀ w, finEmb F v τ (sigR (Fv F v) σ w) = finEmb F v ((τ : E →ₐ[F] FvBar F v).comp σ) w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [sigR]
      | add y z hy hz => simp only [map_add, hy, hz]
    rw [e2]
    exact le_absFin F v _ x
  rw [← e1, hN]
  calc _ ≤ absFin F v x * absFin F v (sigR (Fv F v) σ x) := absFin_mul_le F v _ _
    _ ≤ 1 * 1 := mul_le_mul' hx (hs.trans hx)
    _ = 1 := one_mul 1

theorem absFin_tmul_one_mul (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) (y : Fv F v ⊗[F] E) :
    absFin F v (c ⊗ₜ[F] (1 : E) * y) = ‖c‖₊ * absFin F v y := by
  simp only [absFin, map_mul, finEmb_tmul, map_one, mul_one, absBar_mul, absBar_algebraMap]
  rw [NNReal.mul_finset_sup]

theorem absFin_le_one_of_pow_le {v : HeightOneSpectrum (𝓞 F)} {x : Fv F v ⊗[F] E} {C : ℝ≥0}
    (h : ∀ k : ℕ, absFin F v (x ^ k) ≤ C) : absFin F v x ≤ 1 := by
  refine (absFin_le_iff F v).2 fun τ => ?_
  by_contra hlt
  push_neg at hlt
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop C).exists
  have := (le_absFin F v τ (x ^ k)).trans (h k)
  have hpw : ∀ (z : FvBar F v) (m : ℕ), absBar F v (z ^ m) = absBar F v z ^ m := by
    intro z m
    induction m with
    | zero => simpa using absBar_algebraMap F v 1
    | succ m ih => rw [pow_succ, absBar_mul, ih, pow_succ]
  rw [map_pow, hpw] at this
  exact absurd this (not_le.2 hk)

theorem absFin_det_le (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    absFin F v M.det ≤ normFin F v M ^ n := by
  rw [Matrix.det_apply]
  refine absFin_sum_le F v _ _ fun s _ => ?_
  have hp : absFin F v (∏ i, M (s i) i) ≤ normFin F v M ^ n :=
    calc absFin F v (∏ i, M (s i) i) ≤ ∏ i, absFin F v (M (s i) i) :=
          Finset.le_prod_of_submultiplicative _ (absFin_one F v).le (absFin_mul_le F v) _ _
      _ ≤ ∏ _i : Fin n, normFin F v M := Finset.prod_le_prod' fun i _ => absFin_le_normFin F v M _ _
      _ = normFin F v M ^ n := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
  · rw [h, one_smul]; exact hp
  · rw [h, Units.neg_smul, one_smul, absFin_neg]; exact hp

theorem normDet_le_one {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hM : ∀ x ∈ latLoc F L v, M *ᵥ x ∈ latLoc F L v) : ‖Algebra.norm (Fv F v) M.det‖₊ ≤ 1 := by
  obtain ⟨c, hc, hcL⟩ := GlobalTheory.T.exists_single_mem_localLatticeCompletion L v
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_bound_abs_localLatticeCompletion_entries L v
  have hpow : ∀ k : ℕ, ∀ x ∈ latLoc F L v, (M ^ k) *ᵥ x ∈ latLoc F L v := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih => intro x hx; rw [pow_succ, ← Matrix.mulVec_mulVec]; exact ih _ (hM _ hx)
  have hent : ∀ k i j, absFin F v ((M ^ k) i j) ≤ C / ‖c‖₊ := by
    intro k i j
    have h1 := hC _ (hpow k _ (hcL j)) i
    rw [Matrix.mulVec_single] at h1
    change absFin F v ((M ^ k) i j * c ⊗ₜ[F] (1 : E)) ≤ C at h1
    rw [mul_comm, absFin_tmul_one_mul] at h1
    rw [le_div_iff₀ (nnnorm_pos.2 hc), mul_comm]
    exact h1
  have hdet : ∀ k : ℕ, absFin F v (M.det ^ k) ≤ (C / ‖c‖₊) ^ n := fun k => by
    rw [← Matrix.det_pow]
    exact (absFin_det_le v _).trans (pow_le_pow_left' ((normFin_le_iff F v).2 (hent k)) n)
  exact absNorm_le_one_of_absFin_le_one hσ v _ (absFin_le_one_of_pow_le hdet)

theorem levi_mulVec_mem (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F))
    (y : GLoc σ J v) (p : siegelH (Fv F v) σ Q) {k : GLoc σ Q v} (hk : k ∈ KFin σ Q L v)
    (e : ioH _ σ hQ (y, 1) = p * k) {x : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc F L v) :
    leviMat finSumFinEquiv (matHom _ σ Q p).1 *ᵥ x ∈ latLoc F L v := by
  have hp : KeepsDiag finSumFinEquiv (matHom (Fv F v) σ Q p).1 :=
    (mem_siegelOf (e := finSumFinEquiv) (mat := matHom (Fv F v) σ Q)).1 p.2
  have hk' := inv_mem hk
  have ek : k⁻¹ = ioH _ σ hQ (y⁻¹, 1) * p := by
    have : k = (p : GLoc σ Q v)⁻¹ * ioH _ σ hQ (y, 1) := by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this, mul_inv_rev, inv_inv, ← map_inv, Prod.inv_mk, inv_one]
  have h1 : pairVec finSumFinEquiv x x ∈ latLoc F (sumLat finSumFinEquiv L L) v := by
    rw [latLoc_sumLat]; exact (pairVec_mem_sumLat _).2 ⟨hx, hx⟩
  have h2 := (mem_stabLoc.1 hk' _).1 h1
  have e3 : (matHom _ σ Q (ioH _ σ hQ (y⁻¹, 1))).1 =
      blkMat finSumFinEquiv (matHom _ σ J y⁻¹).1 (matHom _ σ J 1).1 := rfl
  rw [ek, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hp.mulVec_diag, e3, blkMat_mulVec, latLoc_sumLat,
    pairVec_mem_sumLat] at h2
  simpa using h2.2

theorem hgtFin_ioH_le_one {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E))
    [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)) (y : GLoc σ J v) :
    hgtFin σ Q L v (ioH _ σ hQ (y, 1)) ≤ 1 := by
  by_cases h : ∃ p : siegelH (Fv F v) σ Q, ∃ k ∈ KFin σ Q L v, ioH _ σ hQ (y, 1) = p * k
  · obtain ⟨p, k, hk, e⟩ := h
    rw [e, hgtFin_mul p hk, absEv_apply]
    exact normDet_le_one hσ L v _ fun x hx => levi_mulVec_mem σ hQ L v y p hk e hx
  · show iwAbs _ _ _ ≤ 1
    rw [iwAbs, dif_neg h]

end GlobalTheory.Core.Rk.HgtFin

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Rk.IP

theorem hgtFin_ioAt_le_one : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (v : FinPl D) (y : Gv A v), hgtFin D.sp.cm.sig (dblSp A).gram L v (ioAt A v y) ≤ 1 := by
  intro D A L hL v y
  haveI := hL.1
  exact GlobalTheory.Core.Rk.HgtFin.hgtFin_ioH_le_one (isCMExt_host D) (gram_hdbl A) L v y

end GlobalTheory.Core.Rk.IP
