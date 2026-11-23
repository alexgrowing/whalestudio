import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLat
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.AtNormRep

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh Formalism.L2.SG.Pf.StabIntLat

namespace Formalism.L2.SG.Pf.StabIntCong

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem intE_iff (x : D.host.E) : Formalism.L2.SG.Pf.StabilizerIndexVolumes.IntE x ↔ x ∈ (1 : FI D) := by
  rw [FractionalIdeal.mem_one_iff]
  exact ⟨fun ⟨o, h⟩ => ⟨o, h⟩, fun ⟨o, h⟩ => ⟨o, h⟩⟩

theorem one_mem_one_FI : (1 : D.host.E) ∈ (1 : FI D) := (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩

theorem natCast_mem_one_FI (n : ℕ) : (n : D.host.E) ∈ (1 : FI D) := (FractionalIdeal.mem_one_iff _).2 ⟨n, map_natCast _ _⟩

theorem mul_mem_one_FI {x y : D.host.E} (hx : x ∈ (1 : FI D)) (hy : y ∈ (1 : FI D)) : x * y ∈ (1 : FI D) := by
  have := FractionalIdeal.mul_mem_mul hx hy; rwa [one_mul] at this

abbrev ddI (D : D7) : Ideal (𝓞 D.host.E) :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))

theorem ddS_eq : ddS D = (ddI D : FI D) := rfl

theorem ddS_pow_le_one (h : ℕ) : ddS D ^ h ≤ 1 := by
  rw [ddS_eq, ← FractionalIdeal.coeIdeal_pow]; exact FractionalIdeal.coeIdeal_le_one

theorem one_le_ddPow (h : ℕ) : (1 : FI D) ≤ ddPow D h := by
  unfold ddPow
  rw [zpow_neg, zpow_natCast]
  have := FractionalIdeal.inv_anti_mono (pow_ne_zero h (ddS_ne (D := D))) one_ne_zero (ddS_pow_le_one (D := D) h)
  rwa [inv_one] at this

theorem mem_dd_of_int {h : ℕ} {x : D.host.E} (hx : x ∈ (1 : FI D)) : x ∈ ddPow D h := one_le_ddPow h hx

theorem mem_qd_of_qq {h : ℕ} {x : D.host.E} (hx : x ∈ (qq D : FI D)) : x ∈ qdPow D h := by
  unfold qdPow
  have := FractionalIdeal.mul_mem_mul hx (mem_dd_of_int (h := h) one_mem_one_FI)
  rwa [mul_one] at this

theorem mul_mem_qq {x y : D.host.E} (hx : x ∈ (1 : FI D)) (hy : y ∈ (qq D : FI D)) : x * y ∈ (qq D : FI D) := by
  have := FractionalIdeal.mul_mem_mul hx hy; rwa [one_mul] at this

theorem qq_le_one {x : D.host.E} (hx : x ∈ (qq D : FI D)) : x ∈ (1 : FI D) := FractionalIdeal.coeIdeal_le_one hx

theorem gS_mem_qqE (x : D.host.E) (hx : x ∈ (1 : FI D)) : ((gS D : ℕ) : D.host.E) * x ∈ (qq D : FI D) := by
  obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  rw [FractionalIdeal.mem_coeIdeal]
  exact ⟨(gS D : ℕ) * o, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _), by simp⟩

theorem conjF_mem_one_FI {x : D.host.E} (hx : x ∈ (1 : FI D)) : D.conjF x ∈ (1 : FI D) := by
  obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  rw [FractionalIdeal.mem_one_iff]
  have hi : IsIntegral ℤ (D.conjF (algebraMap (𝓞 D.host.E) D.host.E o)) :=
    (RingOfIntegers.isIntegral_coe o).map (D.conjF.toRingHom.toIntAlgHom)
  exact ⟨⟨_, hi⟩, rfl⟩

theorem conj_mem_qq {x : D.host.E} (hx : x ∈ (qq D : FI D)) : D.conjF x ∈ (qq D : FI D) := by
  obtain ⟨o, ho, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 ho
  have ht : D.conjF (algebraMap (𝓞 D.host.E) D.host.E t) ∈ (1 : FI D) :=
    conjF_mem_one_FI ((FractionalIdeal.mem_one_iff _).2 ⟨t, rfl⟩)
  rw [map_mul, map_mul, map_natCast, map_natCast, mul_comm]
  exact gS_mem_qqE _ ht

theorem absNorm_mem_ideal : ((Ideal.absNorm (ddI D) : ℕ) : D.host.E) ∈ ddS D := by
  rw [ddS_eq, FractionalIdeal.mem_coeIdeal]
  exact ⟨_, Ideal.absNorm_mem (ddI D), map_natCast _ _⟩

theorem absNorm_ddI_ne_zero : Ideal.absNorm (ddI D) ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  intro h
  apply ddS_ne (D := D)
  rw [ddS_eq, h, FractionalIdeal.coeIdeal_bot]

theorem pow_mem_ddS (k : ℕ) : ((Ideal.absNorm (ddI D) : ℕ) : D.host.E) ^ k ∈ ddS D ^ k := by
  induction k with
  | zero => simp only [pow_zero]; exact one_mem_one_FI
  | succ k ih => rw [pow_succ, pow_succ]; exact FractionalIdeal.mul_mem_mul ih absNorm_mem_ideal

theorem clear_den (k : ℕ) {x : D.host.E} (hx : x ∈ ddPow D k) :
    ((Ideal.absNorm (ddI D) : ℕ) : D.host.E) ^ k * x ∈ (1 : FI D) := by
  have := FractionalIdeal.mul_mem_mul (pow_mem_ddS k) hx
  unfold ddPow at this
  rwa [← zpow_natCast, ← zpow_add₀ (ddS_ne (D := D)), add_neg_cancel, zpow_zero] at this

theorem aBddOf (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) :
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.ABddOf D u u' F0 what₂ δ M := by
  intro _ _ hA t w F' L U _ _ _ _
  refine ⟨Ideal.absNorm (ddI D) ^ D.R.rS, pow_ne_zero _ absNorm_ddI_ne_zero, fun h hh i j => ?_⟩
  rw [intE_iff]
  have hS := (stabIntShape D δ M hA u u' w h).1 hh
  obtain ⟨hlo, b, hb, hW, hE⟩ := hS
  push_cast
  rcases lt_trichotomy j i with hji | rfl | hij
  · have hk : i.val - j.val ≤ D.R.rS := by have := i.isLt; omega
    rw [show ((Ideal.absNorm (ddI D) : ℕ) : D.host.E) ^ D.R.rS =
        ((Ideal.absNorm (ddI D) : ℕ) : D.host.E) ^ (D.R.rS - (i.val - j.val)) *
          ((Ideal.absNorm (ddI D) : ℕ) : D.host.E) ^ (i.val - j.val) by
        rw [← pow_add, Nat.sub_add_cancel hk], mul_assoc]
    exact mul_mem_one_FI (by rw [← Nat.cast_pow]; exact natCast_mem_one_FI _) (clear_den _ (hE i j hji).1)
  · rw [(hlo _ _).2 rfl, mul_one, ← Nat.cast_pow]; exact natCast_mem_one_FI _
  · rw [(hlo i j).1 hij, mul_zero]; exact FractionalIdeal.zero_mem _

abbrev Sint (D : D7) : Subring D.host.E := (integralClosure ℤ D.host.E).toSubring

theorem mem_Sint_iff (x : D.host.E) : x ∈ Sint D ↔ x ∈ (1 : FI D) := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · intro h; exact ⟨⟨x, h⟩, rfl⟩
  · rintro ⟨o, rfl⟩; exact o.2

theorem sign_mem_one (a c : Fin (D.R.rS + 1)) : (sgm a c : D.host.E) ∈ (1 : FI D) := by
  rcases sgm_cases a c with e | e
  · rw [e]; exact one_mem_one_FI
  · rw [e]; exact (1 : FI D).coeToSubmodule.neg_mem one_mem_one_FI

theorem aCong (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) :
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.ACong D u u' F0 what₂ δ M := by
  intro _ hA t w F' L U _ _ _ _
  refine ⟨gS D, fun h0 => gS_ne (D := D) (by rw [h0]; simp), fun a ha hc => ?_⟩
  obtain ⟨hlo, b, hb, hW⟩ := ha
  have hq : ∀ i j, (a : MatR D) i j - (1 : MatR D) i j ∈ (qq D : FI D) := by
    intro i j
    have h1 := (intE_iff _).1 (hc i j)
    have := gS_mem_qqE _ h1
    rwa [mul_div_cancel₀ _ gS_ne] at this
  rw [mem_stabInt_iff_X δ M hA u u' w a hlo hb hW]
  obtain ⟨-, hU, hB⟩ := X_of_st w hlo hb hW
  set X := (ptMat w)⁻¹ * (a : MatR D) * ptMat w with hXdef
  have hXe : ∀ c d, X c d - (1 : MatR D) c d ∈ (qq D : FI D) := by
    intro c d
    by_cases hs : blkOf w.1 c.val = blkOf w.1 d.val
    · have hcv : cv w c = cv w d := pval_eq_blk w c d hs
      have hone : (1 : MatR D) c d = (1 : MatR D) (pinv w c) (pinv w d) := by
        by_cases hcd : c = d
        · rw [hcd]; simp
        · have : pinv w c ≠ pinv w d := fun e => hcd (pinv_inj w e)
          rw [Matrix.one_apply_ne hcd, Matrix.one_apply_ne this]
      rw [hXdef, conj_apply, hcv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (cv_ne w d), one_mul, hone]
      exact hq _ _
    · have hcd : c ≠ d := fun e => hs (by rw [e])
      rw [hB c d hs, Matrix.one_apply_ne hcd, sub_zero]
      exact FractionalIdeal.zero_mem _
  have hX1 : ∀ c d, X c d ∈ (1 : FI D) := by
    intro c d
    have := (1 : FI D).coeToSubmodule.add_mem (qq_le_one (hXe c d))
      (show (1 : MatR D) c d ∈ (1 : FI D) by
        by_cases h : c = d
        · rw [h, Matrix.one_apply_eq]; exact one_mem_one_FI
        · rw [Matrix.one_apply_ne h]; exact FractionalIdeal.zero_mem _)
    rwa [sub_add_cancel] at this
  have hXi1 : ∀ c d, X⁻¹ c d ∈ (1 : FI D) := by
    have hL : StabIntGrp.LoIn (Sint D) X.transpose := by
      refine ⟨fun c => (hU c c).2 rfl, fun c d h => (hU d c).1 h, fun c d => (mem_Sint_iff _).2 (hX1 d c)⟩
    have := StabIntGrp.loIn_inv hL
    rw [← Matrix.transpose_nonsing_inv] at this
    intro c d
    exact (mem_Sint_iff _).1 (this.2.2 d c)
  have hXd : IsUnit X.det := by rw [upU_det hU]; exact isUnit_one
  have hXie : ∀ c d, X⁻¹ c d - (1 : MatR D) c d ∈ (qq D : FI D) := by
    have hm : X⁻¹ - 1 = -(X⁻¹ * (X - 1)) := by
      rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ hXd, Matrix.mul_one, neg_sub]
    intro c d
    rw [← Matrix.sub_apply, hm, Matrix.neg_apply, Matrix.mul_apply]
    refine (qq D : FI D).coeToSubmodule.neg_mem (Submodule.sum_mem _ fun e _ => ?_)
    rw [Matrix.sub_apply]
    exact mul_mem_qq (hXi1 c e) (hXe e d)
  have hPe : ∀ c d, Psi w X⁻¹ c d - (1 : MatR D) c d ∈ (qq D : FI D) := by
    intro c d
    rw [← Matrix.sub_apply, show Psi w X⁻¹ - 1 = Psi w (X⁻¹ - 1) by rw [Psi_sub, Psi_one]]
    simp only [Formalism.L2.SG.Pf.StabIntLat.Psi]
    exact mul_mem_qq (sign_mem_one c d) (conj_mem_qq (by rw [Matrix.sub_apply]; exact hXie _ _))
  rw [← Xmat_coordX w hU hB, condX_iff, Xmat_coordX w hU hB]
  refine ⟨fun q => mem_dd_of_int (hX1 _ _), fun q => mem_qd_of_qq ?_⟩
  rw [Matrix.sub_apply, show X q.1.1 q.1.2 - Psi w X⁻¹ q.1.1 q.1.2 =
    (X q.1.1 q.1.2 - (1 : MatR D) q.1.1 q.1.2) - (Psi w X⁻¹ q.1.1 q.1.2 - (1 : MatR D) q.1.1 q.1.2) by ring]
  exact (qq D : FI D).coeToSubmodule.sub_mem (hXe _ _) (hPe _ _)

end Formalism.L2.SG.Pf.StabIntCong
