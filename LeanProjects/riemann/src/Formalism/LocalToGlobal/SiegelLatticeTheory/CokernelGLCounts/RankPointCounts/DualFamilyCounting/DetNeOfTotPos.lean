import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GramComb

noncomputable section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section D7

variable (D : Formalism.BasicNotions.D7)

theorem emb_G {T T' : ℕ} (Z : MatZ D) (φ : D.host.E →+* ℂ) :
    φ (GZ (T : D.host.E) (T' : D.host.E) Z) =
      ((Complex.normSq (φ Z.det) - (T : ℝ) * T' * Complex.normSq (φ (leadMinorE Z D.R.rS)) : ℝ) : ℂ) := by
  have hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a) := D.sp.cm.cmUnram.2.1 φ
  rw [GZ, PI.UnitaryGroupMassFormula.CntFormula.DetGa.leadMinorE_full D Z]
  simp only [map_sub, map_mul, map_natCast, hφ, Complex.mul_conj]
  push_cast
  ring

theorem det_ne_of_totPos {T T' : ℕ} (Z : MatZ D) (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (T : D.host.E) (T' : D.host.E) Z)) :
    Z.det ≠ 0 := by
  intro h0
  have : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n; positivity)
  obtain ⟨τ⟩ := this
  have h1 := hP τ
  rw [emb_G D Z, Complex.ofReal_re, h0, map_zero, Complex.normSq_zero, zero_sub] at h1
  have := mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) T) (Nat.cast_nonneg (α := ℝ) T'))
    (Complex.normSq_nonneg (D.host.emb (D.eTau τ) (leadMinorE Z D.R.rS)))
  linarith

theorem inv_last (Z : MatZ D) (hdet : Z.det ≠ 0) :
    Z⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) = leadMinorE Z D.R.rS / Z.det := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply,
    PI.UnitaryGroupMassFormula.CntFormula.DetGa.det_updateRow_last_single, ← PI.UnitaryGroupMassFormula.CntFormula.DetGa.leadMinorE_prev D Z,
    Ring.inverse_eq_inv', smul_eq_mul, div_eq_inv_mul]

theorem gam'_last (N' : ℕ) (Z : MatZ D) :
    Gam' N' Z (Fin.last D.R.rS) (Fin.last D.R.rS) =
      -(N' : D.host.E) * (star (Z⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS)) * Z⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS)) := by
  simp only [Gam', Gam, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, ite_and]
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq, mul_ite, ite_mul]
  ring

theorem tv_star (N N' : ℕ) (Z : MatZ D) : star (tv N N' Z) = tv N N' Z := by
  rw [tv, star_add, gam'_herm, star_inv₀, star_natCast]

theorem tv_pos (hD : TotPosAll) {N N' : ℕ} (hN : 0 < N) (Z : MatZ D)
    (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (N : D.host.E) (N' : D.host.E) Z)) :
    Formalism.HermitianLattices.Ext.L3.TotPos (tv N N' Z) := by
  have hdet := det_ne_of_totPos D Z hP
  have hGs : star (GZ (N : D.host.E) (N' : D.host.E) Z) = GZ (N : D.host.E) (N' : D.host.E) Z := by
    simp only [GZ, star_sub, star_mul, star_star, star_natCast]
    ring
  have hG := hD D _ hGs hP
  intro φ
  have hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a) := D.sp.cm.cmUnram.2.1 φ
  have h1 := hG φ
  rw [emb_G D Z, Complex.ofReal_re] at h1
  have hA : 0 < Complex.normSq (φ Z.det) := Complex.normSq_pos.2 ((map_ne_zero φ).2 hdet)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : φ (tv N N' Z) = (((N : ℝ)⁻¹ - N' * (Complex.normSq (φ (leadMinorE Z D.R.rS)) /
      Complex.normSq (φ Z.det)) : ℝ) : ℂ) := by
    rw [tv, gam'_last, inv_last D Z hdet]
    simp only [map_add, map_mul, map_neg, map_natCast, map_inv₀, hφ, map_div₀, star_div₀]
    rw [div_mul_div_comm, ← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
    push_cast
    ring
  rw [ht, Complex.ofReal_re]
  have e : (N : ℝ)⁻¹ - N' * (Complex.normSq (φ (leadMinorE Z D.R.rS)) / Complex.normSq (φ Z.det)) =
      (Complex.normSq (φ Z.det) - N * N' * Complex.normSq (φ (leadMinorE Z D.R.rS))) /
        (N * Complex.normSq (φ Z.det)) := by
    field_simp
  rw [e]
  exact div_pos h1 (mul_pos hNr hA)

end D7

end Formalism.L2.SG.Pf.Cnt.R1

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem ratPair_of (hD : TotPosAll) : RatPair := by
  intro D u u' _ F0 what₂ _ Z hP
  have hN : 0 < (D.mem u).A.T := (D.mem u).A.T_prime.pos
  obtain ⟨y, hy⟩ := dual_of_flag D hN F0
  have hdet := det_ne_of_totPos D Z hP
  obtain ⟨w0, hw0, hwt⟩ := exists_W_vec D hN hy (tv (D.mem u).A.T (D.mem u').A.T Z)
    (tv_star D _ _ Z) (tv_pos D hD hN Z hP)
  set p := pv F0.e y F0.z (D.mem u).A.T (D.mem u').A.T Z w0 with hp
  set f' : Fin (D.R.rS + 1) → (VS D).V := fun b => ∑ a, Z a b • p a with hf'
  have hfp : ∀ a a', (VS D).hT (F0.fvec a) (p a') = if a = a' then 1 else 0 :=
    fun a a' => hf_pv hy hN hw0 a a'
  have hpp : ∀ a a', (VS D).hT (p a) (p a') = Gam' (D.mem u').A.T Z a a' := hpv_pv hy hN hw0 hwt
  have hzh : ∀ a b, (VS D).hT (F0.fvec a) (f' b) = Z a b := by
    intro a b
    simp only [hf', map_sum, map_smul, smul_eq_mul, hfp, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hgr : ∀ b c, (VS D).hT (f' b) (f' c) = Gam D.host.E D.R.rS (D.mem u').A.T b c := by
    intro b c
    rw [hf', gram_comb' p Z b c]
    have h1 : Matrix.of (fun a a' => (VS D).hT (p a) (p a')) = Gam' (D.mem u').A.T Z := by
      ext a a'; simp [hpp]
    have hinv : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z (isUnit_iff_ne_zero.2 hdet)
    rw [h1, Gam']
    simp only [Matrix.mul_assoc]
    rw [hinv, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have hne : ∀ d : Fin D.R.rS, Fin.castSucc d ≠ Fin.last D.R.rS := fun d => (Fin.castSucc_lt_last d).ne
  have hind : LinearIndependent D.host.E (fun d : Fin D.R.rS => f' (Fin.castSucc d)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc d
    have hv : Z.mulVec (Fin.snoc (α := fun _ => D.host.E) c 0) = 0 := by
      funext a
      have h1 := congrArg ((VS D).hT (F0.fvec a)) hc
      rw [map_sum, map_zero] at h1
      simp only [map_smul, smul_eq_mul, hzh] at h1
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero]
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet hv
    simpa using congrFun this (Fin.castSucc d)
  let Fl : FlagG (VS D) D.R.rS (Tn u') :=
    { e := fun d => f' (Fin.castSucc d)
      z := f' (Fin.last D.R.rS)
      e_indep := hind
      e_iso := fun a b => by rw [hgr]; simp [Gam, hne]
      z_orth := fun a => by rw [hgr]; simp [Gam, hne]
      z_norm := by rw [hgr]; simp [Gam, Tn] }
  refine ⟨⟨Fl, f' (Fin.last D.R.rS)⟩, rfl, ?_⟩
  funext a b
  have hfv : Fl.fvec b = f' b := by
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, Fl]
    | cast b => simp [FlagG.fvec, Fl]
  show brS (VS D) (Fl.fvec b) (F0.fvec a) = Z a b
  rw [brS, hfv, hzh]

end Formalism.L2.SG.Pf.Cnt
