import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemHermitianStandardLatticeIffPairingIntegral
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SplitPrimeCounts.LsSetresInt

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatA

open Alg

variable {D : D7}

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

def SS (I : FI) : Prop := ∀ x ∈ I, star x ∈ I

theorem SS_one : SS (1 : FI) := by
  intro x hx
  obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  obtain ⟨o', ho'⟩ := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_int o
  exact (FractionalIdeal.mem_one_iff _).2 ⟨o', ho'⟩

theorem SS_dIpow (n : ℕ) : SS (((Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI D ^ n : Ideal (𝓞 D.host.E)) : FI)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
  obtain ⟨y', hy', ey⟩ := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_mem_pow n y hy
  exact (FractionalIdeal.mem_coeIdeal _).2 ⟨y', hy', ey⟩

theorem SS_inv {I : FI} (hI : SS I) : SS I⁻¹ := by
  by_cases h0 : I = 0
  · subst h0
    intro x hx
    rw [_root_.inv_zero] at hx ⊢
    rw [(FractionalIdeal.mem_zero_iff _).1 hx, star_zero]
    exact (FractionalIdeal.mem_zero_iff _).2 rfl
  intro x hx
  rw [FractionalIdeal.mem_inv_iff h0] at hx ⊢
  intro y hy
  have h := SS_one _ (hx _ (hI y hy))
  rwa [star_mul, star_star, mul_comm] at h

theorem SS_mul {I J : FI} (hI : SS I) (hJ : SS J) : SS (I * J) := by
  intro x hx
  refine FractionalIdeal.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    rw [star_mul']
    exact FractionalIdeal.mul_mem_mul (hI a ha) (hJ b hb)
  · intro a b ha hb
    rw [star_add]
    exact Submodule.add_mem _ ha hb

theorem SS_aaD (a : Fin D.R.rS) : SS (aaD D a) := by
  rw [Formalism.L2.SG.SplitPrimeNormLemmas.IntG.aaD_eq]
  have : ddS D ^ (D.R.rS - (a : ℕ)) = (((Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI D ^ (D.R.rS - (a : ℕ)) : Ideal (𝓞 D.host.E)) : FI)) := by
    rw [FractionalIdeal.coeIdeal_pow]; rfl
  rw [this]
  exact SS_inv (SS_dIpow _)

theorem aa_ne (a : Fin D.R.rS) : aaD D a ≠ 0 := by
  rw [Formalism.L2.SG.SplitPrimeNormLemmas.IntG.aaD_eq]; exact inv_ne_zero (pow_ne_zero _ Formalism.L2.SG.SplitPrimeNormLemmas.IntG.ddS_ne_zero)

variable (X : HidaSetting D)

theorem smul_aaLb {d : Fin D.R.rS} {c : D.host.E} (hc : c ∈ (aaD D d)⁻¹) {y : (VS D).V} (hy : y ∈ aaLb X d) :
    c • y ∈ X.Lb := by
  have hy' : y ∈ Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D d : Set D.host.E), ∃ l ∈ X.Lb, y = c • l} := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c', hc', l, hl, rfl⟩ := hz
    have hm : c * c' ∈ (1 : FI) := by
      rw [← inv_mul_cancel₀ (aa_ne d)]; exact FractionalIdeal.mul_mem_mul hc hc'
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hm
    rw [smul_smul, ← ho, algebraMap_smul]
    exact Submodule.smul_mem _ o hl
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ o hx

theorem Lb_le : X.Lb ≤ (VS D).L0 := by
  rw [X.Lam_split]; exact le_sup_of_le_left le_sup_right

theorem hT_aaLb_mem {b : Fin D.R.rS} {y : (VS D).V} (hy : y ∈ aaLb X b) {w : (VS D).V} (hw : w ∈ X.Lb) :
    (VS D).hT y w ∈ aaD D b := by
  have hy' : y ∈ Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l} := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, l, hl, rfl⟩ := hz
    obtain ⟨o, ho⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int (VS D).baseLattice_isUnimodular (Lb_le X hl) (Lb_le X hw)
    rw [hT_smulL, ← ho, mul_comm]
    exact fi_smul_mem (SS_aaD b c hc) o
  | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    rw [← algebraMap_smul D.host.E o x, hT_smulL]
    obtain ⟨o', ho'⟩ := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_int o
    rw [show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl, ← ho']
    exact fi_smul_mem hx o'

theorem aa_cancel (a b c : Fin D.R.rS) : aaD D b * (aaD D a)⁻¹ * (aaD D a * (aaD D c)⁻¹) = aaD D b * (aaD D c)⁻¹ := by
  rw [mul_assoc, ← mul_assoc (aaD D a)⁻¹, inv_mul_cancel₀ (aa_ne a), one_mul]

theorem aa_cancel2 (a b c : Fin D.R.rS) : aaD D b * (aaD D a)⁻¹ * (aaD D a * aaD D c) = aaD D b * aaD D c := by
  rw [mul_assoc, ← mul_assoc (aaD D a)⁻¹, inv_mul_cancel₀ (aa_ne a), one_mul]

theorem one_mem_aa (a : Fin D.R.rS) : (1 : D.host.E) ∈ aaD D a * (aaD D a)⁻¹ := by
  rw [mul_inv_cancel₀ (aa_ne a)]; exact FractionalIdeal.one_mem_one _

theorem shape_inv (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (hup : ∀ b a, a < b → X0 b a = 0)
    (hd : ∀ a, X0 a a = 1) (hs : ∀ b a, b < a → X0 b a ∈ aaD D b * (aaD D a)⁻¹) :
    ∀ b a, b < a → X0⁻¹ b a ∈ aaD D b * (aaD D a)⁻¹ := by
  have hdet : X0.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hup i j hij)]
    simp [hd]
  have hU : IsUnit X0.det := by rw [hdet]; exact isUnit_one
  have hXY : X0 * X0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hYup : ∀ b a, a < b → X0⁻¹ b a = 0 := by
    have hbt : X0.BlockTriangular id := fun i j hij => hup i j hij
    haveI : Invertible X0 := Matrix.invertibleOfIsUnitDet X0 hU
    exact fun b a h => Matrix.blockTriangular_inv_of_blockTriangular hbt h
  have hYd : ∀ a, X0⁻¹ a a = 1 := by
    intro a
    have h := congrFun (congrFun hXY a) a
    rw [Matrix.mul_apply, Matrix.one_apply_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), hd, one_mul] at h
    have hz : ∑ e ∈ Finset.univ.erase a, X0 a e * X0⁻¹ e a = 0 := by
      refine Finset.sum_eq_zero fun e he => ?_
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase he) with h1 | h1
      · rw [hup a e h1, zero_mul]
      · rw [hYup e a h1, mul_zero]
    rw [hz, add_zero] at h
    exact h
  have key : ∀ k, ∀ b a : Fin D.R.rS, a.val - b.val = k → b < a → X0⁻¹ b a ∈ aaD D b * (aaD D a)⁻¹ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro b a hk hba
      have h0 : ∑ e, X0 b e * X0⁻¹ e a = 0 := by
        have := congrFun (congrFun hXY b) a
        rw [Matrix.mul_apply, Matrix.one_apply_ne (ne_of_lt hba)] at this
        exact this
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), hd, one_mul] at h0
      rw [eq_neg_of_add_eq_zero_left h0]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun e he => ?_)
      have heb : e ≠ b := Finset.ne_of_mem_erase he
      rcases lt_or_gt_of_ne heb with h1 | h1
      · rw [hup b e h1, zero_mul]; exact Submodule.zero_mem _
      · rcases lt_trichotomy e a with h2 | h2 | h2
        · have hY := ih (a.val - e.val) (by have := Fin.lt_iff_val_lt_val.1 h1; omega) e a rfl h2
          rw [← aa_cancel e b a]
          exact FractionalIdeal.mul_mem_mul (hs b e h1) hY
        · subst h2
          rw [hYd, mul_one]; exact hs b e h1
        · rw [hYup e a h2, mul_zero]; exact Submodule.zero_mem _
  exact fun b a h => key _ b a rfl h

theorem shape_mul (X0 M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (hup : ∀ b a, a < b → X0 b a = 0)
    (hd : ∀ a, X0 a a = 1) (hs : ∀ b a, b < a → X0 b a ∈ aaD D b * (aaD D a)⁻¹)
    (hM : ∀ b a, M b a ∈ aaD D b * aaD D a) : ∀ b a, (X0 * M) b a ∈ aaD D b * aaD D a := by
  intro b a
  rw [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun e _ => ?_
  rcases lt_trichotomy e b with h | h | h
  · rw [hup b e h, zero_mul]; exact Submodule.zero_mem _
  · subst h; rw [hd, one_mul]; exact hM e a
  · rw [← aa_cancel2 e b a]
    exact FractionalIdeal.mul_mem_mul (hs b e h) (hM e a)

end LatA

end Formalism.L2.SG.Pf.NcReal.JX.NOf
