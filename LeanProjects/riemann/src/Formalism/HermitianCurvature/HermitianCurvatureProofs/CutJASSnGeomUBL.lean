import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomUBLTools

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
open scoped ContDiff Matrix ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace S7

variable {k r : ℕ}

theorem adj_pd (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg r (fun g : Mat k r => (Zhat k r z z' g).adjugate a b) := by
  have hfun : (fun g : Mat k r => (Zhat k r z z' g).adjugate a b) = fun g =>
      (-1) ^ ((b : ℕ) + a) * ((Zhat k r z z' g).submatrix b.succAbove a.succAbove).det := by
    funext g
    exact Matrix.adjugate_fin_succ_eq_det_submatrix _ _ _
  rw [hfun]
  exact pd_mono (by omega) (pd_mul (pd_const _ 0) (pd_det _ fun i j => zhat_pd k r z z' _ _))

private theorem isPolyDeg_linear_combination {a : ℕ} (c : Fin (2 * r + k + 1) → ℂ) (f : Mat k r → Fin (2 * r + k + 1) → ℂ)
    (hf : ∀ j, U.IsPolyDeg a (fun g => f g j)) :
    U.IsPolyDeg a (fun g => ∑ j ∈ Finset.univ, c j * f g j) :=
  pd_sum _ fun j _ => pd_mono (by omega) (pd_mul (pd_const (c j) 0) (hf j))

theorem mv_pd (M : Mat k r → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (v : Mat k r → Fin (2 * r + k + 1) → ℂ) {a b : ℕ}
    (hM : ∀ i j, U.IsPolyDeg a (fun g => M g i j)) (hv : ∀ j, U.IsPolyDeg b (fun g => v g j))
    (i : Fin (2 * r + k + 1)) : U.IsPolyDeg (a + b) (fun g => (M g *ᵥ v g) i) := by
  have hfun : (fun g => (M g *ᵥ v g) i) = fun g => ∑ j ∈ Finset.univ, M g i j * v g j := by
    funext g; rfl
  rw [hfun]
  exact pd_sum _ fun j _ => pd_mul (hM i j) (hv j)

theorem herm_pd (v w : Mat k r → Fin (2 * r + k + 1) → ℂ) {a b : ℕ}
    (hv : ∀ j, U.IsPolyDeg a (fun g => v g j)) (hw : ∀ j, U.IsPolyDeg b (fun g => star (w g j))) :
    U.IsPolyDeg (b + a) (fun g => herm (Hpk k r) (v g) (w g)) := by
  have hfun : (fun g => herm (Hpk k r) (v g) (w g)) = fun g =>
      ∑ i ∈ Finset.univ, star (w g i) * ∑ j ∈ Finset.univ, Hpk k r i j * v g j := by
    funext g; rfl
  rw [hfun]
  exact pd_sum _ fun i _ => pd_mul (hw i) (isPolyDeg_linear_combination _ v hv)

theorem gmv_pd (u : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g : Mat k r => (g *ᵥ u) i) := by
  have hfun : (fun g : Mat k r => (g *ᵥ u) i) = fun g => ∑ j ∈ Finset.univ, g i j * u j := by
    funext g; rfl
  rw [hfun]
  exact pd_sum _ fun j _ => pd_mono (by omega) (pd_mul (pd_entry i j) (pd_const (u j) 0))

theorem xcof_pd (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    U.IsPolyDeg (r + 1) (fun g : Mat k r => PI.UnitaryGroupMassFormula.GsFr.xcof k r z z' g i) := by
  have hfun : (fun g : Mat k r => PI.UnitaryGroupMassFormula.GsFr.xcof k r z z' g i) = fun g =>
      ∑ b ∈ Finset.univ, (Zhat k r z z' g).adjugate b (Fin.last r) * (g *ᵥ fvec k r z' b) i := by
    funext g
    unfold PI.UnitaryGroupMassFormula.GsFr.xcof
    exact Finset.sum_apply _ _ _
  rw [hfun]
  exact pd_sum _ fun b _ => pd_mul (adj_pd z z' b (Fin.last r)) (gmv_pd _ i)

private theorem isPolyDeg_adjugate_of_entries_isPolyDeg_one {m : ℕ} (M : Mat k r → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hM : ∀ a b, U.IsPolyDeg 1 (fun g => M g a b)) (a b : Fin (m + 1)) :
    U.IsPolyDeg m (fun g => (M g).adjugate a b) := by
  have hfun : (fun g => (M g).adjugate a b) = fun g =>
      (-1) ^ ((b : ℕ) + a) * ((M g).submatrix b.succAbove a.succAbove).det := by
    funext g
    exact Matrix.adjugate_fin_succ_eq_det_submatrix _ _ _
  rw [hfun]
  exact pd_mono (by omega) (pd_mul (pd_const _ 0) (pd_det _ fun i j => hM _ _))

theorem xcofL_pd (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    U.IsPolyDeg r (fun g : Mat k r => PI.UnitaryGroupMassFormula.GsFr.xcofL k r z z' g i) := by
  have hst : ∀ a, (fun g : Mat k r => star ((Zhat k r z z' g).adjugate (Fin.last r) a)) =
      fun g => ((Zhat k r z z' g)ᴴ).adjugate a (Fin.last r) := by
    intro a
    funext g
    rw [← Matrix.adjugate_conjTranspose]
    rfl
  have hfun : (fun g : Mat k r => PI.UnitaryGroupMassFormula.GsFr.xcofL k r z z' g i) = fun g =>
      ∑ a ∈ Finset.univ, ((Zhat k r z z' g)ᴴ).adjugate a (Fin.last r) * fvec k r z a i := by
    funext g
    unfold PI.UnitaryGroupMassFormula.GsFr.xcofL
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← congrFun (hst a) g]
    rfl
  rw [hfun]
  exact pd_sum _ fun a _ => pd_mono (by omega)
    (pd_mul (isPolyDeg_adjugate_of_entries_isPolyDeg_one (fun g => (Zhat k r z z' g)ᴴ) (fun b c => zhat_star_pd k r z z' c b) a (Fin.last r))
      (pd_const (fvec k r z a i) 0))

theorem pm_pd (z : Fin (2 * r + k + 1) → ℂ) (v : Mat k r → Fin (2 * r + k + 1) → ℂ) {a : ℕ}
    (hv : ∀ j, U.IsPolyDeg a (fun g => v g j)) (i : Fin (2 * r + k + 1)) :
    U.IsPolyDeg a (fun g : Mat k r => PI.UnitaryGroupMassFormula.GsFr.prW k r z (v g) i) := by
  have hw : ∀ j, U.IsPolyDeg a (fun g => PI.UnitaryGroupMassFormula.GsFr.wbPart k r (v g) j) := by
    intro j
    by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · simpa [PI.UnitaryGroupMassFormula.GsFr.wbPart, hj] using hv j
    · simpa [PI.UnitaryGroupMassFormula.GsFr.wbPart, hj] using (pd_const (N := 2 * r + k + 1) (0 : ℂ) a)
  have hfun : (fun g : Mat k r => PI.UnitaryGroupMassFormula.GsFr.prW k r z (v g) i) = fun g =>
      PI.UnitaryGroupMassFormula.GsFr.wbPart k r (v g) i +
        (∑ j ∈ Finset.univ, star (z j) * ∑ l ∈ Finset.univ, Hpk k r j l * PI.UnitaryGroupMassFormula.GsFr.wbPart k r (v g) l) *
          ((Tz k r z : ℂ)⁻¹ * z i) := by
    funext g
    show PI.UnitaryGroupMassFormula.GsFr.wbPart k r (v g) i +
      herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.wbPart k r (v g)) z / (Tz k r z : ℂ) * z i = _
    rw [div_eq_mul_inv, mul_assoc]
    rfl
  rw [hfun]
  exact pd_add (hw i) (pd_mono (by omega)
    (pd_mul (isPolyDeg_linear_combination (fun j => star (z j)) _ fun j => isPolyDeg_linear_combination _ _ hw) (pd_const _ 0)))

theorem omW_pd (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    U.IsPolyDeg (r + 1) (fun g : Mat k r => PI.UnitaryGroupMassFormula.GsFr.omW k r z z' g i) := pm_pd z (fun g => PI.UnitaryGroupMassFormula.GsFr.xcof k r z z' g) (fun j => xcof_pd z z' j) i

theorem hgh_pd (i j : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g : Mat k r => (Hpk k r * gᴴ * Hpk k r) i j) := by
  have hfun : (fun g : Mat k r => (Hpk k r * gᴴ * Hpk k r) i j) = fun g =>
      ∑ b ∈ Finset.univ, (∑ a ∈ Finset.univ, Hpk k r i a * star (g b a)) * Hpk k r b j := by
    funext g; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hfun]
  exact pd_sum _ fun b _ => pd_mono (by omega)
    (pd_mul (pd_sum _ fun a _ => pd_mul (pd_const _ 0) (pd_star_entry b a)) (pd_const _ 0))

theorem omS_pd (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    U.IsPolyDeg (r + 1) (fun g : Mat k r => PI.UnitaryGroupMassFormula.GsFr.omS k r z z' g i) := by
  have h := pm_pd z' (fun g : Mat k r => (Hpk k r * gᴴ * Hpk k r) *ᵥ PI.UnitaryGroupMassFormula.GsFr.xcofL k r z z' g)
    (fun j => mv_pd _ _ (fun a b => hgh_pd a b) (fun b => xcofL_pd z z' b) j) i
  exact pd_mono (by omega) h

theorem prW_sq {z ξ : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hX : ∀ a : Fin r, ξ (esI k r a) = 0) :
    herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z ξ) (PI.UnitaryGroupMassFormula.GsFr.prW k r z ξ) * herm (Hpk k r) z z =
      herm (Hpk k r) ξ ξ * herm (Hpk k r) z z - herm (Hpk k r) ξ z * star (herm (Hpk k r) ξ z) := by
  obtain ⟨w, hwdef⟩ : ∃ w, w = PI.UnitaryGroupMassFormula.GsFr.wbPart k r ξ := ⟨_, rfl⟩
  have hx : ξ - w ∈ PI.UnitaryGroupMassFormula.GsFr.Xsp k r := hwdef ▸ PI.UnitaryGroupMassFormula.GsFr.sub_wbPart_X hX
  have hw : inWb k r w := hwdef ▸ PI.UnitaryGroupMassFormula.GsFr.wbPart_inWb ξ
  have hξ : ξ = w + (ξ - w) := by abel
  have e1 : herm (Hpk k r) ξ ξ = herm (Hpk k r) w w := by
    conv_lhs => rw [hξ]
    exact PI.UnitaryGroupMassFormula.GsFr.herm_add_X hw hw hx hx
  have e2 : herm (Hpk k r) ξ z = herm (Hpk k r) w z := by
    conv_lhs => rw [hξ]
    rw [PI.UnitaryGroupMassFormula.GsFr.hm_add_l, PI.UnitaryGroupMassFormula.GsFr.herm_X_gen hx (PI.UnitaryGroupMassFormula.GsFr.wb_hi hz.1), add_zero]
  have hzw : herm (Hpk k r) z w = star (herm (Hpk k r) w z) := PI.UnitaryGroupMassFormula.GsFr.hm_symm _ PI.UnitaryGroupMassFormula.GsFr.hH_ct w z
  have hpr : PI.UnitaryGroupMassFormula.GsFr.prW k r z ξ = w + (herm (Hpk k r) w z / (Tz k r z : ℂ)) • z := by
    rw [hwdef]; rfl
  have hzz : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq z
  have hT : ((Tz k r z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hz.2.ne'
  rw [e1, e2, hpr, PI.UnitaryGroupMassFormula.GsFr.hm_add_l, PI.UnitaryGroupMassFormula.GsFr.hm_add_r, PI.UnitaryGroupMassFormula.GsFr.hm_add_r, PI.UnitaryGroupMassFormula.GsFr.hm_smul_r,
    PI.UnitaryGroupMassFormula.GsFr.hm_smul_l, PI.UnitaryGroupMassFormula.GsFr.hm_smul_l, PI.UnitaryGroupMassFormula.GsFr.hm_smul_r, hzw, hzz, star_div₀]
  have hs : star ((Tz k r z : ℝ) : ℂ) = ((Tz k r z : ℝ) : ℂ) := by rw [Complex.star_def, Complex.conj_ofReal]
  rw [hs]
  field_simp
  ring

theorem omW_sq {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {g : Mat k r}
    (hg : g ∈ GV k r) :
    herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.omW k r z z' g) (PI.UnitaryGroupMassFormula.GsFr.omW k r z z' g) =
      ((Gf k r z z' g / Tz k r z : ℝ) : ℂ) := by
  have h := prW_sq hz (PI.UnitaryGroupMassFormula.GsFr.xcof_esI z z' g)
  rw [PI.UnitaryGroupMassFormula.GsFr.xcof_self hz' hg, PI.UnitaryGroupMassFormula.GsFr.herm_Hpk_xcof_eq_det_Zhat, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq z,
    Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq z', PI.UnitaryGroupMassFormula.GsFr.adj_LL] at h
  have hT : ((Tz k r z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hz.2.ne'
  have hG : Gf k r z z' g = Complex.normSq (Zhat k r z z' g).det -
      Tz k r z * Tz k r z' * Complex.normSq ((Zhat k r z z' g).submatrix Fin.castSucc Fin.castSucc).det := rfl
  rw [hG, Complex.ofReal_div, eq_div_iff hT]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def] at h
  unfold PI.UnitaryGroupMassFormula.GsFr.omW
  linear_combination -h

theorem omS_sq {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {g : Mat k r}
    (hg : g ∈ GV k r) :
    herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.omS k r z z' g) (PI.UnitaryGroupMassFormula.GsFr.omS k r z z' g) =
      ((Gf k r z z' g / Tz k r z' : ℝ) : ℂ) := by
  rw [← PI.UnitaryGroupMassFormula.GsFr.omS_eq z z' hg]
  have h := prW_sq hz' (PI.UnitaryGroupMassFormula.GsFr.ginv_xcofL_esI z z' hg)
  have hs : herm (Hpk k r) (g⁻¹ *ᵥ PI.UnitaryGroupMassFormula.GsFr.xcofL k r z z' g) (g⁻¹ *ᵥ PI.UnitaryGroupMassFormula.GsFr.xcofL k r z z' g) =
      herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.xcofL k r z z' g) (PI.UnitaryGroupMassFormula.GsFr.xcofL k r z z' g) := by
    rw [← Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hg, PI.UnitaryGroupMassFormula.GsFr.ginv_cancel hg]
  rw [hs, PI.UnitaryGroupMassFormula.GsFr.xcofL_self hz, PI.UnitaryGroupMassFormula.GsFr.xi_hermitian_cofactor_det hg, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq z,
    Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq z', PI.UnitaryGroupMassFormula.GsFr.adj_LL, star_star] at h
  have hT : ((Tz k r z' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hz'.2.ne'
  have hG : Gf k r z z' g = Complex.normSq (Zhat k r z z' g).det -
      Tz k r z * Tz k r z' * Complex.normSq ((Zhat k r z z' g).submatrix Fin.castSucc Fin.castSucc).det := rfl
  rw [hG, Complex.ofReal_div, eq_div_iff hT]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def] at h
  unfold PI.UnitaryGroupMassFormula.GsFr.omW'
  linear_combination -h

theorem geG_sub (z z' : Fin (2 * r + k + 1) → ℂ) (ε : ℝ) : geG k r z z' ε ⊆ GV k r := fun _ hg => hg.1

theorem ubl_unitH (h6 : UBLInvSqrt) {S : Set (Mat k r)} (hSG : S ⊆ GV k r) (v : Mat k r → Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ i, U.IsPolyDeg (r + 1) (fun g => v g i)) {c : ℝ} (hc : 0 < c)
    (hlb : ∀ g ∈ S, c ≤ (herm (Hpk k r) (v g) (v g)).re) (n : ℕ) :
    UBL (fun g => unitH k r (v g)) S n (r + 1) (2 * (r + 1)) := by
  have hP : U.IsPolyDeg (2 * (r + 1)) (fun g => herm (Hpk k r) (v g) (v g)) :=
    pd_mono (by omega) (herm_pd v v hv fun j => Formalism.FourierDecayAlt.P.CutMP.jdh_pd_star (hv j))
  have hs := h6 k r (2 * (r + 1)) _ hP S hSG c hc hlb n
  have hv' : ∀ i, UBL (fun g => v g i) S n (r + 1) (2 * (r + 1)) := fun i => ubl_poly (hv i) S hSG n _
  have hfun : (fun g => unitH k r (v g)) = fun g i =>
      (((Real.sqrt (herm (Hpk k r) (v g) (v g)).re)⁻¹ : ℝ) : ℂ) * v g i := by
    funext g i; rfl
  rw [hfun]
  refine ubl_pi hSG fun i => ?_
  exact ubl_mono hSG (ubl_mul hSG hs (hv' i)) (by omega) le_rfl

theorem ubl_nuG (h6 : UBLInvSqrt) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z')
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) : UBL (nuG z z') (geG k r z z' ε) n (r + 1) (2 * (r + 1)) := by
  have hT : 0 < Tz k r z := hz.2
  refine ubl_unitH h6 (geG_sub z z' ε) (fun g => PI.UnitaryGroupMassFormula.GsFr.omW k r z z' g) (fun i => omW_pd z z' i)
    (c := ε / Tz k r z) (div_pos hε hT) (fun g hg => ?_) n
  show ε / Tz k r z ≤ (herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.omW k r z z' g) (PI.UnitaryGroupMassFormula.GsFr.omW k r z z' g)).re
  rw [omW_sq hz hz' hg.1, Complex.ofReal_re]
  have hT0 : 0 ≤ Tz k r z := hT.le
  have hG : ε ≤ Gf k r z z' g := hg.2
  gcongr

private theorem inv_eq_Hpk_mul_conjTranspose_mul_Hpk_of_mem_GV {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have hH : Hpk k r * Hpk k r = 1 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ (Hpk k r) g, hg', hH]

theorem ubl_nuG' (h6 : UBLInvSqrt) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z')
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) : UBL (nuG' z z') (geG k r z z' ε) n (r + 1) (2 * (r + 1)) := by
  have hT : 0 < Tz k r z' := hz'.2
  have key : UBL (fun g => unitH k r (PI.UnitaryGroupMassFormula.GsFr.omS k r z z' g)) (geG k r z z' ε) n (r + 1) (2 * (r + 1)) := by
    refine ubl_unitH h6 (geG_sub z z' ε) (fun g => PI.UnitaryGroupMassFormula.GsFr.omS k r z z' g) (fun i => omS_pd z z' i)
      (c := ε / Tz k r z') (div_pos hε hT) (fun g hg => ?_) n
    show ε / Tz k r z' ≤ (herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.omS k r z z' g) (PI.UnitaryGroupMassFormula.GsFr.omS k r z z' g)).re
    rw [omS_sq hz hz' hg.1, Complex.ofReal_re]
    have hT0 : 0 ≤ Tz k r z' := hT.le
    have hG : ε ≤ Gf k r z z' g := hg.2
    gcongr
  refine ubl_congr isOpen_univ (Set.subset_univ _) (geG_sub z z' ε) (fun g hg _ => ?_) key
  show unitH k r (PI.UnitaryGroupMassFormula.GsFr.omW' k r z z' g) = unitH k r (PI.UnitaryGroupMassFormula.GsFr.omS k r z z' g)
  congr 1
  show PI.UnitaryGroupMassFormula.GsFr.prW k r z' (g⁻¹ *ᵥ PI.UnitaryGroupMassFormula.GsFr.xcofL k r z z' g) =
    PI.UnitaryGroupMassFormula.GsFr.prW k r z' ((Hpk k r * gᴴ * Hpk k r) *ᵥ PI.UnitaryGroupMassFormula.GsFr.xcofL k r z z' g)
  rw [inv_eq_Hpk_mul_conjTranspose_mul_Hpk_of_mem_GV hg]

theorem ubl_entry {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {v : Mat k r → Fin (2 * r + k + 1) → ℂ} {n e γ : ℕ}
    (h : UBL v S n e γ) (i : Fin (2 * r + k + 1)) : UBL (fun g => v g i) S n e γ := by
  have hfun : (fun g => v g i) =
      fun g => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * r + k + 1) => ℂ) i) (v g) := by
    funext g; rfl
  rw [hfun]
  exact ubl_clm _ hSG h

theorem ubl_neg {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {f : Mat k r → ℂ} {n e γ : ℕ} (h : UBL f S n e γ) :
    UBL (fun g => -f g) S n e γ := by
  have hfun : (fun g => -f g) = fun g => (-ContinuousLinearMap.id ℝ ℂ) (f g) := by
    funext g; simp
  rw [hfun]
  exact ubl_clm _ hSG h

theorem ubl_sub {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {f₁ f₂ : Mat k r → ℂ} {n e γ : ℕ} (h₁ : UBL f₁ S n e γ)
    (h₂ : UBL f₂ S n e γ) : UBL (fun g => f₁ g - f₂ g) S n e γ := by
  simpa only [sub_eq_add_neg] using ubl_add hSG h₁ (ubl_neg hSG h₂)

theorem dlast_det (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) :
    Dmin k r z z' g (Fin.last (r + 1)) = (Zhat k r z z' g).det := by
  have h : (Zhat k r z z' g).submatrix (Fin.castLE (le_refl (r + 1))) (Fin.castLE (le_refl (r + 1))) =
      Zhat k r z z' g := Matrix.ext fun i j => rfl
  rw [← h]
  rfl

theorem ubl_ioG {ε : ℝ} {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z')
    (hnu' : ∀ n, UBL (nuG' z z') (geG k r z z' ε) n (r + 1) (2 * (r + 1))) (hε : 0 < ε) (n : ℕ) :
    UBL (ioG z z') (geG k r z z' ε) n (4 * (r + 1)) (2 * (r + 1)) := by
  set S := geG k r z z' ε
  have hSG : S ⊆ GV k r := geG_sub z z' ε
  have hc : ∀ (M0 : Mat k r) (i j : Fin (2 * r + k + 1)) (e : ℕ), UBL (fun _ : Mat k r => M0 i j) S n e (2 * (r + 1)) :=
    fun M0 i j e => ubl_mono hSG (ubl_const (M0 i j) hSG n _) (Nat.zero_le e) le_rfl
  have hg : ∀ i j : Fin (2 * r + k + 1), UBL (fun g : Mat k r => g i j) S n 1 (2 * (r + 1)) :=
    fun i j => ubl_poly (pd_entry i j) S hSG n _
  have hdetP : U.IsPolyDeg (r + 1) (fun g : Mat k r => (Zhat k r z z' g).det) :=
    pd_det (fun g : Mat k r => Zhat k r z z' g) fun a b => zhat_pd k r z z' a b
  have hdet : UBL (fun g => -((Zhat k r z z' g).det)⁻¹) S n 0 (2 * (r + 1)) := by
    have h := ubl_invpow hdetP hSG hε (fun g hg => by
      rw [← dlast_det]; exact Formalism.FourierDecayAlt.P.gram_function_last_minor k r z z' hz.2.le hz'.2.le g ε hg.2) 1 n
    exact ubl_neg hSG (ubl_mono hSG (by simpa using h) le_rfl (by omega))
  have hadj : ∀ a b, UBL (fun g => (Zhat k r z z' g).adjugate a b) S n r (2 * (r + 1)) :=
    fun a b => ubl_poly (adj_pd z z' a b) S hSG n _

  have hLm : ∀ i j, UBL (fun g => PI.UnitaryGroupMassFormula.GsFr.Lm k r z z' g i j) S n (r + 1) (2 * (r + 1)) := by
    intro i j
    have e : (fun g => PI.UnitaryGroupMassFormula.GsFr.Lm k r z z' g i j) = fun g => (fun _ => (1 : Mat k r) i j) g +
        ∑ c : Fin (r + 1), ∑ a : Fin (r + 1), (-((Zhat k r z z' g).det)⁻¹ * (Zhat k r z z' g).adjugate c a) *
          ((fun _ => PI.UnitaryGroupMassFormula.GsFr.Rk k r (fvec k r z' c) (fvec k r z a)) g * g) i j := by
      funext g
      simp [PI.UnitaryGroupMassFormula.GsFr.Lm, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply]
    rw [e]
    refine ubl_add hSG (hc 1 i j _) (ubl_sum hSG _ fun c _ => ubl_sum hSG _ fun a _ => ?_)
    have h1 := ubl_mul hSG (ubl_mul hSG hdet (hadj c a))
      (ubl_mmul hSG (fun i j => hc (PI.UnitaryGroupMassFormula.GsFr.Rk k r (fvec k r z' c) (fvec k r z a)) i j 0) hg i j)
    exact ubl_mono hSG (by simpa using h1) (by omega) le_rfl
  have hPhi : ∀ i j, UBL (fun g => PI.UnitaryGroupMassFormula.GsFr.Phi k r z z' g i j) S n (r + 2) (2 * (r + 1)) := by
    intro i j
    have h1 := ubl_mmul hSG (ubl_mmul hSG (fun i j => hc (PI.UnitaryGroupMassFormula.GsFr.Pm k r z) i j 0) hg) hLm i j
    exact ubl_mono hSG (by simpa [PI.UnitaryGroupMassFormula.GsFr.Phi] using h1) (by omega) le_rfl
  have hv : ∀ i, UBL (fun g => nuG' z z' g i) S n (r + 1) (2 * (r + 1)) := fun i => ubl_entry hSG (hnu' n) i
  have hRk : ∀ i j, UBL (fun g => PI.UnitaryGroupMassFormula.GsFr.Rk k r (nuG' z z' g) (nuG' z z' g) i j) S n (2 * (r + 1))
      (2 * (r + 1)) := by
    intro i j
    have e : (fun g => PI.UnitaryGroupMassFormula.GsFr.Rk k r (nuG' z z' g) (nuG' z z' g) i j) = fun g =>
        nuG' z z' g i * ∑ l, star (nuG' z z' g l) * (fun _ => Hpk k r l j) g := by
      funext g
      simp [PI.UnitaryGroupMassFormula.GsFr.Rk, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct]
    rw [e]
    have h1 := ubl_mul hSG (hv i) (ubl_sum hSG Finset.univ fun l _ =>
      ubl_mul hSG (ubl_star hSG (hv l)) (hc (Hpk k r) l j 0))
    exact ubl_mono hSG (by simpa using h1) (by omega) le_rfl
  have hPp : ∀ i j, UBL (fun g => PpG z z' g i j) S n (2 * (r + 1)) (2 * (r + 1)) := by
    intro i j
    have h1 := ubl_mmul hSG hRk (fun i j => hc (PI.UnitaryGroupMassFormula.GsFr.Pm k r z') i j 0) i j
    have h2 := ubl_sub hSG (hc (PI.UnitaryGroupMassFormula.GsFr.Pm k r z') i j (2 * (r + 1))) (by simpa using h1)
    simpa [PpG, Matrix.sub_apply] using h2
  have hio : ∀ i j, UBL (fun g => ioG z z' g i j) S n (4 * (r + 1)) (2 * (r + 1)) := by
    intro i j
    have h1 := ubl_mmul hSG hPhi hPp i j
    exact ubl_mono hSG (by simpa [ioG] using h1) (by omega) le_rfl
  exact ubl_pi hSG fun i => ubl_pi hSG fun j => hio i j

end S7

theorem geomUBL_of (h6 : UBLInvSqrt) : GeomUBL := by
  intro k r z z' _ hz hz' ε hε
  refine ⟨⟨r + 1, 2 * (r + 1), by omega, le_rfl, fun n => S7.ubl_nuG h6 hz hz' hε n⟩,
    ⟨r + 1, 2 * (r + 1), by omega, le_rfl, fun n => S7.ubl_nuG' h6 hz hz' hε n⟩,
    ⟨4 * (r + 1), 2 * (r + 1), le_rfl, le_rfl,
      fun n => S7.ubl_ioG hz hz' (fun n => S7.ubl_nuG' h6 hz hz' hε n) hε n⟩⟩

theorem geometry_unipotent_bound_holds : GeomUBL := geomUBL_of unipotent_inverse_sqrt_bound

namespace S7

end S7

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
