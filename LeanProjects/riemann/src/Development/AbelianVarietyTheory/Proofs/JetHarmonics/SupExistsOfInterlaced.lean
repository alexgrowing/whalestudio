import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
import Formalism.PeriodIntegrals.BesselPeriodGGP
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriTensorDecomposition
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorMomentEstimate
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficient
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FixesWedgeAndForm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapExistsFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSidesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilyThroughDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsCoordLeOfLOneNormLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFrameConjUnitaryBlockEqUnitaryComplement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDerivedActionFiniteDimUnitaryRep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHighestWeightIrreducibleUnitaryRepU
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSides
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsBesselMapSmBesselCharIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.FormalDegreeBessel.FinalDS

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.SupNonzero

section exp
open scoped Matrix.Norms.Operator

theorem exp_corner {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℂ) (B : Matrix (Fin k) (Fin n) ℂ) (h : B * A = 1)
    (Z : Matrix (Fin k) (Fin k) ℂ) : NormedSpace.exp (A * Z * B) = 1 + A * (NormedSpace.exp Z - 1) * B := by
  have h' : ∀ X : Matrix (Fin k) (Fin n) ℂ, B * (A * X) = X := fun X => by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  let Ψ : Matrix (Fin k) (Fin k) ℂ × ℂ →+* Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun x => A * x.1 * B + x.2 • (1 - A * B)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [Prod.fst_mul, Prod.snd_mul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h', Matrix.mul_one, Matrix.one_mul, sub_self, smul_zero,
          add_zero]
        module
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.add_mul, Matrix.mul_add, add_smul]; abel }
  have hc : Continuous Ψ := by
    show Continuous fun x : Matrix (Fin k) (Fin k) ℂ × ℂ => A * x.1 * B + x.2 • (1 - A * B)
    fun_prop
  have e := NormedSpace.map_exp Ψ hc (Z, 0)
  have e1 : Ψ (Z, 0) = A * Z * B := by simp [Ψ]
  rw [e1] at e
  refine e.symm.trans ?_
  show A * (NormedSpace.exp (Z, (0 : ℂ))).1 * B + (NormedSpace.exp (Z, (0 : ℂ))).2 • (1 - A * B) = _
  have f1 : (NormedSpace.exp (Z, (0 : ℂ))).1 = NormedSpace.exp Z := Prod.fst_exp (Z, (0 : ℂ))
  have f2 : (NormedSpace.exp (Z, (0 : ℂ))).2 = NormedSpace.exp 0 := Prod.snd_exp (Z, (0 : ℂ))
  rw [f1, f2]
  simp only [NormedSpace.exp_zero, one_smul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel

end exp

section frame
open PI.UpqRep PI.HwUniqW GlobalTheory.BesselFrame Formalism.FourierDecayAlt.P.SettingConstruction

variable {k r : ℕ}

def incl (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin k) ℂ := fun i a => if i = bl k r a then 1 else 0

theorem incl_mul_apply (h : Matrix (Fin k) (Fin k) ℂ) (i j) : (incl k r * h * (incl k r)ᴴ) i j =
    ∑ a, ∑ b, if i = bl k r a ∧ j = bl k r b then h a b else 0 := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.conjTranspose_apply, incl]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h1 : i = bl k r a <;> by_cases h2 : j = bl k r b <;> simp [h1, h2]

theorem blockW_eq (h : Matrix (Fin k) (Fin k) ℂ) : blockW k r h = 1 + incl k r * (h - 1) * (incl k r)ᴴ := by
  ext i j
  rw [Matrix.add_apply, incl_mul_apply]
  by_cases hi : InB k r i
  · obtain ⟨a, rfl⟩ : ∃ a, bl k r a = i := ⟨_, block_mk hi (by unfold InB at hi; omega)⟩
    by_cases hj : InB k r j
    · obtain ⟨b, rfl⟩ : ∃ a, bl k r a = j := ⟨_, block_mk hj (by unfold InB at hj; omega)⟩
      rw [blockW_bl]
      simp [blockIndex_injective.eq_iff, ite_and, Matrix.one_apply]
    · have : ∀ b, j ≠ bl k r b := fun b hb => hj (hb ▸ inB_bl b)
      rw [blockW_in_out _ hi hj, Matrix.one_apply_ne (ne_of_inB hi hj)]
      simp [this]
  · have : ∀ b, i ≠ bl k r b := fun b hb => hi (hb ▸ inB_bl b)
    rw [blockW_out _ hi]
    simp [this, Matrix.one_apply]

theorem incl_H : (incl k r)ᴴ * Hpk k r = (incl k r)ᴴ := by
  ext a j
  rw [Matrix.mul_apply, Finset.sum_eq_single (bl k r a)]
  · simp [incl, Hpk_apply, piI_in (inB_bl a), epsI_in (inB_bl a)]
  · intro b _ hb; simp [incl, hb]
  · simp

theorem incl_incl : (incl k r)ᴴ * incl k r = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (bl k r a)]
  · simp [incl, blockIndex_injective.eq_iff, Matrix.one_apply]
  · intro b _ hb; simp [incl, hb]
  · simp

variable {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem co_eq (hg : g ∈ UH (Hpk k r)) : (g * incl k r)ᴴ * Hpk k r = (incl k r)ᴴ * g⁻¹ := by
  rw [inv_eq_UH hg, Matrix.conjTranspose_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, incl_H]

theorem co_mul (hg : g ∈ UH (Hpk k r)) : (g * incl k r)ᴴ * Hpk k r * (g * incl k r) = 1 := by
  rw [co_eq hg, Matrix.mul_assoc, ← Matrix.mul_assoc g⁻¹, inv_mul_UH' hg, Matrix.one_mul, incl_incl]

theorem conj_blockW (hg : g ∈ UH (Hpk k r)) (h : Matrix (Fin k) (Fin k) ℂ) :
    g * blockW k r h * g⁻¹ = 1 + g * incl k r * (h - 1) * ((g * incl k r)ᴴ * Hpk k r) := by
  rw [co_eq hg, blockW_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, mul_inv_UH hg]
  simp only [Matrix.mul_assoc]

theorem col_eq (a : Fin k) (p) : (g *ᵥ bvec (bl k r a)) p = (g * incl k r) p a := by
  rw [mulVec_bvec_apply]
  simp [Matrix.mul_apply, incl]

theorem unitB_eq (a b : Fin k) : Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) a b =
    g * incl k r * Matrix.single a b (1 : ℂ) * ((g * incl k r)ᴴ * Hpk k r) := by
  ext p q
  have e : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.bvec q) (g *ᵥ bvec (bl k r b)) =
      ((g * incl k r)ᴴ * Hpk k r) b q := by
    rw [Matrix.mul_apply]
    unfold Formalism.QuantumDeterminants.herm dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, col_eq, Matrix.conjTranspose_apply]
    congr 1
    exact mulVec_bvec_apply _ _ _
  simp only [Q.unitB, Matrix.of_apply]
  rw [e, col_eq]
  generalize g * incl k r = A
  generalize Aᴴ * Hpk k r = B
  simp [Matrix.mul_apply, Matrix.single, ite_and, Finset.sum_ite_eq]

theorem isFrameOf (hg : IsFrameW k r z g) : Q.IsFrameOf k r [z] (fun a => g *ᵥ bvec (bl k r a)) := by
  have hf := form_of_unitary (Hpk k r) hg.1
  have h1 : ∀ (a : Fin k) i, Formalism.QuantumDeterminants.herm (Hpk k r) (bvec (bl k r a)) (bvec i) = if i = bl k r a then 1 else 0 := by
    intro a i
    rw [← herm_symm _ Hpk_conjTranspose, herm_right_bvec, piI_in (inB_bl a), epsI_in (inB_bl a), bvec_apply]
    by_cases h : i = bl k r a <;> simp [h, eq_comm]
  refine ⟨fun a i hi => ?_, fun a b => ?_, fun a v hv => ?_⟩
  · have hl := i.isLt
    have hp := piI_val (k := k) (r := r) i
    have hfix : g *ᵥ bvec (piI k r i) = bvec (piI k r i) := by
      rcases hi with hi | hi
      · have e : esI k r ⟨i.val, hi⟩ = piI k r i := Fin.ext (by rw [hp]; simp only [esI]; split_ifs <;> omega)
        rw [← e]; exact (hg.2.1 _).2
      · have e : eI k r ⟨2 * r + k - i.val, by omega⟩ = piI k r i :=
          Fin.ext (by rw [hp]; simp only [eI]; split_ifs <;> omega)
        rw [← e]; exact (hg.2.1 _).1
    have h2 := hf (bvec (bl k r a)) (bvec (piI k r i))
    rw [hfix, herm_right_bvec, piI_piI, h1, if_neg] at h2
    · refine (mul_eq_zero.1 h2).resolve_left fun h => ?_
      have := epsI_mul_self (k := k) (r := r) (piI k r i)
      rw [h] at this; simp at this
    · intro h
      have h3 : (piI k r i).val = r + a.val := congrArg Fin.val h
      have := a.isLt
      rw [hp] at h3
      split_ifs at h3 <;> omega
  · refine (hf _ _).trans ?_
    rw [h1]
    simp [blockIndex_injective.eq_iff, eq_comm]
  · rw [List.mem_singleton.1 hv, ← hg.2.2]
    refine (hf _ _).trans ?_
    rw [herm_smul_right, h1, if_neg, mul_zero]
    intro h
    have := congrArg Fin.val h
    have := a.isLt
    simp only [bl, wI, Fin.val_last] at *
    omega

end frame

section weight
open PI.UpqRep GlobalTheory.UnitaryHighestWeight

theorem not_cdom {k : ℕ} (Λ : Fin k → ℝ) {a b : Fin k} (hab : a < b) : ¬ CDom (allPos k) (Λ + root a b) Λ := by
  rintro ⟨c, hc, e⟩
  have hr : ∀ x y : Fin k, ∑ i : Fin k, (i.val : ℝ) * root x y i = x.val - y.val := by
    intro x y
    simp [root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
  have e2 := congrArg (fun f : Fin k → ℝ => ∑ i : Fin k, (i.val : ℝ) * f i) e
  have l : ∑ i : Fin k, (i.val : ℝ) * (Λ - (Λ + root a b)) i = -((a.val : ℝ) - b.val) := by
    rw [← hr, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp
  have r : ∑ i : Fin k, (i.val : ℝ) * (∑ x, ∑ y, (c x y : ℝ) • root x y) i =
      ∑ x, ∑ y, (c x y : ℝ) * ((x.val : ℝ) - y.val) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← hr]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => by ring
  simp only [l, r] at e2
  have h1 : ∑ x, ∑ y, (c x y : ℝ) * ((x.val : ℝ) - y.val) ≤ 0 := by
    refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
    by_cases h0 : c x y = 0
    · simp [h0]
    · have : (x.val : ℝ) < y.val := by exact_mod_cast (hc x y h0).1
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have : (a.val : ℝ) < b.val := by exact_mod_cast hab
  linarith

theorem lowK_add_rho {k : ℕ} (u : Fin k → ℝ) (s : Fin k) : lowK (allPos k) u s + Formalism.QuantumDeterminants.rhoStd k s = u s := by
  have h1 : (univ.filter fun b : Fin k => s < b) = Finset.Ioi s := by ext; simp
  have h2 : (univ.filter fun b : Fin k => b < s) = Finset.Iio s := by ext; simp
  have := s.isLt
  simp only [lowK, rhoN, rhoC, allPos, Formalism.QuantumDeterminants.rhoStd, Pi.add_apply, Pi.sub_apply, ne_eq, not_true, and_false,
    and_true, Finset.filter_false, Finset.card_empty, h1, h2, Fin.card_Ioi, Fin.card_Iio]
  rw [Nat.sub_sub, Nat.cast_sub (by omega)]
  push_cast
  ring

theorem qdet_eigen {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)} {u : Fin k → ℝ} (hπ : IsHCTypeU k u π)
    (E : Fin k → Fin k → Module.End ℂ W) (hgl : Formalism.REAL.GlRel E)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0) :
    ∃ v : W, v ≠ 0 ∧ ∀ Y : ℂ, Formalism.REAL.qdet E (Y + ((k : ℂ) - 1) / 2) v = (∏ s, (Y + (u s : ℂ))) • v := by
  obtain ⟨-, -, hU, -, -, -, ⟨v, -, hv, hw⟩, hdom⟩ := hπ
  have hw' := isWeight_of_isWtOn E hE _ v hw
  refine ⟨v, hv, fun Y => ?_⟩
  rw [Formalism.QuantumDeterminants.capelliHW W k E (fun a => (lowK (allPos k) u a : ℂ)) v hgl ⟨hw', fun a b hab => ?_⟩ Y]
  · simp only [Formalism.QuantumDeterminants.capP, ← Complex.ofReal_add, lowK_add_rho]
  · by_contra hne
    refine not_cdom _ hab (hdom _ _ trivial hne (isWtOn_of_isWeight hU E hE _ _ fun c => ?_))
    have h := LinearMap.congr_fun (hgl c c a b) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hw' c, map_smul] at h
    rw [sub_eq_iff_eq_add.1 h]
    by_cases h1 : c = a <;> by_cases h2 : b = c
    · exact absurd (h1 ▸ h2 ▸ hab) (lt_irrefl _)
    · subst h1; simp [root, h2, Ne.symm h2, add_smul, add_comm]
    · subst h2; simp [root, h1, add_smul, add_comm]
    · simp [root, h1, h2, Ne.symm h2]

end weight

section param
open PI.UpqRep PI.HwUniqW GlobalTheory.BesselFrame

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem prod_eq {u : ℕ → ℝ} {u₀ : Fin k → ℝ} (hπ : Q.IsType k r z π u) (h₀ : IsHCTypeW k r z u₀ π) (Y : ℂ) :
    ∏ s, (Y + (u₀ s : ℂ)) = ∏ s : Fin k, (Y + (u (s.val + 1) : ℂ)) := by
  obtain ⟨g, hg, h₀⟩ := h₀
  obtain ⟨E, hgl, -, hE⟩ := GlobalTheory.UnitaryDerived.exists_derived_action k W _ h₀.2.2.1
  obtain ⟨v, hv, hq⟩ := qdet_eigen h₀ E hgl hE
  have hB := isFrameOf hg
  obtain ⟨-, hrep, hcont, -, -, hcap⟩ := hπ
  set A := g * incl k r with hA
  set B := Aᴴ * Hpk k r with hBd
  have hd : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ x, Q.dRep π (A * Z * B) x = ∑ a, ∑ b, Z a b • E a b x := by
    intro Z hZ x
    rw [← (hE Z hZ x).deriv]
    unfold Q.dRep
    congr 1
    funext t
    rw [conj_blockW hg.1, ← exp_corner _ _ (co_mul hg.1), Matrix.mul_smul, Matrix.smul_mul]
  have hH : (Formalism.QuantumDeterminants.Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv Hpk_mul_self
  have hc : ∀ Y : Matrix (Fin k) (Fin k) ℂ,
      (Formalism.QuantumDeterminants.Hpk k r)⁻¹ * (A * Y * B)ᴴ * Formalism.QuantumDeterminants.Hpk k r = A * Yᴴ * B := by
    intro Y
    rw [hH, hBd]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_conjTranspose, ← Matrix.mul_assoc,
      Hpk_mul_self, Matrix.one_mul]
    rfl
  have hEB : Qr.EB π (fun a => g *ᵥ bvec (bl k r a)) = E := by
    funext a b
    refine LinearMap.ext fun x => ?_
    have hl := P.QrD.frame_lie hB a b
    show P.QrD.ecOp π _ x = _
    rw [← P.QrD.ecRep_eq hrep hcont hl.1 hl.2, unitB_eq]
    unfold Q.EcRep Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [← hA, ← hBd, hc, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.smul_mul,
      ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.mul_smul, hd, hd]
    · simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← add_smul]
      have e : ∀ c d, ((1 / 2 : ℂ) • (Matrix.single a b (1 : ℂ) - (Matrix.single a b (1 : ℂ))ᴴ)) c d +
          Complex.I * ((1 / (2 * Complex.I) : ℂ) • (Matrix.single a b (1 : ℂ) + (Matrix.single a b (1 : ℂ))ᴴ)) c d =
          Matrix.single a b (1 : ℂ) c d := by
        intro c d
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
        field_simp
        ring
      simp only [e]
      simp [Matrix.single, ite_and, ite_smul]
    · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, ← neg_smul, add_comm]
      congr 1
      simp [Complex.conj_ofNat]
    · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, ← smul_neg, neg_sub]
      congr 1
      simp
  have h1 := (P.frame_general_linear W k r k z π _ ⟨hrep, hcont⟩ hB).2 (Y + ((k : ℂ) - 1) / 2) v
  rw [hEB, hq, hcap _ hB] at h1
  rw [← smul_left_injective ℂ hv h1, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range,
    Nat.add_sub_cancel, ← Fin.prod_univ_eq_prod_range (fun i => Y + ((k : ℂ) - 1) / 2 - k / 2 + 1 / 2 + (u (1 + i) : ℂ))]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [add_comm 1 s.val]
  ring

end param

section main
open PI.BesselPeriodGGP

end main

end GlobalTheory.SupNonzero
