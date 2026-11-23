import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft

open MeasureTheory Matrix
open scoped NNReal

namespace GlobalTheory.CompanionTheory.GLUnimod

variable {n : ℕ}

noncomputable def dg (d : Fin n → ℂˣ) : GL (Fin n) ℂ where
  val := diagonal fun i => (d i : ℂ)
  inv := diagonal fun i => (((d i)⁻¹ : ℂˣ) : ℂ)
  val_inv := by simp [diagonal_mul_diagonal, diagonal_one]
  inv_val := by simp [diagonal_mul_diagonal, diagonal_one]

theorem dg_mul (d e : Fin n → ℂˣ) : dg (d * e) = dg d * dg e := by
  apply Units.ext
  simp [dg, diagonal_mul_diagonal]

theorem dg_one : dg (1 : Fin n → ℂˣ) = 1 := by
  apply Units.ext
  simp [dg, diagonal_one]

noncomputable def pm (σ : Equiv.Perm (Fin n)) : GL (Fin n) ℂ where
  val := σ.toPEquiv.toMatrix
  inv := σ.symm.toPEquiv.toMatrix
  val_inv := by rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [one_apply, eq_comm]
  inv_val := by rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [one_apply, eq_comm]

theorem pm_mul_dg (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂˣ) :
    pm σ * dg d = dg (d ∘ σ) * pm σ := by
  ext1
  ext i j
  simp only [pm, dg, Units.val_mul, mul_diagonal, diagonal_mul, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Function.comp_apply]
  split_ifs with h
  · subst h
    ring
  · ring

noncomputable def tv {i j : Fin n} (hij : i ≠ j) (c : ℂ) : GL (Fin n) ℂ where
  val := transvection i j c
  inv := transvection i j (-c)
  val_inv := by rw [transvection_mul_transvection_same _ _ hij]; simp
  inv_val := by rw [transvection_mul_transvection_same _ _ hij]; simp

theorem tv_mul {i j : Fin n} (hij : i ≠ j) (c : ℂ) : tv hij c * tv hij c = tv hij (2 * c) := by
  ext1
  simp only [tv, Units.val_mul]
  rw [transvection_mul_transvection_same _ _ hij, two_mul]

theorem dg_mul_tv {i j : Fin n} (hij : i ≠ j) (c : ℂ) (d : Fin n → ℂˣ) (hi : (d i : ℂ) = 2)
    (hj : (d j : ℂ) = 1) : dg d * tv hij c = tv hij (2 * c) * dg d := by
  ext1
  ext k l
  simp only [dg, tv, Units.val_mul, transvection, diagonal_mul, mul_diagonal, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hk : i = k <;> by_cases hl : j = l
  · subst hk hl
    simp [hij, hi, hj]
  · subst hk
    simp [hl]
    split_ifs with h <;> simp only [h]
  · subst hl
    simp [hk]
    split_ifs with h <;> simp only [h]
  · simp [hk, hl]
    split_ifs with h <;> simp only [h]

theorem char_ne_zero {H : Type*} [Group H] (χ : H →* ℝ≥0) (g : H) : χ g ≠ 0 := by
  intro h
  have h1 : χ g * χ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem char_tv (χ : GL (Fin n) ℂ →* ℝ≥0) {i j : Fin n} (hij : i ≠ j) (c : ℂ) :
    χ (tv hij c) = 1 := by
  have h1 : χ (tv hij c) * χ (tv hij c) = χ (tv hij (2 * c)) := by rw [← map_mul, tv_mul]
  let d : Fin n → ℂˣ := fun k => if k = i then Units.mk0 2 two_ne_zero else 1
  have hi : (d i : ℂ) = 2 := by simp [d]
  have hj : (d j : ℂ) = 1 := by simp [d, hij.symm]
  have h2 : χ (dg d) * χ (tv hij c) = χ (tv hij (2 * c)) * χ (dg d) := by
    rw [← map_mul, ← map_mul, dg_mul_tv hij c d hi hj]
  have h3 : χ (tv hij c) = χ (tv hij (2 * c)) := by
    rw [mul_comm (χ (tv hij (2 * c)))] at h2
    exact mul_left_cancel₀ (char_ne_zero χ _) h2
  have h4 : χ (tv hij c) * χ (tv hij c) = χ (tv hij c) * 1 := by rw [mul_one, h1, h3]
  exact mul_left_cancel₀ (char_ne_zero χ _) h4

theorem char_dg (χ : GL (Fin n) ℂ →* ℝ≥0) (hz : ∀ z : GL (Fin n) ℂ, (∀ g, z * g = g * z) → χ z = 1)
    (d : Fin n → ℂˣ) : χ (dg d) = 1 := by
  let D : (Fin n → ℂˣ) →* GL (Fin n) ℂ :=
    { toFun := dg, map_one' := dg_one, map_mul' := dg_mul }
  have hperm : ∀ σ : Equiv.Perm (Fin n), χ (dg (d ∘ σ)) = χ (dg d) := by
    intro σ
    have h := congrArg χ (pm_mul_dg σ d)
    rw [map_mul, map_mul, mul_comm (χ (pm σ))] at h
    exact (mul_right_cancel₀ (char_ne_zero χ (pm σ)) h).symm
  obtain ⟨v, hv_def⟩ : ∃ v : Fin n → ℂˣ, v = ∏ σ : Equiv.Perm (Fin n), d ∘ σ := ⟨_, rfl⟩
  have hv : ∀ k l, v k = v l := by
    intro k l
    rw [hv_def, Finset.prod_apply, Finset.prod_apply]
    exact Fintype.prod_equiv (Equiv.mulRight (Equiv.swap k l)) _ _
      (fun σ => by simp [Equiv.Perm.mul_apply, Equiv.swap_apply_right])
  have hcent : ∀ g, dg v * g = g * dg v := by
    intro g
    ext1
    ext k l
    simp only [dg, Units.val_mul, diagonal_mul, mul_diagonal]
    rw [hv k l, mul_comm]
  have h1 : χ (dg v) = 1 := hz _ hcent
  have h2 : χ (dg v) = χ (dg d) ^ (Fintype.card (Equiv.Perm (Fin n))) := by
    have e : χ (dg v) = (χ.comp D) v := rfl
    rw [e, hv_def, map_prod]
    simp only [MonoidHom.comp_apply, D, MonoidHom.coe_mk, OneHom.coe_mk, hperm]
    rw [Finset.prod_const, Finset.card_univ]
  have hm : Fintype.card (Equiv.Perm (Fin n)) ≠ 0 := Fintype.card_ne_zero
  rw [h1] at h2
  exact (pow_eq_one_iff_of_nonneg (by simp) hm).1 h2.symm

theorem char_eq_one (χ : GL (Fin n) ℂ →* ℝ≥0)
    (hz : ∀ z : GL (Fin n) ℂ, (∀ g, z * g = g * z) → χ z = 1) (g : GL (Fin n) ℂ) : χ g = 1 := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ u : GL (Fin n) ℂ, (u : Matrix (Fin n) (Fin n) ℂ) = M → χ u = 1)
    (g : Matrix (Fin n) (Fin n) ℂ) ?_ ?_ ?_ ?_ g rfl
  · exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  · intro D hD u hu
    rw [det_diagonal] at hD
    have hD' : ∀ i, D i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
    have hu' : u = dg (fun i => Units.mk0 (D i) (hD' i)) := by
      ext1
      simp [hu, dg]
    rw [hu']
    exact char_dg χ hz _
  · intro t u hu
    have hu' : u = tv t.hij t.c := by
      ext1
      simp [hu, tv, Matrix.TransvectionStruct.toMatrix]
    rw [hu']
    exact char_tv χ t.hij t.c
  · intro A B hA hB hPA hPB u hu
    obtain ⟨a, rfl⟩ : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hA)
    obtain ⟨b, rfl⟩ : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.2 hB)
    have hu' : u = a * b := by
      ext1
      simp [hu]
    rw [hu', map_mul, hPA a rfl, hPB b rfl, one_mul]

theorem unimod : PositivityTheory.RgBcC.Unimod := by
  intro n _ _ μ _
  haveI : T2Space (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (T2Space (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℂ)).symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (PositivityTheory.RgTw.G n) :=
    (Units.isClosedEmbedding_embedProduct :
      Topology.IsClosedEmbedding (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ))).locallyCompactSpace
  haveI : SecondCountableTopology (PositivityTheory.RgTw.G n) :=
    (Units.isEmbedding_embedProduct :
      Topology.IsEmbedding (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ))).secondCountableTopology
  have hmap : ∀ g : PositivityTheory.RgTw.G n,
      Measure.map (· * g) μ = Measure.modularCharacter g • μ := by
    intro g
    have e1 := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ
    have e2 := Measure.modularCharacterFun_eq_haarScalarFactor μ g
    rw [← e2] at e1
    exact e1
  have hχ : ∀ g : PositivityTheory.RgTw.G n, Measure.modularCharacter g = 1 := by
    refine char_eq_one Measure.modularCharacter ?_
    intro z hz
    have hc : Measure.map (· * z) μ = μ := by
      have h : (fun x => x * z) = (fun x => z * x) := funext fun x => (hz x).symm
      rw [h, map_mul_left_eq_self]
    have e2 := Measure.modularCharacterFun_eq_haarScalarFactor μ z
    simp only [hc, Measure.haarScalarFactor_self] at e2
    exact e2
  have hR : μ.IsMulRightInvariant := ⟨fun g => by rw [hmap, hχ g, one_smul]⟩
  exact ⟨hR, GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ⟩

end GlobalTheory.CompanionTheory.GLUnimod
