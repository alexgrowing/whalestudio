import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExCayK
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExOm

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

section Chart

variable (P Q : ℕ)

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem two_eq : (1 + 1 : Mat) = (2 : ℂ) • (1 : Mat) := (two_smul ℂ (1 : Mat)).symm

theorem cayCand_mem (g : UpqT P Q) : cayCand P Q g ∈ lieU P Q := by
  set G := UpqT.mat g with hG
  set J := HcS.UG.Jpq P Q
  have hU : Gᴴ * J * G = J := by
    have := (mem_Upq_iff P Q _).1 (toS P Q g).2
    rwa [← mat_eq] at this
  by_cases hu : IsUnit (G + 1).det
  · set K := (G + 1)⁻¹
    set X := cayCand P Q g with hX
    have hXdef : X = (1 + 1) * K * (G - 1) := rfl
    have hKG : K * (G + 1) = 1 := Matrix.nonsing_inv_mul _ hu
    have hGK : (G + 1) * K = 1 := Matrix.mul_nonsing_inv _ hu
    have hXG : X * (G + 1) = (1 + 1) * (G - 1) := by
      have e : (G - 1) * (G + 1) = (G + 1) * (G - 1) := by noncomm_ring
      rw [hXdef, Matrix.mul_assoc, Matrix.mul_assoc, e, ← Matrix.mul_assoc K, hKG, Matrix.one_mul]
    have hu' : IsUnit (G + 1)ᴴ.det := by
      rw [Matrix.det_conjTranspose]
      exact hu.star
    show Xᴴ * J + J * X = 0
    have key : (G + 1)ᴴ * (Xᴴ * J + J * X) * (G + 1) = 0 := by
      have e1 : (G + 1)ᴴ * (Xᴴ * J + J * X) * (G + 1) =
          (X * (G + 1))ᴴ * J * (G + 1) + (G + 1)ᴴ * J * (X * (G + 1)) := by
        rw [Matrix.conjTranspose_mul]
        noncomm_ring
      have hJ : Jᴴ = J := Jpq_conjTranspose P Q
      have h2 : ((1 : Mat) + 1)ᴴ = 1 + 1 := by simp
      rw [e1, hXG, Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
        Matrix.conjTranspose_one]
      have e2 : (Gᴴ - 1) * (1 + 1) * J * (G + 1) + (Gᴴ + 1) * J * ((1 + 1) * (G - 1)) =
          (1 + 1) * ((1 + 1) * (Gᴴ * J * G - J)) := by noncomm_ring
      rw [e2, hU, sub_self, Matrix.mul_zero, Matrix.mul_zero]
    have e3 : Xᴴ * J + J * X =
        ((G + 1)ᴴ)⁻¹ * ((G + 1)ᴴ * (Xᴴ * J + J * X) * (G + 1)) * K := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu', Matrix.one_mul,
        Matrix.mul_assoc, hGK, Matrix.mul_one]
    rw [e3, key, Matrix.mul_zero, Matrix.zero_mul]
  · have : cayCand P Q g = 0 := by
      show (1 + 1) * (G + 1)⁻¹ * (G - 1) = 0
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hu, Matrix.mul_zero, Matrix.zero_mul]
    rw [this]
    exact (lieU P Q).zero_mem

theorem cayInv_eq (g : UpqT P Q) : cayInv P Q g = ⟨cayCand P Q g, cayCand_mem P Q g⟩ := by
  unfold cayInv
  rw [dif_pos (cayCand_mem P Q g)]

end Chart

theorem cayley_inverse_iff : CayInvIff := by
  intro P Q g X h
  set G := UpqT.mat g with hG
  set Y : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)
  rw [two_eq] at h
  have h4 : (G + 1) * ((2 : ℂ) • (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) - Y) =
      (4 : ℂ) • (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := by
    rw [add_mul, one_mul, h, show (4 : ℂ) = 2 + 2 by norm_num, add_smul]
    abel
  have hB : (G + 1) * ((1 / 4 : ℂ) • ((2 : ℂ) • (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) - Y)) = 1 := by
    rw [Matrix.mul_smul, h4, smul_smul]
    norm_num
  have hu : IsUnit (G + 1).det := Matrix.isUnit_det_of_right_inverse hB
  have hGY : G * Y = (2 : ℂ) • G - ((2 : ℂ) • (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) + Y) := by
    rw [← h, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
    abel
  have hXY : (G + 1) * Y = (2 : ℂ) • (G - 1) := by
    rw [add_mul, one_mul, hGY, smul_sub]
    abel
  have hc : cayCand P Q g = Y := by
    show (1 + 1) * (G + 1)⁻¹ * (G - 1) = Y
    have eY : Y = (G + 1)⁻¹ * ((G + 1) * Y) := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [eY, hXY, Matrix.mul_smul, two_eq, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [cayInv_eq]
  exact Subtype.ext hc

theorem cayley_inverse_measurable : CayInvMeas := by
  intro P Q
  set O : Set (UpqT P Q) := {g | (UpqT.mat g + 1).det ≠ 0}
  have hmat : Continuous (UpqT.mat (P := P) (Q := Q)) := (isInducing_mat P Q).continuous
  have hdet : Continuous fun g : UpqT P Q => (UpqT.mat g + 1).det :=
    (hmat.add continuous_const).matrix_det
  have hO : IsOpen O := isOpen_ne_fun hdet continuous_const
  have hcand : Continuous fun g : O => cayCand P Q g := by
    have hm : Continuous fun g : O => UpqT.mat (g : UpqT P Q) := hmat.comp continuous_subtype_val
    have hd : Continuous fun g : O => (UpqT.mat (g : UpqT P Q) + 1).det :=
      hdet.comp continuous_subtype_val
    have hinv : Continuous fun g : O => (UpqT.mat (g : UpqT P Q) + 1)⁻¹ := by
      have e : (fun g : O => (UpqT.mat (g : UpqT P Q) + 1)⁻¹) =
          fun g : O => ((UpqT.mat (g : UpqT P Q) + 1).det)⁻¹ • (UpqT.mat (g : UpqT P Q) + 1).adjugate := by
        funext g
        rw [Matrix.inv_def, Ring.inverse_eq_inv']
      rw [e]
      exact (hd.inv₀ fun g => g.2).smul (hm.add continuous_const).matrix_adjugate
    exact (continuous_const.matrix_mul hinv).matrix_mul (hm.sub continuous_const)
  have hcont : ContinuousOn (cayInv P Q) O := by
    refine continuousOn_iff_continuous_domRestrict.2 ?_
    show Continuous fun g : O => cayInv P Q g
    have e : (fun g : O => cayInv P Q g) = fun g : O => ⟨cayCand P Q g, cayCand_mem P Q g⟩ := by
      funext g
      exact cayInv_eq P Q g
    rw [e]
    exact Continuous.subtype_mk hcand _
  have hpw : O.piecewise (cayInv P Q) (fun _ => 0) = cayInv P Q := by
    funext g
    by_cases hg : g ∈ O
    · exact Set.piecewise_eq_of_mem _ _ _ hg
    · rw [Set.piecewise_eq_of_notMem _ _ _ hg]
      have hg' : ¬IsUnit (UpqT.mat g + 1).det := fun hu => hg hu.ne_zero
      rw [cayInv_eq]
      apply Subtype.ext
      show 0 = (1 + 1) * (UpqT.mat g + 1)⁻¹ * (UpqT.mat g - 1)
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hg', Matrix.mul_zero, Matrix.zero_mul]
  rw [← hpw]
  classical
  exact hcont.measurable_piecewise continuousOn_const hO.measurableSet

theorem cayley_set_measurable : CaySUnivMeas := by
  intro P Q
  have hmat : Continuous (UpqT.mat (P := P) (Q := Q)) := (isInducing_mat P Q).continuous
  set C : Set (UpqT P Q × lieU P Q) := {p | UpqT.mat p.1 *
    ((1 + 1) - ((p.2 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) =
      (1 + 1) + ((p.2 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)}
  have hC : IsClosed C := by
    have hv : Continuous fun p : UpqT P Q × lieU P Q =>
        ((p.2 : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
      continuous_subtype_val.comp continuous_snd
    exact isClosed_eq ((hmat.comp continuous_fst).matrix_mul (continuous_const.sub hv))
      (continuous_const.add hv)
  have e : cayS (Set.univ : Set (lieU P Q)) = (fun g => (g, cayInv P Q g)) ⁻¹' C := by
    ext g
    constructor
    · rintro ⟨X, -, h⟩
      show UpqT.mat g * ((1 + 1) - ((cayInv P Q g : lieU P Q) :
          Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) =
        (1 + 1) + ((cayInv P Q g : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)
      rw [cayley_inverse_iff P Q g X h]
      exact h
    · intro h
      exact ⟨cayInv P Q g, Set.mem_univ _, h⟩
  rw [e]
  exact (measurable_id.prodMk (cayley_inverse_measurable P Q)) hC.measurableSet

theorem cayleyLoc_of_dens (h : CayleyDens) : CayleyLoc :=
  cayleyLoc_of cayley_inverse_measurable cayley_inverse_iff cayley_set_measurable h

end HcInf
