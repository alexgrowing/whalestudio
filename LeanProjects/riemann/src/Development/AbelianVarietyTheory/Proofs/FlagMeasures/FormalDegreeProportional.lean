import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DegreeTie

open Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

theorem map_phi_eq {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P Q : MatKR k r} (hP : IsCayley k r ε P)
    (hQ : IsCayley k r ε Q) : (Formalism.REAL.muG ε).map (phi ε P) = (Formalism.REAL.muG ε).map (phi ε Q) := by
  obtain ⟨hPu, hPJ⟩ := hP
  obtain ⟨hQu, hQJ⟩ := hQ

  set Pu := hPu.unit with hPu_def
  set Qu := hQu.unit with hQu_def
  have hQQ : Q * Q⁻¹ = 1 := by
    rw [← hQu.unit_spec, ← Matrix.coe_units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmJ : (P * Q⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * Q⁻¹) = Formalism.REAL.Jm ε := by
    have h1 : (Q⁻¹)ᴴ * Qᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hQQ, Matrix.conjTranspose_one]
    calc (P * Q⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * Q⁻¹) = (Q⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * Q⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((Q⁻¹)ᴴ * Qᴴ) * Formalism.REAL.Jm ε * (Q * Q⁻¹) := by
          rw [hPJ, ← hQJ]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h1, hQQ, Matrix.one_mul, Matrix.mul_one]
  have hmem : Pu * Qu⁻¹ ∈ Formalism.REAL.UJ ε := by
    have hv : ((Pu * Qu⁻¹ : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
        Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = P * Q⁻¹ := by
      rw [Units.val_mul, Matrix.coe_units_inv, hPu_def, hQu_def, hPu.unit_spec, hQu.unit_spec]
    show Formalism.REAL.inUJ ε _
    rw [hv]
    exact hmJ
  set m : Formalism.REAL.UJ ε := ⟨Pu * Qu⁻¹, hmem⟩ with hm_def
  have hval : ∀ (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hA : IsUnit A)
      (u : Formalism.REAL.UJ ε), phi ε A u = ((hA.unit⁻¹ * (u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) * hA.unit :
        (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := by
    intro A hA u
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hA.unit_spec]
    rfl
  have hconj : phi ε Q = phi ε P ∘ (fun u => m * u * m⁻¹) := by
    funext u
    rw [Function.comp_apply, hval Q hQu, hval P hPu]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hm_def]
    rw [hPu_def, hQu_def]
    group <;> rfl
  have hcont : ∀ A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Continuous (phi ε A) := by
    intro A
    have : Continuous (fun u : Formalism.REAL.UJ ε =>
        ((u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
      Units.continuous_val.comp continuous_subtype_val
    exact (continuous_const.matrix_mul this).matrix_mul continuous_const
  have hinv : (Formalism.REAL.muG ε).map (fun u => m * u * m⁻¹) = Formalism.REAL.muG ε := by
    have hL : Measurable (fun u : Formalism.REAL.UJ ε => m * u) := measurable_const_mul m
    have hR : Measurable (fun u : Formalism.REAL.UJ ε => u * m⁻¹) := measurable_mul_const m⁻¹
    calc (Formalism.REAL.muG ε).map (fun u => m * u * m⁻¹)
        = ((Formalism.REAL.muG ε).map (fun u => m * u)).map (fun u => u * m⁻¹) := by
          rw [Measure.map_map hR hL]; rfl
      _ = (Formalism.REAL.muG ε).map (fun u => u * m⁻¹) := by
          rw [MeasureTheory.map_mul_left_eq_self (Formalism.REAL.muG ε) m]
      _ = Formalism.REAL.muG ε := Formalism.REAL.indefinite_unitary_unimodular _ ε m⁻¹
  rw [hconj, ← Measure.map_map (hcont P).measurable (by
    exact (measurable_const_mul m).mul_const m⁻¹), hinv]

theorem deg_eq_mul_fdegH : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS), cdScaleTie D → GoodW D τ w w' θ W → ∃ κ : ℝ, 0 < κ ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → ∀ v : A.H, v ≠ 0 → A.deg = κ * PI.BesselPeriodGGP.fdegH W.μG A.σ v ∧ 0 < A.deg := by
  intro _ D τ w w' θ W _ hW

  by_cases hC : ∃ P0 : MatKR D.R.k D.R.rS, IsCayley D.R.k D.R.rS (epsSH D.R) P0
  swap
  · refine ⟨1, one_pos, ?_⟩
    intro lam A hA
    obtain ⟨P, hP, -⟩ := hA.2.2.2.2.2.2.2.2.2.2
    exact absurd ⟨P, hP⟩ hC
  obtain ⟨P0, hP0⟩ := hC
  have hP0det : IsUnit P0.det := (Matrix.isUnit_iff_isUnit_det P0).1 hP0.1
  obtain ⟨c, hc0, hctop, hμ⟩ :=
    GlobalTheory.BesselDegree.haar_eq_smul (ε := epsSH D.R) hP0det hP0.2 W.μG hW.2.2.2.2.2.2.1
  set cd : NNReal := D.s.cdScale _ (epsSH D.R) with hcd_def

  have hI : ∀ (P : MatKR D.R.k D.R.rS), IsCayley D.R.k D.R.rS (epsSH D.R) P →
      ∀ (F : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ),
        ∫ x, F x ∂W.μG = c.toReal * ∫ u, F (phi (epsSH D.R) P u) ∂(Formalism.REAL.muG (epsSH D.R)) := by
    intro P hP F
    have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).1 hP.1)
    have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).1 hP.1)
    let h : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ ≃ₜ
        Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
      { toFun := fun x => P⁻¹ * x * P
        invFun := fun x => P * x * P⁻¹
        left_inv := fun x => by
          simp only [← Matrix.mul_assoc, hPP, Matrix.one_mul]
          rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
        right_inv := fun x => by
          simp only [← Matrix.mul_assoc, hPP', Matrix.one_mul]
          rw [Matrix.mul_assoc, hPP', Matrix.mul_one]
        continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
        continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
    have hemb : Topology.IsClosedEmbedding (phi (epsSH D.R) P) :=
      h.isClosedEmbedding.comp (Formalism.REAL.isClosedEmbeddingMatrix _ (epsSH D.R)).1
    rw [hμ, map_phi_eq hP0 hP, integral_smul_measure, smul_eq_mul,
      hemb.measurableEmbedding.integral_map]
  by_cases hcd : cd = 0
  · refine ⟨1, one_pos, ?_⟩
    intro lam A hA v hv
    obtain ⟨P, -, hF⟩ := hA.2.2.2.2.2.2.2.2.2.2
    have h2 := (hF.2 v v v v).2
    rw [← hcd_def] at h2
    rw [hcd, ENNReal.coe_zero, zero_smul, integral_zero_measure] at h2
    have hv' : (⟪v, v⟫_ℂ : ℂ) ≠ 0 := inner_self_ne_zero.2 hv
    have hd : (A.deg : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hF.1.ne'
    exact absurd h2.symm (div_ne_zero (mul_ne_zero hv' hv') hd)
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hctop
  have hcdpos : (0 : ℝ) < cd := by
    rw [NNReal.coe_pos]; exact pos_iff_ne_zero.2 hcd
  refine ⟨c.toReal / cd, div_pos hcpos hcdpos, ?_⟩
  intro lam A hA v hv
  obtain ⟨P, hP, hF⟩ := hA.2.2.2.2.2.2.2.2.2.2
  refine ⟨?_, hF.1⟩
  have h2 := (hF.2 v v v v).2
  rw [← hcd_def] at h2

  set J := ∫ u, ‖⟪v, A.σ (P⁻¹ * ((u : (Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)ˣ) :
      Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) * P) v⟫_ℂ‖ ^ 2
      ∂(Formalism.REAL.muG (epsSH D.R)) with hJ
  have hJc : ((cd : ℝ) * J : ℂ) = (‖v‖ ^ 4 / A.deg : ℝ) := by
    have hin : (⟪v, v⟫_ℂ : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    have hint : ∫ g, coefOn (fun g => A.σ (P⁻¹ * g * P)) v v g * star (coefOn (fun g => A.σ (P⁻¹ * g * P)) v v g)
        ∂(Formalism.REAL.muG (epsSH D.R)) = ((J : ℝ) : ℂ) := by
      rw [hJ, ← integral_complex_ofReal]
      congr 1
      funext g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    rw [integral_smul_measure, hint, hin, ENNReal.coe_toReal, Complex.real_smul] at h2
    rw [h2]
    push_cast
    ring
  have hJr : (cd : ℝ) * J = ‖v‖ ^ 4 / A.deg := by exact_mod_cast hJc
  have hIv := hI P hP (fun x => ‖⟪v, A.σ (Matrix.of x) v⟫_ℂ‖ ^ 2)
  have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hdeg := hF.1
  unfold PI.BesselPeriodGGP.fdegH
  rw [hIv]
  change A.deg = c.toReal / cd * (‖v‖ ^ 4 / (c.toReal * J))
  have hJ' : J = ‖v‖ ^ 4 / A.deg / cd := by
    rw [← hJr]; field_simp
  rw [hJ']
  field_simp

end GlobalTheory.DegreeTie

end
