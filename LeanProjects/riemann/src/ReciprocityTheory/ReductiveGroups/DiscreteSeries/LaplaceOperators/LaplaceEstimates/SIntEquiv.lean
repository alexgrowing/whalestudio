import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportGeo
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.EquivA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.HcTypeWURep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition

noncomputable section

open Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence

open Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS

variable {k r : ℕ}

def biEquiv (a b : Mat k r) (ha : IsUnit a.det) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := (a * Matrix.of x * b : Mat k r)
  invFun x := (a⁻¹ * Matrix.of x * b⁻¹ : Mat k r)
  left_inv x := by
    show a⁻¹ * (a * Matrix.of x * b) * b⁻¹ = Matrix.of x
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ ha, Matrix.mul_nonsing_inv _ hb,
      Matrix.mul_one]
  right_inv x := by
    show a * (a⁻¹ * Matrix.of x * b⁻¹) * b = Matrix.of x
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ ha, Matrix.nonsing_inv_mul _ hb,
      Matrix.mul_one]
  measurable_toFun := by
    have hc : @Continuous (Mt k r) (Mt k r) _ _ (fun x : Mt k r => (a * Matrix.of x * b : Mat k r)) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact hc.measurable
  measurable_invFun := by
    have hc : @Continuous (Mt k r) (Mt k r) _ _ (fun x : Mt k r => (a⁻¹ * Matrix.of x * b⁻¹ : Mat k r)) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact hc.measurable

theorem sInt_equiv {u : Fin k → ℝ} {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {Vp : Type}
    [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
    {μW μN : Measure (Mt k r)} (hB : IsBData z c u π μW μN) (f : Mat k r → ℂ) (ξ : Vp) (g : Mat k r)
    {h₀ m₀ : Mat k r} (hh₀ : h₀ ∈ UWset k r z) (hm₀ : m₀ ∈ Nset k r) :
    sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π f ξ (h₀ * m₀ * g) =
      Formalism.MainNotions.S.psiGen k r z c m₀ • π h₀ (sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π f ξ g) := by
  obtain ⟨hz, hT, -, hHC, hW, hN⟩ := hB
  have hπ : Formalism.MainNotions.S.IsURepOn (UWset k r z) π := hcTypeW_uRep k r z u Vp π hz hT hHC
  have hMP := Mult1.S0.A.shift_measurePreserving Mult1.haarUniqueSF' Formalism.FourierDecayAlt.P.weyl_subgroup_closed
    Formalism.FourierDecayAlt.P.weyl_haar_exists Formalism.FourierDecayAlt.P.unipotent_radical_closed Formalism.FourierDecayAlt.P.unipotent_haar_exists
    Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof hz hT hW hN hh₀ hm₀
  have hd := TransportGeo.uh_det hh₀.1
  have hdm := TransportGeo.uh_det hm₀.1
  let e := MeasurableEquiv.prodCongr (biEquiv (1 : Mat k r) h₀ (by simp) hd)
    (biEquiv h₀⁻¹ (h₀ * m₀) (TransportGeo.uh_det (TransportGeo.uh_inv hh₀.1))
      (TransportGeo.uh_det (TransportGeo.uh_mul hh₀.1 hm₀.1)))
  have he : (fun p : Mt k r × Mt k r => Prod.mk (α := Mt k r) (β := Mt k r) (Matrix.of p.1 * h₀ : Mat k r)
      (h₀⁻¹ * Matrix.of p.2 * h₀ * m₀ : Mat k r)) = e := by
    funext p
    refine Prod.ext ?_ ?_
    · show (Matrix.of p.1 * h₀ : Mat k r) = 1 * Matrix.of p.1 * h₀
      rw [Matrix.one_mul]
    · exact Matrix.mul_assoc _ h₀ m₀
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hWae : ∀ᵐ y ∂μW, Matrix.of y ∈ UWset k r z := by rw [ae_iff]; simpa using hW.2.2.1
  have hNae : ∀ᵐ y ∂μN, Matrix.of y ∈ Nset k r := by rw [ae_iff]; simpa using hN.2.2.1
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  set F : Mt k r × Mt k r → Vp := fun p => f (Matrix.of p.1 * Matrix.of p.2 * g) •
    chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ with hF
  let L : Vp →ₗᵢ[ℂ] Vp := ⟨(π h₀ : Vp →ₗ[ℂ] Vp), hπ.2.1 h₀ hh₀⟩
  have h1 : sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π f ξ (h₀ * m₀ * g) =
      ∫ p, Formalism.MainNotions.S.psiGen k r z c m₀ • L (F (e p)) ∂(μW.prod μN) := by
    unfold sInt
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    rw [← he]
    exact Mult1.S0.A.integrand_shift Formalism.FourierDecayAlt.P.weyl_subgroup_closed Formalism.FourierDecayAlt.P.unipotent_radical_closed
      Formalism.QuantumDeterminants.unitary_weyl_normal_holds hz c hπ f ξ hh₀ hm₀ hp.1 hp.2
  rw [he] at hMP
  rw [h1, integral_smul, L.integral_comp_comm (fun p => F (e p)), hMP.integral_comp' F]
  rfl

end ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence
