import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BijectiveCompAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticWeightLinearComb

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.ModelShift

theorem isSelfInter_shift_model : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (L : HermLB M.p) (Δ : Y.Dv) (r : (L.B.pull M.j).ι → Y.Fnˣ), Presents Δ (L.B.pull M.j) r → ∀ (t : (𝓞 F →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (a : ℝ), (haveI := M.ar.isIntegral; L.IsSelfInter a) → (haveI := M.ar.isIntegral; (L.shift t ht).IsSelfInter (a + ((Y.dim : ℝ) + 1) * (Y.inter (fun _ => Δ) : ℝ) * ∑ σ : F →+* ℂ, t (σ.comp (algebraMap (𝓞 F) F)))) := by
  intro hc hd F _ _ Y M L Δ r hr t ht a ha
  have := M.ar.isIntegral
  let E := Equiv.ofBijective _ (TwistTop.bijective_comp_algebraMap F)
  have key (σ : F →+* ℂ) : (L.φ (σ.comp (algebraMap (𝓞 F) F))).chernInt Y.dim Set.univ (fun _ => 1) =
      (Y.inter (fun _ => Δ) : ℝ) := by
    obtain ⟨Φ, hΦ⟩ := TwistTop.exists_homeomorph F Y M σ
    have := CxPts.secondCountableTopology_of_isProjOver (σ.comp (algebraMap (𝓞 F) F)) M.ar.isProjOver
    obtain ⟨h₁, h₂⟩ := GlobalTheory.chernInt_transfer _ _ _ _ M.p Y.str _ σ Y.dim M.j Φ hΦ
      (GlobalTheory.ModelCharts.genSmooth_model F Y M _) inferInstance _ _ (L.cInf _)
    exact h₂.symm.trans (hd.2 F Y σ Δ _ r hr _ h₁).2
  have e₁ : ∑ᶠ τ, t τ * (L.φ τ).chernInt Y.dim Set.univ (fun _ => 1) =
      (Y.inter (fun _ => Δ) : ℝ) * ∑ σ : F →+* ℂ, t (σ.comp (algebraMap (𝓞 F) F)) := by
    rw [← finsum_comp_equiv E, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [show (L.φ (E σ)).chernInt Y.dim Set.univ (fun _ => 1) = _ from key σ, mul_comm]
    rfl
  have h := TwistTop.isSelfInter_shift hc.1 hc.2.1 _ _ _ _ M.ar L a t ht ha
  rw [e₁, ← mul_assoc] at h
  exact h

end GlobalTheory.ModelShift
