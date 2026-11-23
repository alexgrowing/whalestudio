import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfLnSymUpdateSubLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverInducedMetricsArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightBoundedByPrimeWeights
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.LocM
open GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open GlobalTheory.PairTerm
open Classical

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.VertPassDeg

theorem passDeg : GlobalTheory.Published.ArCalc → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (ι : Type) [Fintype ι]
    (A : ι → Adl (cxSt F) Y) (L : ι → HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ),
    (∀ i, (A i).Induced M (L i) m 0) → (haveI := M.ar.isIntegral; IsArFun L Y.dim Ψ) →
    ∃ (V : Cover Y) (L' : ι → HermLB V.p),
      (∀ i, Norms V (L' i) (fun x => genAt (A i).D x ^ (m : ℕ)) (fun σ y => (m : ℕ) * lnAdl (A i) σ y)
        (fun v e y => (m : ℕ) * (A i).lg v e y)) ∧ IsArFun L' Y.dim ((V.deg : ℝ) • Ψ) := by
  intro hA F _ _ Y M ι _ A L m Ψ hI hΨ
  haveI := M.ar.isIntegral
  obtain ⟨Q, ρ, -, hQ, hρ, -, hj, -, -, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M
  haveI := Q.ar.isIntegral
  obtain ⟨eρ, dρ⟩ := GlobalTheory.CoverModelDeg.map_genericPoint_and_deg F Y (Cover.ofModel Q hQ) M ρ hρ
    (by simpa [Cover.ofModel] using hj)
  rw [Cover.deg_ofModel] at dρ
  have dρ' : ρ.residueDegree (genericPoint Q.X) = 1 := dρ
  have nρ : ρ.residueDegree (genericPoint Q.X) ≠ 0 := dρ' ▸ one_ne_zero
  refine ⟨Cover.ofModel Q hQ, fun i => (L i).pull ρ hρ, fun i => ?_, ?_⟩
  · have h₁ := Cover.induces_ofModel hQ (GlobalTheory.T.induced_metric_pullback F _ Y (A i) M Q ρ hρ hj (L i) m 0 (hI i))
    exact norms_of_induces h₁
  · have h₁ := (hA.arProj (𝓞 F) M.X Q.X M.p Q.p Y.dim M.ar Q.ar ρ hρ eρ nρ).2 ι L Ψ hΨ
    rw [dρ'] at h₁
    rw [Cover.deg_ofModel]
    exact h₁

end GlobalTheory.VertPassDeg
end
