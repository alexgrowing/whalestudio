import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementCoversStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapGenericPointAndDeg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertPass

theorem map_genericPoint {F : Type} [Field F] [NumberField F] {Y : Var F} {V' V : Cover Y} (g : V'.G ⟶ V.G)
    (h : g ≫ V.π = V'.π) : g (genericPoint V'.G) = genericPoint V.G := by
  have key (W : Cover Y) : W.π (genericPoint W.G) = genericPoint Y.X := by
    have := (genericPoint_spec W.G).image W.π.continuous
    rw [Set.image_univ, W.π.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  obtain ⟨U, hU, e⟩ := isDiscrete_iff_forall_exists_isOpen.mp (V.π.isDiscrete_preimage_singleton (genericPoint Y.X))
    (g (genericPoint V'.G)) (by rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, h, key]; rfl)
  have h₁ : g (genericPoint V'.G) ∈ U := (e.ge rfl).1
  exact (e.le ⟨(genericPoint_specializes _).mem_open hU h₁, key V⟩).symm

theorem pass : GlobalTheory.Published.ArCalc → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (V : Cover Y) (ι : Type) [Fintype ι] (A : ι → Adl (cxSt F) Y) (L : ι → HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), (∀ i, (A i).Induced M (L i) m 0) → (haveI := M.ar.isIntegral; IsArFun L Y.dim Ψ) → ∃ (V' : Cover Y) (π : V'.X ⟶ V.X) (L' : ι → HermLB V'.p) (d : ℝ), π ≫ V.p = V'.p ∧ Lies V' V π ∧ d ≠ 0 ∧ (∀ i, Norms V' (L' i) (fun x => genAt (A i).D x ^ (m : ℕ)) (fun σ y => (m : ℕ) * lnAdl (A i) σ y) (fun v e y => (m : ℕ) * (A i).lg v e y)) ∧ IsArFun L' Y.dim (d • Ψ) := by
  intro hA F _ _ Y M V ι _ A L m Ψ hI hΨ
  haveI := M.ar.isIntegral
  obtain ⟨Q, ρ, -, hQ, hρ, -, hj, -, -, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M
  haveI := Q.ar.isIntegral
  obtain ⟨V', π, π₀, hπ, hπ₀, hl, hl₀⟩ := GlobalTheory.T.common_refinement_covers F Y V (Cover.ofModel Q hQ)
  obtain ⟨g, hg₁, hg₂⟩ := hl₀
  have hgen := map_genericPoint g hg₂
  obtain ⟨e₀, d₀⟩ := GlobalTheory.CoverDeg.map_genericPoint_and_deg F Y (Cover.ofModel Q hQ) V' π₀ hπ₀ g hg₁.symm hg₂ hgen
  obtain ⟨eρ, dρ⟩ := GlobalTheory.CoverModelDeg.map_genericPoint_and_deg F Y (Cover.ofModel Q hQ) M ρ hρ
    (by simpa [Cover.ofModel] using hj)
  rw [Cover.deg_ofModel] at dρ d₀
  rw [mul_one] at d₀
  have n₀ : π₀.residueDegree (genericPoint V'.X) ≠ 0 := d₀ ▸ V'.deg_pos.ne'
  have nρ : ρ.residueDegree (genericPoint Q.X) ≠ 0 := by
    have : ρ.residueDegree (genericPoint (Cover.ofModel Q hQ).X) = 1 := dρ
    exact this ▸ one_ne_zero
  refine ⟨V', π, fun i => ((L i).pull ρ hρ).pull π₀ hπ₀,
    (π₀.residueDegree (genericPoint V'.X) : ℝ) * (ρ.residueDegree (genericPoint Q.X) : ℝ), hπ, hl,
    mul_ne_zero (Nat.cast_ne_zero.2 n₀) (Nat.cast_ne_zero.2 nρ), fun i => ?_, ?_⟩
  · have h₁ := Cover.induces_ofModel hQ (GlobalTheory.T.induced_metric_pullback F _ Y (A i) M Q ρ hρ hj (L i) m 0 (hI i))
    exact GlobalTheory.CoverNorm.norms_pull F Y (Cover.ofModel Q hQ) V' π₀ hπ₀ g hg₁.symm hg₂ hgen _ _ _ _ (norms_of_induces h₁)
  · have P := hA.arProj
    have h₁ := (P (𝓞 F) M.X Q.X M.p Q.p Y.dim M.ar Q.ar ρ hρ eρ nρ).2 ι L Ψ hΨ
    have h₂ := (P (𝓞 F) Q.X V'.X Q.p V'.p Y.dim Q.ar V'.ar π₀ hπ₀ e₀ n₀).2 ι _ _ h₁
    rwa [smul_smul] at h₂

end GlobalTheory.VertPass

end
