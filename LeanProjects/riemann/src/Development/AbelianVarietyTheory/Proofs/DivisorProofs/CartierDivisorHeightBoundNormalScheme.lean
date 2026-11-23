import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArithVarGlobalSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffSuppOfMultVertical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegAtOfForallCoheightOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMultEqOrd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometricPullToSpec
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

noncomputable section
namespace GlobalTheory.SteinDescent

theorem toSpecΓ_comp_spMap_algX {R : Type} [CommRing R] (X : Scheme.{0}) (p : X ⟶ Sp R) :
    (X.toSpecΓ : X ⟶ Sp Γ(X, ⊤)) ≫ spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤) = p := by
  have e1 : spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤) =
      Spec.map (p.appTop) ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [e1, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

theorem exists_isometric_pull_stein : GlobalTheory.CovTop.Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp (𝓞 F)) (e : ℕ),
    IsArithVar p e → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (L : HermLB p) (r : L.B.ι → X.functionFieldˣ)
    (hr : GlobalTheory.Cartier.IsRatSec L.B r), (∀ z, (L.div hr).mult z ≠ 0 → (p z).asIdeal ≠ ⊥) →
    (∀ σ, ∃ a : ℝ, ∀ y ∈ GlobalTheory.Cartier.offSupp p σ (L.div hr), GlobalTheory.Cartier.logNorm (L.φ σ) r y = a) →
    (∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ]
      [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → topSelfIntersection κ (L.B.pull i) 1 = 0) →
    ∃ (m : ℕ) (k' : Type) (_ : CommRing k') (_ : IsDomain k') (_ : Algebra (𝓞 F) k') (ρ : X ⟶ Sp k')
      (hρ : ρ ≫ spMap (algebraMap (𝓞 F) k') = p) (M : HermLB (spMap (algebraMap (𝓞 F) k'))),
      0 < m ∧ IsArithVar (spMap (algebraMap (𝓞 F) k')) 0 ∧ (L.pow m).Isometric (M.pull ρ hρ) := by
  intro hP F _ _ X _ _ p e hX hN L r hr hv hc hdeg
  have hS : IsArithVar (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤)) 0 := GlobalTheory.SteinBase.isArithVar_globalSections F X p e hX
  have hoff : ∀ (σ : 𝓞 F →+* ℂ) (y : CxPts p σ), y ∈ GlobalTheory.Cartier.offSupp p σ (L.div hr) :=
    GlobalTheory.CxOffSupp.offSupp_of_mult_vertical F X p e hX hN (L.div hr) hv
  obtain ⟨m, g, a, b, hm, hb, hab, hmult⟩ := GlobalTheory.SteinFibre.exists_smul_mult_eq_ord hP F X p e hX hS hN L r hr hv hdeg
  have hD : m • L.div hr = GlobalTheory.Cartier.CartierDiv.principal g := GlobalTheory.WeilCartier.eq_principal_of_mult_eq X hN _ g hmult
  have hc' : ∀ σ, ∃ a : ℝ, ∀ y : CxPts p σ, GlobalTheory.Cartier.logNorm (L.φ σ) r y = a := fun σ =>
    let ⟨a, ha⟩ := hc σ; ⟨a, fun y => ha y (hoff σ y)⟩
  obtain ⟨M, hM⟩ := GlobalTheory.SteinIso.exists_isometric_pull_toSpec F X p e hX hS L r hr hoff hc' m g a b hb hab hD (toSpecΓ_comp_spMap_algX X p)
  letI : Algebra (𝓞 F) Γ(X, ⊤) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤).toAlgebra
  exact ⟨m, Γ(X, ⊤), inferInstance, inferInstance, this, X.toSpecΓ, toSpecΓ_comp_spMap_algX X p, M, hm, hS, hM⟩

end GlobalTheory.SteinDescent
