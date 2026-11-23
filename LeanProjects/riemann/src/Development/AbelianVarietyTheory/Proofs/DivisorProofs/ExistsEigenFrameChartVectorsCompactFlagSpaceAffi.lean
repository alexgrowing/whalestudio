import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramePointEigenframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenspaceFrameFlagCoverChartDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenRingInjectsToRingMappingToDenseStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

section
open GlobalTheory.FlagMod GlobalTheory.Reg
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CompHS.exists_eigFrame_vecAt₀ : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(Y₀ TF.X Z, W)), (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z = spMap φ → ∀ (k : TF.X.F.J) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (x' : Sp Γ(Y₀ TF.X Z, W) ⟶ TF.Y.X) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x'), ∃ fr : GlobalTheory.ShFam.EigFrame TF.Y φ x', ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt k _ hz hx τ j)).left := by
  intro E _ _ _ H Dw l Xo c TF Z W hW φ hφ k hz x' hx
  subst hx
  haveI := TF.X.proper
  haveI := TF.smooth
  haveI : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth Dw.dim TF.Y.s
  haveI : LocallyOfFiniteType TF.Y.s := inferInstance
  haveI : LocallyOfFiniteType (str₀ TF.X Z) := by unfold str₀ flagStr; infer_instance
  haveI : IsLocallyNoetherian (Y₀ TF.X Z) := LocallyOfFiniteType.isLocallyNoetherian (str₀ TF.X Z)
  obtain ⟨K, _, ρ, hρ, hK⟩ := GlobalTheory.T.affineOpen_ring_injects_to_ring_mapping_to_dense (Y₀ TF.X Z) (U₀ TF.X Z) (dense_U₀ TF.X Z) W hW
  letI : Algebra c.F K := (ρ.comp φ).toAlgebra
  have hz' : ⊤ ≤ (spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ⁻¹ᵁ TF.X.F.U k := FlagMod.le_preimage_comp _ hz
  have hr : Set.range ((spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π) ⊆ Set.range TF.Y.j := by
    rintro _ ⟨s, rfl⟩
    exact hK (Set.mem_univ s)
  let yK := IsOpenImmersion.lift TF.Y.j ((spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π) hr
  have hyK : yK ≫ TF.Y.j = (spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π := IsOpenImmersion.lift_fac _ _ _
  have hjs : TF.Y.j ≫ TF.Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := by
    have h1 : spMap (RingHom.id c.F) = 𝟙 _ := by
      unfold spMap; rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, TF.Y.jQ_over, h1, Category.comp_id]
  have hy : yK ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [← hjs, ← Category.assoc, hyK]
    have h2 : spMap ρ ≫ spMap φ = spMap (algebraMap c.F K) := by
      unfold spMap; rw [← Spec.map_comp]; rfl
    rw [← h2, ← hφ]
    simp only [Category.assoc]
  have key : ∀ (x'' : Sp K ⟶ TF.Y.X) (hx : (spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π = x''),
      (∀ σ, initSpan K (TF.X.F.vecAt k _ hz' hx σ) (Dw.mult σ) = eigLie c x'' σ) →
      ∀ σ, initSpan K (TF.X.F.vecAt k _ hz' rfl σ) (Dw.mult σ) =
        eigLie c ((spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π) σ := by
    rintro x'' rfl h
    exact h
  exact GlobalTheory.ChartEigFrame.exists_eigFrame_of_top ρ hρ φ rfl (hW.fromSpec ≫ inc₀ TF.X Z) k hz hz'
    (key _ hyK.symm fun σ => TF.X.top K yK hy _ hyK.symm k hz' σ)

end
