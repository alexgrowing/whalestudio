import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalBoundaryLocalEquation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalBoundaryLocalEquationStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BdEquation
open GlobalTheory.Cartier GlobalTheory.ZH GlobalTheory.FlagBundle
theorem exists_reduced_boundary_equation : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, y ∉ U₀ TF.X Z → ∃ (V : (Y₀ TF.X Z).Opens) (_ : y ∈ V) (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) ∧ (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) := by
  intro _ E _ _ _ H Dw l Xo c T Z hF _ y _
  have hsm := GlobalTheory.VarFlag.smooth_gen T.smooth
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) T.Y c.F (RingEquiv.refl _) hF hsm
  have := (hB Z).1
  obtain ⟨C, f, hπ, -, hl⟩ :=
    GlobalTheory.FlagBundle.exists_flagCpt T.Y (RingEquiv.refl _) (GlobalTheory.T.snc_toroidalGenericBoundary_of_snc_boundary T.snc) (B Z) (j Z) (hB Z).2.2.1
  obtain ⟨h, hiso, hh, -, -⟩ := GlobalTheory.CompProport.exists_iso T Z B j hB hcov C f hπ hl
  have hmem : ∀ z : Y₀ T.X Z, h z ∉ CartierDiv.supp C.bd ↔ z ∈ U₀ T.X Z := fun z => by
    have e : GlobalTheory.Toroidal.genι T.Y (C.π (h z)) = T.X.π (inc₀ T.X Z z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hh]
    refine (not_congr (C.bd_supp (h z))).trans (not_not.trans ?_)
    change C.π (h z) ∈ Set.range T.Y.jQ ↔ T.X.π (inc₀ T.X Z z) ∈ Set.range T.Y.j
    refine exists_congr fun x => ?_
    rw [← e, Model.j, Scheme.Hom.comp_apply]
    exact (GlobalTheory.Toroidal.genι T.Y).isOpenEmbedding.injective.eq_iff.symm
  obtain ⟨V, hyV, t, ht, hrad⟩ := exists_section C.bd C.bd_eff C.bd_red (h y)
  have hg : ∀ z (hz : z ∈ h ⁻¹ᵁ V), ger z hz (h.app V t) = (h.stalkMap z).hom (ger (h z) hz t) :=
    fun z hz => (Scheme.Hom.germ_stalkMap_apply h V z hz t).symm
  have hu : ∀ z (hz : z ∈ h ⁻¹ᵁ V), IsUnit (ger z hz (h.app V t)) ↔ z ∈ U₀ T.X Z := fun z hz => by
    rw [hg, isUnit_map_iff]
    exact (ht (h z) hz).trans (hmem z)
  refine ⟨h ⁻¹ᵁ V, hyV, h.app V t, hu, fun W hW s hs z hz => ?_⟩
  obtain ⟨n, c', hc⟩ := dvd_pow_of_vanishing _ _ _ hu W hW s hs z hz
  have hb := GlobalTheory.BoundaryDivisor.stalkMap_bijective h z
  obtain ⟨b, hb'⟩ := hb.2 (ger z hz s)
  obtain ⟨c'', rfl⟩ := hb.2 c'
  rw [hg, ← hb', ← map_pow, ← map_mul] at hc
  rw [hg, ← hb']
  exact map_dvd _ (hrad _ _ b n ⟨c'', hb.1 hc⟩)
end GlobalTheory.BdEquation
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_divisor_has_reduced_equation : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, y ∉ U₀ TF.X Z → ∃ (V : (Y₀ TF.X Z).Opens) (_ : y ∈ V) (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) ∧ (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) := by
  first | exact @_root_.GlobalTheory.BdEquation.exists_reduced_boundary_equation | exact _root_.GlobalTheory.BdEquation.exists_reduced_boundary_equation | (intros; apply _root_.GlobalTheory.BdEquation.exists_reduced_boundary_equation <;> assumption)
end
