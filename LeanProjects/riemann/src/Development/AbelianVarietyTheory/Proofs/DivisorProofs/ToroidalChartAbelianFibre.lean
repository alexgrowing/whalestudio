import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialLogGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparableHermitianFormsDetBounds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.QCoh (pullbackSections)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitDiffSpan

theorem span_crd_dUnit {k : Type} [CommRing k] {S T : Scheme.{0}} (G : Over S) [GrpObj G]
    [QuasiSeparated G.hom] (j : T ⟶ S) {q : T ⟶ Sp k} {g : ℕ} (ρ : k →+* ℂ) (y : CxPts q ρ)
    (ch : Chart ((Scheme.Modules.pullback j).obj (omega G)) g) (hy : y ∈ ptsIn q ρ ch.U) :
    ∃ (U : S.Opens) (W : G.left.Opens) (hU : U ≤ unitSec G ⁻¹ᵁ W), y ∈ ptsIn q ρ (j ⁻¹ᵁ U) ∧
      Submodule.span ℂ (Set.range fun f : Γ(G.left, W) =>
        ch.crd q ρ (pullbackSections j _ (le_refl (j ⁻¹ᵁ U)) (dUnit G hU f)) y) = ⊤ := by
  obtain ⟨U, W, hxU, -, c⟩ := GlobalTheory.Conormal.exists_isChart (GlobalTheory.LieVB.sec_hom (MonObj.one (X := G)))
    (x := j (y.1 (IsLocalRing.closedPoint ℂ))) (V := ⊤) trivial
  obtain ⟨V, hV, hxV, hle⟩ := GlobalTheory.QCoh.exists_affine_mem_le (U := ch.U ⊓ j ⁻¹ᵁ U)
    (y.1 (IsLocalRing.closedPoint ℂ)) ⟨mem_ptsIn.1 hy, hxU⟩
  have e : V ≤ j ⁻¹ᵁ U := hle.trans inf_le_right
  have hyV : y ∈ ptsIn q ρ V := mem_ptsIn.2 hxV
  refine ⟨U, W, c.le, mem_ptsIn.2 hxU, ?_⟩
  have key (t : Γ((Scheme.Modules.pullback j).obj (omega G), V)) :
      ch.crd q ρ t y ∈ Submodule.span ℂ (Set.range fun f : Γ(G.left, W) =>
        ch.crd q ρ (pullbackSections j _ (le_refl (j ⁻¹ᵁ U)) (dUnit G c.le f)) y) := by
    letI := GlobalTheory.QCoh.appLEAlgebra j e
    letI := GlobalTheory.QCoh.appLEModule j ((Scheme.Modules.pullback j).obj (omega G)) e
    haveI := GlobalTheory.QCoh.appLE_isScalarTower j ((Scheme.Modules.pullback j).obj (omega G)) e
    induction t using
      (GlobalTheory.QCoh.isBaseChange_pullbackSections j (omega G) hV c.affine_base e).inductionOn with
    | zero => rw [Chart.crd_zero]; exact zero_mem _
    | tmul m =>
      obtain ⟨a, rfl⟩ := c.d_surjective (GlobalTheory.LieVB.sec_hom (MonObj.one (X := G))) m
      refine Submodule.subset_span ⟨a, ?_⟩
      refine (ch.crd_resM _ e hyV).symm.trans (congrArg (ch.crd q ρ · y) ?_)
      exact GlobalTheory.QCoh.res_pullbackSections j (omega G) le_rfl e _
    | smul a t ht => rw [Chart.crd_smul]; exact Submodule.smul_mem _ _ ht
    | add t t' ht ht' => rw [Chart.crd_add]; exact add_mem ht ht'
  refine eq_top_iff.2 ((Pi.basisFun ℂ (Fin g)).span_eq.ge.trans (Submodule.span_le.2 ?_))
  rintro _ ⟨a, rfl⟩
  have h := key (GlobalTheory.Twist.resM _ (hle.trans inf_le_left) (ch.e a))
  rw [ch.crd_resM _ _ hyV, ch.crd_frame hy] at h
  rw [Pi.basisFun_apply]
  exact h

theorem span_crd_dUnit_model : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {T : Scheme.{0}} (j : T ⟶ Z.X) {q : T ⟶ Sp Oz} {g : ℕ} (ρ : Oz →+* ℂ) (y : CxPts q ρ) (ch : Chart ((Scheme.Modules.pullback j).obj (omega Z.t.G)) g), y ∈ ptsIn q ρ ch.U → ∃ (U : Z.X.Opens) (W : Z.t.G.left.Opens) (hU : U ≤ unitSec Z.t.G ⁻¹ᵁ W), y ∈ ptsIn q ρ (j ⁻¹ᵁ U) ∧ Submodule.span ℂ (Set.range fun f : Γ(Z.t.G.left, W) => ch.crd q ρ (pullbackSections j _ (le_refl (j ⁻¹ᵁ U)) (dUnit Z.t.G hU f)) y) = ⊤ := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z T j q g ρ y ch hy
  have : QuasiSeparated Z.t.G.hom := have := Z.t.semi.separated; inferInstance
  exact span_crd_dUnit Z.t.G j ρ y ch hy

end GlobalTheory.UnitDiffSpan
