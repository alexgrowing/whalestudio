import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPts
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NotInFibreOfIsUnit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeStableUnderAction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverCoordsExistStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrderStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsProductRefinementStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProperIntegralModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegularStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreProjectiveEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointGenericFibreStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointMemDenseOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointLiftAlongIsoStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothSchemeStalksDomainsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ClosedInProductProjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EveryComponentInSomeChartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsGenerateFunctionFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordChartsMatchRegularStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroIffNonzeroUnitsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingDeterminesComponentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingsEqualImagesEqualStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroCentreOfComplexStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPatchAtEachComponentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptProjectiveModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCoordsOfGenericPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericIsGenericPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteExtensionPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAfterFiniteExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTrdegEqDimensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBlockRefinementLinesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeGlueOverPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelEmbeddingInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerLineBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCptIffNormalSchemeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelOverBaseStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DenseOpenGenericFibreStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreOpenCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPointsTransferDominatingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProjectiveCoordModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelBoundaryCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFramesAwayPrimeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeLineBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.VerticalDivisorDegreeStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
open GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.GeoModel

theorem exists_patches_of_res (hRes : ResK.ResKStatement)
    (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)) (hp : IsProjOver s)
    (hn : Tor.IsNormalScheme P) (U : (pullback s (spMap (algebraMap (𝓞 F) F))).Opens) (hd : Dense (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0})))) (e : ℕ)
    (hU : SmoothOfRelativeDimension e (U.ι ≫ pullback.snd s (spMap (algebraMap (𝓞 F) F))))
    (Ab : Set P) (hAb : pullback.fst s (spMap (algebraMap (𝓞 F) F)) ⁻¹' Ab = U)
    (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ P) (hξ₀ : IsCptGen ξ₀) :
    ∃ (N : ℕ) (x : Fin (N + 1) → Ω) (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (f : X ⟶ P),
      (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ x ∧ ξ ≫ f = ξ₀ ∧
      SncPts ξ e {p | Char0 ξ p ∧ f p.1 ∉ Ab} := by
  obtain ⟨hred, hln, M, i, hi, his⟩ := GlobalTheory.T.generic_fibre_projective_embedding F P s hp hn
  obtain ⟨b, ξF, hF1, hF2, hFg⟩ := GlobalTheory.T.generic_point_generic_fibre F P s Ω ξ₀ hξ₀
  have hmem := GlobalTheory.T.generic_point_mem_dense_open _ Ω ξF U hFg hd
  have hin : ResK.IsResInput M i U e := ⟨hi, hred, hd, by rw [his]; exact hU⟩
  obtain ⟨r, X', j, f', hj, hfj, hsm, hiso, hdense, hsnc⟩ := hRes F M e _ i U hin
  letI algF : Algebra F Ω := b.toAlgebra
  letI algO : Algebra (𝓞 F) Ω := (b.comp (algebraMap (𝓞 F) F)).toAlgebra
  haveI : IsScalarTower (𝓞 F) F Ω := .of_algebraMap_eq' rfl
  have hs0 : ξ₀ ≫ s = spMap (algebraMap (𝓞 F) Ω) := by
    rw [← hF1, Category.assoc, pullback.condition, ← Category.assoc, hF2]
    show _ = Spec.map (CommRingCat.ofHom (b.comp (algebraMap (𝓞 F) F)))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨nu, u, hu⟩ := GlobalTheory.T.projective_over_coords_exist (𝓞 F) P s hp Ω ξ₀ hξ₀ hs0
  have hproj : IsProjOver (f' ≫ i ≫ PSpace.str F M) := by
    have := GlobalTheory.T.closed_in_product_projective F M r X' j hj
    rwa [← Category.assoc, ← hfj, Category.assoc] at this
  have hdom := GlobalTheory.T.smooth_scheme_stalks_domains F e X' _ hsm
  obtain ⟨ξ', h1, hξ'⟩ := GlobalTheory.T.generic_point_lift_along_iso _ X' f' U Ω ξF hiso hmem hFg hdom
  have hξs : ξ' ≫ f' ≫ i ≫ PSpace.str F M = spMap (algebraMap F Ω) := by
    rw [← Category.assoc, h1, his, hF2]
  obtain ⟨nx, x2, hx2⟩ := GlobalTheory.T.projective_over_coords_exist F X' _ hproj Ω ξ' hξ' hξs
  have hg : ξ' ≫ (f' ≫ pullback.fst _ _) = ξ₀ := by rw [← Category.assoc, h1, hF1]
  have hbase := GlobalTheory.T.every_component_in_some_chart X' P Ω ξ' ξ₀ _ (𝓞 F) _ u hu hg
  obtain ⟨n, ht⟩ := GlobalTheory.T.coords_product_refinement X' Ω ξ' F _ _ x2 u hx2 hbase
  obtain ⟨c₀, hc₀, hfrac⟩ := GlobalTheory.T.coords_generate_function_field (𝓞 F) F Ω X' ξ' _ _ ht
  obtain ⟨X, ξ, sX, htX, hirr, -, -, -⟩ := GlobalTheory.T.exists_proper_integral_model Ω (𝓞 F) _ _ c₀ hc₀ hfrac
  have hreg : ∀ (a : 𝓞 F) (p : Cpt ξ), (RingHom.id Ω) (algebraMap (𝓞 F) Ω a) ∈ regAt ξ p := by
    intro a p
    obtain ⟨c, hc⟩ := htX.cover p
    exact (htX.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ a) p hc
  have hchart : ∀ p : Cpt ξ, ∃ c, InChart ξ (fun k => (RingHom.id Ω) (u k)) c p := by
    intro p
    obtain ⟨⟨q1, q2, q3⟩, h0, hc⟩ := htX.cover p
    have hne := h0
    simp only [mul_ne_zero_iff] at hne
    refine ⟨q3, hne.2, fun c' => ?_⟩
    have := hc ⟨q1, q2, c'⟩
    have e1 : ((∏ a, x2 (q1 a)) * x2 q2 * u c') / ((∏ a, x2 (q1 a)) * x2 q2 * u q3) = u c' / u q3 := by
      field_simp [hne.1.1, hne.1.2, hne.2]
    simpa [e1] using this
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.dominates_of_coords_regular P Ω ξ₀ (𝓞 F) _ u X Ω ξ (RingHom.id Ω) hu htX.gen hirr hreg hchart
  have hf' : ξ ≫ f = ξ₀ := by
    have : ξ ≫ f = _ := hf
    rw [this]; simp
  obtain ⟨N, x, hx⟩ := GlobalTheory.T.coord_over_int_of_finite_order X Ω ξ (𝓞 F) _ _ htX
  obtain ⟨R1, R2⟩ := GlobalTheory.T.coord_charts_match_regular (𝓞 F) F Ω X X' ξ ξ' _ _ htX ht
  have hchar := GlobalTheory.T.char_zero_iff_nonzero_units F Ω X ξ _ _ htX
  have hFreg : ∀ (a : F) (p' : Cpt ξ'), algebraMap F Ω a ∈ regAt ξ' p' := by
    intro a p'
    obtain ⟨c, hc⟩ := ht.cover p'
    exact (ht.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ a) p' hc
  have hunit : ∀ (p : Cpt ξ) (p' : Cpt ξ'), regAt ξ p = regAt ξ' p' → Char0 ξ p := by
    intro p p' h
    refine (hchar p).2 fun d hd0 => ?_
    have hd1 : (algebraMap (𝓞 F) F d) ≠ 0 := by simpa using hd0
    have e1 : algebraMap (𝓞 F) Ω d = algebraMap F Ω (algebraMap (𝓞 F) F d) := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [e1]; exact (map_ne_zero _).2 hd1
    · rw [h, e1]; exact hFreg _ p'
    · rw [h, e1, ← map_inv₀]; exact hFreg _ p'
  have hPts : Pts ξ = Set.range (regAt ξ') := by
    ext R
    constructor
    · rintro ⟨p, hp0, rfl⟩
      obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
      exact ⟨p', h.symm⟩
    · rintro ⟨p', rfl⟩
      obtain ⟨p, h⟩ := R1 p'
      exact ⟨p, hunit p p' h, h.symm⟩
  let B : Set (Cpt ξ) := {p | Char0 ξ p ∧ f p.1 ∉ Ab}
  let T : Set X' := f'.base ⁻¹' (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0})))ᶜ
  have hgen : ∀ (p : Cpt ξ) (p' : Cpt ξ'), regAt ξ p = regAt ξ' p' → (f p.1 ∉ Ab ↔ p'.1 ∈ T) := by
    intro p p' h
    have e1 : f p.1 = (f' ≫ pullback.fst _ _) p'.1 :=
      GlobalTheory.T.regular_rings_equal_images_equal P X X' Ω ξ₀ ξ ξ' f _ (𝓞 F) _ u hu htX.gen hξ' hf' hg p p' h
    have e2 : ((f' ≫ pullback.fst s (spMap (algebraMap (𝓞 F) F))) p'.1 ∈ Ab) ↔ f' p'.1 ∈ (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0}))) := by
      rw [← hAb]; simp
    rw [e1, e2]; rfl
  have hBd : regAt ξ '' B = regAt ξ' '' {p | p.1 ∈ T} := by
    ext R
    constructor
    · rintro ⟨p, ⟨hp0, hp1⟩, rfl⟩
      obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
      exact ⟨p', (hgen p p' h).1 hp1, h.symm⟩
    · rintro ⟨p', hp', rfl⟩
      obtain ⟨p, h⟩ := R1 p'
      exact ⟨p, ⟨hunit p p' h, (hgen p p' h).2 hp'⟩, h⟩
  have hpatch := GlobalTheory.T.snc_patch_at_each_component F X' _ e T Ω ξ' hξ' hξs hsm hsnc (GlobalTheory.T.regular_ring_determines_component X' Ω ξ' F _ _ ht)
  refine ⟨N, x, X, ξ, f, hirr, hx, hf', fun p hp0 => ?_⟩
  obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
  show ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A),
    IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p)
  rw [hPts, hBd, h]
  exact hpatch p'

theorem genPt_comp {X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (φ : Ω₀ →+* Ω) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) :
    genPt (Spec.map (CommRingCat.ofHom φ) ≫ ξ) = genPt ξ := by
  show ξ ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint Ω)) = ξ (IsLocalRing.closedPoint Ω₀)
  congr 1
  exact Subsingleton.elim _ _

theorem exists_cst {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {Ω : Type} [Field Ω] (y₀ : Sp Ω ⟶ Xo.XF c) :
    ∃ cst : c.F →+* Ω, y₀ ≫ Y.j ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
  refine ⟨(Spec.preimage (y₀ ≫ pullback.snd _ _)).hom, ?_⟩
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc]
  unfold spMap
  rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem exists_base (hRes : ResK.ResKStatement) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀]
    (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (hg : IsCptGen ξ₀) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k))
      (y : (Σ k, J k) → Ω) (M₁ : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (f₁ : M₁.X ⟶ Y.X)
      (y₀ : Sp Ω ⟶ Xo.XF c) (i : Ω₀ →+* Ω), Nonempty K ∧ (letI := i.toAlgebra; FiniteDimensional Ω₀ Ω) ∧
      Flat.NormalCpt M₁.ξ ∧ M₁.ξ ≫ f₁ = y₀ ≫ Y.j ∧ M₁.ξ ≫ f₁ = spMap i ≫ ξ₀ ∧
      (∀ p ∈ S, FullTorsion Y.t.G (M₁.ξ ≫ f₁) (p ^ 4)) ∧ (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 4)) ∧
      SncPts M₁.ξ D.dim {p | Char0 M₁.ξ p ∧ p.1 ∉ f₁ ⁻¹' abLocus Y.t.G} ∧
      Algebra.trdeg ℤ Ω = ((D.dim : ℕ) : Cardinal) := by
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  have hgen₀ := GlobalTheory.T.component_generic_is_generic_point E H D l Xo c Y Ω₀ ξ₀ hg
  obtain ⟨w₀, -⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω₀ ξ₀ hgen₀
  obtain ⟨cst, -⟩ := exists_cst (Y := Y) w₀
  haveI : CharZero Ω₀ := charZero_of_injective_ringHom cst.injective
  obtain ⟨Ω, _, _, i, hfin, htors, hroot⟩ := GlobalTheory.T.exists_finite_extension_primes E H D l Xo c Y Ω₀ ξ₀ S hgen₀ hS
  obtain ⟨K₀, _, J₀, _, yc, X₀, ξ', f₀, bd₀, -, hall₀, htie₀, hf₀, -, -⟩ := GlobalTheory.T.exists_coords_of_generic_point hRes E H D l Xo c Y Ω₀ ξ₀ hg
  obtain ⟨K₁, _, J₁, _, y₁, bk, bx, M, h, -, -, hdom, hnorm, hsm⟩ :=
    GlobalTheory.T.coords_after_finite_extension hRes K₀ J₀ Ω₀ Ω i yc X₀ ξ' hfin hall₀ htie₀
  have hMξ : M.ξ ≫ h ≫ f₀ = spMap i ≫ ξ₀ := by
    have e : M.ξ ≫ h = Spec.map (CommRingCat.ofHom i) ≫ ξ' := hdom
    rw [← Category.assoc, e, Category.assoc, hf₀]
  have hgenM : genPt (M.ξ ≫ h ≫ f₀) ∈ genericPoints Y.X := by
    rw [hMξ]
    show genPt (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) ∈ _
    rw [genPt_comp]
    exact hgen₀
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω _ hgenM
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hA := GlobalTheory.T.generic_trdeg_eq_dimension E H D l Xo c _ _ Y Ω₀ ξ₀ Ω y₀ i hinj hg (hy₀ ▸ hMξ)
  have htr : Algebra.trdeg ℤ Ω = ((D.dim : ℕ) : Cardinal) := by
    letI : Algebra Ω₀ Ω := i.toAlgebra
    haveI : FiniteDimensional Ω₀ Ω := hfin
    haveI : FaithfulSMul ℤ Ω₀ := (faithfulSMul_iff_algebraMap_injective ℤ Ω₀).mpr Int.cast_injective
    haveI : FaithfulSMul Ω₀ Ω := (faithfulSMul_iff_algebraMap_injective Ω₀ Ω).mpr i.injective
    have htow := trdeg_add_eq ℤ Ω₀ (A := Ω)
    rw [hA, trdeg_eq_zero_iff.2 (Algebra.IsAlgebraic.of_finite Ω₀ Ω), add_zero] at htow
    exact htow.symm
  obtain ⟨U, hd, hAb⟩ := GlobalTheory.T.dense_open_generic_fibre E H D l Xo c Y Ω _ _ M (h ≫ f₀) y₀ hy₀
  have hU := GlobalTheory.T.generic_fibre_open_coords E H D l Xo c Y Ω K₁ J₁ y₁ M (h ≫ f₀) y₀ U hy₀ hsm htr
  have hnm : Tor.IsNormalScheme M.X := ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω M.ξ M.tie.gen M.all).2).1 hnorm
  obtain ⟨N, x, X, ξ, f₂, hall, htie, hf₂, hp⟩ := exists_patches_of_res hRes c.F M.X ((h ≫ f₀) ≫ Y.s)
    (GlobalTheory.T.projective_model_over_base E H D l Xo c Y Ω _ _ M (h ≫ f₀)) hnm U hd D.dim hU _ hAb Ω M.ξ M.tie.gen
  obtain ⟨K, _, J, _, y, M₁, g, hne, hdom₁, hn₁, hp₁⟩ := GlobalTheory.T.exists_projective_coord_model Ω X ξ N x D.dim
    (f₂ ⁻¹' ((h ≫ f₀) ⁻¹' abLocus Y.t.G)) hall htie hp
  have hg₁ : M₁.ξ ≫ g = ξ := by
    have e : M₁.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ := hdom₁
    rw [e]; simp
  have hξ₁ : M₁.ξ ≫ g ≫ f₂ ≫ h ≫ f₀ = M.ξ ≫ h ≫ f₀ := by
    rw [← Category.assoc, hg₁, ← Category.assoc, hf₂]
  refine ⟨Ω, inferInstance, inferInstance, K, inferInstance, J, inferInstance, y, M₁, g ≫ f₂ ≫ h ≫ f₀, y₀, i, hne, hfin, hn₁,
    hξ₁.trans hy₀, hξ₁.trans hMξ, fun p hp' => ?_, hroot, ?_, htr⟩
  · rw [hξ₁, hMξ]
    exact htors p hp'
  · convert hp₁ using 4
    simp

section Shrink

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem ht_isVBOn (A : HodgeCpt Y S y) (hβ : Function.Injective β) {p : ℕ} (hp : p ∈ S) (s : CMType H ⊕ CMType H) :
    (A.HT p s).IsVBOn {q | ∀ r : ℕ, r.Prime → r ≠ p → ¬ InFibre A.ξ r q} (labelRk D s) (A.Vgen s) := by
  intro q _
  obtain ⟨U, hU, b, hb, hfr⟩ := A.vb s q trivial
  refine ⟨U, hU, b, hb, fun q' hq' hU' => ?_⟩
  have h := hfr q' trivial hU'
  have hV : A.V s q' = A.HT p s q' := by
    by_cases hf : InFibre A.ξ p q'
    · refine Lat.patch_of_unique S _ _ hp hf fun p' hp' h' => ?_
      by_contra hne
      exact hq' p' (A.S_prime p' hp') hne h'
    · have hc : ∀ r : ℕ, r.Prime → ¬ InFibre A.ξ r q' := fun r hr => by
        by_cases e : r = p
        · rw [e]; exact hf
        · exact hq' r hr e
      obtain ⟨h1, h2, -⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c O β Y S Ω K J y A hβ q' hc
      rw [h1 s, h2 p (A.S_prime p hp) s]
  exact ⟨h.1, hV ▸ h.2⟩

theorem unitAt_nat {X : Scheme.{0}} {ξ : Sp Ω ⟶ X} [CharZero Ω] (q : Cpt ξ) (n : ℕ) (hn : n ≠ 0)
    (h : ∀ r : ℕ, r.Prime → r ∣ n → ¬ InFibre ξ r q) : unitAt ξ q (n : Ω) := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one =>
    rw [Nat.cast_one]
    exact ⟨one_ne_zero, (regAt ξ q).one_mem, by simpa using (regAt ξ q).one_mem⟩
  | prime r hr =>
    have := h r hr dvd_rfl
    exact not_not.1 this
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hn
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hn
    have h1 := ha ha0 fun r hr hd => h r hr (hd.mul_right b)
    have h2 := hb hb0 fun r hr hd => h r hr (hd.mul_left a)
    rw [Nat.cast_mul]
    refine ⟨mul_ne_zero h1.1 h2.1, mul_mem h1.2.1 h2.2.1, ?_⟩
    rw [mul_inv]
    exact mul_mem h1.2.2 h2.2.2

end Shrink

theorem vb_shrink {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S₀ S₁ : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
    (A : HodgeCpt Y (S₀ ∪ S₁) y) (hβ : Function.Injective β)
    (hd : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) (s : CMType H ⊕ CMType H) :
    (Lat.patch S₀ (A.M.eigLat A.ρ (A.cst.comp (labelEmb c s)))
      fun p => htLabel A.M A.t.PP.L (p ^ A.R p) A.ρ (fun s' => A.cst.comp (labelEmb c s')) s).IsVB (labelRk D s)
      (eigSp A.ρ (A.cst.comp (labelEmb c s))) := by
  classical
  obtain ⟨-, -, hchar, hemb, hrank, -, -, hreg⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c O β Y _ Ω K J y A hβ
  haveI := hchar
  haveI : Fintype (CMType H ⊕ CMType H) := Fintype.ofFinite _
  haveI : IsNoetherian A.X := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω A.ξ ℤ _ _ A.tie).2 A.all).1
  have hS₀ : ∀ p ∈ S₀, p.Prime := fun p hp => A.S_prime p (Finset.mem_union_left _ hp)
  obtain ⟨-, hcard⟩ := GlobalTheory.T.label_embedding_injective E H l c
  have hlat := (GlobalTheory.T.lie_omega_lattice_vector_bundle A.X Ω A.ξ A.t.G A.Li A.M A.tie.gen A.t.semi.smooth).1
  have hsplit := GlobalTheory.T.lattice_eigen_vector_bundle A.X Ω A.ξ A.Li E A.ρ A.M.lat {q | ∀ l ∈ S₀, ¬ InFibre A.ξ l q} _ (CMType H ⊕ CMType H)
    A.emb A.tie.gen hemb (by rw [← hcard, Nat.card_eq_fintype_card])
    (fun p _ => (hlat p trivial) |> fun ⟨U, hU, b, hb, hf⟩ => ⟨U, hU, b, hb, fun q _ hq => hf q trivial hq⟩)
    (fun p _ a e he => GlobalTheory.CompanionTheory.Ar.LieStable.lat_stable _ Ω A.ξ _ _ A.M _ A.t.act A.ρ A.act p a e he)
    (fun p _ s a => hreg s a p)
    (fun p hp => by
      have h := unitAt_nat p (NumberField.discr E).natAbs (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E))
        fun r hr hdv => hp r (hd r hr (Int.natCast_dvd.2 hdv))
      rcases Int.natAbs_eq (NumberField.discr E) with e | e
      · rw [e]; simpa using h
      · rw [e]
        refine ⟨by simpa using h.1, by simpa using neg_mem h.2.1, ?_⟩
        simpa using neg_mem h.2.2)
  have h₀ : (A.dR s).IsVBOn {q | ∀ l ∈ S₀, ¬ InFibre A.ξ l q} (labelRk D s) (A.Vgen s) := by
    have := hsplit.1 s
    rw [show Module.finrank Ω (eigSp A.ρ (A.emb s)) = labelRk D s from hrank s] at this
    exact this
  obtain ⟨L, hL, hoff, hon⟩ := GlobalTheory.T.lattice_glue_over_primes A.X Ω A.ξ A.Li S₀ (A.dR s) (fun p => A.HT p s) (labelRk D s) (A.Vgen s)
    A.tie.gen hS₀ h₀ (fun p hp => ht_isVBOn A hβ (Finset.mem_union_left _ hp) s)
    (fun p hp q hq => ((GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c O β Y _ Ω K J y A hβ q hq).2.1 p (hS₀ p hp) s))
  have he : Lat.patch S₀ (A.dR s) (fun p => A.HT p s) = L := by
    funext q
    by_cases hq : ∃ p ∈ S₀, InFibre A.ξ p q
    · obtain ⟨p, hp, hf⟩ := hq
      rw [hon p hp q hf]
      exact Lat.patch_of_unique S₀ _ _ hp hf fun p' hp' h' => inFibre_unique (hS₀ p hp) (hS₀ p' hp') hf h'
    · push_neg at hq
      rw [hoff q hq]
      exact Lat.patch_of_not S₀ _ _ hq
  show (Lat.patch S₀ (A.dR s) (fun p => A.HT p s)).IsVB (labelRk D s) (A.Vgen s)
  rw [he]
  exact hL

def toS₀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S₀ S₁ : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
    (A : HodgeCpt Y (S₀ ∪ S₁) y) (hβ : Function.Injective β)
    (hd : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) {Ω₀ : Type} [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X)
    (h₀ : IsCptGen ξ₀) (i : Ω₀ →+* Ω) (hi : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f i) {K' : Type} [Fintype K'] {J' : K' → Type}
    [∀ k, Fintype (J' k)] (y' : (Σ k, J' k) → Ω)
    (tie' : CoordTie ℤ A.ξ fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) : HodgeCpt Y S₀ y' where
  X := A.X
  ξ := A.ξ
  all := A.all
  tie := tie'
  normal := A.normal
  f := A.f
  Ω₀ := Ω₀
  ξ₀ := ξ₀
  gen₀ := h₀
  cst := A.cst
  cst_over := A.cst_over
  fn := i
  fn_over := hi
  t := A.t
  m := A.m
  Li := A.Li
  M := A.M
  ρ := A.ρ
  act := A.act
  S_prime := fun p hp => A.S_prime p (Finset.mem_union_left _ hp)
  R := A.R
  R_ge := fun p hp => A.R_ge p (Finset.mem_union_left _ hp)
  tors := fun p hp => A.tors p (Finset.mem_union_left _ hp)
  vb := vb_shrink A hβ hd

theorem unitAt_div_of_span {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {q : Cpt ξ} {t m : Ω}
    (h : Submodule.span (regAt ξ q) {t} = Submodule.span (regAt ξ q) {m}) (hm : m ≠ 0) : unitAt ξ q (t / m) := by
  have h1 : t ∈ Submodule.span (regAt ξ q) {m} := h ▸ Submodule.mem_span_singleton_self t
  have h2 : m ∈ Submodule.span (regAt ξ q) {t} := h ▸ Submodule.mem_span_singleton_self m
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 h2
  rw [Subring.smul_def, smul_eq_mul] at ha hb
  have ht : t ≠ 0 := by
    rintro rfl
    exact hm (by simpa using hb.symm)
  refine ⟨div_ne_zero ht hm, ?_, ?_⟩
  · rw [← ha, mul_div_assoc, div_self hm, _root_.mul_one]
    exact a.2
  · rw [inv_div, ← hb, mul_div_assoc, div_self ht, _root_.mul_one]
    exact b.2

theorem exists_geo : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∀ (S₀ S₁ : Finset ℕ) (sm : CMType H → CMType H ⊕ CMType H) (r : ℕ), (sm = Sum.inl ∨ sm = Sum.inr) → (∀ τ, labelRk D (sm τ) = r) → (∀ p ∈ S₀, p.Prime) → (∀ p ∈ S₁, p.Prime) → Disjoint S₁ S₀ → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S₀ y) (deg : ℕ) (bd : Ideal (MRing J)) (vdeg : ℕ → K → ℤ) (vnum vden : ℕ → MRing J) (s : CMType H → Fin r → 𝔐.Li) (aMu : K → ℤ) (e₀ : Ω), Nonempty K ∧ genPt 𝔐.ξ₀ = genPt ξ₀ ∧ 𝔐.IsCover deg ∧ 𝔐.OmVB ∧ (∀ p ∈ S₀ ∪ S₁, HT.HTFree 𝔐 p) ∧ Algebra.trdeg ℤ Ω = D.dim ∧ Cmp.IsSncModel y D.dim bd ∧ (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ mcPts bd ↔ ¬ 𝔐.Interior z)) ∧ (∀ p ∈ S₁, 4 ≤ 𝔐.R p) ∧ (∀ p ∈ S₁, FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p)) ∧ (∀ p ∈ S₁, ∀ s', (𝔐.HT p s').IsVBOn {q | ∀ r' : ℕ, r'.Prime → r' ≠ p → ¬ InFibre 𝔐.ξ r' q} (labelRk D s') (𝔐.Vgen s')) ∧ (∀ p ∈ S₁, IsVerticalDivisorAt (mCoordIdeal y) p (vdeg p) (vnum p) (vden p)) ∧ (∀ p ∈ S₁, ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → ∀ ch, InChart 𝔐.ξ (segreCoord y) ch q → ∀ (b b' : ∀ τ, Fin (labelRk D (sm τ)) → 𝔐.Li) (T : ∀ τ, Matrix (Fin (labelRk D (sm τ))) (Fin (labelRk D (sm τ))) Ω), (∀ τ, (𝔐.V (sm τ)).IsFrameAt (b τ) q) → (∀ τ, (𝔐.HT p (sm τ)).IsFrameAt (b' τ) q) → (∀ τ k, b' τ k = ∑ k', T τ k' k • b τ k') → unitAt 𝔐.ξ q ((∏ τ, (T τ).det) / (MvPolynomial.aeval y (vnum p) / MvPolynomial.aeval y (vden p) * chartMono y ch (-vdeg p)))) ∧ (∀ τ, LinearIndependent Ω (s τ)) ∧ (∀ τ, Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) ∧ (Lat.tens (fun τ => Cusp.detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ y aMu e₀ := by
  intro hG hW E _ _ _ H D Xo l c Y hgl hp hq Ω₀ _ ξ₀ hξ₀ S₀ S₁ sm r hsm hrk hS₀ hS₁ hdis hdisc
  classical
  have hRes : ResK.ResKStatement := hG.2.2.2.2.1
  have hS : ∀ p ∈ S₀ ∪ S₁, p.Prime := fun p hp' => by
    rcases Finset.mem_union.1 hp' with h | h
    · exact hS₀ p h
    · exact hS₁ p h
  have hSd : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀ ∪ S₁ := fun p h1 h2 =>
    Finset.mem_union_left _ (hdisc p h1 h2)
  obtain ⟨Ω, _, _, K₁, _, J₁, _, y₁, M₁, f₁, z₀, i, ⟨k₁⟩, hfin, hN, hz₀, hdomi, htors, hroot, hsnc₁, htr⟩ :=
    exists_base hRes E H D l (Xo l) c Y Ω₀ ξ₀ hξ₀ (S₀ ∪ S₁) hS
  have hgen₁ : f₁ (genPt M₁.ξ) ∈ genericPoints Y.X := by
    have e : genPt (M₁.ξ ≫ f₁) = genPt ξ₀ := by
      rw [hdomi]; exact genPt_comp i ξ₀
    have h0 := GlobalTheory.T.component_generic_is_generic_point E H D l (Xo l) c Y Ω₀ ξ₀ hξ₀
    rw [← e] at h0
    exact h0
  obtain ⟨K₂, _, J₂, _, y₂, bk, bx, A, g, hbk, hy₂, hdom₂, hf₂, hR₂, hfree, hiso⟩ :=
    GlobalTheory.T.hodge_cpt_projective_model hW E H D l (Xo l) c Y (S₀ ∪ S₁) (fun _ => 4) Ω K₁ J₁ y₁ M₁ f₁ z₀ hN hz₀ hgen₁ hS hSd
      (fun _ _ => le_rfl) htors hroot
  have hgA : A.ξ ≫ g = M₁.ξ := by
    have e : A.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ M₁.ξ := hdom₂
    rw [e]; simp
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hsncA : SncPts A.ξ D.dim {p | Char0 A.ξ p ∧ g p.1 ∉ f₁ ⁻¹' abLocus Y.t.G} :=
    GlobalTheory.T.snc_points_transfer_dominating Ω _ _ _ _ M₁.X A.X M₁.ξ A.ξ g D.dim _ M₁.all A.all M₁.tie A.tie hdom₂ hiso hsnc₁
  have hi : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f i := by
    show A.ξ ≫ A.f = _
    rw [hf₂, ← Category.assoc, hgA]
    exact hdomi
  obtain ⟨-, -, hchar, -, hrank, -, -, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l (Xo l) c _ _ Y _ Ω K₂ J₂ y₂ A hβ
  have hVB : ∀ s', (Lat.patch S₀ (A.dR s') fun p => A.HT p s').IsVB (labelRk D s') (A.Vgen s') :=
    vb_shrink A hβ hdisc
  have hs : ∀ τ, ∃ b : Fin r → A.Li, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = A.Vgen (sm τ) := by
    intro τ
    have hfr : Module.finrank Ω (A.Vgen (sm τ)) = r := (hrank _).trans (hrk τ)
    have hr : 0 < r := by
      rw [← hrk τ]
      rcases hsm with e | e <;> rw [e] <;> simp only [labelRk, Sum.elim_inl, Sum.elim_inr] <;> omega
    haveI : Module.Finite Ω (A.Vgen (sm τ)) := Module.finite_of_finrank_pos (by omega)
    let bs := Module.finBasisOfFinrankEq Ω (A.Vgen (sm τ)) hfr
    refine ⟨fun k => (bs k : A.Li), ?_, ?_⟩
    · exact bs.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
    · have h := congrArg (Submodule.map (A.Vgen (sm τ)).subtype) bs.span_eq
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
      exact h
  choose s hsl hss using hs
  have hdel : ∀ P : S₁, ∃ Δ : Lat A.ξ Ω, Δ.IsVB 1 ⊤ ∧ (∀ q, ¬ InFibre A.ξ P q → Δ q = Submodule.span (regAt A.ξ q) {1}) ∧
      ∀ q, InFibre A.ξ P q → ∀ (b b' : ∀ τ, Fin (labelRk D (sm τ)) → A.Li)
        (T : ∀ τ, Matrix (Fin (labelRk D (sm τ))) (Fin (labelRk D (sm τ))) Ω),
        (∀ τ, (Lat.patch S₀ (A.dR (sm τ)) fun p => A.HT p (sm τ)).IsFrameAt (b τ) q) →
        (∀ τ, (A.HT P (sm τ)).IsFrameAt (b' τ) q) → (∀ τ k, b' τ k = ∑ k', T τ k' k • b τ k') →
        Δ q = Submodule.span (regAt A.ξ q) {∏ τ, (T τ).det} := fun P =>
    GlobalTheory.T.lattice_frames_away_prime A.X Ω A.ξ _ _ A.Li (CMType H) (fun τ => labelRk D (sm τ)) (fun τ => A.Vgen (sm τ))
      (fun τ => Lat.patch S₀ (A.dR (sm τ)) fun p => A.HT p (sm τ)) (fun τ => A.HT P (sm τ)) P A.tie A.all (hS₁ P P.2)
      (fun τ => hVB _) (fun τ => ht_isVBOn A hβ (Finset.mem_union_right _ P.2) _)
      (fun τ q hq => by
        have hB := GlobalTheory.T.hodge_cpt_away_from_primes E H D l (Xo l) c _ _ Y _ Ω K₂ J₂ y₂ (toS₀ A hβ hdisc ξ₀ hξ₀ i hi y₂ A.tie) hβ q hq
        exact ((GlobalTheory.T.hodge_cpt_away_from_primes E H D l (Xo l) c _ _ Y _ Ω K₂ J₂ y₂ A hβ q hq).2.1 P (hS₁ P P.2) (sm τ)).trans
          (hB.1 (sm τ)).symm)
  choose Δ hΔv hΔ1 hΔf using hdel
  let lmu : Lat A.ξ Ω := Lat.tens (fun τ => Cusp.detLat (Lat.patch S₀ (A.dR (sm τ)) fun p => A.HT p (sm τ)) (s τ)) fun _ => -1
  have hmu : lmu.IsVB 1 ⊤ := (GlobalTheory.T.lattice_tensor_power_line_bundle A.X Ω A.ξ _ _ Set.univ (fun τ => GlobalTheory.T.det_lattice_line_bundle A.X Ω A.ξ A.Li _ r (A.Vgen (sm τ)) (s τ)
    (hsl τ) (hss τ) (hrk τ ▸ hVB (sm τ))) _).1
  let Λ : Option S₁ → Lat A.ξ Ω := fun o => o.elim lmu Δ
  have hΛ : ∀ o, (Λ o).IsVB 1 ⊤ := by
    rintro (_ | P)
    · exact hmu
    · exact hΔv P
  obtain ⟨K₃, _, J₃, _, y₃, κ, v, hκ, hv, tie₃, hdeg⟩ := GlobalTheory.T.exists_block_refinement_lines A.X Ω A.ξ K₂ J₂ y₂ (Option S₁) Λ A.tie hΛ
  choose a e hde using hdeg
  have hver : ∀ P : S₁, ∃ f g : MRing J₃, IsVerticalDivisorAt (mCoordIdeal y₃) P (-(a (some P))) f g ∧
      MvPolynomial.aeval y₃ g ≠ 0 ∧ MvPolynomial.aeval y₃ f / MvPolynomial.aeval y₃ g = e (some P) := fun P =>
    GlobalTheory.T.vertical_divisor_degree A.X Ω A.ξ K₃ J₃ y₃ P (Δ P) (a (some P)) (e (some P)) tie₃ A.all (hde (some P)) (hΔ1 P)
  choose fv gv hvd hgv hfg using hver
  obtain ⟨bd, hbd, hbd'⟩ := GlobalTheory.T.snc_model_boundary_coords Ω A.X A.ξ K₃ J₃ y₃ D.dim {p | Char0 A.ξ p ∧ g p.1 ∉ f₁ ⁻¹' abLocus Y.t.G} tie₃
    (fun p hp' => hp'.1) hsncA
  have hab : abLocus A.t.G = A.f ⁻¹' abLocus Y.t.G :=
    (Set.ext fun x => abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 x).symm
  letI algi : Algebra Ω₀ Ω := i.toAlgebra
  haveI : FiniteDimensional Ω₀ Ω := hfin
  refine ⟨K₃, inferInstance, J₃, inferInstance, Ω, inferInstance, inferInstance, y₃, toS₀ A hβ hdisc ξ₀ hξ₀ i hi y₃ tie₃,
    Module.finrank Ω₀ Ω, bd, fun p => if h : p ∈ S₁ then -(a (some ⟨p, h⟩)) else 0,
    fun p => if h : p ∈ S₁ then fv ⟨p, h⟩ else 0, fun p => if h : p ∈ S₁ then gv ⟨p, h⟩ else 0, s, a none, e none,
    ⟨κ (bk k₁)⟩, rfl, ⟨Module.finrank_pos, rfl⟩, fun p hp' => hfree p (Finset.mem_union_left _ hp'), hfree, htr, hbd, ?_, ?_, ?_, ?_,
    ?_, ?_, hsl, hss, hde none⟩
  · intro z w hw
    rw [hbd' z w hw]
    constructor
    · rintro ⟨h, -, h2⟩ hI
      have h3 : centre z ∈ abLocus A.t.G := hI
      rw [hab, hf₂] at h3
      exact h2 h3
    · intro hn
      refine ⟨A.all _, GlobalTheory.T.char_zero_centre_of_complex Ω A.X A.ξ z _ A.tie.gen, fun h => hn ?_⟩
      show centre z ∈ abLocus A.t.G
      rw [hab, hf₂]
      exact h
  · intro p hp'
    show 4 ≤ A.R p
    rw [hR₂]
  · intro p hp'
    exact A.tors p (Finset.mem_union_right _ hp')
  · intro p hp' s'
    exact ht_isVBOn A hβ (Finset.mem_union_right _ hp') s'
  · intro p hp'
    simp only [dif_pos hp']
    exact hvd ⟨p, hp'⟩
  · intro p hp' q hf ch hch b b' T hb hb' hT
    simp only [dif_pos hp']
    have h1 := hΔf ⟨p, hp'⟩ q hf b b' T hb hb' hT
    have h2 := (hde (some ⟨p, hp'⟩)).2 q trivial ch hch
    have he0 : e (some ⟨p, hp'⟩) ≠ 0 := (hde (some ⟨p, hp'⟩)).1
    have hne : ∀ k, y₃ ⟨k, ch k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hch.1 k (Finset.mem_univ k)
    have hm : e (some ⟨p, hp'⟩) * GroundTheory.Heights₂.Heights.LowerBoundFree.chartMono y₃ ch (a (some ⟨p, hp'⟩)) ≠ 0 :=
      mul_ne_zero he0 (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k))
    have h3 : Submodule.span (regAt A.ξ q) {∏ τ, (T τ).det} = Submodule.span (regAt A.ξ q)
        {e (some ⟨p, hp'⟩) * GroundTheory.Heights₂.Heights.LowerBoundFree.chartMono y₃ ch (a (some ⟨p, hp'⟩))} := by
      rw [← h1]
      refine Eq.trans h2 ?_
      rw [smul_eq_mul, mul_comm]
      rfl
    rw [neg_neg, hfg ⟨p, hp'⟩]
    exact unitAt_div_of_span h3 hm

end GlobalTheory.CompanionTheory.Ar.GeoModel
