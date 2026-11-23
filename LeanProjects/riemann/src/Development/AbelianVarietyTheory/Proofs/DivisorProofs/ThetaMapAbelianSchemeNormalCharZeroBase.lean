import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescendStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueProjectiveSpaceMapsOfAgreeGeometricPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenNormalNoetherianCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdThetaMapOnNormalCharZeroAffineStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThetaMapGen

theorem agree_at_geom : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen →
    ∀ (g m n : ℕ) (o K : Type) [CommRing o] [Field K] [IsAlgClosed K] (z : Sp K ⟶ S) (f₁ f₂ : Sp K ⟶ PSpace o n),
    Odd m → IsUnit (m : o) → n + 1 = m ^ (4 * g) → PolFib G L g z → f₁ ≫ PSpace.str o n = f₂ ≫ PSpace.str o n →
    (∀ c : Fin (n + 1) → K, HasTh G L ρ m z c → PCrd f₁ (symTup c)) → (∀ c : Fin (n + 1) → K, HasTh G L ρ m z c → PCrd f₂ (symTup c)) → f₁ = f₂ := by
  intro S G _ _ L ρ hL hρ g m n o K _ _ _ z f₁ f₂ hm hu hn hP hs h₁ h₂
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable S G L hL g K z hP
  have hmK : (m : K) ≠ 0 := by
    let φ : o →+* K := (Spec.preimage (f₁ ≫ PSpace.str o n)).hom
    have := hu.map φ
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨pt, c, hc⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed S G L ρ hL hρ g m (n + 1) K z θ hm hmK hn hP
  have hH : HasTh G L ρ m z c := ⟨θ, pt, hθ, hc⟩
  exact (GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend).1 o K n f₁ f₂ (symTup c) hs (h₁ c hH) (h₂ c hH)

theorem main : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) → Geo.Tor.IsNormalScheme X → IsLocallyNoetherian X → (∀ x : X, CharZero (X.residueField x)) → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) → ∃ f : X ⟶ PSpace o n, f ≫ PSpace.str o n = s ∧ ThMap G L ρ m q f := by
  intro S G _ _ L ρ hL hρ g m n o _ X s q hm h3 hu hn hN hLN h0 hP
  have loc : ∀ x : X, ∃ (W : X.Opens) (h : W.toScheme ⟶ PSpace o n), x ∈ W ∧ h ≫ PSpace.str o n = W.ι ≫ s ∧
      ThMap G L ρ m (W.ι ≫ q) h := by
    intro x
    obtain ⟨U, hxU, h1, h2, h3', h4⟩ := GlobalTheory.T.exists_affineOpen_normal_noetherian_charZero X hN hLN h0 x
    exact GlobalTheory.T.exists_nhd_thetaMap_on_normal_charZero_affine S G L ρ hL hρ g m n o X s q hm h3 hu hn hP U h1 h2 h3' h4 x hxU
  choose W h hxW hs hT using loc
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    haveI := (hN x).1; infer_instance
  haveI : IsReduced X := isReduced_of_isReduced_stalk X
  have hcov : (⨆ x, W x) = ⊤ := by
    rw [eq_top_iff]; intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩
  obtain ⟨f, hf, hfW⟩ := GlobalTheory.T.glue_projectiveSpace_maps_of_agree_geometric_points o n X s X W h hcov hs (by
    intro i j K _ _ y y' hyy
    refine agree_at_geom S G L ρ hL hρ g m n o K (y ≫ (W i).ι ≫ q) _ _ hm hu hn (by rw [← Category.assoc]; exact hP K _) ?_ ?_ ?_
    · rw [Category.assoc, hs, Category.assoc, hs, ← Category.assoc, hyy, Category.assoc]
    · intro c hc; exact hT i K y c hc
    · intro c hc
      have := hT j K y' c (by rwa [← Category.assoc, ← hyy, Category.assoc])
      exact this)
  refine ⟨f, hf, ?_⟩
  intro K _ x c hc
  let p0 : Sp K := IsLocalRing.closedPoint K
  let i := x.base p0
  have hr : Set.range x.base ⊆ Set.range (W i).ι.base := by
    rintro _ ⟨y, rfl⟩
    have : y = p0 := Subsingleton.elim _ _
    subst this
    rw [Scheme.Opens.range_ι]; exact hxW i
  let x' := IsOpenImmersion.lift (W i).ι x hr
  have hx' : x' ≫ (W i).ι = x := IsOpenImmersion.lift_fac _ _ _
  have := hT i K x' c (by rw [← Category.assoc, hx']; exact hc)
  rw [← hx', Category.assoc, hfW i]; exact this

end GlobalTheory.UMin.ThetaMapGen
