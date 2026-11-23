import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsOfFinOrderOfQuadratic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToOfComponents
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isHolTo_fibreSlice {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {B : Set V} {y : V × W → (Sp ℂ ⟶ X)} (h : IsHolTo (B ×ˢ Set.univ) y)
    {b : V} (hb : b ∈ B) : IsHolTo Set.univ (fun z => y (b, z)) := by
  intro U f
  have hc : Differentiable ℂ (fun z : W => (b, z)) := by fun_prop
  refine ⟨?_, (h U f).2.comp hc.differentiableOn fun z hz => ⟨⟨hb, trivial⟩, hz.2⟩⟩
  convert (h U f).1.preimage hc.continuous using 1
  ext z
  exact ⟨fun hz => ⟨⟨hb, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩

theorem tangent_of_isGrpPullback {tB : SAB H (Sp ℂ)} (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ tB.G.left)
    (hφ : IsGrpPullback A tB.G (𝟙 _) φ) (hP : IsPrincipal tB) {g : ℕ} (u : HolUnif A (tB.PP.L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hu : u.IsAH Hm χ) :
    IsAbelianScheme A ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) := by
  have := tB.semi.smooth
  have := tB.semi.geomConnected
  have hAb : IsAbelianScheme tB.G := ⟨tB.semi.comm, tB.semi.smooth, hP.1, tB.semi.geomConnected⟩
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hAb hφ
  have : ConnectedSpace tB.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := tB.G.hom) (𝟙 _) (𝟙 _) tB.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected tB.G.hom (eSec tB.G (default : PrimeSpectrum ℂ))
  obtain ⟨-, ws, gs', -⟩ := tB.sym
  have hL' := pull_isLB tB.PP.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let Q : Out.PolAV (Sp ℂ) :=
    { A := A, isAb := hA, g := d
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 hd
      L := tB.PP.L.pull φ, isLB := hL'
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hφ ⟨tB.PP.rig, tB.PP.rigGen⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hφ fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
      ample := relAmple_pull hφ.1 tB.PP.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) hP.2.1
      ktriv := kTriv_pull hφ tB.PP.isLB hL' hw hP.2.2 }
  obtain ⟨-, -, -, -, h₁, h₂, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all Q g u Hm χ hu
  exact ⟨hA, h₁, h₂⟩

theorem exists_isAbLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → ∃ ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ := by
  intro E _ _ _ H R _ t g n M B ψ e b P A _ φ g' u Hm χ hb hφ hu hP
  obtain ⟨hA, h₁, h₂⟩ := tangent_of_isGrpPullback A φ hφ hP u Hm χ hu
  obtain ⟨p, hp⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv P.m.cart (𝟙_ _) (s := spMap (ψ b)) (Category.id_comp _).symm
  obtain ⟨c, hc⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv hφ (𝟙_ _) (s := 𝟙 _) (Category.comp_id _).symm
  letI := P.τ.grpB
  haveI : IsMonHom P.τ.q := P.τ.q_hom
  haveI : IsMonHom P.e.hom := P.e_hom
  let r : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.tB.G) := fun y => p.symm (e.ex b y) ≫ P.τ.q ≫ P.e.hom
  let G : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun y => c.symm (r y)
  have hr : ∀ z w, r (z + w) = r z * r w := fun z w => by
    simp only [r, e.add b hb, map_mul, MonObj.mul_comp]
  have hG : ∀ z w, G (z + w) = G z * G w := fun z w => by
    simp only [G, hr, map_mul]
  have hGr : ∀ y, (G y).left ≫ φ = (r y).left := fun y => by
    rw [← hc, c.apply_symm_apply]
  have hs : IsHolTo Set.univ (fun y => (p.symm (e.ex b y)).left) := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback P.m.cart.1 ?_ ?_
    · have h := isHolTo_fibreSlice e.hol hb
      have e₁ : (fun y => (p.symm (e.ex b y)).left ≫ P.m.cm.F) = fun y => (e.ex b y).left :=
        funext fun y => by rw [← hp, p.apply_symm_apply]
      rw [e₁]
      exact h
    · have e₁ : (fun y => (p.symm (e.ex b y)).left ≫ P.tK.G.hom) = fun _ => 𝟙 (Sp ℂ) :=
        funext fun y => Over.w (p.symm (e.ex b y))
      rw [e₁]
      exact GlobalTheory.HolFibre.isHolTo_const isOpen_univ _
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (G z).left) := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback hφ.1 ?_ ?_
    · have h := GlobalTheory.CMSpreadCompare.isHolTo_postcomp hs (P.τ.q ≫ P.e.hom).left
      have e₁ : (fun y => (G y).left ≫ φ) = fun y => (p.symm (e.ex b y)).left ≫ (P.τ.q ≫ P.e.hom).left :=
        funext fun y => by rw [hGr]; rfl
      rw [e₁]
      exact h
    · have e₁ : (fun y => (G y).left ≫ A.hom) = fun _ => 𝟙 (Sp ℂ) := funext fun y => Over.w (G y)
      rw [e₁]
      exact GlobalTheory.HolFibre.isHolTo_const isOpen_univ _
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA _ g' g u h₁ h₂ G hG hol
  refine ⟨F, fun y s hs' => ?_⟩
  have es : s = p.symm (e.ex b y) := by
    rw [eq_comm, MulEquiv.symm_apply_eq]
    exact Over.OverMorphism.ext ((hp s).trans hs').symm
  rw [hF, hGr, es]

end GlobalTheory.CompanionTheory.Ar.QuotLoc
