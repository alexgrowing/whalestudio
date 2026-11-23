import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtPull

theorem seccomp : ∀ (B : Type) [CommRing B] (Z Z' : Scheme.{0}) (x : Spec (CommRingCat.of B) ⟶ Z') (φ : Z' ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ W)) (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ W) (s : Γ(Z, W)), secVal x (φ ⁻¹ᵁ W) h (φ.app W s) = secVal (x ≫ φ) W h' s := by
  intro B _ Z Z' x φ W h h' s
  unfold secVal
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem secring : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ψ : B →+* B') (Z : Scheme.{0}) (x : Spec (CommRingCat.of B) ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ W) (s : Γ(Z, W)), secVal (spMap ψ ≫ x) W h' s = ψ (secVal x W h s) := by
  intro B B' _ _ ψ Z x W h h' s
  unfold secVal
  have e : (spMap ψ ≫ x).appLE W ⊤ h' = x.appLE W ⊤ h ≫ (spMap ψ).appTop := by
    have e₁ : (spMap ψ).appTop = (spMap ψ).appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    rw [e₁]
    exact (Scheme.Hom.appLE_comp_appLE (spMap ψ) x W ⊤ ⊤ h _).symm
  rw [e]
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have n' : (Scheme.ΓSpecIso (CommRingCat.of B')).hom.hom ((spMap ψ).appTop.hom ((x.appLE W ⊤ h).hom s)) =
      ψ ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((x.appLE W ⊤ h).hom s)) :=
    (ConcreteCategory.congr_hom n.symm ((x.appLE W ⊤ h).hom s)).symm
  exact n'

theorem eta : ∀ (X X' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (f : X' ⟶ X) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  intro X X' G _ G' _ f φ h
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over X'))))
  have e₁ : (1 : 𝟙_ (Over X') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

theorem tanin : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (q : X) (v : epsAt (X.fromSpecStalk q) ⟶ G), IsTanAt G _ v → ∀ W : G.left.Opens, (η[G]).left q ∈ W → ⊤ ≤ v.left ⁻¹ᵁ W := by
  intro X G _ q v hv W hq z _
  obtain ⟨p, rfl⟩ := LieCarrier.surjective_fst z
  have h1 : (1 : Over.mk (X.fromSpecStalk q) ⟶ G).left = X.fromSpecStalk q ≫ (η[G]).left := by
    rw [Hom.one_def]
    simp
  have e : v.left (Spec.map _ p) = (η[G]).left (X.fromSpecStalk q p) := congrArg (fun g => g p) (hv.trans h1)
  show v.left _ ∈ W
  refine e.symm ▸ ?_
  have h3 : X.fromSpecStalk q p ⤳ q := by
    have : X.fromSpecStalk q p ∈ Set.range (X.fromSpecStalk q) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact (h3.map (η[G]).left.continuous).mem_open W.isOpen hq

theorem comp_ring {B B' : Type} [CommRing B] [CommRing B'] (ψ : B →+* B') {Z Z' : Scheme.{0}}
    (x' : Spec (CommRingCat.of B') ⟶ Z') (x : Spec (CommRingCat.of B) ⟶ Z) (φ : Z' ⟶ Z) (hx : x' ≫ φ = spMap ψ ≫ x)
    (W : Z.Opens) (h : ⊤ ≤ x' ⁻¹ᵁ (φ ⁻¹ᵁ W)) (h0 : ⊤ ≤ x ⁻¹ᵁ W) (s : Γ(Z, W)) :
    secVal x' (φ ⁻¹ᵁ W) h (φ.app W s) = ψ (secVal x W h0 s) := by
  have key : ∀ (t : Spec (CommRingCat.of B') ⟶ Z) (_ : t = spMap ψ ≫ x) (h2 : ⊤ ≤ t ⁻¹ᵁ W),
      secVal t W h2 s = ψ (secVal x W h0 s) := by
    rintro _ rfl h2
    exact secring B B' ψ Z x W h0 h2 s
  rw [seccomp B' Z Z' x' φ W h h s]
  exact key _ hx h

theorem dualMap_snd {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (a : DualNumber R) :
    (dualMap φ a).snd = φ a.snd := by
  simp [dualMap]

end GlobalTheory.CompanionTheory.Ar.HtPull
