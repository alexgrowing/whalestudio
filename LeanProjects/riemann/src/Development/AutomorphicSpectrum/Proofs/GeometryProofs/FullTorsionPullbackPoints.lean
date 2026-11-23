import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSectionAdditiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapSnd
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorsPull

theorem spMap_cancel {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω') {Z : Scheme.{0}}
    (a b : Spec (CommRingCat.of Ω) ⟶ Z) (h : spMap i ≫ a = spMap i ≫ b) : a = b := by
  have : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom i)) :=
    GlobalTheory.CompanionTheory.Ar.LieEx.std_of_inj (CommRingCat.ofHom i) i.injective
  refine GlobalTheory.CompanionTheory.Ar.LieEx.epi_of_surj (Spec.map (CommRingCat.ofHom i)) ?_ a b h
  intro y
  have hs : Subsingleton (Spec (CommRingCat.of Ω)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of Ω')) :=
    inferInstanceAs (Nonempty (PrimeSpectrum Ω'))
  exact ⟨x, Subsingleton.elim _ _⟩

theorem tr_pow {S : Scheme.{0}} {T : Scheme.{0}} {G : Over S} [GrpObj G] {a b : T ⟶ S} (h : a = b)
    (n : ℕ) (u : Over.mk a ⟶ G) (hu : u ^ n = 1) :
    ∃ u' : Over.mk b ⟶ G, u'.left = u.left ∧ u' ^ n = 1 := by
  subst h
  exact ⟨u, rfl, hu⟩

theorem torsion_of_pullback : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ n : ℕ, FullTorsion G ξ n →
  FullTorsion G' ξ' n ∧
  (∀ y : Over.mk ξ ⟶ G, y ^ n = 1 → ∃ y' : Over.mk ξ' ⟶ G', y' ^ n = 1 ∧ y'.left ≫ φ = spMap i ≫ y.left) ∧
  (∀ y' : Over.mk ξ' ⟶ G', y' ^ n = 1 → ∃ y : Over.mk ξ ⟶ G, y ^ n = 1 ∧ y'.left ≫ φ = spMap i ≫ y.left) ∧
  (∀ (a a' : Over.mk ξ' ⟶ G') (c c' : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a'.left ≫ φ = spMap i ≫ c'.left → (a * a').left ≫ φ = spMap i ≫ (c * c').left) ∧
  (∀ (a a' : Over.mk ξ' ⟶ G') (c : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a'.left ≫ φ = spMap i ≫ c.left → a = a') ∧
  (∀ (a : Over.mk ξ' ⟶ G') (c c' : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a.left ≫ φ = spMap i ≫ c'.left → c = c') := by
  intro X X' Ω Ω' _ _ ξ ξ' f i hd G _ _ G' _ _ φ h n hf
  have hd' : ξ' ≫ f = spMap i ≫ ξ := hd
  let u : Over.mk (ξ' ≫ f) ⟶ Over.mk ξ := Over.homMk (spMap i) (by simpa using hd'.symm)
  let P : (Over.mk ξ' ⟶ G') →* (Over.mk (ξ' ≫ f) ⟶ G) := pushHom h (Over.mk ξ')
  let Q : (Over.mk ξ ⟶ G) →* (Over.mk (ξ' ≫ f) ⟶ G) := preHom u
  have rel : ∀ (a : Over.mk ξ' ⟶ G') (c : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → P a = Q c :=
    fun a c e => Over.OverMorphism.ext e
  have lerp : ∀ (a : Over.mk ξ' ⟶ G') (c : Over.mk ξ ⟶ G), P a = Q c → a.left ≫ φ = spMap i ≫ c.left :=
    fun a c e => congrArg (fun z => z.left) e
  have Pinj : Function.Injective P := by
    intro a a' e
    have e1 : a.left ≫ φ = a'.left ≫ φ := congrArg (fun z => z.left) e
    have w : ∀ b : Over.mk ξ' ⟶ G', b.left ≫ G'.hom = ξ' := fun b => by simpa using Over.w b
    exact Over.OverMorphism.ext (h.1.hom_ext e1 ((w a).trans (w a').symm))
  have Qinj : Function.Injective Q := by
    intro c c' e
    have e1 : spMap i ≫ c.left = spMap i ≫ c'.left := congrArg (fun z => z.left) e
    exact Over.OverMorphism.ext (spMap_cancel i _ _ e1)
  refine ⟨GlobalTheory.CompanionTheory.Ar.HcptPull.fullTorsion_of_dominates X X' Ω Ω' ξ ξ' f i G G' φ n hd h hf, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hxw : y.left ≫ G.hom = ξ := by simpa using Over.w y
    have hw : (spMap i ≫ y.left) ≫ G.hom = ξ' ≫ f := by rw [Category.assoc, hxw, hd']
    let y' : Over.mk ξ' ⟶ G' := Over.homMk (h.1.lift (spMap i ≫ y.left) ξ' hw) (h.1.lift_snd _ _ _)
    have e : y'.left ≫ φ = spMap i ≫ y.left := h.1.lift_fst _ _ _
    refine ⟨y', Pinj ?_, e⟩
    rw [map_pow, map_one, rel y' y e, ← map_pow, hy, map_one]
  · intro y' hy'
    have hP : (P y') ^ n = 1 := by rw [← map_pow, hy', map_one]
    obtain ⟨g, hl, hg⟩ := tr_pow hd' n (P y') hP
    obtain ⟨y, hy⟩ := hf Ω' i g hg
    have e : y'.left ≫ φ = spMap i ≫ y.left := hl.symm.trans hy
    refine ⟨y, Qinj ?_, e⟩
    rw [map_pow, map_one, ← rel y' y e, hP]
  · intro a a' c c' e e'
    apply lerp
    rw [map_mul, map_mul, rel a c e, rel a' c' e']
  · intro a a' c e e'
    exact Pinj ((rel a c e).trans (rel a' c e').symm)
  · intro a c c' e e'
    exact Qinj ((rel a c e).symm.trans (rel a c' e'))

end GlobalTheory.CompanionTheory.Ar.TorsPull
