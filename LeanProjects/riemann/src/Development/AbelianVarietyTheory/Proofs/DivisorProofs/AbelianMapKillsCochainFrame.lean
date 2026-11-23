import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CochAbKer

open ReciprocityTheory.ChartRestriction.G.Out

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem epsScaleR_zero (k : Type) [CommRing k] :
    epsScaleR (0 : k) = (algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom := by
  ext x <;> simp [epsScaleR]

theorem fst_comp_algebraMap (k : Type) [CommRing k] :
    (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
  ext x; simp

theorem one_left {k : Type} [CommRing k] {G : Over (Sp k)} [GrpObj G] :
    (1 : epsR k ⟶ G).left = spMap (algebraMap k (DualNumber k)) ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1
  first | done | simpa using Over.w (toUnit (epsR k))

theorem isTangent_one {k : Type} [CommRing k] {G : Over (Sp k)} [GrpObj G] : IsTangent (1 : epsR k ⟶ G) := by
  unfold IsTangent
  rw [one_left, ← Category.assoc, ← spMap_comp', fst_comp_algebraMap]
  simp [spMap]

theorem isLieComb_zero_one {k : Type} [CommRing k] {G : Over (Sp k)} [GrpObj G] {n : ℕ}
    {v : Fin n → (epsR k ⟶ G)} (hv : ∀ i, IsTangent (v i)) : IsLieComb (0 : Fin n → k) v 1 := by
  refine ⟨fun _ => 1, fun i => ?_, by simp⟩
  rw [one_left, Pi.zero_apply, epsScaleR_zero, spMap_comp' (TrivSqZeroExt.fstHom k k k).toRingHom (algebraMap k (DualNumber k)), Category.assoc]
  have := hv i
  unfold IsTangent at this
  rw [this]

theorem cochFrame_abMap_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] (x : Sp k ⟶ X) (φ : Fib k) (m : CubeMap φ.G t.G), FibAt t x φ m → ∀ (n : ℕ) (v : Fin n → (epsR k ⟶ φ.P.A)), IsLieBasis v → ∀ q : TanM x t.G →ₗ[k] (Fin n → k), IsAbMap φ m v q → ∀ (r : ℕ) (ε : Fin r → TanM x t.G), IsCochFrame t x ε → ∀ i, q (ε i) = 0 := by
  intro E _ _ _ H X t k _ x φ m hF n v hv q hq r ε hε i
  obtain ⟨u, hu, -, he⟩ := hε
  obtain ⟨e, -, he2⟩ := he i
  obtain ⟨w', hw', hc⟩ := hq (ε i)
  obtain ⟨ψ, hψ, hψF⟩ := grpPullback_iso (isGrpPullback_pullback t.G x) hF.1
  haveI := hu
  haveI := hψ
  haveI : IsProper φ.P.A.hom := φ.P.isAb.proper
  have htriv : u ≫ ψ.hom ≫ φ.q = toUnit _ ≫ η[φ.P.A] :=
    splitTorus_hom_proper_trivial_local k (Fin r → ℤ) φ.P.A _ inferInstance
  have hw : w' = e.1 ≫ u ≫ ψ.hom := by
    apply Over.OverMorphism.ext
    apply hF.1.1.hom_ext
    · rw [hw', he2, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hψF]
    · rw [Over.w, Over.w]
  have h1 : w' ≫ φ.q = 1 := by
    rw [hw, Category.assoc, Category.assoc, htriv, ← Category.assoc]
    rw [Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  rw [h1] at hc
  have h0 := isLieComb_zero_one (v := v) hv.1
  exact (hv.2 1 isTangent_one).unique hc h0

end GlobalTheory.CochAbKer
