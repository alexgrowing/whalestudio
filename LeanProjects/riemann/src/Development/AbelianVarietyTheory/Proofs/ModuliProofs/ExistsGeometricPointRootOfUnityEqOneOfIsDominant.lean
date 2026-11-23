import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory

theorem exists_geometricPoint_rootOfUnity_eq_one_of_isDominant :
    ∀ (X U V : Scheme.{0}) (j : U ⟶ X) (v : V ⟶ X), IsDominant j → IsOpenImmersion v → ∀ (ζ : Γ(V, ⊤)) (N : ℕ), ζ ^ N = 1 → ∀ (k : Type) [Field k] (y : Sp k ⟶ V), (N : k) ≠ 0 → y.appTop.hom ζ = 1 → ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (u : Sp K ⟶ U) (z : Sp K ⟶ V), z ≫ v = u ≫ j ∧ z.appTop.hom ζ = 1 := by
  intro X U V j v hj hv ζ N hζ k _ y hN hy
  classical
  set s : Γ(V, ⊤) := ∑ i ∈ Finset.range N, ζ ^ i with hs
  have hmul : s * (ζ - 1) = 0 := by rw [hs, geom_sum_mul, hζ, sub_self]
  have hys : y.appTop.hom s = (N : Γ(Sp k, ⊤)) := by
    simp [hs, map_sum, map_pow, hy]
  have hunit : IsUnit (y.appTop.hom s) := by
    rw [hys]
    have h1 : IsUnit (N : k) := isUnit_iff_ne_zero.mpr hN
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    rwa [map_natCast] at h2
  have hpre : y ⁻¹ᵁ V.basicOpen s = ⊤ := by
    rw [Scheme.preimage_basicOpen_top]
    exact (Sp k).basicOpen_of_isUnit hunit
  have hne : ((V.basicOpen s : V.Opens) : Set V).Nonempty := by
    obtain ⟨p⟩ : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
    refine ⟨y p, ?_⟩
    have : p ∈ y ⁻¹ᵁ V.basicOpen s := by rw [hpre]; trivial
    exact this
  have hopen : IsOpen (v '' ((V.basicOpen s : V.Opens) : Set V)) :=
    v.isOpenEmbedding.isOpenMap _ (V.basicOpen s).isOpen
  obtain ⟨u₀, z₀, hz₀, hzu⟩ := j.denseRange.exists_mem_open hopen (hne.image _)
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := v) (g := j) z₀ u₀ hzu
  let P := pullback v j
  let K : Type := AlgebraicClosure (P.residueField w)
  let q : Sp K ⟶ P := spMap (algebraMap (P.residueField w) K) ≫ P.fromSpecResidueField w
  have hq : ∀ p, q p = w := by
    intro p
    simp only [q, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  refine ⟨K, inferInstance, inferInstance, q ≫ pullback.snd v j, q ≫ pullback.fst v j, ?_, ?_⟩
  · simp only [Category.assoc, pullback.condition]
  · set z := q ≫ pullback.fst v j with hz
    have hzs : z.appTop.hom s ≠ 0 := by
      intro h0
      obtain ⟨p⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
      have hp : p ∈ z ⁻¹ᵁ V.basicOpen s := by
        change z p ∈ V.basicOpen s
        rw [hz, Scheme.Hom.comp_apply, hq, hw1]
        exact hz₀
      rw [Scheme.preimage_basicOpen_top] at hp
      have : (Sp K).basicOpen (z.appTop.hom s) = ⊥ := by
        rw [h0]; exact (Sp K).basicOpen_zero _
      have hp' : p ∈ (Sp K).basicOpen (z.appTop.hom s) := hp
      rw [this] at hp'
      exact hp'
    haveI : IsDomain Γ(Sp K, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain
    have h := congrArg z.appTop.hom hmul
    rw [map_mul, map_zero, map_sub, map_one] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hzs)

end GlobalTheory
