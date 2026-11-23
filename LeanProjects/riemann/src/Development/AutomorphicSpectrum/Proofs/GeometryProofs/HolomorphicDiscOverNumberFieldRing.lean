import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InducedModelMorphismCompStructureMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlag
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.ConstEmbedding

theorem exists_spMap {A : Type} [CommRing A] (x : Sp ℂ ⟶ Sp A) : ∃ ψ : A →+* ℂ, spMap ψ = x :=
  ⟨(Spec.preimage x).hom, by
    show Spec.map (CommRingCat.ofHom (Spec.preimage x).hom) = x
    simp⟩

theorem exists_extend (F : Type) [Field F] [NumberField F] (ψ : 𝓞 F →+* ℂ) :
    ∃ τ : F →+* ℂ, τ.comp (algebraMap (𝓞 F) F) = ψ := by
  have hinj : Function.Injective ψ :=
    GlobalTheory.CompanionTheory.Ar.GrNorm.injective_of_algebraic (algebraMap (𝓞 F) F)
      (IsFractionRing.injective (𝓞 F) F) ψ
  refine ⟨IsFractionRing.lift hinj, RingHom.ext fun a => ?_⟩
  simp

theorem exists_embedding (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (n : ℕ)
    (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)) (hol : IsHolTo (Metric.ball 0 1) p) :
    ∃ τ : F →+* ℂ, ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ q = spMap (τ.comp (algebraMap (𝓞 F) F)) := by
  choose ψ hψ using fun u => exists_spMap (p u ≫ q)
  choose κ hκ using fun u => exists_extend F (ψ u)
  have hd : ∀ a : 𝓞 F, DifferentiableOn ℂ (fun b => κ b (a : F)) (Metric.ball 0 1) := by
    intro a
    have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hol q
    have h3 := (h2 ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv a)).2
    have hset : Metric.ball (0 : Fin n → ℂ) 1 ⊆ {b ∈ Metric.ball (0 : Fin n → ℂ) 1 | ⊤ ≤ (p b ≫ q) ⁻¹ᵁ ⊤} :=
      fun b hb => ⟨hb, le_top⟩
    refine (h3.mono hset).congr fun b _ => ?_
    show κ b (a : F) = valAt' (p b ≫ q) ⊤ _
    rw [← hψ b, ← hκ b]
    exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_spMap ((κ b).comp (algebraMap (𝓞 F) F)) a).symm
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  refine ⟨κ 0, fun u hu => ?_⟩
  have hc := GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.embedding_const_preconnected (convex_ball (0 : Fin n → ℂ) 1).isPreconnected κ hd hu h0
  rw [← hc, hκ u, hψ u]

end GlobalTheory.CompanionTheory.Ar.ConstEmbedding
