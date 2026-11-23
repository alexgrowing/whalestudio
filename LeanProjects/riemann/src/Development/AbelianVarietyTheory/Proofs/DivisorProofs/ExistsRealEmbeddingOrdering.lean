import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCMTypeOfEmbeddingsCardEqFinrank
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMTypeRestrict

theorem exists_equiv_realEmbeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (e₀ : Fin (Module.finrank ℚ (FR E)) ≃ I),
    ∃ e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ), ∀ j (x : FR E), (e j x : ℂ) = φ (e₀ j) (x : E) := by
  intro E _ _ _ I _ φ hφ e₀
  have hreal : ∀ i, ComplexEmbedding.IsReal ((φ i).comp (algebraMap (FR E) E)) := fun i =>
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  let g : Fin (Module.finrank ℚ (FR E)) → (FR E →+* ℝ) := fun j => (hreal (e₀ j)).embedding
  have hg : ∀ j (x : FR E), (g j x : ℂ) = φ (e₀ j) (x : E) := fun j x =>
    (hreal (e₀ j)).coe_embedding_apply x
  have hinj : Function.Injective g := by
    intro j k hjk
    have hc : (φ (e₀ j)).comp (algebraMap (FR E) E) = (φ (e₀ k)).comp (algebraMap (FR E) E) := by
      ext x
      have h1 := hg j x
      have h2 := hg k x
      rw [hjk] at h1
      simp only [RingHom.comp_apply]
      exact h1.symm.trans h2
    have hm : IsCMField.equivInfinitePlace E (InfinitePlace.mk (φ (e₀ j))) =
        IsCMField.equivInfinitePlace E (InfinitePlace.mk (φ (e₀ k))) := by
      rw [IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply,
        InfinitePlace.comap_mk, InfinitePlace.comap_mk, hc]
    have := (GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hφ).1 ((IsCMField.equivInfinitePlace E).injective hm)
    exact e₀.injective this
  have hcard : Fintype.card (Fin (Module.finrank ℚ (FR E))) = Fintype.card (FR E →+* ℝ) := by
    rw [Fintype.card_fin, GlobalTheory.card_realEmbeddings]
  exact ⟨Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).2 ⟨hinj, hcard⟩), fun j x => hg j x⟩

end GlobalTheory.CMTypeRestrict
