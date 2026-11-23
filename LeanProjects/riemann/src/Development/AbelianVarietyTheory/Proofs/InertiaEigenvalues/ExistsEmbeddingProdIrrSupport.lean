import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRegularOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInjectiveOfSubsingleton
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel GlobalTheory.BCen

namespace GlobalTheory.BCen.SuppEmbed

theorem exists_embedding_prodIrr_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible →
    ∃ (t : ℕ) (x : Fin t → IrrGL k) (hx : ∑ a, (x a).1 = n) (φ : π.IntertwiningMap (prodIrr x hx)),
      (∀ a, (x a).IsCusp) ∧ Function.Injective φ ∧ ∀ s, HasSupport π s ↔ Finset.univ.val.map x = s := by
  intro k _ _ _ _ n V _ _ π hs hi
  obtain ⟨t, x, hx, hc, φ, hφ⟩ :=
    GlobalTheory.CompanionTheory.SubEmb.subEmbedding_of_stage GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k n V π hs hi
  have hsupp : HasSupport π (Finset.univ.val.map x) :=
    hasSupport_of_isSubquotient hi hc (.of_injective φ hφ)
  refine ⟨t, x, hx, φ, hc, hφ, fun s => ⟨fun h => ?_, fun h => h ▸ hsupp⟩⟩
  exact GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.bernsteinZelevinskyFiniteness_holds hsupp h

end GlobalTheory.BCen.SuppEmbed
