import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
open scoped Topology

namespace GlobalTheory.AdeleBaseChange

theorem continuous_symm_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ι : FiniteAdeleRing (𝓞 F) F ⊗[F] E ≃+* FiniteAdeleRing (𝓞 E) E), (∀ y, y ∈ AddSubgroup.closure {y : FiniteAdeleRing (𝓞 F) F ⊗[F] E | ∃ a ∈ {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} ↔ ∀ P, Valued.v (ι y P) ≤ 1) → letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); Continuous ι.symm := by
  intro F E _ _ _ _ _ ι hι
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (FiniteAdeleRing (𝓞 F) F) _
  have h0 := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E 0 ⊤ (Subsingleton.elim _ _)).2
  refine continuous_of_continuousAt_zero ι.symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  intro W hW
  obtain ⟨N, hN, hNW⟩ := h0 W hW
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds E N hN) ?_
  rintro _ ⟨a, ha, rfl⟩
  rw [Set.mem_preimage, map_nsmul]
  apply hNW
  have h1 := (hι (ι.symm a)).2 (fun P => by rw [ι.apply_symm_apply]; exact ha P)
  refine AddSubgroup.closure_mono ?_ h1
  rintro _ ⟨b, hb, x, rfl⟩
  exact ⟨b, hb, _, ⟨x, rfl⟩, rfl⟩

end GlobalTheory.AdeleBaseChange
