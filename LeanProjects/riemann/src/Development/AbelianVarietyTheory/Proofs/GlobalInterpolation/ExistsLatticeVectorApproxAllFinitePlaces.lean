import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsGeneratorsMemCompletedLatticeIffStatement

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.OverCompare

theorem exists_int_approx_all (F : Type) [Field F] [NumberField F] (T : ℕ) (hT : T ≠ 0)
    (t : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ht : ∀ v, t v ∈ v.adicCompletionIntegers F) :
    ∃ ρ : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F), ∃ w ∈ v.adicCompletionIntegers F,
      t v = algebraMap F (v.adicCompletion F) (ρ : F) + T • w := by
  let a : FiniteAdeleRing (𝓞 F) F := ⟨t, Filter.Eventually.of_forall ht⟩
  obtain ⟨ρ, w, hw, e⟩ := Formalism.UG.P.csGlob_intAdApprox F (T : 𝓞 F) (by exact_mod_cast hT) a ht
  refine ⟨ρ, fun v => ⟨w v, hw v, ?_⟩⟩
  rw [map_natCast, ← nsmul_eq_mul] at e
  have h : a v = (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) ρ + T • w) v := by rw [← e]
  exact h

theorem exists_lattice_approx_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → ∀ (T : ℕ), T ≠ 0 → ∀ (y : ∀ v : HeightOneSpectrum (𝓞 F), Fin k → E ⊗[F] v.adicCompletion F), (∀ v, y v ∈ locLat v Λ) → ∃ x ∈ Λ, ∀ v : HeightOneSpectrum (𝓞 F), ∃ z ∈ locLat v Λ, y v = (fun i => inclE (F := F) (v.adicCompletion F) (x i)) + T • z := by
  intro F E _ _ _ _ _ k Λ hΛ T hT y hy
  obtain ⟨m, l, hl, H⟩ := GlobalTheory.T.exists_generators_mem_completedLattice_iff F E k Λ hΛ
  choose t ht hyt using fun v : HeightOneSpectrum (𝓞 F) =>
    (H (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring (y v)).1 (hy v)
  choose ρ hρ using fun j : Fin m =>
    exists_int_approx_all F T hT (fun v => t v j) (fun v => ht v j)
  refine ⟨∑ j, algebraMap (𝓞 F) (𝓞 E) (ρ j) • l j,
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hl j), fun v => ?_⟩
  choose w hw hwt using fun j => hρ j v
  refine ⟨fun i => ∑ j, l j i ⊗ₜ[F] w j,
    (H (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring _).2 ⟨w, hw, rfl⟩, ?_⟩
  rw [hyt v]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, map_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hwt j, TensorProduct.tmul_add]
  congr 1
  · have h1 : algebraMap (𝓞 F) (𝓞 E) (ρ j) • l j i = (ρ j : F) • l j i := by
      rw [Algebra.smul_def, Algebra.smul_def]; rfl
    rw [h1, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
    rfl
  · exact map_nsmul (TensorProduct.mk F E (v.adicCompletion F) (l j i)) T (w j)

end GlobalTheory.OverCompare
