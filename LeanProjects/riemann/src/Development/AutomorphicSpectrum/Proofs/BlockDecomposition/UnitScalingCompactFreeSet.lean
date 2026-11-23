import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil

def dilHomeo {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (M : ℕ) (u : Aˣ) :
    (Fin 1 → Fin M → A) ≃ₜ (Fin 1 → Fin M → A) where
  toFun X p k := (u : A) * X p k
  invFun X p k := ((u⁻¹ : Aˣ) : A) * X p k
  left_inv X := by
    funext p k
    simp
  right_inv X := by
    funext p k
    simp
  continuous_toFun := continuous_pi fun p => continuous_pi fun k =>
    continuous_const.mul ((continuous_apply k).comp (continuous_apply p))
  continuous_invFun := continuous_pi fun p => continuous_pi fun k =>
    continuous_const.mul ((continuous_apply k).comp (continuous_apply p))

theorem linearIndependent_dil {A : Type} [CommRing A] {M : ℕ} (u : Aˣ) (X : Fin 1 → Fin M → A)
    (hX : LinearIndependent A X) :
    LinearIndependent A (fun (p : Fin 1) (k : Fin M) => (u : A) * X p k) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro g hg i
  have h0 : ∑ i, (g i * (u : A)) • X i = 0 := by
    funext k
    have := congrFun hg k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h1 := hX (fun i => g i * (u : A)) h0 i
  exact (Units.mul_left_eq_zero u).1 h1

theorem dil_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v ⊗[F] E)ˣ) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsCompact P → IsOpen P → P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} → IsCompact ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P) ∧ IsOpen ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P) ∧ (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
  intro F E _ _ _ _ _ σ _ M v u P hc ho hP
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := TopK.isTopRing (Fv F v)
  refine ⟨hc.image (dilHomeo M u).continuous, (dilHomeo M u).isOpenMap _ ho, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  exact linearIndependent_dil u X (hP hX)

end GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil
