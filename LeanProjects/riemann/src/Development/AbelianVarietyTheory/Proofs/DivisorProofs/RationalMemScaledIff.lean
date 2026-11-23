import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiFinRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical
open GlobalTheory.BoxLattice GlobalTheory.EvAdm

noncomputable section

namespace GlobalTheory.BoxLattice

theorem ratFin_mem_scaledInt_iff (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F) (ha : a ≠ 0)
    (η : κ → F) : ratFin F κ η ∈ scaledInt F κ a ↔ ∃ b : κ → 𝓞 F, η = fun i => a * (b i : F) := by
  have hev : ∀ (x : F) (v : HeightOneSpectrum (𝓞 F)),
      (algebraMap F (v.adicCompletion F) a)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) x) v =
        algebraMap F (v.adicCompletion F) (a⁻¹ * x) := by
    intro x v
    rw [map_mul, map_inv₀]
    rfl
  rw [mem_scaledInt]
  constructor
  · intro h
    have hx : ∀ i, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = a⁻¹ * η i := by
      intro i
      refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (a⁻¹ * η i) fun v => ?_
      have h1 := h i v
      simp only [ratFin] at h1
      rw [hev, HeightOneSpectrum.mem_adicCompletionIntegers] at h1
      first
        | (rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at h1)
        | (erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1; exact h1)
        | (rwa [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v (a⁻¹ * η i)])
        | (simpa using h1)
    choose b hb using hx
    refine ⟨b, funext fun i => ?_⟩
    show η i = a * algebraMap (𝓞 F) F (b i)
    rw [hb i, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  · rintro ⟨b, rfl⟩ i v
    simp only [ratFin]
    rw [hev, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v (b i)

end GlobalTheory.BoxLattice
