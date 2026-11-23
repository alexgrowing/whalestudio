import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiFinRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAnnihilatorOpenSubgroupFiniteAdeles

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical
open GlobalTheory.BoxLattice GlobalTheory.EvAdm

noncomputable section

namespace GlobalTheory.BoxLattice

theorem psi_fin_scaledInt_dot : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ a : F, a ≠ 0 → ∀ z : κ → F, (∀ l ∈ boxLat F κ a, ∃ k : ℤ, GlobalTheory.VacLn.trPair F κ l (ratInf F κ z) = k) →
      ∀ u ∈ scaledInt F κ a, ψ (pairA F 0 (u ⬝ᵥ ratFin F κ z)) = 1 := by
  intro F _ _ κ _ ψ hψ a ha z hz u hu

  have hdual : ∀ i, ∀ b : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((b : F) * (a * z i)))) = 1 := by
    intro i b
    obtain ⟨k, hk⟩ := hz (ratInf F κ (Pi.single i (a * (b : F)))) ⟨Pi.single i b, funext fun j => by
      by_cases h : j = i
      · subst h; simp [ratInf]
      · simp [ratInf, Pi.single_eq_of_ne h]⟩
    have h1 := psi_fin_rat (κ := κ) hψ (Pi.single i (a * (b : F))) z
    have e : ratFin F κ (Pi.single i (a * (b : F))) ⬝ᵥ ratFin F κ z =
        algebraMap F (Af F) ((b : F) * (a * z i)) := by
      have e2 : ratFin F κ (Pi.single i (a * (b : F))) = Pi.single i (algebraMap F (Af F) (a * (b : F))) := by
        funext j
        by_cases h : j = i
        · subst h; simp [ratFin]
        · simp [ratFin, Pi.single_eq_of_ne h]
      rw [e2, single_dotProduct]
      simp only [ratFin, ← map_mul]
      congr 1
      ring
    rw [e, hk] at h1
    rw [h1, Complex.exp_eq_one_iff]
    exact ⟨k, by push_cast; ring⟩

  set t : κ → Af F := fun i => algebraMap F (Af F) a⁻¹ * u i with ht
  have hti : ∀ i (v : HeightOneSpectrum (𝓞 F)), t i v ∈ v.adicCompletionIntegers F := by
    intro i v
    have h := hu i v
    have e : t i v = (algebraMap F (v.adicCompletion F) a)⁻¹ * (u i) v := by
      show (algebraMap F (Af F) a⁻¹ * u i) v = _
      rw [← map_inv₀ (algebraMap F (v.adicCompletion F))]
      rfl
    rw [e]; exact h
  have hsum : u ⬝ᵥ ratFin F κ z = ∑ i, t i * algebraMap F (Af F) (a * z i) := by
    simp only [dotProduct, ratFin]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ht, map_mul]
    rw [show algebraMap F (Af F) a⁻¹ * u i * (algebraMap F (Af F) a * algebraMap F (Af F) (z i)) =
      (algebraMap F (Af F) a⁻¹ * algebraMap F (Af F) a) * (u i * algebraMap F (Af F) (z i)) by ring,
      ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  let P : Af F →+ AF F :=
    { toFun := pairA F 0, map_zero' := rfl, map_add' := GlobalTheory.AnnCompactStd.pairA_zero_add }
  have hP : ∀ y, pairA F 0 y = P y := fun _ => rfl
  rw [hsum, hP, map_sum]
  have hone : ∀ i, ψ (P (t i * algebraMap F (Af F) (a * z i))) = 1 := fun i =>
    GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hψ.1 (a * z i) (hdual i) (t i) (hti i)
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, AddChar.map_add_eq_mul, hone j, ih, one_mul]

end GlobalTheory.BoxLattice
