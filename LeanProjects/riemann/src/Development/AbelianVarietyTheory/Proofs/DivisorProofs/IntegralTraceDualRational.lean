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

namespace GlobalTheory.BoxLattice.DualRat

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem trPair_ratInf (x y : κ → F) :
    GlobalTheory.VacLn.trPair F κ (ratInf F κ x) (ratInf F κ y) = ((Algebra.trace ℚ F (x ⬝ᵥ y) : ℚ) : ℝ) := by
  rw [GlobalTheory.VacLn.trPair_apply, ← GlobalTheory.PsiNontriv.trace_mixedEmbedding]
  simp [ratInf, dotProduct, map_sum, map_mul]

def vec (a : F) (i : κ) (k : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) : κ → F :=
  Pi.single i (a * integralBasis F k)

theorem vec_mem (a : F) (i : κ) (k : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
    ratInf F κ (vec a i k) ∈ boxLat F κ a := by
  refine ⟨Pi.single i (RingOfIntegers.basis F k), funext fun i' => ?_⟩
  by_cases h : i' = i
  · subst h; simp [ratInf, vec, integralBasis_apply]
  · simp [ratInf, vec, h]

theorem vec_dot (a : F) (i : κ) (k : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) (z : κ → F) :
    vec a i k ⬝ᵥ z = a * integralBasis F k * z i := by
  simp [vec, dotProduct, Pi.single_apply]

theorem ratInf_vec (a : F) (i : κ) (k : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
    ratInf F κ (vec a i k) = Pi.single i (mixedEmbedding F (a * integralBasis F k)) := by
  funext i'
  by_cases h : i' = i
  · subst h; simp [ratInf, vec]
  · simp [ratInf, vec, h]

end GlobalTheory.BoxLattice.DualRat

open GlobalTheory.BoxLattice.DualRat in

theorem GlobalTheory.BoxLattice.dual_rat : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ μ : κ → mixedEmbedding.mixedSpace F, (∀ l ∈ boxLat F κ a, ∃ k : ℤ, GlobalTheory.VacLn.trPair F κ l μ = k) →
      ∃ z : κ → F, μ = ratInf F κ z := by
  intro F _ _ κ _ a ha μ hμ
  choose n hn using fun (j : κ × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) => hμ _ (vec_mem a j.1 j.2)
  let T : (κ → F) →ₗ[ℚ] (κ × Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℚ) :=
    LinearMap.pi fun j => (Algebra.trace ℚ F) ∘ₗ LinearMap.mulLeft ℚ (a * integralBasis F j.2) ∘ₗ
      LinearMap.proj j.1
  have hT : ∀ z j, T z j = Algebra.trace ℚ F (a * integralBasis F j.2 * z j.1) := fun z j => rfl
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    funext i
    have h2 : ∀ y : F, Algebra.trace ℚ F (y * (a * z i)) = 0 := by
      intro y
      have e := (integralBasis F).ext (f₁ := (Algebra.trace ℚ F) ∘ₗ LinearMap.mulRight ℚ (a * z i)) (f₂ := 0)
        (fun k => by
          have := congrFun hz (i, k)
          rw [hT] at this
          simpa [mul_comm, mul_left_comm, mul_assoc] using this)
      simpa [mul_assoc] using LinearMap.congr_fun e y
    by_contra hne
    have hz0 : a * z i ≠ 0 := mul_ne_zero ha hne
    have h3 := h2 (a * z i)⁻¹
    rw [inv_mul_cancel₀ hz0, ← map_one (algebraMap ℚ F), Algebra.trace_algebraMap] at h3
    simp at h3
    exact (Module.finrank_pos (R := ℚ) (M := F)).ne' h3
  have hdim : Module.finrank ℚ (κ → F) = Module.finrank ℚ (κ × Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℚ) := by
    simp [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card,
      Module.finrank_eq_card_basis (integralBasis F), Fintype.card_prod]
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
    (fun j => (n j : ℚ))
  refine ⟨z, ?_⟩
  set w := μ - ratInf F κ z with hw
  have hj : ∀ i k, Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (mixedEmbedding F (a * integralBasis F k) * w i) = 0 := by
    intro i k
    have h1 := hn (i, k)
    have h2 := trPair_ratInf (vec a i k) z
    rw [vec_dot] at h2
    have h3 := congrFun hz (i, k)
    rw [hT] at h3
    have h4 : GlobalTheory.VacLn.trPair F κ (ratInf F κ (vec a i k)) w = 0 := by
      rw [hw, map_sub, h1, h2, h3]; simp
    rw [ratInf_vec, GlobalTheory.VacLn.trPair_apply] at h4
    simpa [Pi.single_apply] using h4
  have hall : ∀ i (t : mixedEmbedding.mixedSpace F),
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (t * w i) = 0 := by
    intro i t
    have e := (mixedEmbedding.latticeBasis F).ext
      (f₁ := (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) ∘ₗ
        LinearMap.mulRight ℝ (mixedEmbedding F a * w i)) (f₂ := 0)
      (fun k => by
        have := hj i k
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
          mixedEmbedding.latticeBasis_apply, LinearMap.zero_apply]
        rw [← this, map_mul (mixedEmbedding F) a]; congr 1; ring)
    have e2 := LinearMap.congr_fun e (mixedEmbedding F a⁻¹ * t)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
      LinearMap.zero_apply] at e2
    have e3 : mixedEmbedding F a⁻¹ * t * (mixedEmbedding F a * w i) =
        mixedEmbedding F (a⁻¹ * a) * (t * w i) := by rw [map_mul (mixedEmbedding F) a⁻¹ a]; ring
    rw [e3, inv_mul_cancel₀ ha, map_one, one_mul] at e2
    exact e2
  have hw0 : w = 0 := by
    apply GlobalTheory.VacLn.trPair_nondeg
    intro x
    rw [GlobalTheory.VacLn.trPair_apply, map_sum]
    exact Finset.sum_eq_zero fun i _ => hall i (x i)
  exact sub_eq_zero.1 hw0
