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
namespace GlobalTheory.ThetaCoset
open GlobalTheory.BoxLattice GlobalTheory.EvAdm
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem ratFin_mem_scaledInt_iff {a : F} (ha : a ≠ 0) (ξ : κ → F) :
    ratFin F κ ξ ∈ scaledInt F κ a ↔ ∃ b : κ → 𝓞 F, ξ = fun i => a * (b i : F) := by
  constructor
  · intro h
    have hi : ∀ i, ∃ c : 𝓞 F, (c : F) = a⁻¹ * ξ i := by
      intro i
      obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (a⁻¹ * ξ i) fun v => by
        have h1 := h i v
        have e : (algebraMap F (v.adicCompletion F) a)⁻¹ * (ratFin F κ ξ i) v =
            algebraMap F (v.adicCompletion F) (a⁻¹ * ξ i) := by
          rw [map_mul, map_inv₀]; rfl
        rw [e, HeightOneSpectrum.mem_adicCompletionIntegers] at h1
        rwa [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact ⟨c, hc⟩
    choose b hb using hi
    refine ⟨b, funext fun i => ?_⟩
    rw [hb i, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  · rintro ⟨b, rfl⟩ i v
    have e : (algebraMap F (v.adicCompletion F) a)⁻¹ * (ratFin F κ (fun i => a * (b i : F)) i) v =
        algebraMap F (v.adicCompletion F) ((b i : 𝓞 F) : F) := by
      have e2 : (ratFin F κ (fun i => a * (b i : F)) i) v = algebraMap F (v.adicCompletion F) (a * (b i : F)) := rfl
      rw [e2, map_mul, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).2 ha), one_mul]
    rw [e, HeightOneSpectrum.mem_adicCompletionIntegers]
    show Valued.v ((((b i : 𝓞 F) : F)) : v.adicCompletion F) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact v.valuation_le_one _

theorem thetaSum_coset (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F) (ha : a ≠ 0)
    (r : κ → FiniteAdeleRing (𝓞 F) F) (ρ : κ → F) (hρ : ratFin F κ ρ - r ∈ scaledInt F κ a)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :
    thetaSum F (pureA F f (Set.indicator {y | y - r ∈ scaledInt F κ a} fun _ => (1 : ℂ))) =
      ∑' l : boxLat F κ a, f (ratInf F κ ρ + l) := by
  set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := Set.indicator {y | y - r ∈ scaledInt F κ a} fun _ => (1 : ℂ)

  have hterm : ∀ ξ : κ → F, pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) =
      f (ratInf F κ ξ) * g (ratFin F κ ξ) := by
    intro ξ
    simp only [pureA]
    congr 2
    funext i
    exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm

  have hmem : ∀ ξ : κ → F, ratFin F κ ξ - r ∈ scaledInt F κ a ↔ ∃ b : κ → 𝓞 F, ξ = ρ + fun i => a * (b i : F) := by
    intro ξ
    have e : ratFin F κ ξ - r = ratFin F κ (ξ - ρ) + (ratFin F κ ρ - r) := by
      funext i; simp [ratFin]
    rw [e, AddSubgroup.add_mem_cancel_right _ hρ, ratFin_mem_scaledInt_iff ha]
    constructor
    · rintro ⟨b, hb⟩; exact ⟨b, by rw [← hb]; abel⟩
    · rintro ⟨b, hb⟩; exact ⟨b, by rw [hb]; abel⟩
  set e1 : (κ → 𝓞 F) → (κ → F) := fun b => ρ + fun i => a * (b i : F) with he1
  have hinj1 : Function.Injective e1 := by
    intro b b' h
    funext i
    have h1 := congrFun h i
    simp only [he1, Pi.add_apply, add_right_inj] at h1
    exact RingOfIntegers.coe_injective (mul_left_cancel₀ ha h1)
  have hg1 : ∀ b, g (ratFin F κ (e1 b)) = 1 := by
    intro b
    simp only [g]
    rw [Set.indicator_of_mem]
    exact (hmem _).2 ⟨b, rfl⟩
  have hL : thetaSum F (pureA F f g) = ∑' b : κ → 𝓞 F, f (ratInf F κ (e1 b)) := by
    rw [thetaSum, ← hinj1.tsum_eq]
    · refine tsum_congr fun b => ?_
      rw [hterm, hg1, mul_one]
    · intro ξ hξ
      rw [Function.mem_support, hterm] at hξ
      by_contra hn
      apply hξ
      have : g (ratFin F κ ξ) = 0 := by
        simp only [g]
        rw [Set.indicator_of_notMem]
        intro hm
        obtain ⟨b, hb⟩ := (hmem ξ).1 hm
        exact hn ⟨b, hb.symm⟩
      rw [this, mul_zero]

  set e2 : (κ → 𝓞 F) → boxLat F κ a := fun b => ⟨ratInf F κ fun i => a * (b i : F), b, rfl⟩ with he2
  have hinj2 : Function.Injective e2 := by
    intro b b' h
    have h1 := congrArg Subtype.val h
    funext i
    have h2 := congrFun h1 i
    simp only [he2, ratInf] at h2
    exact RingOfIntegers.coe_injective (mul_left_cancel₀ ha (mixedEmbedding_injective F h2))
  have hsurj2 : Function.Surjective e2 := by
    rintro ⟨l, b, rfl⟩
    exact ⟨b, rfl⟩
  rw [hL, ← (Equiv.ofBijective e2 ⟨hinj2, hsurj2⟩).tsum_eq]
  refine tsum_congr fun b => ?_
  congr 1
  funext i
  simp [he1, he2, ratInf, map_add]

end GlobalTheory.ThetaCoset
