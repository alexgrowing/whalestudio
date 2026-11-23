import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassGroupFiniteRepresentativesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsShintaniConeDomainStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassConeParametrizationStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuationBis
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaTwistedEntireDifferenceStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaRayClassSummableStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsPrimeDegreeOneAvoidingStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaMeromorphicFromTwistsStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassPrimeMultiplicationPermutationStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaPrimeTwistSummableStatement

set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def classSeries {F : Type} [Field F] [NumberField F] (𝔣 𝔞 : Ideal (𝓞 F)) (s : ℂ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)

theorem exists_avoid_one (𝔣 𝔞 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (h𝔞 : CoprimeTo F 𝔣 𝔞) (ι : Type) [Fintype ι] (r : ι → ℕ)
    (v : ∀ c, Fin (r c) → F) (hv : IsConeDomain 𝔣 r v) :
    ∃ W : Finset (𝓞 F), (∀ x ∈ W, x ≠ 0) ∧
      (∀ s : ℂ, 1 < s.re → Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
        ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s))) ∧
      ∀ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → (∀ x ∈ W, x ∉ 𝔠) →
        ∃ T : ℂ → ℂ, Differentiable ℂ T ∧
          (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
            (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) ∧
          ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) := by
  classical
  obtain ⟨𝔟, J, _, r', y, v', hP⟩ := GlobalTheory.T.ray_class_cone_parametrization F 𝔣 h𝔣 ι r v hv 𝔞 h𝔞
  refine ⟨Finset.univ.biUnion fun j : J => Finset.univ.image (v' j), ?_, GlobalTheory.T.partial_zeta_ray_class_summable F 𝔣 𝔞 𝔟 J r' y v' hP, ?_⟩
  · intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨j, i, rfl⟩ := hx
    intro h0
    have hpos := (hP.2.2.1 j i).2
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have := hpos ((NumberField.InfinitePlace.mk φ).embedding_of_isReal (IsTotallyReal.isReal _))
    simp [h0] at this
  · intro 𝔠 hpr hl hav
    refine GlobalTheory.T.partial_zeta_twisted_entire_difference GlobalTheory.T.abel_continuation F 𝔣 𝔞 𝔟 𝔠 J r' y v' hP hpr hl fun j i hmem => ?_
    have hle : 𝔠 * 𝔟 ≤ 𝔠 := Ideal.mul_le_left
    refine hav (v' j i) ?_ (hle hmem)
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨j, i, rfl⟩

theorem exists_avoid (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (S : Finset (Ideal (𝓞 F))) (hS : ∀ a ∈ S, CoprimeTo F 𝔣 a) :
    ∃ W : Finset (𝓞 F), (∀ x ∈ W, x ≠ 0) ∧
      (∀ c : S, ∀ s : ℂ, 1 < s.re → Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1} =>
        ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s))) ∧
      ∀ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → (∀ x ∈ W, x ∉ 𝔠) → ∀ c : S,
        ∃ T : ℂ → ℂ, Differentiable ℂ T ∧
          (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1} =>
            (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) ∧
          ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) := by
  classical
  obtain ⟨ι, _, r, v, hv⟩ := GlobalTheory.T.exists_shintani_cone_domain F 𝔣 h𝔣
  have h := fun c : S => exists_avoid_one F 𝔣 c.1 h𝔣 (hS _ c.2) ι r v hv
  choose W hW0 hWs hWt using h
  refine ⟨Finset.univ.biUnion W, ?_, hWs, fun 𝔠 hpr hl hav c => hWt c 𝔠 hpr hl fun x hx => hav x ?_⟩
  · intro x hx
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 hx
    exact hW0 c x hc
  · exact Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, hx⟩

theorem exists_classZeta (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (S : Finset (Ideal (𝓞 F))) (hS : ∀ a ∈ S, CoprimeTo F 𝔣 a)
    (hd : ∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) (hc : ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) :
    ∃ Z : S → ℂ → ℂ, ∀ c, IsRayZeta 𝔣 c.1 (Z c) ∧ ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, Z c (1 - (k : ℂ)) = (q : ℂ) := by
  classical
  obtain ⟨W, hW0, hsum, hWt⟩ := exists_avoid F 𝔣 h𝔣 S hS
  have key : ∀ B : ℕ, ∃ 𝔠 : Ideal (𝓞 F), (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧
      ∃ (τ : Equiv.Perm S) (T : S → ℂ → ℂ), (∀ c, Differentiable ℂ (T c)) ∧
        (∀ c s, 1 < s.re → ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (1 - s) * classSeries 𝔣 (τ c).1 s - classSeries 𝔣 c.1 s = T c s) ∧
        ∀ c, ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T c (1 - (k : ℂ)) = (q : ℂ) := by
    intro B
    obtain ⟨𝔠, hpr, hl, hB, hcop, hav⟩ := GlobalTheory.T.exists_prime_degree_one_avoiding F 𝔣 h𝔣 W B hW0
    have h𝔠0 : 𝔠 ≠ ⊥ := by
      rintro rfl
      simp only [Ideal.absNorm_bot] at hl
      exact Nat.not_prime_zero hl
    obtain ⟨τ, hτ⟩ := GlobalTheory.T.ray_class_prime_multiplication_permutation F 𝔣 𝔠 S h𝔣 hpr h𝔠0 hcop hS hd hc
    choose T hTd hTs hTq using hWt 𝔠 hpr hl hav
    refine ⟨𝔠, hl, hB, τ, T, hTd, fun c s hs => ?_, hTq⟩
    obtain ⟨e, he⟩ := hτ c
    exact GlobalTheory.T.partial_zeta_prime_twist_summable F 𝔣 𝔠 (τ c).1 c.1 hl e he s _ hs (hsum _ s hs) (hsum _ s hs) (hTs c s hs)
  obtain ⟨𝔠, hl, -, τ, T, hTd, hTr, hTq⟩ := key 0
  obtain ⟨𝔠', hl', hB', τ', T', hTd', hTr', -⟩ := key (Ideal.absNorm 𝔠)
  obtain ⟨Z, hZd, hZD, hZq⟩ := GlobalTheory.T.partial_zeta_meromorphic_from_twists S (fun c => classSeries 𝔣 c.1) T T' _ _ τ τ' hl hl' hB'.ne hTd hTd' hTr hTr'
  refine ⟨Z, fun c => ⟨⟨hZd c, fun s hs => ?_⟩, fun k hk => hZq k hk (fun c => hTq c k hk) c⟩⟩
  rw [hZD c s hs]
  exact (hsum c s hs).hasSum

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂

open GlobalTheory.CompanionTheory.Hypotheses₂.Shintani in

theorem siegelKlingen : GlobalTheory.Published.SiegelKlingen := by
  classical
  intro F _ _ _ 𝔣 h𝔣 ε hε
  obtain ⟨S, hS, hd, hc⟩ := GlobalTheory.T.ray_class_group_finite_representatives F 𝔣 h𝔣
  obtain ⟨Z, hZ⟩ := exists_classZeta F 𝔣 h𝔣 S hS hd hc
  have hZ' : ∀ c : S, IsRayL 𝔣 (rayIndicator 𝔣 c.1) (Z c) := fun c => isRayZeta_iff.1 (hZ c).1
  have hind : ∀ I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I}, ∑ c : S, (ε c.1 : ℂ) * ((rayIndicator 𝔣 c.1 I.1 : ℚ) : ℂ) = (ε I.1 : ℂ) := by
    intro I
    obtain ⟨a, ha, hIa⟩ := hc I.1 I.2
    rw [Finset.sum_eq_single (⟨a, ha⟩ : S)]
    · have : ε a = ε I.1 := hε _ _ (hS a ha) I.2 (rayRel_symm hIa)
      simp [rayIndicator, hIa, this]
    · intro b _ hb
      have : ¬ RayRel F 𝔣 I.1 b.1 := fun h =>
        hb (Subtype.ext (hd _ b.2 _ ha (rayRel_trans (rayRel_symm h) hIa)))
      simp [rayIndicator, this]
    · simp
  refine ⟨fun s => ∑ c : S, (ε c.1 : ℂ) * Z c s, ⟨?_, fun s hs => ?_⟩, fun k hk => ?_⟩
  · intro s hs
    refine DifferentiableWithinAt.fun_sum fun c _ => ?_
    exact (differentiableWithinAt_const _).mul ((hZ' c).1 s hs)
  · have h1 := hasSum_sum (s := Finset.univ) fun c (_ : c ∈ (Finset.univ : Finset S)) => ((hZ' c).2 s hs).mul_left (ε c.1 : ℂ)
    have he : (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} => (ε I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) =
        fun I => ∑ c : S, (ε c.1 : ℂ) * (((rayIndicator 𝔣 c.1 I.1 : ℚ) : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
      funext I
      rw [← hind I, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [he]
    exact h1
  · choose q hq using fun c : S => (hZ c).2 k hk
    refine ⟨∑ c : S, ε c.1 * q c, ?_⟩
    simp only [hq]
    push_cast
    rfl

end GlobalTheory.CompanionTheory.Hypotheses₂
