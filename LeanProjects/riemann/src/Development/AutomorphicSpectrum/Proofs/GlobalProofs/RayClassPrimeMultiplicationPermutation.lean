import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem rayRel_of_mul_left {F : Type} [Field F] [NumberField F] {𝔣 𝔠 I J : Ideal (𝓞 F)} (h𝔠 : 𝔠 ≠ ⊥)
    (h : RayRel F 𝔣 (𝔠 * I) (𝔠 * J)) : RayRel F 𝔣 I J := by
  obtain ⟨a, b, ha, hb, ha', hb', hp, e⟩ := h
  refine ⟨a, b, ha, hb, ha', hb', hp, mul_left_cancel₀ h𝔠 ?_⟩
  rw [mul_left_comm, e, mul_left_comm]

theorem shift_perm (F : Type) [Field F] [NumberField F] (𝔣 𝔠 : Ideal (𝓞 F)) (S : Finset (Ideal (𝓞 F))) (_h𝔣 : 𝔣 ≠ ⊥)
    (_hp : 𝔠.IsPrime) (h0 : 𝔠 ≠ ⊥) (hs : 𝔠 ⊔ 𝔣 = ⊤)
    (hS : ∀ a ∈ S, CoprimeTo F 𝔣 a) (hu : ∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b)
    (hr : ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) :
    ∃ τ : Equiv.Perm S, ∀ c : S,
      ∃ e : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I (τ c).1} ≃
          {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1) ∧ I ≤ 𝔠},
        ∀ J, (e J).1 = 𝔠 * J.1 := by
  have hc : CoprimeTo F 𝔣 𝔠 := ⟨h0, hs⟩
  have hex : ∀ d : S, ∃ a : S, RayRel F 𝔣 (𝔠 * d.1) a.1 := fun d => by
    obtain ⟨a, ha, h⟩ := hr _ (coprimeTo_mul hc (hS d.1 d.2))
    exact ⟨⟨a, ha⟩, h⟩
  choose φ hφ using hex
  have hinj : Function.Injective φ := fun d d' h => by
    have h1 : RayRel F 𝔣 (𝔠 * d.1) (𝔠 * d'.1) := rayRel_trans (hφ d) (h ▸ rayRel_symm (hφ d'))
    exact Subtype.ext (hu _ d.2 _ d'.2 (rayRel_of_mul_left h0 h1))
  let τ : Equiv.Perm S := (Equiv.ofBijective φ (Finite.injective_iff_bijective.1 hinj)).symm
  have hτ : ∀ c : S, RayRel F 𝔣 (𝔠 * (τ c).1) c.1 := fun c => by
    have h1 : φ (τ c) = c := (Equiv.ofBijective φ (Finite.injective_iff_bijective.1 hinj)).apply_symm_apply c
    have h2 := hφ (τ c)
    rwa [h1] at h2
  refine ⟨τ, fun c => ?_⟩
  let f : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I (τ c).1} →
      {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1) ∧ I ≤ 𝔠} := fun J =>
    ⟨𝔠 * J.1, ⟨coprimeTo_mul hc J.2.1, rayRel_trans (rayRel_mul_left 𝔠 J.2.2) (hτ c)⟩, Ideal.mul_le_left⟩
  have hf : Function.Bijective f := by
    constructor
    · intro J J' h
      have h1 : 𝔠 * J.1 = 𝔠 * J'.1 := congrArg (fun x : {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1) ∧ I ≤ 𝔠} => x.1) h
      exact Subtype.ext (mul_left_cancel₀ h0 h1)
    · rintro ⟨I, ⟨hI, hIc⟩, hle⟩
      obtain ⟨J, rfl⟩ := Ideal.dvd_iff_le.2 hle
      have hJ0 : J ≠ ⊥ := fun h => hI.1 (by rw [h, Ideal.mul_bot])
      have hJ : CoprimeTo F 𝔣 J :=
        ⟨hJ0, top_le_iff.1 (hI.2 ▸ sup_le_sup_right Ideal.mul_le_right 𝔣)⟩
      exact ⟨⟨J, hJ, rayRel_of_mul_left h0 (rayRel_trans hIc (rayRel_symm (hτ c)))⟩, rfl⟩
  exact ⟨Equiv.ofBijective f hf, fun J => rfl⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
