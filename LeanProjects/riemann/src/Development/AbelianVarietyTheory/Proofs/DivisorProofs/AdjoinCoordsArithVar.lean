import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedVirtualCharacterNormOneSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFunStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLIsCharacterNormOneOfRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacterHarishChandraProductCuspidalGLOfRegulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftClassFunctionIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterShintaniPsiLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLDegRegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraProductShintaniLiftGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGaloisPairingEqPmOnePrimeDegreeStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem shLift_const_mul {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (a : ℂ) (f : GL (Fin n) F → ℂ) (δ : GL (Fin n) F') :
    shLift s (fun x => a * f x) δ = a * shLift s f δ := by
  unfold shLift
  split_ifs <;> simp

theorem shLift_cusp_kills_J : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ n k : ℕ, 0 < n → Module.finrank F F' ∣ n → Reg (Nat.card F) n k →
    Kills (shLift s (cusp (pullθ ι θ) n k)) (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n) := by
  intro F F' _ _ _ _ s hl hs ι θ hθ n k hn hln hreg
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  haveI : Module.Finite F F' := Module.Finite.of_finite
  haveI : IsGalois F F' := inferInstance
  have hΓ : Nat.card (F' ≃ₐ[F] F') = Module.finrank F F' := IsGalois.card_aut_eq_finrank F F'
  haveI : Finite (F' ≃ₐ[F] F') := Nat.finite_of_card_ne_zero (by rw [hΓ]; exact hl.ne_zero)
  letI : Fintype (F' ≃ₐ[F] F') := Fintype.ofFinite _
  haveI : Fact (Nat.card (F' ≃ₐ[F] F')).Prime := ⟨hΓ ▸ hl⟩
  have hgen : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := by
    intro t
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (Subgroup.zpowers s) with h | h
    · exact absurd (Subgroup.zpowers_eq_bot.1 h) hs
    · rw [h]; exact Subgroup.mem_top t

  have hθ' : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → pullθ ι θ x = pullθ ι θ y → x = y := by
    intro x y hx hy hxy
    apply ι.toRingHom.injective
    exact hθ (ι x) (ι y) ((map_ne_zero ι.toRingHom).2 hx) ((map_ne_zero ι.toRingHom).2 hy) hxy
  set l := Module.finrank F F' with hldef
  set q := Nat.card F with hqdef
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hcardF' : Nat.card F' = q ^ l := Module.natCard_eq_pow_finrank

  obtain ⟨X, hX, hXg, hXs⟩ := GlobalTheory.T.exists_virtualCharacter_shintani_psi_lift F F' s hl hs ι θ hθ k n
  set c : ℂ := (-1) ^ (n - 1) with hc
  have hc2 : c = 1 ∨ c = -1 := neg_one_pow_eq_or ℂ (n - 1)
  set X' : GHat F F' n → ℂ := fun g => c * X g with hX'
  have hX'v : X' ∈ Virt ℂ ℂ (GHat F F' n) := by
    rcases hc2 with h | h
    · have : X' = X := by funext g; simp [hX', h]
      rw [this]; exact hX
    · have : X' = -X := by funext g; simp [hX', h]
      rw [this]; exact neg_mem hX
  have hcusp : cusp (pullθ ι θ) n k = fun x => c * psiG (rootSum (pullθ ι θ) k) n x := rfl
  have hX's : ∀ δ, X' (inl δ * inr s) = shLift s (cusp (pullθ ι θ) n k) δ := by
    intro δ
    rw [hcusp, shLift_const_mul, ← hXs δ]

  obtain ⟨hchar, hnorm⟩ := GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular F (pullθ ι θ) hθ' n k hn hreg
  have hclc : IsCl (cusp (pullθ ι θ) n k) := by
    intro x y
    rw [hcusp]
    simp only
    rw [((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 n (fun _ => 0) (fun _ => 0)).2.2 (rootSum (pullθ ι θ) k)).1 x y]
  have hiso := GlobalTheory.T.shintaniLiftClassFunction_isometry F F' s hgen n _ _ hclc hclc
  rw [hnorm] at hiso
  have hGne : (Nat.card (GL (Fin n) F) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := GL (Fin n) F)).ne'
  have hnorm' : ∑ᶠ δ, X' (inl δ * inr s) * star (X' (inl δ * inr s)) = (Nat.card (GL (Fin n) F') : ℂ) := by
    simp only [hX's]
    apply mul_left_cancel₀ hGne
    rw [hiso, mul_comm]

  obtain ⟨hdeg, hlift⟩ := GlobalTheory.T.deg_liftL_and_reg_pow q l [(n, k)] hq2 hl.pos (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨hn, hln, hreg⟩)
  have hdegn : deg (liftL q l [(n, k)]) = n := by rw [hdeg]; simp [deg]
  have hYchar : IsChar ℂ ℂ (J θ (liftL q l [(n, k)]) n) := by
    apply GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ _ _ n hdegn.symm
    intro p hp
    rw [hcardF']
    exact hlift p hp
  have hYst : ∀ g, J θ (liftL q l [(n, k)]) n (galAct F F' n s g) = J θ (liftL q l [(n, k)]) n g :=
    GlobalTheory.T.harishChandraProduct_shintaniLift_galois F F' θ s [(n, k)] n hdegn.symm

  obtain ⟨m, hm⟩ := hln
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hm; omega
    · exact h
  obtain ⟨z, hz, hzsum⟩ := GlobalTheory.T.cuspidal_galois_pairing_eq_pm_one_prime_degree F F' s hl hs ι θ hθ m k n hm0 hm hreg
  have hpair : ∑ᶠ g, X' (inl g) * star (J θ (liftL q l [(n, k)]) n g)
      = ((if c = 1 then z else -z : ℤ) : ℂ) * (Nat.card (GL (Fin n) F') : ℂ) := by
    have : (fun g : GL (Fin n) F' => X' (inl g) * star (J θ (liftL q l [(n, k)]) n g))
        = fun g => c * (X (inl g) * star (J θ (liftL q l [(n, k)]) n g)) := by
      funext g; simp only [hX']; ring
    rw [this, ← mul_finsum]
    simp only [hXg]
    rw [hzsum]
    rcases hc2 with h | h
    · rw [h]; simp
    · rw [h]; have : (-1 : ℂ) ≠ 1 := by norm_num
      simp [this]
  have hndvd : ¬ ((Nat.card (F' ≃ₐ[F] F') : ℤ) ∣ (if c = 1 then z else -z)) := by
    rw [hΓ]
    intro hd
    have hd' : (l : ℤ) ∣ z := by
      split_ifs at hd
      · exact hd
      · exact (dvd_neg).1 hd
    have h1 : (l : ℤ) ∣ 1 := by
      rcases hz with h | h
      · rwa [h] at hd'
      · rw [h] at hd'; exact (dvd_neg).1 hd'
    have : l ∣ 1 := by exact_mod_cast h1
    exact hl.one_lt.ne' (Nat.dvd_one.1 this)
  have hK := GlobalTheory.T.twisted_virtualCharacter_norm_one_support (GL (Fin n) F') (F' ≃ₐ[F] F') (galAct F F' n) s (hΓ ▸ hl) hs X' hX'v hnorm'
    (J θ (liftL q l [(n, k)]) n) hYchar hYst _ hpair hndvd
  have hfun : (fun δ => X' (inl δ * inr s)) = shLift s (cusp (pullθ ι θ) n k) := funext hX's
  rw [hfun] at hK
  exact hK

end GlobalTheory.Shin
