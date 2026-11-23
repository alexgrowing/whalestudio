import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem relIndex_ker_prime {Γ : Type} [Group Γ] (H H' : Subgroup Γ) (s : Γ →* ℂˣ) (p : ℕ) (hp : p.Prime)
    (hH' : ∀ g, g ∈ H' ↔ g ∈ H ∧ s g = 1) (hs : ∀ g ∈ H, s g ^ p = 1) (τ : Γ) (hτ : τ ∈ H) (hτs : s τ ≠ 1) :
    (H'.relIndex H).Prime := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let f : H →* ℂˣ := s.comp H.subtype
  have hker : f.ker = H'.subgroupOf H := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hH']
    simp [f]
  have hidx : H'.relIndex H = Nat.card f.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hle : f.range ≤ rootsOfUnity p ℂ := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    exact hs g g.2
  have hcard : Nat.card (rootsOfUnity p ℂ) = p := by
    exact Complex.card_rootsOfUnity p
  have hdvd : Nat.card f.range ∣ p := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hcard] at this
  have hne : Nat.card f.range ≠ 1 := by
    intro h1
    have hbot : f.range = ⊥ := by
      haveI : Finite (rootsOfUnity p ℂ) := inferInstance
      exact (Subgroup.eq_bot_iff_card _).2 h1
    have : f ⟨τ, hτ⟩ ∈ f.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hτs this
  rw [hidx]
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact absurd h hne
  · rwa [h]

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.groupStep :
    GroupStep := by
  intro Γ _ Gd P D Pl Dc I hI hinf hmono hpsi hstep H₀ r hH₀ hP hr n hn hrn
  have hpowk : ∀ (s : Γ →* ℂˣ) (k : ℕ), Gd s.ker → Gd (s ^ k).ker := by
    intro s k hs
    refine hmono _ _ (fun g hg => ?_) hs
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.pow_apply, hg, one_pow]
  have key : ∀ n : ℕ, 0 < n → ∀ r : Γ →* ℂˣ, Gd r.ker → P (H₀ ⊓ (r ^ n).ker) →
      ∃ r' : Γ →* ℂˣ, Gd r'.ker ∧ (∀ g ∈ D, r' g = r g) ∧ P (H₀ ⊓ r'.ker) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn r hr hP
      rcases Nat.lt_or_ge 1 n with h1 | h1
      swap
      · have hn1 : n = 1 := by omega
        subst hn1
        exact ⟨r, hr, fun _ _ => rfl, by simpa using hP⟩
      obtain ⟨p, hp, n', rfl⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      have hn' : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hlt : n' < p * n' := by
        have := hp.two_le
        nlinarith
      obtain ⟨ψ, hψk, hψn, hψD, u, hDc, τ, hτ, hτo⟩ := hpsi (H₀ ⊓ r.ker) (hinf _ _ hH₀ hr) (p * n') hn
      have hr1 : Gd (r * ψ).ker := by
        refine hmono _ _ (fun g hg => ?_) (hinf _ _ hr hψk)
        have h1 : r g = 1 := hg.1
        have h2 : ψ g = 1 := hg.2
        rw [MonoidHom.mem_ker, MonoidHom.mul_apply, h1, h2, one_mul]
      have hr1n : (r * ψ) ^ (p * n') = r ^ (p * n') := by
        rw [mul_pow, hψn, mul_one]
      have hτU : τ ∈ H₀ ⊓ r.ker := hDc (hI u hτ)
      have hτr : r τ = 1 := hτU.2
      have hGH : Gd (H₀ ⊓ (r ^ (p * n')).ker) := hinf _ _ hH₀ (hpowk _ _ hr)
      have hGH' : Gd (H₀ ⊓ ((r * ψ) ^ n').ker) := hinf _ _ hH₀ (hpowk _ _ hr1)
      have hval : ∀ g, ((r * ψ) ^ n') g ^ p = (r ^ (p * n')) g := by
        intro g
        rw [← hr1n, MonoidHom.pow_apply, MonoidHom.pow_apply, ← pow_mul, mul_comm n' p]
      have hle : H₀ ⊓ ((r * ψ) ^ n').ker ≤ H₀ ⊓ (r ^ (p * n')).ker := by
        intro g hg
        refine ⟨hg.1, ?_⟩
        have h1 : ((r * ψ) ^ n') g = 1 := hg.2
        show (r ^ (p * n')) g = 1
        rw [← hval, h1, one_pow]
      have hUH : H₀ ⊓ r.ker ≤ H₀ ⊓ (r ^ (p * n')).ker := by
        intro g hg
        refine ⟨hg.1, ?_⟩
        have h1 : r g = 1 := hg.2
        show (r ^ (p * n')) g = 1
        rw [MonoidHom.pow_apply, h1, one_pow]
      have hτs : ((r * ψ) ^ n') τ ≠ 1 := by
        intro h
        rw [MonoidHom.pow_apply, MonoidHom.mul_apply, hτr, one_mul] at h
        have := Nat.le_of_dvd hn' (orderOf_dvd_of_pow_eq_one h)
        omega
      have hprime : ((H₀ ⊓ ((r * ψ) ^ n').ker).relIndex (H₀ ⊓ (r ^ (p * n')).ker)).Prime := by
        refine relIndex_ker_prime _ _ ((r * ψ) ^ n') p hp (fun g => ?_) (fun g hg => ?_) τ (hUH hτU) hτs
        · constructor
          · intro hg
            exact ⟨hle hg, hg.2⟩
          · rintro ⟨hg, hs⟩
            exact ⟨hg.1, hs⟩
        · have h1 : (r ^ (p * n')) g = 1 := hg.2
          rw [hval, h1]
      have hP' : P (H₀ ⊓ ((r * ψ) ^ n').ker) :=
        hstep _ _ u hGH hGH' hP hle hprime (fun x hx => hUH (hDc hx))
          ⟨τ, hτ, fun h => hτs h.2⟩
      obtain ⟨r', h1, h2, h3⟩ := ih n' hlt hn' (r * ψ) hr1 hP'
      refine ⟨r', h1, fun g hg => ?_, h3⟩
      rw [h2 g hg, MonoidHom.mul_apply, hψD g hg, mul_one]
  refine key n hn r hr ?_
  rw [hrn, MonoidHom.ker_one, inf_top_eq]
  exact hP
