import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInv
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem trace_fin_eq_sum_diag (m : ℕ) (A : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    LinearMap.trace ℂ (Fin m → ℂ) A = ∑ i, A (Pi.single i 1) i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin m)), LinearMap.toMatrix_eq_toMatrix',
    Matrix.trace]
  simp [LinearMap.toMatrix'_apply]

variable {G : Type} [Group G] [Fintype G]

theorem sum_char_inv_mul_char_eq_zero_iff {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ G V) (ρ : Representation ℂ G W) :
    ∑ g, σ.character g⁻¹ * ρ.character g = 0 ↔ (Representation.linHom σ ρ).invariants = ⊥ := by
  have hpos : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hpos
  have hfr := Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom σ ρ)
  simp only [Representation.char_linHom] at hfr
  constructor
  · intro h
    rw [h, mul_zero] at hfr
    apply Submodule.finrank_eq_zero.mp
    exact_mod_cast hfr.symm
  · intro hb
    rw [hb, finrank_bot, Nat.cast_zero] at hfr
    exact (mul_eq_zero.mp hfr).resolve_left (inv_ne_zero hpos)

theorem comm_of_mem_invariants {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G V) (ρ : Representation ℂ G W) {p : V →ₗ[ℂ] W}
    (hp : p ∈ (Representation.linHom σ ρ).invariants) (g : G) (x : V) : p (σ g x) = ρ g (p x) := by
  have h := congrArg (fun F : V →ₗ[ℂ] W => F (σ g x)) (hp g)
  simp only [Representation.linHom_apply, LinearMap.comp_apply] at h
  rw [← h, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem invariants_bot_of_quot {U V W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G U) (ρ' : Representation ℂ G V)
    (ρ : Representation ℂ G W) (hirr : ρ'.IsIrreducible) {p : U →ₗ[ℂ] V}
    (hp : p ∈ (Representation.linHom σ ρ').invariants) (hp0 : p ≠ 0)
    (hb : (Representation.linHom σ ρ).invariants = ⊥) :
    (Representation.linHom ρ' ρ).invariants = ⊥ := by

  let S : Subrepresentation ρ' :=
    { toSubmodule := LinearMap.range p
      apply_mem_toSubmodule := by
        rintro g _ ⟨x, rfl⟩
        exact ⟨σ g x, comm_of_mem_invariants σ ρ' hp g x⟩ }
  have hrange : ∀ y : V, y ∈ LinearMap.range p := by
    rcases hirr.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hp0
      ext x
      have hx : p x ∈ S.toSubmodule := ⟨x, rfl⟩
      have hb0 : (⊥ : Subrepresentation ρ').toSubmodule = ⊥ := rfl
      rw [h, hb0] at hx
      exact (Submodule.mem_bot ℂ).mp hx
    · intro y
      have ht : (⊤ : Subrepresentation ρ').toSubmodule = ⊤ := rfl
      have : y ∈ (⊤ : Subrepresentation ρ').toSubmodule := by rw [ht]; exact Submodule.mem_top
      rw [← h] at this
      exact this
  rw [eq_bot_iff]
  intro q hq
  rw [Submodule.mem_bot]
  have hqp : q ∘ₗ p ∈ (Representation.linHom σ ρ).invariants := by
    intro g
    ext x
    simp only [Representation.linHom_apply, LinearMap.comp_apply]
    rw [← comm_of_mem_invariants ρ' ρ hq, ← comm_of_mem_invariants σ ρ' hp, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hb, Submodule.mem_bot] at hqp
  ext y
  obtain ⟨x, rfl⟩ := hrange y
  exact LinearMap.congr_fun hqp x

theorem sum_trace_smul_eq_zero {m : ℕ} (ρ₀ : Representation ℂ G (Fin m → ℂ)) {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (hbot : (Representation.linHom ρ₀ ρ).invariants = ⊥)
    (B : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    ∑ g : G, LinearMap.trace ℂ (Fin m → ℂ) (B ∘ₗ ρ₀ g⁻¹) • ρ g = 0 := by
  have hsum : ∀ f : (Fin m → ℂ) →ₗ[ℂ] V, ∑ g : G, Representation.linHom ρ₀ ρ g f = 0 := by
    intro f
    have hm : ∑ g : G, Representation.linHom ρ₀ ρ g f ∈ (Representation.linHom ρ₀ ρ).invariants := by
      intro h
      rw [map_sum]
      simp only [← Module.End.mul_apply, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)
    rw [hbot] at hm
    exact (Submodule.mem_bot ℂ).mp hm
  ext v
  have key : ∀ i : Fin m, ∑ g : G, (B (ρ₀ g⁻¹ (Pi.single i 1))) i • ρ g v = 0 := by
    intro i
    have := congrArg (fun F : (Fin m → ℂ) →ₗ[ℂ] V => F (Pi.single i 1))
      (hsum (((LinearMap.proj i : (Fin m → ℂ) →ₗ[ℂ] ℂ) ∘ₗ B).smulRight v))
    simpa [Representation.linHom_apply, LinearMap.sum_apply] using this
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply]
  simp only [trace_fin_eq_sum_diag, Finset.sum_smul, LinearMap.comp_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero (fun i _ => key i)

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem kills_twist_of_pair_ne_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ]
    (φ : Γ →* MulAut G) (s : Γ), ∀ (χ : G ⋊[φ] Γ → ℂ) (Y : G → ℂ), IsChar ℂ ℂ χ →
    IsIrrChar ℂ ℂ (fun g => χ (inl g)) → IsChar ℂ ℂ Y → ∑ᶠ g, χ (inl g) * star (Y g) ≠ 0 →
    Kills (fun δ => χ (inl δ * inr s)) Y := by
  intro G Γ _ _ _ _ φ s χ Y hχ hirr hY hne V _ _ _ ρ h
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Finite (G ⋊[φ] Γ) :=
    Finite.of_injective (fun x : G ⋊[φ] Γ => (x.left, x.right))
      (fun x y hxy => SemidirectProduct.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  obtain ⟨m, ρh, hρh⟩ := hχ
  obtain ⟨k, ρ', hρ'irr, hρ'⟩ := hirr
  obtain ⟨n, σ, hσ⟩ := hY
  have hχc : ∀ x, χ x = ρh.character x := fun x => by simpa using hρh x
  have hYc : ∀ g, Y g = σ.character g := fun g => by simpa using hσ g
  have h0c : ∀ g, χ (inl g) = ρ'.character g := fun g => by simpa using hρ' g
  have hst : ∀ g, star (Y g) = σ.character g⁻¹ := fun g => by
    rw [star_virt_eq_inv G Y (AddSubgroup.subset_closure ⟨n, σ, hσ⟩) g, hYc]
  rw [finsum_eq_sum_of_fintype] at h hne

  have hb : (Representation.linHom σ ρ).invariants = ⊥ := by
    rw [← sum_char_inv_mul_char_eq_zero_iff]
    simp only [hst] at h
    exact h

  have hne' : (Representation.linHom σ ρ').invariants ≠ ⊥ := by
    rw [Ne, ← sum_char_inv_mul_char_eq_zero_iff]
    intro h'
    apply hne
    rw [← h']
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hst, h0c, mul_comm]
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
  have hb' := invariants_bot_of_quot σ ρ' ρ hρ'irr hp hp0 hb

  let ρ₀ : Representation ℂ G (Fin m → ℂ) := ρh.comp (inl : G →* G ⋊[φ] Γ)
  have hρ₀ : ∀ g, ρ₀.character g = ρ'.character g := fun g => by
    rw [← h0c, hχc]; rfl
  have hb₀ : (Representation.linHom ρ₀ ρ).invariants = ⊥ := by
    rw [← sum_char_inv_mul_char_eq_zero_iff]
    have := (sum_char_inv_mul_char_eq_zero_iff ρ' ρ).mpr hb'
    simpa only [hρ₀] using this
  have hstf : ∀ g, star (χ (inl g * inr s)) =
      LinearMap.trace ℂ (Fin m → ℂ) (ρh (inr s⁻¹) ∘ₗ ρ₀ g⁻¹) := fun g => by
    rw [star_virt_eq_inv (G ⋊[φ] Γ) χ (AddSubgroup.subset_closure ⟨m, ρh, hρh⟩), hχc, mul_inv_rev,
      ← map_inv, ← map_inv]
    simp only [Representation.character, map_mul]
    rfl
  rw [finsum_eq_sum_of_fintype]
  simp only [hstf]
  exact sum_trace_smul_eq_zero ρ₀ ρ hb₀ _

end GlobalTheory.Shin
