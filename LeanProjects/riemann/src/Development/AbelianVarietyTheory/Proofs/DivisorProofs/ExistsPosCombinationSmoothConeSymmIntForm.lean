import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.ConeInterior

section Help

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem exists_nat_comb {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCone bar φ γ)
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X) {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (h : toReal β = ∑ i, c i • toReal (γ i)) : ∃ n : Fin m → ℕ, β = ∑ i, n i • γ i := by
  classical
  obtain ⟨f, hf⟩ := hγ.basis.exists_dual
  have hz : ∀ i, c i = (f i ⟨β, hβ⟩ : ℤ) := fun i => by
    have h0 : ∑ o : Option (Fin m), (Option.elim o (-1) c) • toReal ((balForms bar X).subtype
        (Option.elim o (⟨β, hβ⟩ : balForms bar X) fun k => ⟨γ k, hγ.mem k⟩)) = 0 := by
      rw [Fintype.sum_option]
      simp only [Option.elim_none, Option.elim_some, Submodule.subtype_apply, h, neg_one_smul, neg_add_cancel]
    have := sum_mul_eq_zero_of_sum_toReal Subtype.val_injective (f i) h0
    rw [Fintype.sum_option] at this
    simp only [Option.elim_none, Option.elim_some, hf] at this
    simp at this
    linarith
  have hn : ∀ i, ∃ n : ℕ, c i = n := fun i => by
    have h1 : (0 : ℤ) ≤ f i ⟨β, hβ⟩ := by exact_mod_cast (hz i ▸ hc i : (0 : ℝ) ≤ (f i ⟨β, hβ⟩ : ℤ))
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h1
    exact ⟨n, by rw [hz i, hn, Int.cast_natCast]⟩
  choose n hn using hn
  refine ⟨n, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ h a b
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, hn, nsmul_eq_mul] at this ⊢
  exact_mod_cast this

theorem exists_pos_comb (hP : IsPolFanOn bar φ X) {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : toReal β ∈ psdCone bar X) :
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (cf : Fin m → ℕ),
      IsCone bar φ γ ∧ (∀ j, 0 < cf j) ∧ β = ∑ j, cf j • γ j := by
  classical
  obtain ⟨m, γ, c, hγ, hc, h⟩ := hP.cover _ hp
  obtain ⟨n, hn⟩ := exists_nat_comb hγ hβ hc h
  let S : Finset (Fin m) := Finset.univ.filter fun i => 0 < n i
  let s : Fin S.card ↪ Fin m := (S.orderEmbOfFin rfl).toEmbedding
  have hs : Finset.univ.map s = S := Finset.map_orderEmbOfFin_univ S rfl
  refine ⟨S.card, fun i => γ (s i), fun i => n (s i), hP.face _ _ γ s hγ, fun j => ?_, ?_⟩
  · exact (Finset.mem_filter.1 (S.orderEmbOfFin_mem rfl j)).2
  · rw [hn, ← Finset.sum_map Finset.univ s fun i => n i • γ i, hs]
    refine (Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_).symm
    have : n i = 0 := by simpa [S] using hi
    rw [this, zero_smul]

end Help

theorem exists_pos_comb_int : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ r : ℕ, r ≤ g → ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → toReal b ∈ psdCone (id : ℤ → ℤ) (Fin r → ℤ) → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) (cf : Fin m → ℕ), IsCone id φ γ ∧ (∀ j, 0 < cf j) ∧ b = ∑ j, cf j • γ j := by
  intro g φ hφ r hr b hb hp
  exact exists_pos_comb (hφ (Fin r → ℤ) (by simpa using hr)) (mem_balForms_int.2 hb) hp

end GlobalTheory.ConeInterior
