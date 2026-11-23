import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclic
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInv
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.CliffTwo

def twistRep {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (ν : H →* ℂˣ) : Representation ℂ H V where
  toFun x := ((ν x : ℂˣ) : ℂ) • ρ x
  map_one' := by simp
  map_mul' x y := by rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

theorem twistRep_apply {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (ν : H →* ℂˣ) (x : H) : twistRep ρ ν x = ((ν x : ℂˣ) : ℂ) • ρ x := rfl

theorem isIrreducible_twistRep {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ H V} (h : ρ.IsIrreducible) (ν : H →* ℂˣ) :
    (twistRep ρ ν).IsIrreducible := by
  let f : Subrepresentation (twistRep ρ ν) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have := S.toSubmodule.smul_mem (((ν g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
        simpa [twistRep_apply, smul_smul] using this⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv =>
        S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact f.isSimpleOrder_iff.2 h

theorem isIrrChar_mul_char {H : Type} [Group H] {χ : H → ℂ} (hχ : IsIrrChar ℂ ℂ χ) (ν : H →* ℂˣ) :
    IsIrrChar ℂ ℂ (fun x => χ x * ((ν x : ℂˣ) : ℂ)) := by
  obtain ⟨n, ρ, hρ, hc⟩ := hχ
  refine ⟨n, twistRep ρ ν, isIrreducible_twistRep hρ ν, fun g => ?_⟩
  simp only [hc, Representation.character, twistRep_apply, map_smul, smul_eq_mul,
    Algebra.algebraMap_self, RingHom.id_apply]
  ring

end GlobalTheory.CliffTwo

open GlobalTheory.CliffTwo in

theorem GlobalTheory.Shin.coset_pair_eq_zero_or_twist :
    ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ),
    (Nat.card Γ).Prime → s ≠ 1 → ∀ χ χ' : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ → IsIrrChar ℂ ℂ χ' →
    ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0 ∨
      ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ ∀ x, χ x = χ' x * (η x : ℂ) := by
  intro G Γ _ _ _ _ φ s hp hs χ χ' hχ hχ'
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ (SemidirectProduct.equivProd (φ := φ)).symm
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero
  obtain ⟨η, hη1, -, hsum⟩ := GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s hgen _ hζ
  have hS := (hsum χ χ').2
  by_cases h0 : ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0
  · exact Or.inl h0
  right
  have hne : ∑ a ∈ Finset.range (Nat.card Γ), Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ)) ^ a *
      ∑ᶠ x, χ x * star (χ' x * (η x : ℂ) ^ a) ≠ 0 := by
    rw [← hS]; exact mul_ne_zero (by exact_mod_cast hp.ne_zero) h0
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hT : ∑ᶠ x, χ x * star (χ' x * (η x : ℂ) ^ a) ≠ 0 := right_ne_zero_of_mul ha
  have hpow : ∀ x, ((η ^ a) x : ℂ) = (η x : ℂ) ^ a := fun x => by simp
  have hψ : IsIrrChar ℂ ℂ (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) := isIrrChar_mul_char hχ' (η ^ a)
  refine ⟨η ^ a, fun g => by simp [hη1], fun x => ?_⟩
  by_contra hx
  have hne' : χ ≠ fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ) := fun e => hx (congrFun e x)
  have hpair : pair χ (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) = 0 := by
    first | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne (G ⋊[φ] Γ) χ _ hχ hψ hne' | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne χ _ hχ hψ hne' | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne hχ hψ hne'
  have hvirt : (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := by
    obtain ⟨n, ρ, -, hc⟩ := hψ
    exact AddSubgroup.subset_closure ⟨n, ρ, hc⟩
  have hstar : ∀ g, star ((fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) g) = (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) g⁻¹ := by
    first | exact GlobalTheory.CuspGL.star_virt_eq_inv (G ⋊[φ] Γ) _ hvirt | exact GlobalTheory.CuspGL.star_virt_eq_inv _ hvirt | exact GlobalTheory.CuspGL.star_virt_eq_inv hvirt
  apply hT
  have hcard : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have : ∑ᶠ x, χ x * star (χ' x * (η x : ℂ) ^ a) =
      ∑ᶠ x, χ x * (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) x⁻¹ := by
    congr 1; ext x; have hx := hstar x; simp only [hpow] at hx ⊢; rw [← hx]
  rw [this]
  unfold pair at hpair
  exact (mul_eq_zero.1 hpair).resolve_left (inv_ne_zero hcard)
