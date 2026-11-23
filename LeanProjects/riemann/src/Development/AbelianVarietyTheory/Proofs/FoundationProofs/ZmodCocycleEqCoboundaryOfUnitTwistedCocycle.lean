import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExponentOfGaloisElementIsKummerCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90LocallyConstantCocycleStatement
open GlobalTheory.NeedB Polynomial

noncomputable section

open IntermediateField

namespace GlobalTheory.Hilbert90CupCoboundary

theorem isLocallyConstant_eval {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (τ : Ω) : IsLocallyConstant (fun g : Ω ≃ₐ[K] Ω => g τ) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  haveI : FiniteDimensional K K⟮τ⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral τ)
  have hopen : IsOpen ((K⟮τ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  refine ⟨(fun g' => g⁻¹ * g') ⁻¹' ((K⟮τ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)),
    hopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact Subgroup.one_mem _
  · intro g' hg'
    have hfτ : (g⁻¹ * g') τ = τ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg' τ
        (IntermediateField.mem_adjoin_simple_self K τ)
    have e : g' = g * (g⁻¹ * g') := by group
    show g' τ = g τ
    rw [e, AlgEquiv.mul_apply, hfτ]

theorem zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (c : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω) → ZMod N) (v : (Ω ≃ₐ[K] Ω) → Ωˣ), IsLocallyConstant v →
  (∀ g h, (v g : Ω) * g (v h) = ζ ^ (c g h).val * v (g * h)) →
  ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧ ∀ g h, c g h = η h - η (g * h) + η g := by
  intro K Ω _ _ _ _ _ N ζ hN0 hζ hfix c v hv hcoc
  classical
  haveI : NeZero N := ⟨by omega⟩
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let u : (Ω ≃ₐ[K] Ω) → Ωˣ := fun g => v g ^ N
  have hu_lc : IsLocallyConstant u := hv.comp (fun x : Ωˣ => x ^ N)
  have hu_coc : ∀ g h, ((u (g * h) : Ωˣ) : Ω) = u g * g (u h) := by
    intro g h
    simp only [u, Units.val_pow_eq_pow_val, map_pow]
    rw [← mul_pow, hcoc g h, mul_pow, ← pow_mul, mul_comm (c g h).val N, pow_mul, hζ.pow_eq_one,
      one_pow, one_mul]
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_eq_div_of_locallyConstant_cocycle K Ω u hu_lc hu_coc
  obtain ⟨τ, hτ⟩ := IsAlgClosed.exists_pow_nat_eq (t : Ω) hN0
  have ht0 : (t : Ω) ≠ 0 := t.ne_zero
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0.ne'] at hτ
    exact ht0 hτ.symm
  have hgτ0 : ∀ g : Ω ≃ₐ[K] Ω, g τ ≠ 0 := fun g => (map_ne_zero g).2 hτ0
  let w : (Ω ≃ₐ[K] Ω) → Ω := fun g => (v g : Ω) * τ / g τ
  have hw_lc : IsLocallyConstant w :=
    (hv.comp (fun x : Ωˣ => (x : Ω))).comp₂ (isLocallyConstant_eval (K := K) τ) (fun a b => a * τ / b)
  have hw_pow : ∀ g, w g ^ N = 1 := by
    intro g
    have h1 : (v g : Ω) ^ N = g t / t := by rw [← Units.val_pow_eq_pow_val]; exact ht g
    have h2 : (g τ) ^ N = g t := by rw [← map_pow, hτ]
    have h3 : g (t : Ω) ≠ 0 := (map_ne_zero g).2 ht0
    simp only [w]
    rw [div_pow, mul_pow, h1, h2, hτ]
    field_simp
  have hw_coc : ∀ g h, w g * g (w h) = ζ ^ (c g h).val * w (g * h) := by
    intro g h
    have hghτ : g (h τ) ≠ 0 := (map_ne_zero g).2 (hgτ0 h)
    have hg := hgτ0 g
    have e1 : w g * g (w h) = ((v g : Ω) * g (v h)) * τ / g (h τ) := by
      simp only [w, map_div₀, map_mul]
      field_simp
    rw [e1, hcoc g h]
    simp only [w, AlgEquiv.mul_apply]
    ring
  let E : Ω → ZMod N := fun x => if hx : ∃ i : ZMod N, ζ ^ i.val = x then hx.choose else 0
  let η : (Ω ≃ₐ[K] Ω) → ZMod N := fun g => E (w g)
  have hη : ∀ g, ζ ^ (η g).val = w g := by
    intro g
    obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one (hw_pow g)
    have hex : ∃ j : ZMod N, ζ ^ j.val = w g := ⟨(i : ZMod N), by rw [ZMod.val_cast_of_lt hi, hi']⟩
    simp only [η, E, dif_pos hex]
    exact hex.choose_spec
  refine ⟨η, hw_lc.comp E, ?_⟩
  intro g h
  have key : ζ ^ (η g + η h).val = ζ ^ (c g h + η (g * h)).val := by
    rw [KumLemma.pow_val_add hζ, KumLemma.pow_val_add hζ, hη g, hη h, hη (g * h)]
    have : g (w h) = w h := by rw [← hη h, map_pow, hfix]
    rw [← hw_coc, this]
  have hinj : η g + η h = c g h + η (g * h) :=
    ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) key)
  linear_combination -hinj

end GlobalTheory.Hilbert90CupCoboundary
