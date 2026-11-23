import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ValCount
import Development.AutomorphicArithmetic.DivisorFrames.ExistsComplexExtensionCountable
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
open IsLocalRing NumberField IsDedekindDomain GlobalTheory.ValCount
open scoped Classical

private theorem UpperTheory.isAlgebraic_of_finite_algHoms (K L : Type) [Field K] [Field L] [Algebra K L] [Algebra K ℂ]
    [Finite (L →ₐ[K] ℂ)] (q : L →ₐ[K] ℂ) : Algebra.IsAlgebraic K L := by
  refine ⟨fun x => ?_⟩
  by_contra hx
  have hx' : Transcendental K (q x) := fun h =>
    hx ((isAlgebraic_algHom_iff q q.toRingHom.injective).1 h)
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_algEquiv_apply_eq_add_one hx'
  have hm : ∀ m : ℕ, (σ ^ m) (q x) = q x + m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_add, hσ, map_natCast]
      push_cast
      ring
  let f : ℕ → (L →ₐ[K] ℂ) := fun m => (σ ^ m : ℂ ≃ₐ[K] ℂ).toAlgHom.comp q
  have hf : Function.Injective f := by
    intro a b hab
    have h : (σ ^ a) (q x) = (σ ^ b) (q x) := DFunLike.congr_fun hab x
    rw [hm, hm] at h
    exact_mod_cast add_left_cancel h
  haveI : Finite ℕ := Finite.of_injective f hf
  exact not_finite ℕ

private theorem UpperTheory.finite_of_algebraic_finite_algHoms (K L : Type) [Field K] [Field L] [Countable L] [Algebra K L]
    [Algebra K ℂ] [Finite (L →ₐ[K] ℂ)] [Algebra.IsAlgebraic K L] : Module.Finite K L := by
  haveI : CharZero K := RingHom.charZero (algebraMap K ℂ)
  have hr : Module.rank K L ≤ (Nat.card (L →ₐ[K] ℂ) : ℕ) := by
    refine rank_le fun s hs => ?_
    let E : IntermediateField K L := IntermediateField.adjoin K (s : Set L)
    haveI : FiniteDimensional K E :=
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
    let v : s → E := fun i => ⟨i, IntermediateField.subset_adjoin K _ i.2⟩
    have hv : LinearIndependent K v :=
      LinearIndependent.of_comp E.val.toLinearMap hs
    have h1 : s.card ≤ Module.finrank K E := by
      simpa using hv.fintype_card_le_finrank
    have h2 : Nat.card (E →ₐ[K] ℂ) = Module.finrank K E := AlgHom.natCard_of_splits K E ℂ
      (fun x => IsAlgClosed.splits _)
    have h3 : Function.Surjective (fun q : L →ₐ[K] ℂ => q.comp E.val) := by
      intro g
      obtain ⟨q, hq⟩ := UpperTheory.exists_complex_extension_countable E L E.val.toRingHom g.toRingHom
      have hq' : ∀ e : E, q e = g e := fun e => DFunLike.congr_fun hq e
      refine ⟨{ q with commutes' := fun k => ?_ }, ?_⟩
      · have := hq' (algebraMap K E k)
        rw [g.commutes] at this
        exact this
      · ext e
        exact hq' e
    exact h1.trans (h2 ▸ Nat.card_le_card_of_surjective _ h3)
  exact Module.rank_lt_aleph0_iff.1 (hr.trans_lt (Cardinal.natCast_lt_aleph0))

theorem UpperTheory.finite_of_finite_extensions :
    ∀ (K L : Type) [Field K] [Field L] [Countable L] (φ : K →+* L) (ι : K →+* ℂ), {q : L →+* ℂ | q.comp φ = ι}.Finite → φ.Finite := by
  intro K L _ _ _ φ ι h
  letI : Algebra K L := φ.toAlgebra
  letI : Algebra K ℂ := ι.toAlgebra
  haveI : Finite {q : L →+* ℂ | q.comp φ = ι} := h
  haveI : Finite (L →ₐ[K] ℂ) := by
    refine Finite.of_injective
      (fun j : L →ₐ[K] ℂ => (⟨j.toRingHom, j.comp_algebraMap⟩ : {q : L →+* ℂ | q.comp φ = ι})) ?_
    intro a b hab
    ext x
    exact DFunLike.congr_fun (congrArg Subtype.val hab) x
  obtain ⟨q, hq⟩ := UpperTheory.exists_complex_extension_countable K L φ ι
  haveI := UpperTheory.isAlgebraic_of_finite_algHoms K L { q with commutes' := fun k => DFunLike.congr_fun hq k }
  exact UpperTheory.finite_of_algebraic_finite_algHoms K L
