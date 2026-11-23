import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.ImportsAlt
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGeneratesStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussSumValuationTeichmullerStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalCharacterIdealPowersStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualHopfOrderGaussSumStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraFurther
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem exists_addChar_ne_one (C F : Type) [Field C] [IsAlgClosed C] [CharZero C] [Field F]
    [Finite F] : ∃ ψ : AddChar F C, ψ ≠ 1 := by
  have hch : ringChar C ≠ ringChar F := by
    rw [ringChar.eq_zero]
    exact (CharP.char_ne_zero_of_finite F (ringChar F)).symm
  let P := AddChar.FiniteField.primitiveChar F C hch
  haveI : NeZero (P.n : ℕ) := ⟨P.n.ne_zero⟩
  haveI : Algebra.IsIntegral C (CyclotomicField P.n C) :=
    IsCyclotomicExtension.integral {(P.n : ℕ)} C _
  let j : CyclotomicField P.n C →ₐ[C] C := IsAlgClosed.lift
  let ψ : AddChar F C :=
    { toFun := fun a => j (P.char a)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by simp [AddChar.map_add_eq_mul] }
  refine ⟨ψ, fun h => ?_⟩
  refine P.prim one_ne_zero ?_
  ext a
  have h1 : j (P.char a) = 1 := by
    have := congrArg (fun χ : AddChar F C => χ a) h
    simpa [ψ] using this
  have h2 : P.char a = 1 := j.toRingHom.injective (by simpa using h1)
  simpa [AddChar.mulShift_apply] using h2

theorem exists_shift_equiv {C F : Type} [Field C] [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F C) (hψ : ψ ≠ 1) :
    ∃ e : F ≃ AddChar F C, (∀ h h', e (h + h') = e h * e h') ∧ ∀ h a, e h a = ψ (h * a) :=
  _root_.UpperTheory.Reformulated.B.AddCharacterCount.main ψ hψ

theorem rank_one_sum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∃ AD : HopfOrder (C := C) R F, FStable F AD.carrier ∧ (∀ cN cD, HasColen R v AA.carrier cN → HasColen R v AD.carrier cD → (cN * cD) ^ 2 = v (p : C) ^ (f * p ^ f)) ∧ ∀ τ : MulChar F R, IsFund p τ → ∀ c cD : R, xIdeal AA.carrier τ = Ideal.span {c} → xIdeal AD.carrier τ = Ideal.span {cD} → (v (algebraMap R C c) * v (algebraMap R C cD)) ^ (p - 1) = v (p : C) := by
  intro p _ C _ _ _ v R _ _ hv hvp F _ _ _ _ f hcard AA hFS
  obtain ⟨ψ, hψ⟩ := exists_addChar_ne_one C F
  obtain ⟨e, he, heψ⟩ := exists_shift_equiv ψ hψ
  obtain ⟨AD, hAD, -, hcol⟩ := h1 C R v hv F F e he rfl AA
  have hfun : (fun (h a : F) => e h a) = fun (h a : F) => ψ (h * a) := by
    funext h a; exact heψ h a
  rw [hfun] at hAD
  obtain ⟨hFD, hdual⟩ := GlobalTheory.T.dual_hopf_order_gauss_sum p C v R hv hvp F f hcard AA hFS ψ hψ AD hAD
  refine ⟨AD, hFD, ?_, ?_⟩
  · intro cN cD hN hD
    rw [hcol cN cD hN hD, hcard, Nat.cast_pow, map_pow, ← pow_mul]
  · intro τ hτ c cD hc hcD
    have hord := (GlobalTheory.T.teichmuller_character_order_generates p C v R hv hvp F f hcard τ hτ).1
    by_cases h2 : Fintype.card F = 2
    · have hpf : p ^ f = 2 := hcard.symm.trans h2
      obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 hpf
      have ht : τ = 1 := orderOf_eq_one_iff.1 (by rw [hord]; norm_num)
      have hN := (GlobalTheory.T.fundamental_character_ideal_powers 2 C v R hv hvp F 1 hcard AA hFS τ hτ (fun _ => c)
        (fun m => by rw [ht, one_pow, ← ht]; exact hc)).2.2
      have hD := (GlobalTheory.T.fundamental_character_ideal_powers 2 C v R hv hvp F 1 hcard AD hFD τ hτ (fun _ => cD)
        (fun m => by rw [ht, one_pow, ← ht]; exact hcD)).2.2
      have hI : Finset.Icc 1 (2 ^ 1 - 1) = ({1} : Finset ℕ) := by decide
      rw [hI, Finset.prod_singleton] at hN hD
      have key := hcol _ _ hN hD
      rw [h2] at key
      have := (pow_left_inj₀ zero_le zero_le two_ne_zero).1 key
      simpa using this
    · have hne : τ ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hord
        apply h2
        rw [hcard]
        have : 1 ≤ p ^ f := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
        omega
      rw [hdual τ hne c cD hc hcD]
      exact GlobalTheory.T.gauss_sum_valuation_teichmuller p C v R hv hvp F f hcard h2 τ hτ ψ hψ

end GlobalTheory.CompanionTheory.Ar.GR
