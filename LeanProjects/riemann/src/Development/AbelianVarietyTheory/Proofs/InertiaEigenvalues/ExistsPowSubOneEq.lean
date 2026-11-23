import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildEqOneOfCharpolyUnipotentModL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildInertiaKilledByAdditiveLocallyConstant
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.WildUnipotent

open Polynomial in

theorem exists_pow_sub_one_eq {O : Type} [CommRing O] {n l : ℕ} (hl : l.Prime) (u : Matrix (Fin n) (Fin n) O)
    (hu : u.charpoly = (X - 1) ^ n) (M : ℕ) :
    ∃ c : Matrix (Fin n) (Fin n) O, u ^ (l ^ (n + M)) - 1 = ((l : O) ^ (M + 1)) • c := by
  have h0 : (u - 1) ^ n = 0 := by
    have := Matrix.aeval_self_charpoly u
    rw [hu] at this
    simpa using this
  have h1 : (u - 1) ^ (l ^ n) = 0 := pow_eq_zero_of_le (Nat.lt_pow_self hl.one_lt).le h0
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hl (1 : O[X]) (X - 1) n
  have h2 : (l : O[X]) ∣ X ^ (l ^ n) - (1 + (X - 1) ^ (l ^ n)) := by
    rw [add_sub_cancel, one_pow] at hr
    rw [hr, add_sub_cancel_left, mul_assoc, mul_assoc]
    exact dvd_mul_right _ _
  obtain ⟨c, hc⟩ := dvd_sub_pow_of_dvd_sub h2 M
  refine ⟨aeval u c, ?_⟩
  have h3 := congrArg (aeval u) hc
  simp only [map_sub, map_pow, map_add, map_one, aeval_X, h1, add_zero, one_pow, map_mul, map_natCast] at h3
  rw [pow_add, pow_mul, h3, Algebra.smul_def, map_pow, map_natCast]

theorem eq_one_of_wild {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) {l : ℕ} (hl : l.Prime) (hA : ¬ A.valuation (l : Ω) < 1)
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (had : IsAdic (IsLocalRing.maximalIdeal O)) (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O)
    {n : ℕ} (r : G E Ω →* GL (Fin n) O)
    (hr : Continuous (fun g => ((r g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)))
    (σ : G E Ω) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1)
    (hc : ((r σ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O).charpoly = (Polynomial.X - 1) ^ n) : r σ = 1 := by
  have key : ∀ M : ℕ, ∀ a b, (((r σ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) - 1) a b ∈
      IsLocalRing.maximalIdeal O ^ M := by
    intro M
    let q := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ M)
    let H : Subgroup (G E Ω) := ((Matrix.GeneralLinearGroup.map q).comp r).ker
    have hH : ∀ g, g ∈ H ↔ ∀ a b, (((r g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) - 1) a b ∈
        IsLocalRing.maximalIdeal O ^ M := by
      intro g
      rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
      refine forall_congr' fun a => forall_congr' fun b => ?_
      rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
      have e : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ M) ((1 : Matrix (Fin n) (Fin n) O) a b) =
          (1 : Matrix (Fin n) (Fin n) (O ⧸ IsLocalRing.maximalIdeal O ^ M)) a b := by
        by_cases h : a = b <;> simp [Matrix.one_apply, h]
      rw [e]
      rfl
    have ho : IsOpen (H : Set (G E Ω)) := by
      have e : (H : Set (G E Ω)) = ⋂ a, ⋂ b,
          (fun g => (((r g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) - 1) a b) ⁻¹'
            ((IsLocalRing.maximalIdeal O ^ M : Ideal O) : Set O) := by
        ext g
        simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
        exact hH g
      rw [e]
      refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
      exact ((isAdic_iff.1 had).1 M).preimage ((hr.sub continuous_const).matrix_elem a b)
    refine (hH σ).1 (GlobalTheory.WildKill.mem_of_wild A H ho σ (l ^ (n + M)) ?_ hσ ?_)
    · have h1 : A.valuation (l : Ω) = 1 :=
        le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hA)
      rw [Nat.cast_pow, map_pow, h1, one_pow]
      exact lt_irrefl _
    · rw [hH]
      intro a b
      obtain ⟨c, hc'⟩ := exists_pow_sub_one_eq hl _ hc M
      rw [map_pow, Units.val_pow_eq_pow_val, hc', Matrix.smul_apply, smul_eq_mul, pow_succ, mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlO M)
  rw [Units.ext_iff, Units.val_one, ← sub_eq_zero]
  ext a b
  have h2 := Ideal.mem_iInf.2 fun M => key M a b
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top] at h2
  simpa using h2

theorem main : ∀ (D : D7) (i : D.nd.Loc) (n : ℕ) (r : GE D.nd →* GL (Fin n) (D.nd.O i)), Continuous (fun g => ((r g : GL (Fin n) (D.nd.O i)) : Matrix (Fin n) (Fin n) (D.nd.O i))) → ∀ v : HeightOneSpectrum (𝓞 D.host.E), v ∉ placesOver D.host.E (D.nd.l i) → ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 v), ((r σ : GL (Fin n) (D.nd.O i)) : Matrix (Fin n) (Fin n) (D.nd.O i)).charpoly = (Polynomial.X - 1) ^ n → r σ = 1 := by
  intro D i n r hr v hv σ hσ hc
  have := D.nd.trO i
  refine eq_one_of_wild (D.nd.plOm.1 v) (l := D.nd.l i) Fact.out ?_ (D.nd.O_adic i)
    (GlobalTheory.WildAdditive.not_isUnit_natCast (D.nd.l i) (D.nd.O i)) r hr σ hσ hc
  intro h
  apply hv
  have hA : IsPlaceOver (D.nd.plOm.1 v) v := D.nd.plOm.2 v
  show ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal
  rw [← hA]
  simpa using h

end GlobalTheory.WildUnipotent
