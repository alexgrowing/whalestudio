import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

open IsLocalRing in
private theorem complete_of_finite (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [IsLocalRing R'] : IsAdicComplete (maximalIdeal R') R' := by
  haveI hN : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  have hcomap : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal R'))
  have hle : (maximalIdeal R).map (algebraMap R R') ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨h1, h2⟩ := hP
    have h3 : P.comap (algebraMap R R') = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ h2.ne_top)
        (Ideal.map_le_iff_le_comap.1 h1)).symm
    have h4 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P (h3 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h4).ge
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have h0 : IsAdicComplete (maximalIdeal R) R' := GlobalTheory.isAdicComplete_of_finite _ R'
  have hP : IsPrecomplete (maximalIdeal R') R' :=
    prec_cofinal hle he (IsPrecomplete.map_algebraMap_iff.2 h0.toIsPrecomplete)
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := hP }

theorem UpperTheory.V.AlgebraTools.local_factor :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (n : Ideal A) [n.IsMaximal],
      Function.Surjective (algebraMap A (Localization.AtPrime n)) ∧ Module.Finite R (Localization.AtPrime n) ∧
      IsLocalHom (algebraMap R (Localization.AtPrime n)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (Localization.AtPrime n)) (Localization.AtPrime n) ∧
      (Module.Free R A → Module.Free R (Localization.AtPrime n)) ∧
      (∃ e : A, IsIdempotentElem e ∧ (∀ n' : Ideal A, n'.IsMaximal → (e ∉ n' ↔ n' = n)) ∧
        RingHom.ker (algebraMap A (Localization.AtPrime n)) = Ideal.span {1 - e}) ∧
      ∀ (C : Type) [CommRing C] [IsLocalRing C] (f : A →+* C), (IsLocalRing.maximalIdeal C).comap f = n →
        ∃ g : Localization.AtPrime n →+* C, g.comp (algebraMap A _) = f := by
  intro R _ _ _ _ A _ _ _ n hn
  letI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_henselianRing R
  have hfin : Module.Finite R (Localization.AtPrime n) := GlobalTheory.finite_localization_of_henselian R n
  refine ⟨GlobalTheory.surjective_algebraMap_localization_of_henselian R n, hfin, ⟨fun a ha => ?_⟩,
    complete_of_finite R _, fun hF => ?_, ?_, fun C _ _ f hf => ?_⟩
  · by_contra h
    have h1 : a ∈ IsLocalRing.maximalIdeal R := h
    rw [← GlobalTheory.comap_eq_maximalIdeal_of_finite (IsLocalRing.maximalIdeal (Localization.AtPrime n)),
      Ideal.mem_comap] at h1
    exact h1 ha
  · haveI : Module.Flat A (Localization.AtPrime n) := IsLocalization.flat _ n.primeCompl
    haveI : Module.Flat R (Localization.AtPrime n) := Module.Flat.trans R A _
    exact Module.free_of_flat_of_isLocalRing
  · obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian R n
    refine ⟨e, he, H, le_antisymm (fun x hx => ?_) ?_⟩
    · obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff n.primeCompl _ x).1 hx
      have heq : e ∉ n := (H n hn).2 rfl
      have hu : IsUnit (e * s + (1 - e)) := by
        by_contra h
        obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits h
        by_cases hen : e ∈ m
        · rw [Submodule.add_mem_iff_right _ (Ideal.mul_mem_right _ _ hen),
            GlobalTheory.one_sub_mem_iff_notMem_of_isIdempotentElem he] at hmem
          exact hmem hen
        · rw [Submodule.add_mem_iff_left _
              ((GlobalTheory.one_sub_mem_iff_notMem_of_isIdempotentElem he m).2 hen),
            (H m hm).1 hen] at hmem
          exact (hn.isPrime.mem_or_mem hmem).elim heq s.2
      obtain ⟨v, hv⟩ := hu.exists_left_inv
      refine Ideal.mem_span_singleton'.2 ⟨v * x, ?_⟩
      linear_combination x * hv - v * e * hs
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
      exact ((IsIdempotentElem.iff_eq_one_of_isUnit (IsLocalization.map_units _
        (⟨e, (H n hn).2 rfl⟩ : n.primeCompl))).1 (he.map _)).symm
  · have hu : ∀ y : n.primeCompl, IsUnit (f y) := fun y => by
      by_contra h
      have h1 : (y : A) ∈ (IsLocalRing.maximalIdeal C).comap f := h
      rw [hf] at h1
      exact y.2 h1
    exact ⟨IsLocalization.lift hu, IsLocalization.lift_comp hu⟩
