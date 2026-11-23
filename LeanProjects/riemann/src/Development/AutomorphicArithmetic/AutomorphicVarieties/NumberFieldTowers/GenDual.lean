import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.nakayama
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLen
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CokerDual

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem span_of_length_le {A : Type} [CommRing A] (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module A V], Module.length A V ≤ n →
      ∃ s : Fin n → V, Submodule.span A (Set.range s) = ⊤ := by
  induction n with
  | zero =>
    intro V _ _ h
    have h0 : Module.length A V = 0 := by simpa using h
    have : Subsingleton V := Module.length_eq_zero_iff.1 h0
    exact ⟨fun _ => 0, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro V _ _ h
    rcases subsingleton_or_nontrivial V with hV | hV
    · exact ⟨fun _ => 0, Subsingleton.elim _ _⟩
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    set P : Submodule A V := Submodule.span A {v} with hP
    have hadd : Module.length A V = Module.length A P + Module.length A (V ⧸ P) :=
      Module.length_eq_add_of_exact P.subtype P.mkQ P.injective_subtype P.mkQ_surjective
        (LinearMap.exact_subtype_mkQ P)
    have hP1 : 1 ≤ Module.length A P := by
      rw [Order.one_le_iff_ne_zero, Ne, Module.length_eq_zero_iff]
      intro hs
      exact hv (congrArg Subtype.val (Subsingleton.elim
        (⟨v, Submodule.mem_span_singleton_self v⟩ : P) 0))
    have hq : Module.length A (V ⧸ P) ≤ n := by
      have h2 : Module.length A (V ⧸ P) + 1 ≤ (n : ℕ∞) + 1 := by
        calc Module.length A (V ⧸ P) + 1 ≤ Module.length A (V ⧸ P) + Module.length A P := by gcongr
          _ = Module.length A V := by rw [hadd, add_comm]
          _ ≤ (n : ℕ∞) + 1 := by simpa using h
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 h2
    obtain ⟨t, ht⟩ := ih (V ⧸ P) hq
    choose s hs using fun i => P.mkQ_surjective (t i)
    refine ⟨Fin.cons v s, ?_⟩
    rw [Fin.range_cons, Submodule.span_insert, ← hP, ← Submodule.map_mkQ_eq_top, Submodule.map_span,
      ← Set.range_comp, ← ht]
    congr 2
    exact funext hs

theorem UpperTheory.V.Tower.genDual :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (R : ℕ), (∀ m : M, ∃ r : ℕ, (l : ℤ_[l]) ^ r • m = 0) →
        (GenLE ℤ_[l] (M →ₗ[ℤ_[l]] QZ l) R ↔ Module.length ℤ_[l] (Submodule.torsionBy ℤ_[l] M (l : ℤ_[l])) ≤ R) := by
  intro l _ M _ _ R hM
  have hc := UpperTheory.V.Tower.cokerDual l M ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] M))
    ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] (M →ₗ[ℤ_[l]] QZ l))) (fun x φ => by simp)
  have hk : LinearMap.ker ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] M))
      = Submodule.torsionBy ℤ_[l] M (l : ℤ_[l]) := by
    ext m; simp
  rw [hk] at hc
  rw [← hc]
  constructor
  · intro h
    exact UpperTheory.V.PropA.cokL l _ R h
  · intro h
    set I : Ideal ℤ_[l] := Ideal.span {(l : ℤ_[l])} with hI
    haveI : IsPrecomplete I ℤ_[l] := by
      rw [hI, ← PadicInt.maximalIdeal_eq_span_p]
      infer_instance
    haveI : IsHausdorff I (M →ₗ[ℤ_[l]] QZ l) := by
      refine ⟨fun x hx => LinearMap.ext fun m => ?_⟩
      obtain ⟨r, hr⟩ := hM m
      have h1 := hx r
      rw [SModEq.zero, hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
        Submodule.mem_smul_pointwise_iff_exists] at h1
      obtain ⟨y, -, rfl⟩ := h1
      rw [LinearMap.smul_apply, ← map_smul, hr, map_zero, LinearMap.zero_apply]
    set N : Submodule ℤ_[l] (M →ₗ[ℤ_[l]] QZ l) :=
      LinearMap.range ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] (M →ₗ[ℤ_[l]] QZ l))) with hN
    have hNI : N = I • (⊤ : Submodule ℤ_[l] (M →ₗ[ℤ_[l]] QZ l)) := by
      ext x
      rw [hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists, hN]
      simp
    obtain ⟨t, ht⟩ := span_of_length_le R ((M →ₗ[ℤ_[l]] QZ l) ⧸ N) h
    choose s hs using fun i => N.mkQ_surjective (t i)
    have h2 : Submodule.span ℤ_[l] (Set.range s) = ⊤ := by
      refine (UpperTheory.V.abelian₂.nakayama ℤ_[l] I _).1 R s ?_
      rw [← hNI, sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp, ← ht]
      congr 2
      exact funext hs
    refine ⟨Fintype.linearCombination ℤ_[l] s, ?_⟩
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, h2]
