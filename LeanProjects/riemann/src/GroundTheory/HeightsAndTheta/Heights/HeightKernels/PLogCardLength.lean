import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLogCardLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

namespace logCardLength

open Module

variable (R : Type) [CommRing R]

def term (N : Type) [AddCommGroup N] [Module R N] (m : Ideal R) : ℝ :=
  ∑ᶠ (_ : m.IsMaximal), (locLen m N : ℝ) * Real.log (Nat.card (R ⧸ m))

def FinLoc (N : Type) [AddCommGroup N] [Module R N] : Prop :=
  ∀ (m : Ideal R) [m.IsPrime],
    Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N) ≠ ⊤

variable {R}

lemma term_eq (N : Type) [AddCommGroup N] [Module R N] (m : Ideal R) [hm : m.IsMaximal] :
    term R N m = ((Module.length (Localization.AtPrime m)
      (LocalizedModule m.primeCompl N)).toNat : ℝ) * Real.log (Nat.card (R ⧸ m)) := by
  classical
  rw [term, finsum_eq_if, if_pos hm, locLen, dif_pos hm.isPrime]

lemma term_of_not (N : Type) [AddCommGroup N] [Module R N] (m : Ideal R) (hm : ¬ m.IsMaximal) :
    term R N m = 0 := by
  classical
  rw [term, finsum_eq_if, if_neg hm]

lemma length_loc_add {N₀ N₁ N₂ : Type} [AddCommGroup N₀] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module R N₀] [Module R N₁] [Module R N₂] (f : N₀ →ₗ[R] N₁) (g : N₁ →ₗ[R] N₂)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g)
    (m : Ideal R) [m.IsPrime] :
    Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N₁) =
      Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N₀) +
        Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N₂) :=
  Module.length_eq_add_of_exact
    ((IsLocalizedModule.map m.primeCompl (LocalizedModule.mkLinearMap m.primeCompl N₀)
      (LocalizedModule.mkLinearMap m.primeCompl N₁) f).extendScalarsOfIsLocalization
        m.primeCompl (Localization.AtPrime m))
    ((IsLocalizedModule.map m.primeCompl (LocalizedModule.mkLinearMap m.primeCompl N₁)
      (LocalizedModule.mkLinearMap m.primeCompl N₂) g).extendScalarsOfIsLocalization
        m.primeCompl (Localization.AtPrime m))
    (IsLocalizedModule.map_injective _ _ _ _ hf) (IsLocalizedModule.map_surjective _ _ _ _ hg)
    (LocalizedModule.map_exact m.primeCompl f g H)

lemma length_loc_simple (M : Type) [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    (I : Ideal R) (hI : I.IsMaximal) (hkill : ∀ a ∈ I, ∀ x : M, a • x = 0)
    (m : Ideal R) [hm : m.IsPrime] :
    Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl M) =
      if m = I then 1 else 0 := by
  split_ifs with h
  · subst h
    have hsurj : Function.Surjective (LocalizedModule.mkLinearMap m.primeCompl M) := by
      intro y
      refine LocalizedModule.induction_on (fun x s => ?_) y
      obtain ⟨t, i, hi, hts⟩ := hI.exists_inv (Ideal.mem_primeCompl_iff.mp s.2)
      refine ⟨t • x, ?_⟩
      rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      have hx : ((s : R) * t) • x = x := by
        rw [show (s : R) * t = 1 - i by linear_combination hts, sub_smul, one_smul, hkill i hi x,
          sub_zero]
      simp only [one_smul, Submonoid.smul_def, smul_smul, hx]
    apply le_antisymm
    · calc Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl M)
          = Module.length (Localization.AtPrime m)
              (⊤ : Submodule (Localization.AtPrime m) (LocalizedModule m.primeCompl M)) :=
            Module.length_top.symm
        _ ≤ Module.length R
              ((⊤ : Submodule (Localization.AtPrime m) (LocalizedModule m.primeCompl M)).restrictScalars
                R) := Submodule.length_le_length_restrictScalars R ⊤
        _ = Module.length R (LocalizedModule m.primeCompl M) := by
            rw [Submodule.restrictScalars_top]; exact Module.length_top
        _ ≤ Module.length R M := Module.length_le_of_surjective _ hsurj
        _ = 1 := Module.length_eq_one R M
    · have : Nontrivial (LocalizedModule m.primeCompl M) := by
        rw [← not_subsingleton_iff_nontrivial, LocalizedModule.subsingleton_iff]
        push Not
        have := IsSimpleModule.nontrivial R M
        obtain ⟨x, hx⟩ := exists_ne (0 : M)
        refine ⟨x, fun r hr hrx => hx ?_⟩
        obtain ⟨t, i, hi, hts⟩ := hI.exists_inv (Ideal.mem_primeCompl_iff.mp hr)
        calc x = (t * r + i) • x := by rw [hts, one_smul]
          _ = 0 := by rw [add_smul, mul_smul, hrx, smul_zero, hkill i hi x, add_zero]
      exact Order.one_le_iff_pos.mpr Module.length_pos
  · rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
    have hle : ¬ I ≤ m := fun hle => h (hI.eq_of_le hm.ne_top hle).symm
    obtain ⟨a, haI, ham⟩ := SetLike.not_le_iff_exists.mp hle
    exact fun x => ⟨a, Ideal.mem_primeCompl_iff.mpr ham, hkill a haI x⟩

lemma term_simple (M : Type) [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    (I : Ideal R) (hI : I.IsMaximal) (hkill : ∀ a ∈ I, ∀ x : M, a • x = 0)
    (hcard : Nat.card M = Nat.card (R ⧸ I)) (m : Ideal R) :
    term R M m = if m = I then Real.log (Nat.card M) else 0 := by
  by_cases hm : m.IsMaximal
  · rw [term_eq, length_loc_simple M I hI hkill m]
    split_ifs with h
    · subst h; simp [hcard]
    · simp
  · rw [term_of_not M m hm, if_neg (fun (h : m = I) => hm (h ▸ hI))]

theorem main (n : ℕ) : ∀ (N : Type) [AddCommGroup N] [Module R N] [Finite N], Nat.card N = n →
    FinLoc R N ∧ (Function.support (term R N)).Finite ∧
      Real.log (Nat.card N) = ∑ᶠ m, term R N m := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N _ _ _ hn
  rcases subsingleton_or_nontrivial N with hN | hN
  · have h0 : ∀ (m : Ideal R) [m.IsPrime],
        Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N) = 0 :=
      fun m _ => Module.length_eq_zero
    have ht : ∀ m, term R N m = 0 := by
      intro m
      by_cases hm : m.IsMaximal
      · rw [term_eq, h0]; simp
      · exact term_of_not N m hm
    refine ⟨fun m _ => by rw [h0]; exact ENat.zero_ne_top,
      by rw [show term R N = 0 from funext ht, Function.support_zero]; exact Set.finite_empty, ?_⟩
    rw [Nat.card_of_subsingleton (0 : N)]
    simp [ht]
  · have := isArtinian_of_finite (R := R) (M := N)
    obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R N)
    rw [← isSimpleModule_iff_isAtom] at hS
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hS
    have hkill : ∀ a ∈ I, ∀ x : S, a • x = 0 := by
      intro a ha x
      apply e.injective
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e x)
      rw [map_smul, ← hr, map_zero, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact I.mul_mem_right r ha
    have hcS : Nat.card S = Nat.card (R ⧸ I) := Nat.card_congr e.toEquiv
    have : Finite (N ⧸ S) := Finite.of_surjective _ S.mkQ_surjective
    have hcard : Nat.card N = Nat.card S * Nat.card (N ⧸ S) := S.card_eq_card_quotient_mul_card
    have := IsSimpleModule.nontrivial R S
    have hS1 : 1 < Nat.card S := Finite.one_lt_card
    have hQpos : 0 < Nat.card (N ⧸ S) := Nat.card_pos
    have hlt : Nat.card (N ⧸ S) < n := by
      rw [← hn, hcard]; exact lt_mul_of_one_lt_left hQpos hS1
    obtain ⟨hQf, hQs, hQl⟩ := ih _ hlt (N ⧸ S) rfl
    have hadd : ∀ (m : Ideal R) [m.IsPrime],
        Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N) =
          Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl S) +
            Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl (N ⧸ S)) :=
      fun m _ => length_loc_add S.subtype S.mkQ S.injective_subtype S.mkQ_surjective
        (LinearMap.exact_subtype_mkQ S) m
    have hSt := term_simple S I hI hkill hcS
    have hterm : ∀ m, term R N m = term R S m + term R (N ⧸ S) m := by
      intro m
      by_cases hm : m.IsMaximal
      · have hQm := hQf m
        rw [term_eq, term_eq, term_eq, hadd, length_loc_simple S I hI hkill m] at *
        split_ifs <;> simp [ENat.toNat_add _ hQm]; ring
      · rw [term_of_not N m hm, term_of_not S m hm, term_of_not _ m hm, add_zero]
    have hSs : (Function.support (term R S)).Finite := by
      refine (Set.finite_singleton I).subset fun m hm => ?_
      by_contra h
      exact hm (by rw [hSt, if_neg (by simpa using h)])
    refine ⟨fun m _ => ?_, ?_, ?_⟩
    · rw [hadd, length_loc_simple S I hI hkill m]
      split_ifs <;> simpa using hQf m
    · exact (hSs.union hQs).subset (by
        rw [show term R N = fun m => term R S m + term R (N ⧸ S) m from funext hterm]
        exact Function.support_add _ _)
    · rw [show term R N = fun m => term R S m + term R (N ⧸ S) m from funext hterm,
        finsum_add_distrib hSs hQs, ← hQl,
        finsum_eq_single _ I (fun m hm => by rw [hSt, if_neg hm]), hSt, if_pos rfl, hcard,
        Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]

end logCardLength

open logCardLength in

theorem LogCardLength.proof : LogCardLength.Statement := by
  intro R _ N _ _ _
  exact (main (Nat.card N) N rfl).2.2

end

end GroundTheory.Heights₂.Heights
