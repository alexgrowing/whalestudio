import Formalism.SubspaceCounting.StatementB
import Formalism.SubspaceCounting.SubspaceCountingProofs.QVandermonde
import Formalism.SubspaceCounting.SubspaceCountingProofs.SubspaceCount

noncomputable section

open scoped BigOperators

namespace Formalism.G0

namespace TypeIIUpP

def qint (q n : ℕ) : ℕ := ∑ i ∈ Finset.range n, q ^ i

def qfact (q n : ℕ) : ℕ := ∏ i ∈ Finset.range n, qint q (i + 1)

theorem qint_succ_pos (q n : ℕ) : 0 < qint q (n + 1) := by
  unfold qint
  rw [Finset.sum_range_succ', pow_zero]
  omega

theorem qfact_pos (q n : ℕ) : 0 < qfact q n := by
  unfold qfact
  exact Finset.prod_pos fun i _ => qint_succ_pos q i

theorem qfact_succ (q n : ℕ) : qfact q (n + 1) = qfact q n * qint q (n + 1) := by
  unfold qfact
  rw [Finset.prod_range_succ]

theorem qint_add (q a b : ℕ) : qint q (a + b) = qint q a + q ^ a * qint q b := by
  unfold qint
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]

theorem gb_fact (q : ℕ) : ∀ n k : ℕ, k ≤ n →
    gaussBinom q n k * qfact q k * qfact q (n - k) = qfact q n
  | 0, 0, _ => by simp [gaussBinom, qfact]
  | n + 1, 0, _ => by simp [QVandermondeP.gb_zero_right, qfact]
  | 0, k + 1, h => absurd h (by omega)
  | n + 1, k + 1, h => by
    rw [QVandermondeP.gb_succ_succ]
    have e1 : n + 1 - (k + 1) = n - k := by omega
    rw [e1, qfact_succ q k, qfact_succ q n]
    have h1 := gb_fact q n k (by omega)
    rcases Nat.lt_or_ge k n with hk | hk
    · have h2 := gb_fact q n (k + 1) (by omega)
      have e2 : n - k = (n - (k + 1)) + 1 := by omega
      have e3 : n + 1 = (k + 1) + (n - k) := by omega
      have key : qint q (n + 1) = qint q (k + 1) + q ^ (k + 1) * qint q (n - k) := by
        rw [e3, qint_add]
      rw [key]
      have hq : qfact q (n - k) = qfact q (n - (k + 1)) * qint q (n - k) := by
        conv_lhs => rw [e2]
        rw [qfact_succ]
        rw [← e2]
      calc (gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1)) * (qfact q k * qint q (k + 1)) *
            qfact q (n - k)
          = (gaussBinom q n k * qfact q k * qfact q (n - k)) * qint q (k + 1)
            + q ^ (k + 1) * (gaussBinom q n (k + 1) * (qfact q k * qint q (k + 1)) *
              qfact q (n - (k + 1))) * qint q (n - k) := by rw [hq]; ring
        _ = qfact q n * (qint q (k + 1) + q ^ (k + 1) * qint q (n - k)) := by
          rw [h1, ← qfact_succ, h2]; ring
    · have hkn : k = n := by omega
      subst hkn
      rw [QVandermondeP.gb_eq_zero q k (k + 1) (by omega)]
      have : (gaussBinom q k k + q ^ (k + 1) * 0) * (qfact q k * qint q (k + 1)) * qfact q (k - k)
          = (gaussBinom q k k * qfact q k * qfact q (k - k)) * qint q (k + 1) := by ring
      rw [this, h1]

theorem gb_symm (q n k : ℕ) (h : k ≤ n) : gaussBinom q n k = gaussBinom q n (n - k) := by
  have h1 := gb_fact q n k h
  have h2 := gb_fact q n (n - k) (Nat.sub_le n k)
  rw [Nat.sub_sub_self h] at h2
  have hpos : 0 < qfact q k * qfact q (n - k) := Nat.mul_pos (qfact_pos q k) (qfact_pos q (n - k))
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← mul_assoc, h1, ← h2]
  ring

theorem arith (q N g j ρ : ℕ) (hρ : ρ ≤ N) :
    (if ρ ≤ j then gaussBinom q (N + g - ρ) (j - ρ) else 0) =
      ∑ l ∈ Finset.range (j + 1), q ^ (l * (N + l - j)) * gaussBinom q g l *
        (if j - l ≤ N then gaussBinom q (N - ρ) (N - (j - l)) else 0) := by
  have hV := (qVandermondeIdentity q (N - ρ) g (j - ρ)).1
  have hz : ∀ n k : ℕ, n < k → gaussBinom q n k = 0 := by
    intro n
    induction n with
    | zero =>
      intro k hk
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp [gaussBinom]
    | succ n ih =>
      intro k hk
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hg : gaussBinom q (n + 1) (k + 1) =
          gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1) := by simp [gaussBinom]
      rw [hg, ih k (by omega), ih (k + 1) (by omega)]
      simp
  have key : ∀ l, ρ ≤ j → l ≤ j - ρ →
      q ^ (l * (N - ρ + l - (j - ρ))) * gaussBinom q (N - ρ) (j - ρ - l) * gaussBinom q g l =
        (q ^ (l * (N + l - j)) * gaussBinom q g l *
          if j - l ≤ N then gaussBinom q (N - ρ) (N - (j - l)) else 0) := by
    intro l hρj hl
    rw [show N - ρ + l - (j - ρ) = N + l - j by omega]
    split_ifs with hjl
    · rw [gb_symm q (N - ρ) (j - ρ - l) (by omega), show N - ρ - (j - ρ - l) = N - (j - l) by omega]
      ring
    · rw [hz (N - ρ) (j - ρ - l) (by omega)]
      ring
  have hzero : ∀ l, l ≤ j → j - l < ρ →
      (q ^ (l * (N + l - j)) * gaussBinom q g l *
        if j - l ≤ N then gaussBinom q (N - ρ) (N - (j - l)) else 0) = 0 := by
    intro l hl1 hl2
    split_ifs with hjl
    · rw [hz (N - ρ) (N - (j - l)) (by omega)]
      ring
    · ring
  split_ifs with hρj
  · rw [show N + g - ρ = N - ρ + g by omega, hV]
    calc _ = ∑ l ∈ Finset.range (j - ρ + 1), (q ^ (l * (N + l - j)) * gaussBinom q g l *
            if j - l ≤ N then gaussBinom q (N - ρ) (N - (j - l)) else 0) :=
          Finset.sum_congr rfl (fun l hl => key l hρj (by rw [Finset.mem_range] at hl; omega))
      _ = _ := Finset.sum_subset
          (by intro l hl; simp only [Finset.mem_range] at hl ⊢; omega)
          (fun l hl hl' => hzero l (by simp only [Finset.mem_range] at hl; omega)
            (by simp only [Finset.mem_range] at hl hl'; omega))
  · symm
    apply Finset.sum_eq_zero
    intro l hl
    rw [Finset.mem_range] at hl
    exact hzero l (by omega) (by omega)

section LA

variable {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]

theorem finite_quot (A : Submodule F W) : Finite (W ⧸ A) := Finite.of_surjective A.mkQ (Submodule.mkQ_surjective A)

attribute [local instance] finite_quot

theorem countBelow_eq (A : Submodule F W) (d : ℕ) :
    countBelow A d = countBelow (⊤ : Submodule F A) d := by
  unfold countBelow
  have hfr : ∀ U' : Submodule F A, Module.finrank F (U'.map A.subtype) = Module.finrank F U' :=
    fun U' => (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective A.subtype A.injective_subtype U')).symm
  have hmc : ∀ U : Submodule F W, U ≤ A → (U.comap A.subtype).map A.subtype = U := by
    intro U hU; rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hU
  have hcm : ∀ U' : Submodule F A, (U'.map A.subtype).comap A.subtype = U' :=
    fun U' => Submodule.comap_map_eq_of_injective A.injective_subtype U'
  apply Nat.card_congr
  exact
    { toFun := fun U => ⟨U.1.comap A.subtype, le_top, by rw [← hfr, hmc U.1 U.2.1]; exact U.2.2⟩
      invFun := fun U' => ⟨U'.1.map A.subtype, Submodule.map_subtype_le A U'.1, by rw [hfr]; exact U'.2.2⟩
      left_inv := fun U => Subtype.ext (hmc U.1 U.2.1)
      right_inv := fun U' => Subtype.ext (hcm U'.1) }

theorem finrank_comap_mkQ (A : Submodule F W) (V : Submodule F (W ⧸ A)) :
    Module.finrank F (V.comap A.mkQ) = Module.finrank F V + Module.finrank F A := by
  haveI : Module.Finite F (V.comap A.mkQ) := Module.Finite.of_finite
  let f : (V.comap A.mkQ) →ₗ[F] V := A.mkQ.restrict (fun x hx => hx)
  have hsurj : Function.Surjective f := by
    rintro ⟨v, hv⟩
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective A v
    exact ⟨⟨w, hv⟩, rfl⟩
  have hker : (LinearMap.ker f).map (V.comap A.mkQ).subtype = A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h0 : A.mkQ (y : W) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hy)
      exact (Submodule.Quotient.mk_eq_zero A).mp h0
    · intro hx
      have hmk : A.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero A).mpr hx
      have hxU : x ∈ V.comap A.mkQ := by
        show A.mkQ x ∈ V
        rw [hmk]; exact V.zero_mem
      refine ⟨⟨x, hxU⟩, ?_, rfl⟩
      show f ⟨x, hxU⟩ = 0
      exact Subtype.ext hmk
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h1
  have h2 : Module.finrank F (LinearMap.ker f) = Module.finrank F A :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (V.comap A.mkQ).subtype
      (Submodule.injective_subtype _) (LinearMap.ker f))).trans
      (LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _ hker))
  omega

theorem countAbove_eq (A : Submodule F W) (j : ℕ) :
    countAbove A j = if Module.finrank F A ≤ j then
      countBelow (⊤ : Submodule F (W ⧸ A)) (j - Module.finrank F A) else 0 := by
  haveI : Module.Finite F W := Module.Finite.of_finite
  unfold countAbove countBelow
  split_ifs with hj
  · apply Nat.card_congr
    exact
      { toFun := fun U => ⟨U.1.map A.mkQ, le_top, by
            have h3 := finrank_comap_mkQ A (U.1.map A.mkQ)
            rw [Submodule.comap_map_mkQ, sup_eq_right.mpr U.2.1, U.2.2] at h3
            omega⟩
        invFun := fun V => ⟨V.1.comap A.mkQ,
          (Submodule.ker_mkQ A).ge.trans (LinearMap.ker_le_comap _),
          by rw [finrank_comap_mkQ, V.2.2]; omega⟩
        left_inv := fun U => Subtype.ext (by
          show (U.1.map A.mkQ).comap A.mkQ = U.1
          rw [Submodule.comap_map_mkQ]; exact sup_eq_right.mpr U.2.1)
        right_inv := fun V => Subtype.ext
          (Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective A) V.1) }
  · rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨U, hAU, hU⟩
    have h3 : Module.finrank F A ≤ Module.finrank F U := Submodule.finrank_mono hAU
    omega

end LA

end TypeIIUpP

theorem typeIIUp_of (hS : SubspaceCount) : TypeIIUp := by
  intro F P Q _ _ _ _ _ _ _ _ f N g j hP hQ
  haveI : Module.Finite F P := Module.Finite.of_finite
  haveI : Module.Finite F Q := Module.Finite.of_finite
  haveI := TypeIIUpP.finite_quot (LinearMap.range f)
  obtain ⟨ρ, hρ⟩ : ∃ ρ, Module.finrank F (LinearMap.range f) = ρ := ⟨_, rfl⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hquot := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  rw [hρ, hP] at hrn
  rw [hρ, hQ] at hquot
  have hK : ∀ l, Nat.card {U : Submodule F P // U ≤ LinearMap.ker f ∧ Module.finrank F U + (j - l) = N} =
      if j - l ≤ N then gaussBinom (Fintype.card F) (N - ρ) (N - (j - l)) else 0 := by
    intro l
    split_ifs with hl
    · rw [Nat.card_congr (Equiv.subtypeEquivRight
          (q := fun U : Submodule F P => U ≤ LinearMap.ker f ∧ Module.finrank F U = N - (j - l))
          (fun U => and_congr_right (fun _ => ⟨fun h => by omega, fun h => by omega⟩)))]
      show countBelow (LinearMap.ker f) (N - (j - l)) = _
      rw [TypeIIUpP.countBelow_eq, hS]
      congr 1
      omega
    · rw [Nat.card_eq_zero]
      left
      constructor
      rintro ⟨U, _, hU⟩
      omega
  have hA : countAbove (LinearMap.range f) j =
      if ρ ≤ j then gaussBinom (Fintype.card F) (N + g - ρ) (j - ρ) else 0 := by
    rw [TypeIIUpP.countAbove_eq, hS]
    have hq : Module.finrank F (Q ⧸ LinearMap.range f) = N + g - ρ := by omega
    rw [hq, hρ]
  rw [hA]
  simp only [hK]
  have key := TypeIIUpP.arith (Fintype.card F) N g j ρ (by omega)
  exact_mod_cast key

theorem type_two_upper : TypeIIUp := typeIIUp_of countSubspacesEq

end Formalism.G0
