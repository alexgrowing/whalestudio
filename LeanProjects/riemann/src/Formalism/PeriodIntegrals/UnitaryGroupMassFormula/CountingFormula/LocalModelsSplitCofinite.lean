import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensMultOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def GoodAt {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (L : LocSp D M)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : D.host.E) (Z : MatZ D) (p : PlF D) : Prop :=
  (M p).split = none ∧ (L.H p).IsSelfDual (lattice₂ L p (VS D).L0) ∧
    (∀ a b, GaPlus M δ p T T' Z a b ∈ (M p).L.O) ∧
    ∃ y ∈ (M p).L.O, (GaPlus M δ p T T' Z).det * y = 1

def GoodCofinite : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ →
        ∀ Z : MatZ D, TotPos (GZ (Tn u) (Tn u') Z) →
          ∀ᶠ p in Filter.cofinite, GoodAt L δ (Tn u) (Tn u') Z p

def DensAtGood : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ →
      ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
        ∀ (Z : MatZ D) (p : PlF D), GoodAt L δ (Tn u) (Tn u') Z p →
          ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
            densP L δ ϖ (Tn u) (Tn u') Z p =
              Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[(D.s.atP p).Fp]) η D.R.r (2 * (D.R.rS + 1)) 0

def DensProdBound : Prop :=
  ∀ n m : ℕ, m + 1 ≤ n → ∃ C : ℝ, ∀ (q : ℕ) (η : ℝ), (η = 1 ∨ η = -1) →
    |Formalism.L2.SG.DensExact.densProd q η n m 0 - 1| ≤ C * (1 / ((q : ℝ) ^ 2))

def ResCard : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : PlF D), Nat.card 𝓀[(D.s.atP p).Fp] = p.asIdeal.absNorm

theorem tuple_short (D : Formalism.BasicNotions.D7) : 2 * (D.R.rS + 1) + 1 ≤ D.R.r := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  obtain ⟨a, ha⟩ := D.R.m_even
  unfold Formalism.BasicNotions.Ranks.rS Formalism.BasicNotions.Ranks.r
  omega

def ModeLCofinite : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ᶠ p in Filter.cofinite, (M p).split = none

def GoodRest : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ →
        ∀ Z : MatZ D, TotPos (GZ (Tn u) (Tn u') Z) →
          ∀ᶠ p in Filter.cofinite, (L.H p).IsSelfDual (lattice₂ L p (VS D).L0) ∧
            (∀ a b, GaPlus M δ p (Tn u) (Tn u') Z a b ∈ (M p).L.O) ∧
            ∃ y ∈ (M p).L.O, (GaPlus M δ p (Tn u) (Tn u') Z).det * y = 1

theorem resChar_finite (D : Formalism.BasicNotions.D7) (ℓ : ℕ) : {p : PlF D | Loc.resChar p = ℓ}.Finite := by
  have hsub : {p : PlF D | Loc.resChar p = ℓ} ⊆
      {v | v.asIdeal ∣ Ideal.span {(ℓ : 𝓞 D.host.F)}} := by
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [Ideal.dvd_span_singleton, ← hp, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  by_cases hℓ : ℓ = 0
  · subst hℓ
    convert Set.finite_empty
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hp
    have h1 : ((Ideal.absNorm p.asIdeal : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.absNorm_mem p.asIdeal
    have hc : CharP (𝓞 D.host.F ⧸ p.asIdeal) 0 := by
      have h2 := ringChar.charP (𝓞 D.host.F ⧸ p.asIdeal)
      unfold Loc.resChar at hp
      rwa [hp] at h2
    rw [CharP.cast_eq_zero_iff _ 0, zero_dvd_iff, Ideal.absNorm_eq_zero_iff] at h1
    exact p.ne_bot h1
  · refine (Ideal.finite_factors ?_).subset hsub
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hℓ

theorem local_models_split_cofinite : ModeLCofinite := by
  intro D δ M hA
  have hfin : {p : PlF D | Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)}.Finite := by
    have he : {p : PlF D | Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)} =
        {p | Loc.resChar p = D.host.g 0} ∪ {p | Loc.resChar p = D.host.g 1} := by
      ext p
      simp
    rw [he]
    exact (resChar_finite D _).union (resChar_finite D _)
  rw [Filter.eventually_cofinite]
  refine hfin.subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [← D.s_split p]
  have hAp := (hA p).2.2.2.2.2
  cases hM : (M p).split with
  | none => exact absurd hM hp
  | some g =>
    cases hS : (D.s.atP p).split with
    | none =>
      rw [hM, hS] at hAp
      exact hAp.elim
    | some sg => rfl

end PI.UnitaryGroupMassFormula.CntFormula
