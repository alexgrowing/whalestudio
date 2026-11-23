import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsXPowMul
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkFilLevEq
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.JumpsLetExists
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSDivMem
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.GammaLevelsExpansion
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.QpEqUnit
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.H2Bound

set_option linter.unusedVariables false

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.WachCoordinates

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section H2A

variable {W : LocWach PD LL O v n}

theorem idempotent_mem_invariants_letter (a : ZMod n) : (letE a : LetA O n) ∈ W.AΔ := by
  intro δ _
  funext i
  simp only [LocWach.γA, letγ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply, letE,
    Pi.single_apply]
  split_ifs <;> simp

theorem idempotent_mul_self_letter (a : ZMod n) : (letE a : LetA O n) * letE a = letE a := by
  funext i
  simp only [Pi.mul_apply, letE, Pi.single_apply]
  split_ifs <;> simp

theorem level_idempotent_one (a : ZMod n) (ζ : LL) : W.lev a ζ (letE a : LetA O n) = 1 := by
  have h : W.lev a ζ (1 - letE a) = 0 := W.lev_letter a ζ _ (by simp [letE])
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h.symm

theorem level_idempotent_mul (a : ZMod n) (ζ : LL) (g : LetA O n) :
    W.lev a ζ ((letE a : LetA O n) * g) = W.lev a ζ g := by
  rw [map_mul, level_idempotent_one, one_mul]

theorem prime_natCast_ne_zero (W : LocWach PD LL O v n) : ((PD.p : ℕ) : O) ≠ 0 := by
  intro h
  have h1 : ((PD.p : ℕ) : LL) = 0 := by rw [← map_natCast (algebraMap O LL), h, map_zero]
  have h2 := W.v_l
  rw [h1, AddValuation.map_zero] at h2
  exact absurd h2 (by simp)

theorem qP_eq_qp : qP W = Formalism.MainNotions.LiftingTheory.qp W := rfl

variable [IsDomain O]

theorem q_component_ne_zero (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (i : ZMod n) : qP W i ≠ 0 :=
  Formalism.MainNotions.UnusedSlot80.ToolsR.q_component_ne_zero' hR (prime_natCast_ne_zero W) i

theorem q_pow_component_ne_zero (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (k : ℕ) (i : ZMod n) : (qP W ^ k) i ≠ 0 := by
  rw [Pi.pow_apply]; exact pow_ne_zero _ (q_component_ne_zero hR i)

theorem level_qParameter_eq_X_mul_unit (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (a : ZMod n) (ζ : LL)
    (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ S : PowerSeries LL, IsUnit S ∧ W.lev a ζ (qP W) = X * S := by
  obtain ⟨⟨u, hu, hq⟩, -, -⟩ := expRing_of W hR hA a ζ hζ
  exact ⟨u, hu, by rw [qP_eq_qp, hq, mul_comm]⟩

theorem const_eq_zero_of_qP_dvd (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hinj : Function.Injective (algebraMap O LL)) (a : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (r : O) (h : LetA O n) (e : r • (letE a : LetA O n) = qP W * h) : r = 0 := by
  obtain ⟨S, -, hS⟩ := level_qParameter_eq_X_mul_unit hR hA a ζ hζ
  have hL := congrArg (fun x => coeff 0 (W.lev a ζ x)) e
  simp only [map_smul, level_idempotent_one, map_mul, hS] at hL
  rw [mul_assoc, coeff_zero_X_mul, coeff_smul, coeff_zero_eq_constantCoeff, map_one,
    Algebra.smul_def, mul_one] at hL
  exact hinj (by rw [hL, map_zero])

variable [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem weierstrass_division_qP (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (a : ZMod n)
    (g : LetA O n) (hg : g ∈ W.AΔ) :
    ∃ r : O, ∃ h ∈ W.AΔ, (letE a : LetA O n) * g = qP W * h + r • (letE a : LetA O n) := by
  obtain ⟨f, hf, -⟩ := hR.2.1 g hg
  set I : Ideal O := Ideal.span {((PD.p : ℕ) : O)} with hIdef
  have : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, hIdef, Ideal.span_singleton_eq_top]; exact hpu)
  have hpI : Ideal.Quotient.mk I ((PD.p : ℕ) : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  set D : PowerSeries O := X + C ((PD.p : ℕ) : O) with hD
  have hmap : D.map (Ideal.Quotient.mk I) = X := by
    rw [hD, map_add, map_X, map_C, hpI, map_zero, add_zero]
  have hord : (D.map (Ideal.Quotient.mk I)).order.toNat = 1 := by rw [hmap, order_X]; rfl
  have hdiv : D.IsWeierstrassDivisorAt I := by
    unfold IsWeierstrassDivisorAt
    rw [hord, hD, map_add, coeff_C, if_neg one_ne_zero, add_zero]
    simp [coeff_X]
  have HD := hdiv.isWeierstrassDivisionAt_div_mod (f := f a)
  set H := hdiv.div (f a)
  set r := hdiv.mod (f a)
  have hdeg : r.degree < 1 := by
    have := HD.degree_lt
    rw [hord] at this
    exact_mod_cast this
  have heq : f a = D * H + (r : PowerSeries O) := HD.eq_mul_add
  have hr : (r : PowerSeries O) = r.coeff 0 • (1 : PowerSeries O) := by
    have hle : r.degree ≤ 0 := by
      exact Nat.WithBot.lt_one_iff_le_zero.mp hdeg
    conv_lhs => rw [Polynomial.eq_C_of_degree_le_zero hle]
    rw [Polynomial.coe_C, smul_eq_C_mul, mul_one]
  have hDn : D = X + ((PD.p : ℕ) : PowerSeries O) := by rw [hD, map_natCast]
  have ha0 : constantCoeff W.π₀₁ = 0 := Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR
  have hs0 := HasSubst.of_constantCoeff_zero' ha0
  have hga : g a = (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) * subst W.π₀₁ H +
      r.coeff 0 • (1 : PowerSeries O) := by
    rw [hf a]
    change subst W.π₀₁ (f a) = _
    rw [heq, hr, hDn, ← coe_substAlgHom hs0, map_add, map_mul, map_add, substAlgHom_X, map_natCast,
      map_smul, map_one]
  set h : LetA O n := Pi.single a (subst W.π₀₁ H) with hh
  have key : (letE a : LetA O n) * g = qP W * h + r.coeff 0 • (letE a : LetA O n) := by
    funext i
    by_cases hi : i = a
    · subst hi
      simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, hh, letE, Pi.single_eq_same, one_mul,
        hga, qP, LocWach.π₀, Pi.natCast_apply]
    · simp [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, hh, letE, Pi.single_eq_of_ne hi]
  refine ⟨r.coeff 0, h, ?_, key⟩
  refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR) (q_component_ne_zero hR) ?_
  have e2 : qP W * h = (letE a : LetA O n) * g - r.coeff 0 • (letE a : LetA O n) := by
    rw [key]; abel
  rw [e2]
  exact W.AΔ.sub_mem (W.AΔ.mul_mem (idempotent_mem_invariants_letter a) hg) (W.AΔ.smul_mem (idempotent_mem_invariants_letter a) _)

theorem q_pow_dvd_of_level_vanishing (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (hinj : Function.Injective (algebraMap O LL)) (a : ZMod n)
    (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∀ k : ℕ, ∀ g ∈ W.AΔ, (∀ j < k, coeff j (W.lev a ζ g) = 0) →
      ∃ h ∈ W.AΔ, (letE a : LetA O n) * g = qP W ^ k * h := by
  intro k
  induction k with
  | zero =>
    intro g hg _
    exact ⟨letE a * g, W.AΔ.mul_mem (idempotent_mem_invariants_letter a) hg, by simp⟩
  | succ k ih =>
    intro g hg hv
    obtain ⟨S, hSu, hS⟩ := level_qParameter_eq_X_mul_unit hR hA a ζ hζ
    obtain ⟨r, h1, h1m, e1⟩ := weierstrass_division_qP hR hpu a g hg
    have hL0 := congrArg (fun x => coeff 0 (W.lev a ζ x)) e1
    simp only [map_add, map_smul, map_mul, level_idempotent_one, one_mul, hS] at hL0
    rw [hv 0 (Nat.succ_pos _), mul_assoc, coeff_zero_X_mul, zero_add, coeff_smul,
      coeff_zero_eq_constantCoeff, map_one, Algebra.smul_def, mul_one] at hL0
    have hr : r = 0 := hinj (by rw [← hL0, map_zero])
    rw [hr, zero_smul, add_zero] at e1
    have hLg : W.lev a ζ g = X * (S * W.lev a ζ h1) := by
      rw [← level_idempotent_mul, e1, map_mul, hS, mul_assoc]
    have hv1 : ∀ j < k, coeff j (W.lev a ζ h1) = 0 := by
      have hd : X ^ (k + 1) ∣ X * (S * W.lev a ζ h1) := by
        rw [← hLg]
        exact X_pow_dvd_iff.mpr hv
      rw [pow_succ', mul_dvd_mul_iff_left X_ne_zero] at hd
      exact X_pow_dvd_iff.mp ((hSu.dvd_mul_left).mp hd)
    obtain ⟨h2, h2m, e2⟩ := ih h1 h1m hv1
    refine ⟨h2, h2m, ?_⟩
    rw [← idempotent_mul_self_letter a, mul_assoc, e1, mul_left_comm, e2, ← mul_assoc, ← pow_succ']

end H2A

section Char

variable {W : LocWach PD LL O v n} [IsDomain O]

def QExpansionAlt (W : LocWach PD LL O v n) (a : ZMod n) (g : LetA O n) (F : PowerSeries O) : Prop :=
  ∀ N : ℕ, ∃ h ∈ W.AΔ, (letE a : LetA O n) * g =
    (letE a : LetA O n) * Polynomial.aeval (qP W) (trunc N F) + qP W ^ N * h

theorem trunc_add_alt (F G : PowerSeries O) (N : ℕ) : trunc N (F + G) = trunc N F + trunc N G := by
  ext m
  simp only [PowerSeries.coeff_trunc, Polynomial.coeff_add, map_add]
  all_goals split_ifs <;> simp

theorem trunc_sub_alt (F G : PowerSeries O) (N : ℕ) : trunc N (F - G) = trunc N F - trunc N G := by
  ext m
  simp only [PowerSeries.coeff_trunc, Polynomial.coeff_sub, map_sub]
  all_goals split_ifs <;> simp

theorem trunc_smul_alt (o : O) (F : PowerSeries O) (N : ℕ) : trunc N (o • F) = o • trunc N F := by
  ext m
  simp only [PowerSeries.coeff_trunc, Polynomial.coeff_smul, PowerSeries.coeff_smul]
  all_goals split_ifs <;> simp

theorem aeval_mem_invariants (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (p : Polynomial O) :
    Polynomial.aeval (qP W) p ∈ W.AΔ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact W.AΔ.add_mem hp hq
  | monomial k c =>
    rw [Polynomial.aeval_monomial]
    exact W.AΔ.mul_mem (W.AΔ.algebraMap_mem c) (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR) k)

theorem qExpansion_add_alt {a : ZMod n} {g g' : LetA O n} {F F' : PowerSeries O} (hF : QExpansionAlt W a g F)
    (hF' : QExpansionAlt W a g' F') : QExpansionAlt W a (g + g') (F + F') := by
  intro N
  obtain ⟨h, hh, e1⟩ := hF N
  obtain ⟨h', hh', e2⟩ := hF' N
  refine ⟨h + h', add_mem hh hh', ?_⟩
  rw [mul_add, e1, e2, trunc_add_alt, map_add]
  ring

theorem qExpansion_sub_alt {a : ZMod n} {g g' : LetA O n} {F F' : PowerSeries O} (hF : QExpansionAlt W a g F)
    (hF' : QExpansionAlt W a g' F') : QExpansionAlt W a (g - g') (F - F') := by
  intro N
  obtain ⟨h, hh, e1⟩ := hF N
  obtain ⟨h', hh', e2⟩ := hF' N
  refine ⟨h - h', sub_mem hh hh', ?_⟩
  rw [mul_sub, e1, e2, trunc_sub_alt, map_sub]
  ring

theorem qExpansion_smul_alt {a : ZMod n} {g : LetA O n} {F : PowerSeries O} (o : O) (hF : QExpansionAlt W a g F) :
    QExpansionAlt W a (o • g) (o • F) := by
  intro N
  obtain ⟨h, hh, e1⟩ := hF N
  refine ⟨o • h, SMulMemClass.smul_mem o hh, ?_⟩
  simp only [trunc_smul_alt, map_smul, mul_smul_comm, e1, smul_add]

theorem qExpansion_mul_alt (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {a : ZMod n} {g g' : LetA O n}
    {F F' : PowerSeries O} (hF : QExpansionAlt W a g F) (hF' : QExpansionAlt W a g' F') :
    QExpansionAlt W a (g * g') (F * F') := by
  intro N
  obtain ⟨h, hm, e⟩ := hF N
  obtain ⟨h', hm', e'⟩ := hF' N
  have hdvd : (Polynomial.X : Polynomial O) ^ N ∣ trunc N F * trunc N F' - trunc N (F * F') := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    have h1 : (trunc N F * trunc N F').coeff d = (trunc N (F * F')).coeff d := by
      rw [← trunc_trunc_mul_trunc, coeff_trunc, if_pos hd, ← Polynomial.coe_mul, Polynomial.coeff_coe]
    rw [Polynomial.coeff_sub, h1, sub_self]
  obtain ⟨Q, hQ⟩ := hdvd
  have hPP : Polynomial.aeval (qP W) (trunc N F) * Polynomial.aeval (qP W) (trunc N F') =
      Polynomial.aeval (qP W) (trunc N (F * F')) + qP W ^ N * Polynomial.aeval (qP W) Q := by
    have := congrArg (Polynomial.aeval (qP W)) hQ
    rw [map_sub, map_mul (Polynomial.aeval (qP W)), map_mul (Polynomial.aeval (qP W)), map_pow, Polynomial.aeval_X] at this
    linear_combination this
  set E := (letE a : LetA O n)
  set P := Polynomial.aeval (qP W) (trunc N F)
  set P' := Polynomial.aeval (qP W) (trunc N F')
  refine ⟨E * Polynomial.aeval (qP W) Q + E * P * h' + E * P' * h + qP W ^ N * (h * h'), ?_, ?_⟩
  · have hE := idempotent_mem_invariants_letter (W := W) a
    refine W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.mul_mem hE (aeval_mem_invariants hR Q))
      (W.AΔ.mul_mem (W.AΔ.mul_mem hE (aeval_mem_invariants hR _)) hm'))
      (W.AΔ.mul_mem (W.AΔ.mul_mem hE (aeval_mem_invariants hR _)) hm))
      (W.AΔ.mul_mem (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR) N) (W.AΔ.mul_mem hm hm'))
  · have hEE : E * E = E := idempotent_mul_self_letter a
    calc E * (g * g') = (E * g) * (E * g') := by rw [mul_mul_mul_comm, hEE]
      _ = (E * P + qP W ^ N * h) * (E * P' + qP W ^ N * h') := by rw [e, e']
      _ = (E * E) * (P * P') + qP W ^ N * (E * P * h' + E * P' * h + qP W ^ N * (h * h')) := by ring
      _ = _ := by rw [hEE, hPP]; ring

theorem qExpansion_algebraMap (a : ZMod n) (o : O) : QExpansionAlt W a (algebraMap O (LetA O n) o) (C o) := by
  intro N
  cases N with
  | zero =>
    exact ⟨_, W.AΔ.mul_mem (idempotent_mem_invariants_letter a) (W.AΔ.algebraMap_mem o), by simp [trunc_zero']⟩
  | succ k =>
    refine ⟨0, W.AΔ.zero_mem, ?_⟩
    have : trunc (k + 1) (C o) = Polynomial.C o := by
      ext m
      rw [coeff_trunc, Polynomial.coeff_C, coeff_C]
      by_cases hm : m = 0 <;> simp [hm]
    rw [this, Polynomial.aeval_C]; simp

theorem qExpansion_qP (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (a : ZMod n) : QExpansionAlt W a (qP W) X := by
  intro N
  rcases N with _ | _ | N
  · exact ⟨letE a * qP W, W.AΔ.mul_mem (idempotent_mem_invariants_letter a) (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR),
      by simp [trunc_zero']⟩
  · refine ⟨letE a, idempotent_mem_invariants_letter a, ?_⟩
    have : trunc 1 (X : PowerSeries O) = 0 := by
      ext m; rw [coeff_trunc, coeff_X]; by_cases hm : m = 0 <;> simp [hm]
    rw [this]; simp [mul_comm]
  · refine ⟨0, W.AΔ.zero_mem, ?_⟩
    have : trunc (N + 2) (X : PowerSeries O) = Polynomial.X := by
      ext m; rw [coeff_trunc, coeff_X, Polynomial.coeff_X]
      by_cases hm : m = 1
      · subst hm; simp
      · rw [if_neg hm, if_neg (Ne.symm hm)]; simp
    rw [this, Polynomial.aeval_X]; simp

theorem qExpansion_pow_alt (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {a : ZMod n} {g : LetA O n} {F : PowerSeries O}
    (hF : QExpansionAlt W a g F) (k : ℕ) : QExpansionAlt W a (g ^ k) (F ^ k) := by
  induction k with
  | zero => simpa using (qExpansion_algebraMap (W := W) a 1)
  | succ k ih => rw [pow_succ, pow_succ]; exact qExpansion_mul_alt hR ih hF

theorem qExpansion_idempotent_mul {a : ZMod n} {g : LetA O n} {F : PowerSeries O} (hF : QExpansionAlt W a g F) :
    QExpansionAlt W a ((letE a : LetA O n) * g) F := by
  intro N
  obtain ⟨h, hm, e⟩ := hF N
  exact ⟨h, hm, by rw [← mul_assoc, idempotent_mul_self_letter, e]⟩

variable [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem exists_qExpansion (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hpu : ¬ IsUnit ((PD.p : ℕ) : O))
    (a : ZMod n) (g : LetA O n) (hg : g ∈ W.AΔ) : ∃ F, QExpansionAlt W a g F := by
  have D : ∀ x : W.AΔ, ∃ r : O, ∃ h : W.AΔ,
      (letE a : LetA O n) * x = qP W * h + r • (letE a : LetA O n) := by
    intro x
    obtain ⟨r, h, hm, e⟩ := weierstrass_division_qP hR hpu a x x.2
    exact ⟨r, ⟨h, hm⟩, e⟩
  choose R H hRH using D
  let rem : ℕ → W.AΔ := fun k => Nat.rec (motive := fun _ => W.AΔ) ⟨g, hg⟩ (fun _ x => H x) k
  refine ⟨PowerSeries.mk fun k => R (rem k), fun N =>
    ⟨(letE a : LetA O n) * ((rem N : W.AΔ) : LetA O n), W.AΔ.mul_mem (idempotent_mem_invariants_letter a) (rem N).2, ?_⟩⟩
  induction N with
  | zero => simp [rem, trunc_zero']
  | succ N ih =>
    have hrem : (rem (N + 1) : LetA O n) = H (rem N) := rfl
    have e := hRH (rem N)
    have e2 : (letE a : LetA O n) * (rem N : LetA O n) =
        qP W * ((letE a : LetA O n) * H (rem N)) + R (rem N) • (letE a : LetA O n) := by
      calc (letE a : LetA O n) * (rem N : LetA O n) =
            (letE a : LetA O n) * ((letE a : LetA O n) * (rem N : LetA O n)) := by
            rw [← mul_assoc, idempotent_mul_self_letter]
        _ = _ := by
            rw [e, mul_add, mul_left_comm, mul_smul_comm, idempotent_mul_self_letter]
    rw [ih, trunc_succ, map_add, Polynomial.aeval_monomial, coeff_mk, e2, hrem]
    simp only [Algebra.smul_def]
    ring

theorem qExpansion_unique (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hinj : Function.Injective (algebraMap O LL)) (a : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    {g : LetA O n} {F G : PowerSeries O} (hF : QExpansionAlt W a g F) (hG : QExpansionAlt W a g G) : F = G := by
  ext k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  obtain ⟨h, hm, e⟩ := hF (k + 1)
  obtain ⟨h', hm', e'⟩ := hG (k + 1)
  have htr : trunc (k + 1) F - trunc (k + 1) G = Polynomial.monomial k (coeff k F - coeff k G) := by
    ext j
    rw [Polynomial.coeff_sub, coeff_trunc, coeff_trunc, Polynomial.coeff_monomial]
    by_cases hj : j < k + 1
    · rw [if_pos hj, if_pos hj]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | hjk
      · rw [ih j hjk, sub_self, if_neg (Nat.ne_of_gt hjk)]
      · subst hjk; simp
    · rw [if_neg hj, if_neg hj, sub_self, if_neg (by omega)]
  have h3 : (letE a : LetA O n) * Polynomial.aeval (qP W) (trunc (k + 1) F - trunc (k + 1) G) =
      qP W ^ (k + 1) * (h' - h) := by
    rw [map_sub, mul_sub]; linear_combination e' - e
  rw [htr, Polynomial.aeval_monomial] at h3
  have e3 : qP W ^ k * ((coeff k F - coeff k G) • (letE a : LetA O n)) =
      qP W ^ k * (qP W * (h' - h)) := by
    rw [Algebra.smul_def]; linear_combination h3
  have e4 := Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_comp (q_pow_component_ne_zero hR k) e3
  exact sub_eq_zero.mp (const_eq_zero_of_qP_dvd hR hA hinj a ζ hζ _ _ e4)

end Char

section Scalar

variable {W : LocWach PD LL O v n}

def h2cp (l y b : ℕ) : ℕ := ⌈(y : ℝ) - (b : ℝ) / (l : ℝ) + 2 + Real.logb (l : ℝ) (y : ℝ)⌉₊

variable [IsDomain O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem pk_mem_invariants (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : Formalism.MainNotions.LiftingTheory.pk W 1 ∈ W.AΔ :=
  Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_AΔ 1 (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR)

theorem qExpansion_pk_one (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hpu : ¬ IsUnit ((PD.p : ℕ) : O))
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hinj : Function.Injective (algebraMap O LL)) (a : ZMod n) (ζ : LL)
    (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ ε u : PowerSeries O, IsUnit ε ∧ IsUnit u ∧
      QExpansionAlt W a (Formalism.MainNotions.LiftingTheory.pk W 1) (C ((PD.p : ℕ) : O) * ε + u * X ^ PD.p) := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.2.1
  rw [Formalism.MainNotions.UnusedSlot80.ToolsR.eat_qP] at hw
  have hwm : (w : LetA O n) ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.ToolsR.w_AΔ hR (prime_natCast_ne_zero W) hw
  have hwi : ((w⁻¹ : (LetA O n)ˣ) : LetA O n) ∈ W.AΔ := by
    refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ hwm (fun i => ?_) (by rw [Units.mul_inv]; exact W.AΔ.one_mem)
    intro h0
    have := congrFun (Units.mul_inv w) i
    rw [Pi.mul_apply, h0, zero_mul, Pi.one_apply] at this
    exact zero_ne_one this
  obtain ⟨Fw, hFw⟩ := exists_qExpansion hR hpu a _ hwm
  obtain ⟨Fw', hFw'⟩ := exists_qExpansion hR hpu a _ hwi
  have hone : Fw * Fw' = 1 := by
    have h1 := qExpansion_mul_alt hR hFw hFw'
    rw [Units.mul_inv] at h1
    have h2 : QExpansionAlt W a (1 : LetA O n) 1 := by simpa using (qExpansion_algebraMap (W := W) a 1)
    exact qExpansion_unique hR hA hinj a ζ hζ h1 h2
  have hFwu : IsUnit Fw := ⟨⟨Fw, Fw', hone, by rw [mul_comm]; exact hone⟩, rfl⟩

  have hpk : Formalism.MainNotions.LiftingTheory.pk W 1 = (w : LetA O n) * (qP W - algebraMap O (LetA O n) ((PD.p : ℕ) : O)) *
      qP W ^ (PD.p - 1) + algebraMap O (LetA O n) ((PD.p : ℕ) : O) := by
    have e1 : Formalism.MainNotions.LiftingTheory.pk W 1 = W.φA W.π₀ + ((PD.p : ℕ) : LetA O n) := by
      simp [Formalism.MainNotions.LiftingTheory.pk, Formalism.MainNotions.LiftingTheory.qp, map_natCast]
    have e2 : W.π₀ = qP W - ((PD.p : ℕ) : LetA O n) := by simp [qP]
    rw [e1, hw, e2, map_natCast]
  have hc : QExpansionAlt W a (Formalism.MainNotions.LiftingTheory.pk W 1)
      (Fw * (X - C ((PD.p : ℕ) : O)) * X ^ (PD.p - 1) + C ((PD.p : ℕ) : O)) := by
    rw [hpk]
    exact qExpansion_add_alt (qExpansion_mul_alt hR (qExpansion_mul_alt hR hFw (qExpansion_sub_alt (qExpansion_qP hR a)
      (qExpansion_algebraMap a _))) (qExpansion_pow_alt hR (qExpansion_qP hR a) _)) (qExpansion_algebraMap a _)
  refine ⟨1 - Fw * X ^ (PD.p - 1), Fw, ?_, hFwu, ?_⟩
  · rw [isUnit_iff_constantCoeff, map_sub, map_one, map_mul, map_pow, constantCoeff_X,
      zero_pow (by have := PD.hp.two_le; omega), mul_zero, sub_zero]
    exact isUnit_one
  · have hXl : (X : PowerSeries O) ^ PD.p = X * X ^ (PD.p - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel PD.hp.one_le]
    have e : C ((PD.p : ℕ) : O) * (1 - Fw * X ^ (PD.p - 1)) + Fw * X ^ PD.p =
        Fw * (X - C ((PD.p : ℕ) : O)) * X ^ (PD.p - 1) + C ((PD.p : ℕ) : O) := by
      rw [hXl]; ring
    rw [e]; exact hc

theorem scalar_integrality_relation [IsDiscreteValuationRing O] [IsFractionRing O LL] (hC2 : Formalism.MainNotions.CrystallineLiftingInputs.PowerSeriesDVRFactorisation)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hpu : ¬ IsUnit ((PD.p : ℕ) : O))
    (hinj : Function.Injective (algebraMap O LL)) (a : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (y b η : ℕ) (hb : 1 ≤ b) (hby : (b : ℝ) / (PD.p : ℝ) ≤ (y : ℝ))
    (α : LetA O n) (hα : α ∈ W.AΔ) (θ : LL)
    (hrel : ∀ R < b + η, coeff R (W.lev a ζ α) =
      θ * coeff R (W.lev a ζ (Formalism.MainNotions.LiftingTheory.pk W 1 ^ y * qP W ^ η))) :
    ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ h2cp PD.p y b * θ := by
  haveI : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖL : algebraMap O LL ϖ ≠ 0 := by
    intro h; exact hϖ0 (hinj (by rw [h, map_zero]))
  obtain ⟨eO, ⟨μ, hμ⟩⟩ := IsDiscreteValuationRing.associated_pow_irreducible (prime_natCast_ne_zero W) hϖ
  have heO : 1 ≤ eO := by
    rcases Nat.eq_zero_or_pos eO with h | h
    · exfalso; apply hpu
      rw [h, pow_zero] at hμ
      exact ⟨⟨_, _, hμ, by rw [mul_comm]; exact hμ⟩, rfl⟩
    · exact h

  by_cases hθ : ∃ o : O, algebraMap O LL o = θ
  · obtain ⟨o, ho⟩ := hθ
    exact ⟨((PD.p : ℕ) : O) ^ h2cp PD.p y b * o, by rw [map_mul, map_pow, map_natCast, ho]⟩
  obtain ⟨x, z, hz, hxz⟩ := IsFractionRing.div_surjective (A := O) θ
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hzL : algebraMap O LL z ≠ 0 := by intro h; exact hz0 (hinj (by rw [h, map_zero]))
  have hx0 : x ≠ 0 := by
    rintro rfl; apply hθ; exact ⟨0, by rw [map_zero, ← hxz, map_zero, zero_div]⟩
  obtain ⟨m, ⟨ux, hux⟩⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0 hϖ
  obtain ⟨k, ⟨uz, huz⟩⟩ := IsDiscreteValuationRing.associated_pow_irreducible hz0 hϖ
  have hθz : θ * algebraMap O LL z = algebraMap O LL x := by rw [← hxz, div_mul_cancel₀ _ hzL]

  have hθ2 : θ * algebraMap O LL (ϖ ^ k) * algebraMap O LL (ux : O) =
      algebraMap O LL (ϖ ^ m) * algebraMap O LL (uz : O) := by
    rw [← huz, ← hux, map_mul, map_mul, ← hθz]; ring
  have hmk : m < k := by
    by_contra hle
    push_neg at hle
    apply hθ
    refine ⟨ϖ ^ (m - k) * (uz : O) * ((ux⁻¹ : Oˣ) : O), ?_⟩
    have hk : algebraMap O LL (ϖ ^ k) * algebraMap O LL (ux : O) ≠ 0 := by
      rw [← map_mul]; intro h
      exact mul_ne_zero (pow_ne_zero _ hϖ0) ux.ne_zero (hinj (by rw [h, map_zero]))
    apply mul_right_cancel₀ hk
    rw [← mul_assoc θ, hθ2]
    have hpow : ϖ ^ m = ϖ ^ (m - k) * ϖ ^ k := by rw [← pow_add, Nat.sub_add_cancel hle]
    simp only [← map_mul]
    rw [hpow]
    congr 1
    have hu : ((ux⁻¹ : Oˣ) : O) * ux = 1 := Units.inv_mul ux
    linear_combination (ϖ ^ (m - k) * uz * ϖ ^ k) * hu
  set t := k - m with ht
  set ε : Oˣ := uz * ux⁻¹ with hε
  have hθt : θ * algebraMap O LL (ϖ ^ t) = algebraMap O LL (ε : O) := by
    have hmL : algebraMap O LL (ϖ ^ m) * algebraMap O LL (ux : O) ≠ 0 := by
      rw [← map_mul]; intro h
      exact mul_ne_zero (pow_ne_zero _ hϖ0) ux.ne_zero (hinj (by rw [h, map_zero]))
    apply mul_right_cancel₀ hmL
    have hk : ϖ ^ k = ϖ ^ t * ϖ ^ m := by rw [← pow_add, ht, Nat.sub_add_cancel hmk.le]
    calc θ * algebraMap O LL (ϖ ^ t) * (algebraMap O LL (ϖ ^ m) * algebraMap O LL (ux : O))
        = θ * algebraMap O LL (ϖ ^ k) * algebraMap O LL (ux : O) := by rw [hk, map_mul]; ring
      _ = algebraMap O LL (ϖ ^ m) * algebraMap O LL (uz : O) := hθ2
      _ = _ := by
          rw [hε, Units.val_mul, map_mul]
          have : algebraMap O LL ((ux⁻¹ : Oˣ) : O) * algebraMap O LL (ux : O) = 1 := by
            rw [← map_mul, Units.inv_mul, map_one]
          linear_combination (-(algebraMap O LL (ϖ ^ m) * algebraMap O LL (uz : O))) * this

  obtain ⟨S, -, hS⟩ := level_qParameter_eq_X_mul_unit hR hA a ζ hζ
  have hPi : W.lev a ζ (Formalism.MainNotions.LiftingTheory.pk W 1 ^ y * qP W ^ η) =
      X ^ η * (W.lev a ζ (Formalism.MainNotions.LiftingTheory.pk W 1) ^ y * S ^ η) := by
    rw [map_mul, map_pow, map_pow, hS]; ring
  have hα0 : ∀ j < η, coeff j (W.lev a ζ α) = 0 := by
    intro j hj
    rw [hrel j (by omega), hPi, coeff_X_pow_mul', if_neg (by omega), mul_zero]
  obtain ⟨α', hα'm, hα'⟩ := q_pow_dvd_of_level_vanishing hR hA hpu hinj a ζ hζ η α hα hα0

  have hPm : Formalism.MainNotions.LiftingTheory.pk W 1 ^ y * qP W ^ η ∈ W.AΔ :=
    W.AΔ.mul_mem (W.AΔ.pow_mem (pk_mem_invariants hR) y) (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR) η)
  set β := (ϖ ^ t) • α - (ε : O) • (Formalism.MainNotions.LiftingTheory.pk W 1 ^ y * qP W ^ η) with hβ
  have hβm : β ∈ W.AΔ := W.AΔ.sub_mem (W.AΔ.smul_mem hα _) (W.AΔ.smul_mem hPm _)
  have hβ0 : ∀ j < b + η, coeff j (W.lev a ζ β) = 0 := by
    intro j hj
    rw [hβ, map_sub, map_smul, map_smul, map_sub, coeff_smul, coeff_smul, hrel j hj,
      Algebra.smul_def, Algebra.smul_def, ← hθt]
    ring
  obtain ⟨h₁, hh₁m, hh₁⟩ := q_pow_dvd_of_level_vanishing hR hA hpu hinj a ζ hζ (b + η) β hβm hβ0

  have hcan : qP W ^ η * ((ϖ ^ t) • α' - (ε : O) • ((letE a : LetA O n) * Formalism.MainNotions.LiftingTheory.pk W 1 ^ y)) =
      qP W ^ η * (qP W ^ b * h₁) := by
    have e1 : (letE a : LetA O n) * β = (ϖ ^ t) • ((letE a : LetA O n) * α) -
        (ε : O) • ((letE a : LetA O n) * (Formalism.MainNotions.LiftingTheory.pk W 1 ^ y * qP W ^ η)) := by
      rw [hβ, mul_sub, mul_smul_comm, mul_smul_comm]
    rw [hh₁, hα'] at e1
    simp only [Algebra.smul_def] at e1 ⊢
    linear_combination -e1
  have hrel2 := Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_comp (q_pow_component_ne_zero hR η) hcan

  obtain ⟨ε', u', hε', hu', hFp⟩ := qExpansion_pk_one hR hpu hA hinj a ζ hζ
  obtain ⟨Fα, hFα⟩ := exists_qExpansion hR hpu a α' hα'm
  obtain ⟨Fh, hFh⟩ := exists_qExpansion hR hpu a h₁ hh₁m
  have hL := qExpansion_sub_alt (qExpansion_smul_alt (ϖ ^ t) hFα)
    (qExpansion_smul_alt (ε : O) (qExpansion_idempotent_mul (qExpansion_pow_alt hR hFp y)))
  have hR2 := qExpansion_mul_alt hR (qExpansion_pow_alt hR (qExpansion_qP hR a) b) hFh
  rw [hrel2] at hL
  have hEq := qExpansion_unique hR hA hinj a ζ hζ hL hR2
  set Fp := C ((PD.p : ℕ) : O) * ε' + u' * X ^ PD.p
  have hmem : Fp ^ y ∈ Ideal.span {C (ϖ ^ t), (X : PowerSeries O) ^ b} := by
    rw [Ideal.mem_span_pair]
    refine ⟨C ((ε⁻¹ : Oˣ) : O) * Fα, -(C ((ε⁻¹ : Oˣ) : O) * Fh), ?_⟩
    have hu : C ((ε⁻¹ : Oˣ) : O) * C (ε : O) = (1 : PowerSeries O) := by
      rw [← map_mul, Units.inv_mul, map_one]
    simp only [smul_eq_C_mul] at hEq
    linear_combination (C ((ε⁻¹ : Oˣ) : O)) * hEq + Fp ^ y * hu
  have hc2 := hC2 O PD.p ϖ eO hϖ heO ⟨μ, hμ⟩ ε' u' hε' hu' b y t hb hby hmem

  have hcp : (t : ℝ) ≤ (eO : ℝ) * (h2cp PD.p y b : ℝ) := by
    have heO' : (0 : ℝ) < eO := by exact_mod_cast heO
    have h1 : (t : ℝ) ≤ (h2cp PD.p y b : ℝ) * (eO : ℝ) := (div_le_iff₀ heO').mp (hc2.trans (Nat.le_ceil _))
    linarith [mul_comm (h2cp PD.p y b : ℝ) (eO : ℝ)]
  have htc : t ≤ eO * h2cp PD.p y b := by exact_mod_cast hcp

  refine ⟨((μ⁻¹ : Oˣ) : O) ^ h2cp PD.p y b * (ε : O) * ϖ ^ (eO * h2cp PD.p y b - t), ?_⟩
  have htL : algebraMap O LL (ϖ ^ t) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hϖL
  apply mul_right_cancel₀ htL
  have hl : ((PD.p : ℕ) : O) = ϖ ^ eO * ((μ⁻¹ : Oˣ) : O) := by
    rw [← hμ, mul_assoc, Units.mul_inv, mul_one]
  calc algebraMap O LL (((μ⁻¹ : Oˣ) : O) ^ h2cp PD.p y b * (ε : O) * ϖ ^ (eO * h2cp PD.p y b - t)) *
        algebraMap O LL (ϖ ^ t)
      = algebraMap O LL (((PD.p : ℕ) : O) ^ h2cp PD.p y b * (ε : O)) := by
        rw [← map_mul, hl, mul_pow, ← pow_mul]
        congr 1
        have : ϖ ^ (eO * h2cp PD.p y b) = ϖ ^ (eO * h2cp PD.p y b - t) * ϖ ^ t := by
          rw [← pow_add, Nat.sub_add_cancel htc]
        rw [this]; ring
    _ = (PD.p : LL) ^ h2cp PD.p y b * θ * algebraMap O LL (ϖ ^ t) := by
        rw [map_mul, map_pow, map_natCast, ← hθt]; ring

end Scalar

end Formalism.MainNotions.N.Pv.LocalLengthBound

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.WachCoordinates Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

section SerH2

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

theorem smulSeries_eq_zero_below {m : ℤ} {e : ℤ → V} (he : LB m e) {M : ℤ} (hv : ∀ s < M, e s = 0)
    (g : PowerSeries LL) {J : ℕ} (hg : ∀ j < J, coeff j g = 0) (R : ℤ) (hR : R < M + J) :
    smulS g e R = 0 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, R - m < N :=
    ⟨Int.toNat (R - m) + 1, by have := Int.self_le_toNat (R - m); push_cast; omega⟩
  rw [smulS_eq_sum he g R N hN]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j < J
  · rw [hg j hj, zero_smul]
  · rw [hv _ (by omega), smul_zero]

theorem smulSeries_eq_coeff_delta {m : ℤ} {e : ℤ → V} (he : LB m e) {M : ℤ} (hv : ∀ s < M, s ≠ 0 → e s = 0)
    (g : PowerSeries LL) {J : ℕ} (hg : ∀ j < J, coeff j g = 0) (R : ℕ) (hR : (R : ℤ) < M + J) :
    smulS g e R = coeff R g • e 0 := by
  obtain ⟨N, hN, hN'⟩ : ∃ N : ℕ, (R : ℤ) - m < N ∧ R < N :=
    ⟨Int.toNat ((R : ℤ) - m) + R + 1, by have := Int.self_le_toNat ((R : ℤ) - m); push_cast; omega,
      by omega⟩
  rw [smulS_eq_sum he g R N hN, Finset.sum_eq_single R]
  · simp
  · intro j _ hjR
    by_cases hj : j < J
    · rw [hg j hj, zero_smul]
    · rw [hv _ (by omega) (by omega), smul_zero]
  · intro h; exact absurd (Finset.mem_range.2 hN') h

theorem expansion_vanishes_below {m : ℤ} {e : ℤ → V} (he : LB m e) (k : ℕ) (U : PowerSeries LL)
    (hU : constantCoeff U ≠ 0) (M : ℤ) (h : ∀ r < M, smulS (X ^ k * U) e r = 0) :
    ∀ s < M - k, e s = 0 := by
  have h1 : ∀ s < M - k, smulS U e s = 0 := by
    intro s hs
    have := h (s + k) (by omega)
    rw [smulS_mul he, smulS_X_pow (LB_smulS he U)] at this
    simpa using this
  intro s hs
  rw [← smulS_inv he U hU]
  exact smulSeries_eq_zero_below (LB_smulS he U) h1 U⁻¹ (J := 0) (by simp) s (by simpa using hs)

end SerH2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section DelH2

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem frobenius_smul_series (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem frobenius_pow_smul_series (j : ℕ) (a : LetA O n) (x : W.DD T) :
    ((W.φD T) ^ j) (a • x) = (W.φA ^ j) a • ((W.φD T) ^ j) x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, frobenius_smul_series, pow_succ', AlgHom.mul_apply, Module.End.mul_apply]

theorem gamma_smul_series (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

theorem frobenius_pow_gamma_comm (j : ℕ) (g : W.Gam) (x : W.DD T) :
    ((W.φD T) ^ j) (W.γD T g x) = W.γD T g (((W.φD T) ^ j) x) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, W.φγ_comm]; rfl

theorem gammaRing_mul (g h : W.Gam) (a : LetA O n) : W.γA (g * h) a = W.γA g (W.γA h a) := by
  simp only [LocWach.γA, map_mul]
  rfl

theorem finiteDelta_mul_mem_group {g h : W.Gam} (hg : g ∈ W.DelF) (hh : h ∈ W.DelF) : g * h ∈ W.DelF := by
  obtain ⟨k, hk, hgk⟩ := (W.DelF_def g).1 hg
  obtain ⟨k', hk', hhk⟩ := (W.DelF_def h).1 hh
  refine (W.DelF_def _).2 ⟨k * k', Nat.mul_pos hk hk', ?_⟩
  rw [mul_pow, pow_mul, hgk, one_pow, one_mul, mul_comm, pow_mul, hhk, one_pow]

theorem finiteDelta_inv_mem_group {g : W.Gam} (hg : g ∈ W.DelF) : g⁻¹ ∈ W.DelF := by
  obtain ⟨k, hk, hgk⟩ := (W.DelF_def g).1 hg
  exact (W.DelF_def _).2 ⟨k, hk, by rw [inv_pow, hgk, inv_one]⟩

theorem sum_finiteDelta_translate {M : Type} [AddCommMonoid M] (f : W.Gam → M) {g : W.Gam} (hg : g ∈ W.DelF) :
    ∑ h ∈ W.DelF, f (g * h) = ∑ h ∈ W.DelF, f h := by
  refine Finset.sum_nbij' (fun h => g * h) (fun h => g⁻¹ * h) (fun h hh => finiteDelta_mul_mem_group W hg hh)
    (fun h hh => finiteDelta_mul_mem_group W (finiteDelta_inv_mem_group W hg) hh) (fun h _ => by simp) (fun h _ => by simp)
    (fun h _ => rfl)

def h2avA (κ : O) (a : LetA O n) : LetA O n := κ • ∑ h ∈ W.DelF, W.γA h a

def h2avD (κ : O) (x : W.DD T) : W.DD T := κ • ∑ h ∈ W.DelF, W.γD T h x

theorem averageRing_mem_invariants (κ : O) (a : LetA O n) : h2avA W κ a ∈ W.AΔ := by
  intro g hg
  simp only [h2avA, map_smul, map_sum]
  congr 1
  rw [← sum_finiteDelta_translate W (fun h => W.γA h a) hg]
  exact Finset.sum_congr rfl fun h _ => (gammaRing_mul W g h a).symm

theorem average_of_invariant (κ : O) (hκ : κ * (W.DelF.card : O) = 1) {x : W.DD T}
    (hx : ∀ h ∈ W.DelF, W.γD T h x = x) : h2avD W T κ x = x := by
  simp only [h2avD]
  rw [Finset.sum_congr rfl hx, Finset.sum_const, ← Nat.cast_smul_eq_nsmul O, smul_smul, hκ, one_smul]

theorem average_smul_invariant (κ : O) (a : LetA O n) {z : W.DD T} (hz : ∀ h ∈ W.DelF, W.γD T h z = z) :
    h2avD W T κ (a • z) = h2avA W κ a • z := by
  simp only [h2avD, h2avA]
  rw [Finset.sum_congr rfl fun h hh => by rw [gamma_smul_series, hz h hh], ← Finset.sum_smul, smul_assoc]

theorem average_add (κ : O) (x y : W.DD T) : h2avD W T κ (x + y) = h2avD W T κ x + h2avD W T κ y := by
  simp only [h2avD, map_add, Finset.sum_add_distrib, smul_add]

theorem average_sub (κ : O) (x y : W.DD T) : h2avD W T κ (x - y) = h2avD W T κ x - h2avD W T κ y := by
  simp only [h2avD, map_sub, Finset.sum_sub_distrib, smul_sub]

theorem average_finset_sum (κ : O) {ι : Type} (s : Finset ι) (x : ι → W.DD T) :
    h2avD W T κ (∑ i ∈ s, x i) = ∑ i ∈ s, h2avD W T κ (x i) := by
  simp only [h2avD, map_sum]
  rw [Finset.sum_comm, Finset.smul_sum]

theorem average_smul_invariant_ring (κ : O) {a : LetA O n} (ha : a ∈ W.AΔ) (x : W.DD T) :
    h2avD W T κ (a • x) = a • h2avD W T κ x := by
  simp only [h2avD]
  rw [Finset.sum_congr rfl fun h hh => by rw [gamma_smul_series, ha h hh], ← Finset.smul_sum, smul_comm]

theorem average_scalar_smul (κ o : O) (x : W.DD T) : h2avD W T κ (o • x) = o • h2avD W T κ x := by
  simp only [h2avD, map_smul, ← Finset.smul_sum]
  rw [smul_comm]

theorem pullback_gamma_stable (i : ZMod n) (j : ℕ) {g : W.Gam} (hg : g ∈ W.DelF) {x : W.DD T}
    (hx : x ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T i j) : W.γD T g x ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T i j := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, ⟨hzN, hzD⟩, rfl⟩ := hy
    rw [← frobenius_pow_gamma_comm, hzD.2 g hg]
    exact Submodule.subset_span ⟨z, ⟨hzN, hzD⟩, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [gamma_smul_series]; exact Submodule.smul_mem _ _ hy

theorem average_mem_pullback (κ : O) (i : ZMod n) (j : ℕ) {x : W.DD T}
    (hx : x ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T i j) : h2avD W T κ x ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T i j := by
  simp only [h2avD]
  rw [← algebraMap_smul (LetA O n)]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun h hh => pullback_gamma_stable W T i j hh hx)

end DelH2

end Formalism.MainNotions.N.Pv.LocalLengthBound

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.WachCoordinates Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section TrH2

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) [IsDomain O]

theorem prime_pow_component_ne_zero (hp : ((PD.p : ℕ) : O) ≠ 0) (e : ℕ) (i : ZMod n) :
    ((((PD.p : ℕ) : LetA O n)) ^ e) i ≠ 0 := by
  simp only [Pi.pow_apply, Pi.natCast_apply]
  exact pow_ne_zero _ (fun h => hp (by simpa using congrArg constantCoeff h))

theorem truncation_delta_invariant (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (i : ZMod n) (j M X σ : ℕ) {w z : W.DD T}
    (hwD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i w) (hz : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T i j M X σ w z) :
    ∀ g ∈ W.DelF, W.γD T g z = z := by
  intro g hg
  obtain ⟨cc, r, s, hser, hrs, rfl⟩ := hz
  have hs : ∀ y, W.γA g (s y) = s y := by
    intro y
    obtain ⟨⟨a, ha⟩, -⟩ := (hrs y).1
    have hr : r y ∈ W.AΔ := by
      rw [ha]
      exact Subalgebra.sum_mem _ fun k _ =>
        W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hR.1 _)
    have e1 := (hrs y).2
    apply Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_comp (prime_pow_component_ne_zero (prime_natCast_ne_zero W) (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y))
    have e2 := congrArg (W.γA g) e1
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, hr g hg] at e2
    rw [e2, e1]
  rw [map_sub, map_smul, map_sum, ← frobenius_pow_gamma_comm, hwD.2 g hg]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [gamma_smul_series, hs y, ← frobenius_pow_gamma_comm, ((hser.2.1 y).1).2 g hg]

theorem frobenius_idempotent_succ (i : ZMod n) : W.φA (letE i : LetA O n) = letE (i + 1) := by
  funext k
  simp only [LocWach.φA, letφ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply, letE,
    Pi.single_apply]
  by_cases h : k = i + 1
  · subst h; simp
  · rw [if_neg (by intro h'; apply h; rw [← h']; ring), if_neg h, map_zero]

theorem frobenius_shifts_idempotent {i : ZMod n} {x : W.DD T} (hx : (letE i : LetA O n) • x = x) :
    (letE (i + 1) : LetA O n) • W.φD T x = W.φD T x := by
  conv_rhs => rw [← hx]
  rw [frobenius_smul_series, frobenius_idempotent_succ]

theorem frobenius_sq_mem_pullback (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (i : ZMod n) {m : W.DD T}
    (hm : m ∈ W.Nl T i) : ((W.φD T) ^ 2) m ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T i 2 := by
  obtain ⟨⟨r, bb, hbΔ, hspan, -⟩, -⟩ := hmod
  have hmN := MC.Nl_le_N W T i hm
  have hme := MC.letE_smul_of_mem_Nl W hm
  obtain ⟨a, ha, -⟩ := hspan m hmN
  have e1 : m = ∑ k, a k • ((letE i : LetA O n) • bb k) := by
    conv_lhs => rw [← hme, ha]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, smul_smul, mul_comm]
  rw [e1, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [frobenius_pow_smul_series]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨?_, ?_, ?_⟩, rfl⟩)
  · exact (W.N T).smul_mem _ (hbΔ k).1
  · rw [smul_smul, MC.letE_mul_self]
  · intro g hg
    rw [gamma_smul_series, (hbΔ k).2 g hg, idempotent_mem_invariants_letter i g hg]

theorem pullback_mem_of_level_bound (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hs : W.s = 1)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (Mi hi : ZMod n → ℕ) (hp5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T Mi hi)
    (c : ZMod n) (η : ℕ) {w : W.DD T}
    (hw : Formalism.MainNotions.LiftingTheory.qp W ^ η • w ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (c - 1) 1) :
    (Formalism.MainNotions.LiftingTheory.pk W 1 ^ hi (c - 1) * Formalism.MainNotions.LiftingTheory.qp W ^ η) • w ∈
      Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (c - 1 - 1) 2 := by
  obtain ⟨U, hU⟩ := qp_eq_unit W hs hR
  rw [mul_smul]
  generalize Formalism.MainNotions.LiftingTheory.qp W ^ η • w = x at hw ⊢
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, ⟨hzN, hzD⟩, rfl⟩ := hy
    rw [pow_one]
    have hzl : z ∈ W.Nl T (c - 1) := MC.mem_Nl_of W hzN hzD.1
    have h1 := hp5.2.1 (c - 1) z hzl
    have h2 : Formalism.MainNotions.LiftingTheory.qp W ^ hi (c - 1) • z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1 - 1)) := by
      rw [hU, mul_pow, mul_smul]
      exact Submodule.smul_mem _ _ h1
    have e : Formalism.MainNotions.LiftingTheory.pk W 1 ^ hi (c - 1) • W.φD T z =
        W.φD T (Formalism.MainNotions.LiftingTheory.qp W ^ hi (c - 1) • z) := by
      rw [frobenius_smul_series, map_pow]; rfl
    rw [e]
    clear e h1
    generalize Formalism.MainNotions.LiftingTheory.qp W ^ hi (c - 1) • z = t at h2 ⊢
    induction h2 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      have := frobenius_sq_mem_pullback W T hmod (c - 1 - 1) hm
      rwa [pow_two, Module.End.mul_apply] at this
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y y' _ _ h h' => rw [map_add]; exact Submodule.add_mem _ h h'
    | smul a y _ h => rw [frobenius_smul_series]; exact Submodule.smul_mem _ _ h
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact Submodule.add_mem _ h h'
  | smul a y _ h => rw [smul_comm]; exact Submodule.smul_mem _ _ h

theorem pole_clearing_multiplier (Mi hi : ZMod n → ℕ) (hp5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T Mi hi) (c : ZMod n) {x : W.DD T}
    (hx : x ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (c - 1 - 1) 2) :
    (W.Q ^ Mi c * W.φA W.Q ^ Mi (c - 1)) • x ∈ W.N T := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, ⟨hzN, hzD⟩, rfl⟩ := hy
    have hzl : z ∈ W.Nl T (c - 1 - 1) := MC.mem_Nl_of W hzN hzD.1
    have h1 := hp5.1 (c - 1) z hzl
    have hlet : (letE (c - 1) : LetA O n) • (W.Q ^ Mi (c - 1) • W.φD T z) =
        W.Q ^ Mi (c - 1) • W.φD T z := by
      rw [smul_comm, show c - 1 = c - 1 - 1 + 1 by ring, frobenius_shifts_idempotent W T hzD.1]
    have h2 := hp5.1 c _ (MC.mem_Nl_of W h1 hlet)
    rw [frobenius_smul_series, map_pow, smul_smul] at h2
    rw [pow_two, Module.End.mul_apply, mul_smul]
    rw [mul_smul] at h2
    exact h2
  | zero => rw [smul_zero]; exact (W.N T).zero_mem
  | add y y' _ _ h h' => rw [smul_add]; exact (W.N T).add_mem h h'
  | smul a y _ h => rw [smul_comm]; exact (W.N T).smul_mem _ h

end TrH2

end Formalism.MainNotions.N.Pv.LocalLengthBound

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.WachCoordinates Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section KR

variable (W : LocWach PD LL O v n) [IsDomain O]

theorem kernel_rank_bound [NeZero n] (hT2 : Formalism.MainNotions.CrystallineLiftingInputs.TTool2 W) (hTH : Formalism.MainNotions.CrystallineLiftingInputs.THor W)
    (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (hN : GamN W) (hA' : GamA W)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 11 ≤ PD.p)
    (hΔ : IsUnit ((W.DelF.card : ℕ) : O))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (Mi hi : ZMod n → ℕ) (hp5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T Mi hi)
    (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (η bb X₀ σ : ℕ) (hTC : Formalism.MainNotions.CrystallineLiftingInputs.TCase PD.p 2 1 X₀ σ) (hX1 : bb + η ≤ X₀) (hX2 : bb + Mi c ≤ X₀ + 1)
    (w : W.DD T) (hwD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c w)
    (hw : Formalism.MainNotions.LiftingTheory.qp W ^ η • w ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (c - 1) 1)
    (K : ℕ) (hK : W.Q ^ K • w ∈ W.N T) (dd : ℤ → T.V ⊗[Qp] BdR) (hdd : ∃ m, LB m dd)
    (u : PowerSeries LL) (hu : W.lev c ζ W.q = X * u) (hu0 : constantCoeff u ≠ 0)
    (hexp : W.levN T c ζ ⟨W.Q ^ K • w, hK⟩ = smulS ((X * u) ^ K) dd)
    (hddF : ∀ s < (bb : ℤ), s ≠ 0 → dd s ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-(η : ℤ))) :
    ∃ (N : ℕ) (ak : Fin N → LetA O n) (wk : Fin N → W.DD T), (∀ k, ak k ∈ W.AΔ) ∧
      (∀ k, wk k ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1)) ∧
      ∀ R : ℕ, R < bb + η →
        ((PD.p : LL) ^ σ * coeff R (W.lev c ζ (Formalism.MainNotions.LiftingTheory.pk W 1 ^ hi (c - 1) * Formalism.MainNotions.LiftingTheory.qp W ^ η))) •
            dd 0 - ∑ k, coeff R (W.lev c ζ (ak k)) •
              ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V)
                (φVB PD (LL := LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T (wk k)))) ∈
          Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-(η : ℤ)) := by
  have hs : W.s = 1 := hCA.2.1
  have hp := p_ne_zero_LL W
  obtain ⟨κu, hκu⟩ := hΔ
  set κ : O := ((κu⁻¹ : Oˣ) : O) with hκdef
  have hκ : κ * (W.DelF.card : O) = 1 := by rw [hκdef, ← hκu, Units.inv_mul]
  set Fl := Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-(η : ℤ)) with hFl
  set π := Fl.mkQ with hπ
  have ER := expRules_of W h4 hN hA' hCA T hT c ζ hζ
  obtain ⟨⟨Sq, hSq, hqp⟩, -, hpku⟩ := expRing_of W hR hCA c ζ hζ
  obtain ⟨U, hU⟩ := qp_eq_unit W hs hR
  have hQq : W.Q = W.q := MC.Q_eq_q W hs

  set y := hi (c - 1) with hy
  set Pc : LetA O n := Formalism.MainNotions.LiftingTheory.pk W 1 ^ y * Formalism.MainNotions.LiftingTheory.qp W ^ η with hPc
  have hPcm : Pc ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_AΔ 1 (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR)) _)
    (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR) _)
  have hPmem := pullback_mem_of_level_bound W T hR hs hmod Mi hi hp5 c η hw
  obtain ⟨hTT, -⟩ := hT2 hCA hl 2 1 X₀ σ hTC
  obtain ⟨-, hB, -, -, -, hF⟩ := hTT T hT (c - 1 - 1)
  obtain ⟨p', hp'm, hsp⟩ := hF _ hPmem
  rw [Submodule.mem_span_set'] at hsp
  obtain ⟨N, a, g, hsum⟩ := hsp
  choose wk hwkN hwkI hwkT using fun k => (g k).2
  set zk : Fin N → W.DD T := fun k => (g k : W.DD T) with hzk
  have hzinv : ∀ k, ∀ h ∈ W.DelF, W.γD T h (zk k) = zk k := fun k =>
    truncation_delta_invariant W T hR (c - 1 - 1) 2 1 X₀ σ (hwkI k).1 (hwkT k)
  have hPinv : ∀ h ∈ W.DelF, W.γD T h (Pc • w) = Pc • w := by
    intro h hh; rw [gamma_smul_series, hPcm h hh, hwD.2 h hh]
  have hfm : Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 X₀ ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem hR.1 _)
    (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR) _)
  set ak : Fin N → LetA O n := fun k => h2avA W κ (a k) with hak
  set p'' := h2avD W T κ p' with hp''
  have hrel : ∑ k, ak k • zk k = ((PD.p : ℕ) : O) ^ (2 * σ) • (Pc • w) -
      Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 X₀ • p'' := by
    have := congrArg (h2avD W T κ) hsum
    rw [average_finset_sum, average_sub, average_scalar_smul, average_of_invariant W T κ hκ hPinv, average_smul_invariant_ring W T κ hfm]
      at this
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => (average_smul_invariant W T κ (a k) (hzinv k)).symm
  have hp''m : p'' ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (c - 1 - 1) 2 := average_mem_pullback W T κ _ _ hp'm

  set g₀ : LetA O n := W.Q ^ Mi c * W.φA W.Q ^ Mi (c - 1) with hg₀
  set a₀ : LetA O n := ((U⁻¹ : (LetA O n)ˣ) : LetA O n) ^ Mi c * W.φA W.Q ^ Mi (c - 1) with ha₀
  have hQU : W.Q = ((U⁻¹ : (LetA O n)ˣ) : LetA O n) * Formalism.MainNotions.LiftingTheory.qp W := by
    rw [hU, ← mul_assoc, Units.inv_mul, one_mul]
  have hga : g₀ = Formalism.MainNotions.LiftingTheory.qp W ^ Mi c * a₀ := by
    rw [hg₀, ha₀, hQU]; ring
  have hφQ : W.φA W.Q = W.φA ((U⁻¹ : (LetA O n)ˣ) : LetA O n) * Formalism.MainNotions.LiftingTheory.pk W 1 := by
    rw [hQU, map_mul]; rfl
  set V₀ : PowerSeries LL := u ^ Mi c * W.lev c ζ (W.φA W.Q) ^ Mi (c - 1) with hV₀
  have hlevφQ : IsUnit (W.lev c ζ (W.φA W.Q)) := by
    rw [hφQ, map_mul]
    exact ((((U⁻¹ : (LetA O n)ˣ).isUnit).map W.φA).map (W.lev c ζ)).mul hpku
  have hV₀0 : constantCoeff V₀ ≠ 0 := by
    rw [hV₀, map_mul, map_pow, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hu0) (pow_ne_zero _ ((hlevφQ.map constantCoeff).ne_zero))
  have hlg : W.lev c ζ g₀ = X ^ Mi c * V₀ := by
    rw [hg₀, map_mul, map_pow, map_pow, hV₀, show W.lev c ζ W.Q = X * u by rw [hQq, hu]]; ring
  have hlg0 : W.lev c ζ g₀ ≠ 0 := by
    rw [hlg]; intro h
    have := congrArg (coeff (Mi c)) h
    rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff, map_zero] at this
    exact hV₀0 this

  have hexE : ∀ (x : W.DD T) (hx : g₀ • x ∈ W.N T), ∃ d : ℤ → T.V ⊗[Qp] BdR,
      Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T c ζ x d ∧ (∃ m, LB m d) ∧
        smulS (W.lev c ζ g₀) d = W.levN T c ζ ⟨g₀ • x, hx⟩ := by
    intro x hx
    obtain ⟨m, hm⟩ := W.levN_supp T c ζ ⟨g₀ • x, hx⟩
    obtain ⟨m', d, hd, hde⟩ := smulS_div (m := m) hm _ hlg0
    exact ⟨d, ⟨⟨m', hd⟩, g₀, hx, hlg0, fun k => (congrFun hde k).symm⟩, ⟨m', hd⟩, hde⟩

  have hzpull : ∀ k, zk k ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (c - 1 - 1) 2 := by
    intro k
    have h1 := (hB (wk k) (zk k) (hwkI k) (hwkT k)).1
    have h2 : ((W.φD T) ^ 2) (wk k) ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (c - 1 - 1) 2 :=
      Submodule.subset_span ⟨wk k, ⟨hwkN k, (hwkI k).1⟩, rfl⟩
    have := Submodule.add_mem _ h1 (Submodule.smul_of_tower_mem _ (((PD.p : ℕ) : O) ^ σ) h2)
    rwa [sub_add_cancel] at this
  set μ : Fin N → T.V ⊗[Qp] BdR := fun k => ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V)
    (φVB PD (LL := LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T (wk k)))) with hμ
  have hlet : c - 1 - 1 + ((2 : ℕ) : ZMod n) = c := by push_cast; ring
  have hzE : ∀ k, ∃ d : ℤ → T.V ⊗[Qp] BdR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T c ζ (zk k) d ∧ (∃ m, LB m d) ∧
      ∀ s : ℤ, s < X₀ → d s = if s = 0 then (PD.p : LL) ^ σ • μ k else 0 := by
    intro k
    have hx := pole_clearing_multiplier W T Mi hi hp5 c (hzpull k)
    obtain ⟨d, hdE, ⟨m, hm⟩, hde⟩ := hexE _ hx
    refine ⟨d, hdE, ⟨m, hm⟩, ?_⟩
    have hx' : (Formalism.MainNotions.LiftingTheory.qp W ^ Mi c * a₀) • zk k ∈ W.N T := by rw [← hga]; exact hx
    have hth := hTH hCA hl 2 1 X₀ σ hTC T hT (c - 1 - 1) (wk k) (zk k) (hwkN k) (hwkI k) (hwkT k)
      ζ (Mi c + X₀) (Mi c) a₀ hx' (Or.inl ⟨hζ, rfl⟩)
    rw [hlet] at hth
    obtain ⟨hneg, hpos⟩ := hth
    have hcm : Formalism.MainNotions.ArcLiftingSetup.cmpD W T (wk k) = W.cmp T ⟨wk k, hwkN k⟩ := by
      simp [Formalism.MainNotions.ArcLiftingSetup.cmpD, hwkN k]
    set c₀ : ℤ → T.V ⊗[Qp] BdR := fun s => if s = 0 then (PD.p : LL) ^ σ • μ k else 0 with hc₀
    have hc₀L : LB 0 c₀ := fun s hs => by simp [hc₀, show s ≠ 0 by omega]
    have hdiff : ∀ r < (Mi c : ℤ) + X₀, smulS (X ^ Mi c * V₀) (d - c₀) r = 0 := by
      intro r hr
      have hm' : LB (min m 0) d := LB_mono hm (min_le_left _ _)
      have hc₀' : LB (min m 0) c₀ := LB_mono hc₀L (min_le_right _ _)
      have e1 : smulS (W.lev c ζ g₀) d r = W.levN T c ζ ⟨g₀ • zk k, hx⟩ r := congrFun hde r
      have hsub : (⟨g₀ • zk k, hx⟩ : ↥(W.N T)) = ⟨(Formalism.MainNotions.LiftingTheory.qp W ^ Mi c * a₀) • zk k, hx'⟩ :=
        Subtype.ext (show g₀ • zk k = _ by rw [hga])
      rw [← hlg, smulS_sub hm' hc₀', Pi.sub_apply, sub_eq_zero, e1, hsub]
      rcases lt_or_ge r 0 with hr0 | hr0
      · rw [LB_smulS hc₀L _ r hr0]
        exact hneg r hr0
      · obtain ⟨r', rfl⟩ : ∃ r' : ℕ, r = r' := ⟨r.toNat, by omega⟩
        rw [smulSeries_eq_coeff_delta hc₀L (M := (r' : ℤ) + 1) (fun s _ hs => by simp [hc₀, hs]) _ (J := 0)
          (by simp) r' (by omega)]
        rw [hpos r' (by omega), hga]
        have hc₀0 : c₀ 0 = (PD.p : LL) ^ σ • μ k := by simp [hc₀]
        rw [hc₀0]
        simp only [hμ, hcm]
        try rfl
    have hb := expansion_vanishes_below (LB_sub (LB_mono hm (min_le_left m 0)) (LB_mono hc₀L (min_le_right m 0)))
      (Mi c) V₀ hV₀0 _ hdiff
    intro s hs
    have := hb s (by omega)
    rw [Pi.sub_apply, sub_eq_zero] at this
    rw [this]
  choose dz hdzE hdzL hdz using hzE

  have hp''x := pole_clearing_multiplier W T Mi hi hp5 c hp''m
  obtain ⟨d'', hd''E, ⟨m'', hm''⟩, hd''e⟩ := hexE _ hp''x
  have hd''π : ∀ s < (η : ℤ) + 1 - Mi c, π (d'' s) = 0 := by
    have hprim : IsPrimitiveRoot ζ (PD.p ^ (0 + 1)) := by rwa [zero_add, pow_one]
    have hLv := (h4 T hT c 0 ζ hprim).1 ⟨g₀ • p'', hp''x⟩
    have h1 : ∀ r < (η : ℤ) + 1, smulS (X ^ Mi c * V₀) (fun j => π (d'' j)) r = 0 := by
      intro r hr
      rw [← hlg, ← smulS_linMap π hm'' _ r, hd''e, hπ, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T c 0 (by omega) (hLv r)
    have hL : LB m'' (fun j => π (d'' j)) := fun j hj => by simp [hm'' j hj]
    intro s hs
    exact expansion_vanishes_below hL (Mi c) V₀ hV₀0 _ h1 s hs

  obtain ⟨mdd, hmdd⟩ := hdd
  have hwE : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T c ζ w dd := by
    refine ⟨⟨mdd, hmdd⟩, W.Q ^ K, hK, ?_, fun k => ?_⟩
    · rw [map_pow, hQq, hu]
      exact pow_ne_zero _ (mul_ne_zero X_ne_zero (by intro h; exact hu0 (by rw [h, map_zero])))
    · rw [hexp, map_pow, hQq, hu]; rfl
  obtain ⟨-, -, hAdd, hOs, hAs, -, -⟩ := ER
  have hPE := hAs Pc w dd hwE

  have hLHS : ∀ s : Finset (Fin N), Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T c ζ (∑ k ∈ s, ak k • zk k)
      (∑ k ∈ s, Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev c ζ (ak k)) (dz k)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      have := hOs 0 w dd hwE
      rw [zero_smul] at this
      convert this using 1
      funext k; simp
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk]
      exact hAdd _ _ _ _ (hAs _ _ _ (hdzE k)) ih
  have hRHS : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T c ζ
      (((PD.p : ℕ) : O) ^ (2 * σ) • (Pc • w) - Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 X₀ • p'')
      ((fun k => algebraMap O LL (((PD.p : ℕ) : O) ^ (2 * σ)) •
          Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev c ζ Pc) dd k) +
        (fun k => algebraMap O LL (-1) •
          Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev c ζ (Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 X₀)) d'' k)) := by
    rw [sub_eq_add_neg, ← neg_one_smul O (Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 X₀ • p'')]
    exact hAdd _ _ _ _ (hOs _ _ _ hPE) (hOs _ _ _ (hAs _ _ _ hd''E))
  have hEq := isExp_unique W T c ζ (hrel ▸ hLHS Finset.univ) hRHS

  refine ⟨N, ak, wk, fun k => averageRing_mem_invariants W κ (a k), fun k => ⟨hwkN k, (hwkI k).1⟩, ?_⟩
  intro R hR
  have hER := congrArg (fun f => π (f R)) hEq
  simp only [Finset.sum_apply, Pi.add_apply, map_sum, map_add, map_smul] at hER

  have hl1 : ∀ k, π (Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev c ζ (ak k)) (dz k) R) =
      coeff R (W.lev c ζ (ak k)) • π ((PD.p : LL) ^ σ • μ k) := by
    intro k
    obtain ⟨mk, hmk⟩ := hdzL k
    rw [conv_eq, smulS_linMap π hmk]
    have hL : LB mk (fun j => π (dz k j)) := fun j hj => by simp [hmk j hj]
    rw [smulSeries_eq_coeff_delta hL (M := (X₀ : ℤ)) (fun s hs hs0 => by rw [hdz k s hs, if_neg hs0, map_zero])
      _ (J := 0) (by simp) R (by omega)]
    rw [hdz k 0 (by omega), if_pos rfl]

  have hPc0 : ∀ j < η, coeff j (W.lev c ζ Pc) = 0 := by
    intro j hj
    rw [hPc, map_mul, map_pow, map_pow, hqp, mul_pow, ← mul_assoc, coeff_mul_X_pow', if_neg (by omega)]
  have hl2 : π (Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev c ζ Pc) dd R) = coeff R (W.lev c ζ Pc) • π (dd 0) := by
    rw [conv_eq, smulS_linMap π hmdd]
    have hL : LB mdd (fun j => π (dd j)) := fun j hj => by simp [hmdd j hj]
    rw [smulSeries_eq_coeff_delta hL (M := (bb : ℤ)) (fun s hs hs0 => by
      rw [hπ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hddF s hs hs0) _ hPc0 R
      (by omega)]

  have hf0 : ∀ j < X₀, coeff j (W.lev c ζ (Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 X₀)) = 0 := by
    intro j hj
    rw [Formalism.MainNotions.CrystallineLiftingInputs.fMX, map_mul, map_pow, map_pow, ← qP_eq_qp, qP_eq_qp, hqp, mul_pow,
      ← mul_assoc, coeff_mul_X_pow', if_neg (by omega)]
  have hl3 : π (Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev c ζ (Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 X₀)) d'' R) = 0 := by
    rw [conv_eq, smulS_linMap π hm'']
    have hL : LB m'' (fun j => π (d'' j)) := fun j hj => by simp [hm'' j hj]
    exact smulSeries_eq_zero_below hL hd''π _ hf0 R (by omega)
  rw [Finset.sum_congr rfl fun k _ => hl1 k, hl2, hl3, smul_zero, add_zero] at hER

  have hσ0 : (PD.p : LL) ^ σ ≠ 0 := pow_ne_zero _ hp
  simp only [map_smul, map_pow, map_natCast] at hER
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, ← hπ]
  refine (smul_eq_zero.mp ?_).resolve_left hσ0
  rw [map_sub, map_sum, smul_sub, Finset.smul_sum]
  have e3 : ∑ k, (PD.p : LL) ^ σ • π (coeff R (W.lev c ζ (ak k)) • μ k) =
      ∑ k, coeff R (W.lev c ζ (ak k)) • ((PD.p : LL) ^ σ • π (μ k)) :=
    Finset.sum_congr rfl fun k _ => by rw [map_smul, smul_comm]
  rw [e3, hER, map_smul]
  simp only [smul_smul]
  rw [← sub_smul]
  convert zero_smul LL (π (dd 0)) using 2
  ring

end KR

end Formalism.MainNotions.N.Pv.LocalLengthBound

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.WachCoordinates Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

section Coord

variable {LL O : Type} [Field LL] [CommRing O] [Algebra O LL] [IsDomain O]
  [IsPrincipalIdealRing O] [IsFractionRing O LL]

theorem integral_coordinate_of_relation (hinj : Function.Injective (algebraMap O LL)) {Q : Type} [AddCommGroup Q]
    [Module LL Q] {N : ℕ} (lam : Fin N → Q) (vbar : Q) (Rm R₀ : ℕ) (hR₀ : R₀ < Rm)
    (P : ℕ → LL) (hP : P R₀ ≠ 0) (cc : ℕ → Fin N → LL)
    (hrel : ∀ R < Rm, P R • vbar = ∑ k, cc R k • lam k) (L : LL)
    (hSL : ∀ (mm : Fin N → O) (θ : LL), (∀ R < Rm, ∑ k, algebraMap O LL (mm k) * cc R k = θ * P R) →
      ∃ o : O, algebraMap O LL o = L * θ) :
    ∃ o : Fin N → O, L • vbar = ∑ k, algebraMap O LL (o k) • lam k := by
  letI : Module O Q := Module.compHom Q (algebraMap O LL)
  have hsm : ∀ (a : O) (x : Q), a • x = algebraMap O LL a • x := fun _ _ => rfl
  haveI : IsScalarTower O LL Q := ⟨fun a b x => by rw [hsm, Algebra.smul_def, mul_smul]⟩
  haveI : NoZeroSMulDivisors O Q := ⟨fun {a x} h => by
    rw [hsm] at h
    rcases smul_eq_zero.mp h with h | h
    · exact Or.inl (hinj (by rw [h, map_zero]))
    · exact Or.inr h⟩
  set M' : Submodule O Q := Submodule.span O (Set.range lam) with hM'
  haveI : Module.Finite O M' := Module.Finite.span_of_finite O (Set.finite_range lam)
  haveI : Module.Free O M' := Module.free_of_finite_type_torsion_free'
  set bas := Module.Free.chooseBasis O M' with hbas
  set ι := Module.Free.ChooseBasisIndex O M'

  have hind : ∀ β : ι → LL, ∑ j, β j • ((bas j : M') : Q) = 0 → ∀ j, β j = 0 := by
    intro β hβ
    obtain ⟨⟨dn, hdn⟩, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
      (Finset.univ.image β)
    have hint : ∀ j, ∃ o : O, algebraMap O LL o = algebraMap O LL dn * β j := by
      intro j
      obtain ⟨o, ho⟩ := hd (β j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
      exact ⟨o, by rw [ho, Algebra.smul_def]⟩
    choose o ho using hint
    have h1 : ∑ j, o j • bas j = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero, hsm, ho, mul_smul]
      rw [← Finset.smul_sum, hβ, smul_zero]
    have h2 := (Fintype.linearIndependent_iff.mp bas.linearIndependent) o h1
    have hdn0 : algebraMap O LL dn ≠ 0 := by
      intro h
      exact nonZeroDivisors.ne_zero hdn (hinj (by rw [h, map_zero]))
    intro j
    have := ho j
    rw [h2 j, map_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hdn0

  have hlamM : ∀ k, lam k ∈ M' := fun k => Submodule.subset_span ⟨k, rfl⟩
  set mm : Fin N → ι → O := fun k j => bas.repr ⟨lam k, hlamM k⟩ j with hmm
  have hlam : ∀ k, lam k = ∑ j, algebraMap O LL (mm k j) • ((bas j : M') : Q) := by
    intro k
    have := congrArg (fun x : M' => (x : Q)) (bas.sum_repr ⟨lam k, hlamM k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hsm] at this
    exact this.symm

  have hcoord : ∀ R < Rm, ∀ vv : ι → LL, vbar = ∑ j, vv j • ((bas j : M') : Q) →
      ∀ j, P R * vv j = ∑ k, cc R k * algebraMap O LL (mm k j) := by
    intro R hR vv hv
    have h1 := hrel R hR
    simp only [hlam, Finset.smul_sum, smul_smul, hv] at h1
    rw [Finset.sum_comm] at h1
    have h2 : ∑ j, (P R * vv j - ∑ k, cc R k * algebraMap O LL (mm k j)) • ((bas j : M') : Q) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, Finset.sum_smul, smul_smul]
      rw [sub_eq_zero, h1]
    intro j
    exact sub_eq_zero.mp (hind _ h2 j)

  set vv : ι → LL := fun j => (P R₀)⁻¹ * ∑ k, cc R₀ k * algebraMap O LL (mm k j) with hvv
  have hv : vbar = ∑ j, vv j • ((bas j : M') : Q) := by
    have h1 := hrel R₀ hR₀
    have h2 : vbar = (P R₀)⁻¹ • ∑ k, cc R₀ k • lam k := by rw [← h1, inv_smul_smul₀ hP]
    rw [h2]
    simp only [hlam, Finset.smul_sum, smul_smul, hvv]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_smul]

  have hoj : ∀ j, ∃ o : O, algebraMap O LL o = L * vv j := by
    intro j
    refine hSL (fun k => mm k j) (vv j) fun R hR => ?_
    rw [mul_comm (vv j), hcoord R hR vv hv j]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  choose oj hoj using hoj
  have hmem : L • vbar ∈ M' := by
    have : L • vbar = ((∑ j, oj j • bas j : M') : Q) := by
      rw [hv, Finset.smul_sum]
      simp only [Submodule.coe_sum, Submodule.coe_smul, hsm, hoj, smul_smul]
    rw [this]
    exact Subtype.prop _
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp hmem
  exact ⟨o, by rw [← ho]; rfl⟩

end Coord

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem exponent_bound_second (l H bc bc1 S η : ℕ) (hl : 11 ≤ l) (hH1 : bc + S + η ≤ H) (hH2 : bc1 + S ≤ H)
    (hb1 : 1 ≤ bc1) (hby : (bc : ℝ) / l ≤ ((bc1 + S : ℕ) : ℝ)) :
    (((⌈((2 * bc + S + η : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉₊ + h2cp l (bc1 + S) bc : ℕ)) : ℝ) ≤
      Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ l H + ((bc1 + S : ℕ) : ℝ) - (bc : ℝ) / (l : ℝ) + Formalism.MainNotions.RamifiedCoefficientChains.lam l H + 3 := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hl1 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hsq : (0 : ℝ) < ((l : ℝ) - 1) ^ 2 := by positivity
  set y : ℕ := bc1 + S with hy
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
  have hyH : (y : ℝ) ≤ 2 * (H : ℝ) := by
    have : (y : ℝ) ≤ H := by exact_mod_cast hH2
    linarith [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)]
  have hlog0 : 0 ≤ Real.logb (l : ℝ) (y : ℝ) := Real.logb_nonneg (by linarith) hy1
  have hlogle : Real.logb (l : ℝ) (y : ℝ) ≤ Real.logb (l : ℝ) (2 * (H : ℝ)) :=
    Real.logb_le_logb_of_le (by linarith) (by linarith) hyH
  have hX : ((2 * bc + S + η : ℕ) : ℝ) ≤ 2 * (H : ℝ) := by
    have : (2 * bc + S + η : ℕ) ≤ 2 * H := by omega
    exact_mod_cast this
  have hσ := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ ((2 * bc + S + η : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1 by positivity)
  have hσ2 : ((2 * bc + S + η : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 ≤ 2 * (H : ℝ) / ((l : ℝ) - 1) ^ 2 :=
    div_le_div_of_nonneg_right hX hsq.le
  have hr0 : 0 ≤ (y : ℝ) - (bc : ℝ) / (l : ℝ) + 2 + Real.logb (l : ℝ) (y : ℝ) := by linarith
  have hc := Nat.ceil_lt_add_one hr0
  unfold h2cp
  unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ Formalism.MainNotions.RamifiedCoefficientChains.lam
  push_cast at hσ hσ2 ⊢
  linarith

theorem filtration_gap_vanishing [NeZero n] (W : LocWach PD LL O v n) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) {d : ℕ}
    {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ}
    (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (c : ZMod n) (hc : (c.val + d) % 2 = 0)
    (s : ℤ) (hs1 : (η : ℤ) ≤ s) (hs2 : s < (b c : ℤ)) :
    Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-s) = Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-(η : ℤ)) := by
  have hbij : Function.Bijective (algebraMap K₀ K) := hS.1.1
  have hT₂ : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  set τ := tauOf W hbij c with hτdef
  have hτ : τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb c :=
    AlgHom.ext fun x => tauOf_over W hbij c x
  rw [rk_filLev_eq W hbij hQ T₂ hT₂ c τ hτ, rk_filLev_eq W hbij hQ T₂ hT₂ c τ hτ]
  have hnj : ∀ x : ℤ, -s ≤ x → x < -(η : ℤ) → FildR PD T₂.ρ τ (x + 1) = FildR PD T₂.ρ τ x := by
    intro x h1 h2
    by_contra hne
    have := rk_jumps₂ W hE hC hQ hS c τ hτ x hne
    unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at this
    rw [if_pos hc] at this
    simp only [Set.mem_union, Set.mem_Icc] at this
    push_cast at this
    omega
  have key : ∀ k : ℕ, (k : ℤ) ≤ s - η → FildR PD T₂.ρ τ (-s + k) = FildR PD T₂.ρ τ (-s) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [show -s + ((k + 1 : ℕ) : ℤ) = (-s + k) + 1 by push_cast; ring,
        hnj _ (by omega) (by push_cast at hk; omega), ih (by push_cast at hk; omega)]
  have := key (s - η).toNat (by omega)
  rw [show -s + (((s - η).toNat : ℕ) : ℤ) = -(η : ℤ) by omega] at this
  exact this.symm

theorem comparison_linear_sum (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {N : ℕ} (o : Fin N → O)
    (wk : Fin N → W.DD T) (hw : ∀ k, wk k ∈ W.N T) :
    Formalism.MainNotions.ArcLiftingSetup.cmpD W T (∑ k, o k • wk k) =
      ∑ k, algebraMap O LL (o k) • Formalism.MainNotions.ArcLiftingSetup.cmpD W T (wk k) := by
  have hmem : ∑ k, o k • wk k ∈ W.N T := by
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [← algebraMap_smul (LetA O n)]
    exact (W.N T).smul_mem _ (hw k)
  have e : (⟨∑ k, o k • wk k, hmem⟩ : ↥(W.N T)) = ∑ k, o k • (⟨wk k, hw k⟩ : ↥(W.N T)) :=
    Subtype.ext (by simp)
  simp only [Formalism.MainNotions.ArcLiftingSetup.cmpD, dif_pos hmem, dif_pos (hw _), e, map_sum, W.cmp_smul]

end Formalism.MainNotions.N.Pv.LocalLengthBound

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.WachCoordinates Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem h2Bound_of_hypotheses [NeZero n] (W : LocWach PD LL O v n)
    [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (hinj : Function.Injective (algebraMap O LL))
    (hΔ : IsUnit ((W.DelF.card : ℕ) : O))
    (hC2 : Formalism.MainNotions.CrystallineLiftingInputs.PowerSeriesDVRFactorisation)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W)
    (hT2 : Formalism.MainNotions.CrystallineLiftingInputs.TTool2 W) (hTH : Formalism.MainNotions.CrystallineLiftingInputs.THor W)
    (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (hχ0 : algebraMap O LL (W.χΓ W.gam : O) ≠ 0)
    (hχ : ∀ i : ℤ, i ≠ 0 → (algebraMap O LL (W.χΓ W.gam : O)) ^ i ≠ 1)
    (hγN : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (c : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
      ∀ (x : W.DD T) (hx : x ∈ W.N T) (hγx : W.γ T x ∈ W.N T) (k : ℤ),
        W.levN T c ζ ⟨W.γ T x, hγx⟩ k = (algebraMap O LL (W.χΓ W.gam : O)) ^ k • W.levN T c ζ ⟨x, hx⟩ k)
    (hγA : ∀ (c : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ f : LetA O n,
      W.lev c ζ (W.γA W.gam f) = PowerSeries.rescale (algebraMap O LL (W.χΓ W.gam : O)) (W.lev c ζ f)) :
    H2Bound W := by
  intro d T₁ T₂ F b S η m hset c hc
  have hset' := hset
  obtain ⟨hCA, hl, hn, ⟨hDom, hDVR, hFrac⟩, -, hSur, -, -, hbig, hhalf⟩ := hset'
  haveI := hDom
  haveI := hDVR
  haveI := hFrac
  have hCA' := hCA
  obtain ⟨hbij, hs, hp2⟩ := hCA
  have hK1 : Module.finrank K₀ K = 1 := Formalism.MainNotions.UnusedSlot80.SatW.finrank_one_of_bij' hbij
  have hT₂ : IsCrys PD T₂.ρ := hSur.2.1
  obtain ⟨-, -, h9₂⟩ := h9 T₂ hT₂ hs hp2
  obtain ⟨hR, hmod₂⟩ := h9₂ hK1
  have h5₂ := h5 T₂ (boxM d b S η) (boxH d b S η) hT₂ (rk_jumpsLet₂ W hE hC hQ hset)
  have hN : GamN W := fun T hT i ζ hζ x hx k => hγN T hT i ζ hζ x x.2 hx k
  have hA' : GamA W := hγA
  have hcD : (c.val + d) % 2 = 0 := (Finset.mem_filter.mp hc).2
  have hcU : ((c - 1).val + d) % 2 ≠ 0 := by
    have := Formalism.MainNotions.RamifiedCoefficientChains.S9.parity_succ hn d (c - 1)
    rw [sub_add_cancel, hcD] at this
    exact fun h => this h.symm
  have hboxH : boxH d b S η (c - 1) = b (c - 1) + S := by unfold boxH; rw [if_neg hcU]
  have hboxM : boxM d b S η c = b c + S := by unfold boxM; rw [if_pos hcD]
  have hpu : ¬ IsUnit ((PD.p : ℕ) : O) := by
    intro hu
    have htop : Ideal.span {((PD.p : ℕ) : O)} = ⊤ := Ideal.span_singleton_eq_top.mpr hu
    have h1 : (1 : O) = 0 := by
      apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {((PD.p : ℕ) : O)})) 1
      intro k
      rw [htop, Ideal.top_pow, Submodule.top_smul]
      exact SModEq.top
    exact one_ne_zero h1

  have hl2 : 2 ≤ PD.p := by omega
  have haR := Formalism.MainNotions.RamifiedCoefficientChains.aR_nonneg PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) hl2
  have hb1 : ∀ i, 1 ≤ b i := by
    intro i
    have h1 := hbig i
    have h2 : (1 : ℝ) ≤ b i := by
      have : (0 : ℝ) ≤ η := by positivity
      linarith
    exact_mod_cast h2
  have hle : ∀ i, b i ≤ Finset.univ.sup b := fun i => Finset.le_sup (Finset.mem_univ i)
  have hH1 : b c + S + η ≤ Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η := by
    unfold Formalism.MainNotions.RamifiedCoefficientChains.hpar; have := hle c; omega
  have hH2 : b (c - 1) + S ≤ Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η := by
    unfold Formalism.MainNotions.RamifiedCoefficientChains.hpar; have := hle (c - 1); omega
  have hby : (b c : ℝ) / (PD.p : ℝ) ≤ ((b (c - 1) + S : ℕ) : ℝ) := by
    have h1 := hhalf (c - 1)
    have h2 : (b c : ℝ) ≤ ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S : ℕ) : ℝ) := by
      have : b c ≤ Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S := by unfold Formalism.MainNotions.RamifiedCoefficientChains.hpar; have := hle c; omega
      exact_mod_cast this
    have hl' : (2 : ℝ) ≤ PD.p := by exact_mod_cast hl2
    have h3 : (b c : ℝ) / PD.p ≤ (b c : ℝ) / 2 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hl'
    push_cast
    have : (0 : ℝ) ≤ S := by positivity
    linarith
  set X₀ : ℕ := 2 * b c + S + η with hX₀
  set σ : ℕ := ⌈(X₀ : ℝ) / ((PD.p : ℝ) - 1) ^ 2 + 1⌉₊ with hσ
  refine ⟨σ + h2cp PD.p (boxH d b S η (c - 1)) (b c), ?_, ?_⟩
  · rw [hboxH]
    exact exponent_bound_second PD.p _ (b c) (b (c - 1)) S η hl hH1 hH2 (hb1 _) hby
  intro ζ hζ u hu hu0 w hw K hK dd hdd hexp

  have hddF : ∀ s < (b c : ℤ), s ≠ 0 → dd s ∈ Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-(η : ℤ)) := by
    have hγw : W.γ T₂ w - w ∈ W.N T₂ := by
      obtain ⟨y', hy'N, -, hy'⟩ := hw.2.2.2
      rw [hy', pow_one]; exact (W.N T₂).smul_mem _ hy'N
    have hLv : ∀ (x : ↥(W.N T₂)) (k : ℤ), W.levN T₂ c ζ x k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-k) :=
      (h4 T₂ hT₂ c 0 ζ (by rwa [zero_add, pow_one])).1
    obtain ⟨d', ⟨m', hm'⟩, hde, hχd⟩ := gamma_levels_expansion W T₂ hs c ζ hLv _ hχ0
      (fun x hx hγx k => hγN T₂ hT₂ c ζ hζ x hx hγx k) (hγA c ζ hζ) u hu hu0 hK hγw
    obtain ⟨md, hmd⟩ := hdd
    have hdd' : dd = d' := div_unique (m := min md m') (LB_mono hmd (min_le_left _ _))
      (LB_mono hm' (min_le_right _ _)) u hu0 K (hexp.symm.trans hde)
    intro s hs hs0
    have hmem : dd s ∈ Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-s) := by
      have h1 := hχd s
      rw [← hdd'] at h1
      have hne : (algebraMap O LL (W.χΓ W.gam : O)) ^ s - 1 ≠ 0 := sub_ne_zero.mpr (hχ s hs0)
      have := Submodule.smul_mem _ (((algebraMap O LL (W.χΓ W.gam : O)) ^ s - 1)⁻¹) h1
      rwa [inv_smul_smul₀ hne] at this
    rcases le_or_gt s η with hsη | hsη
    · exact Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T₂ c 0 (by omega) hmem
    · rw [← filtration_gap_vanishing W hE hC hQ hset c hcD s (by omega) hs]; exact hmem

  obtain ⟨N, ak, wk, hakm, hwk, hKR⟩ := kernel_rank_bound W hT2 hTH h4 hN hA' hR hCA' hl hΔ T₂ hT₂ hmod₂
    (boxM d b S η) (boxH d b S η) h5₂ c ζ hζ η (b c) X₀ σ (Or.inr ⟨rfl, rfl, rfl⟩) (by omega)
    (by rw [hboxM]; omega) w hw.2.1 hw.1 K hK dd hdd u hu hu0 hexp hddF
  set Fl := Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-(η : ℤ)) with hFl
  set π := Fl.mkQ with hπ
  set Pc : LetA O n := Formalism.MainNotions.LiftingTheory.pk W 1 ^ boxH d b S η (c - 1) * Formalism.MainNotions.LiftingTheory.qp W ^ η with hPc
  set μ : Fin N → T₂.V ⊗[Qp] BdR := fun k => ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V)
    (φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (wk k)))) with hμ
  have hrel : ∀ R < b c + η, ((PD.p : LL) ^ σ * coeff R (W.lev c ζ Pc)) • π (dd 0) =
      ∑ k, coeff R (W.lev c ζ (ak k)) • π (μ k) := by
    intro R hR
    have h0 : π (((PD.p : LL) ^ σ * coeff R (W.lev c ζ Pc)) • dd 0 -
        ∑ k, coeff R (W.lev c ζ (ak k)) • μ k) = 0 := by
      rw [hπ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hKR R hR
    rw [map_sub, map_sum, sub_eq_zero, map_smul] at h0
    rw [h0]
    exact Finset.sum_congr rfl fun k _ => map_smul _ _ _
  obtain ⟨⟨Sq, hSq, hqp⟩, -, hpku⟩ := expRing_of W hR hCA' c ζ hζ
  have hPη : (PD.p : LL) ^ σ * coeff η (W.lev c ζ Pc) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ (p_ne_zero_LL W)) ?_
    rw [hPc, map_mul, map_pow, map_pow, hqp, mul_pow, ← mul_assoc, coeff_mul_X_pow', if_pos le_rfl,
      Nat.sub_self, coeff_zero_eq_constantCoeff, map_mul, map_pow, map_pow]
    exact mul_ne_zero (pow_ne_zero _ (hpku.map constantCoeff).ne_zero)
      (pow_ne_zero _ (hSq.map constantCoeff).ne_zero)
  have hSL : ∀ (mm : Fin N → O) (θ : LL), (∀ R < b c + η,
      ∑ k, algebraMap O LL (mm k) * coeff R (W.lev c ζ (ak k)) =
        θ * ((PD.p : LL) ^ σ * coeff R (W.lev c ζ Pc))) →
      ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ (σ + h2cp PD.p (boxH d b S η (c - 1)) (b c)) * θ := by
    intro mm θ hθ
    have hα : ∑ k, mm k • ak k ∈ W.AΔ := Subalgebra.sum_mem _ fun k _ => W.AΔ.smul_mem (hakm k) _
    obtain ⟨o, ho⟩ := scalar_integrality_relation hC2 hR hCA' hpu hinj c ζ hζ (boxH d b S η (c - 1)) (b c) η (hb1 c)
      (by rw [hboxH]; exact hby) _ hα ((PD.p : LL) ^ σ * θ) (fun R hR => by
        rw [map_sum, map_sum]
        simp only [map_smul, coeff_smul]
        simp only [Algebra.smul_def]
        rw [hθ R hR, qP_eq_qp]
        ring)
    exact ⟨o, by rw [ho, pow_add]; ring⟩
  obtain ⟨o, ho⟩ := integral_coordinate_of_relation hinj (fun k => π (μ k)) (π (dd 0)) (b c + η) η (by have := hb1 c; omega)
    (fun R => (PD.p : LL) ^ σ * coeff R (W.lev c ζ Pc)) hPη (fun R k => coeff R (W.lev c ζ (ak k)))
    hrel _ hSL
  refine ⟨∑ k, o k • wk k, Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hwk k), ?_⟩
  rw [comparison_linear_sum W T₂ o wk (fun k => (hwk k).1)]
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, ← hπ]
  simp only [map_sum, map_smul, map_sub]
  rw [ho, sub_eq_zero]
