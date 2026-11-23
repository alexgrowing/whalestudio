import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.ZetaZeroFreeRegion
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.RamificationTwoAndConjugationAtQAndD
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Development.AutomorphicArithmetic.ConductorsKronecker.dataField
import Development.AutomorphicArithmetic.ConductorsKronecker.Imports
import Development.AutomorphicArithmetic.ConductorsKronecker.kronecker
import Development.AutomorphicArithmetic.ConductorsKronecker.RecSurj
import Development.AutomorphicArithmetic.ConductorsKronecker.InertiaD
import Development.AutomorphicArithmetic.ConductorsKronecker.ChCond
import Development.AutomorphicArithmetic.ConductorsKronecker.IsInertIff
import Development.AutomorphicArithmetic.PrimitiveCosets.hostFactsS
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChBalance
import Development.AutomorphicArithmetic.ConductorsKronecker.CostPropositionBasicBound
import Formalism.LocalRingCardinality.HostCls
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion.Br

open DirichletCharacter Filter

theorem prim_unique {N1 N2 : ℕ} [NeZero N1] [NeZero N2] (χ1 : DirichletCharacter ℂ N1)
    (χ2 : DirichletCharacter ℂ N2) (h1 : χ1.IsPrimitive) (h2 : χ2.IsPrimitive) (M : ℕ) (hM : M ≠ 0)
    (h : ∀ p : ℕ, p.Prime → ¬ p ∣ M → χ1 (p : ZMod N1) = χ2 (p : ZMod N2)) :
    (∀ n : ℕ, χ1 (n : ZMod N1) = χ2 (n : ZMod N2)) ∧ (χ1 = 1 ↔ χ2 = 1) := by
  have hall : ∀ n : ℕ, χ1 (n : ZMod N1) = χ2 (n : ZMod N2) := by
    refine Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.prim_unique χ1 χ2 h1 h2 (2 * M) (by omega) ?_
    intro a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at ha
      omega
    have hl : ∀ p ∈ a.primeFactorsList, p.Prime ∧ ¬ p ∣ M := by
      intro p hp
      have hp' := Nat.prime_of_mem_primeFactorsList hp
      refine ⟨hp', fun hpM => ?_⟩
      have hc := Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactorsList hp) ha
      exact (Nat.Prime.coprime_iff_not_dvd hp').mp hc (dvd_mul_of_dvd_right hpM 2)
    have key : ∀ l : List ℕ, (∀ p ∈ l, p.Prime ∧ ¬ p ∣ M) →
        χ1 ((l.prod : ℕ) : ZMod N1) = χ2 ((l.prod : ℕ) : ZMod N2) := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons p l ih =>
        intro hl'
        simp only [List.prod_cons, Nat.cast_mul, map_mul]
        rw [h p (hl' p (by simp)).1 (hl' p (by simp)).2, ih (fun q hq => hl' q (by simp [hq]))]
    have := key a.primeFactorsList hl
    rwa [Nat.prod_primeFactorsList ha0] at this
  refine ⟨hall, ?_⟩
  have triv : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ = 1 → N = 1 := by
    intro N _ χ hp h1
    rw [DirichletCharacter.IsPrimitive, h1, DirichletCharacter.conductor_one] at hp
    exact hp.symm
  have allone : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), (∀ n : ℕ, χ (n : ZMod N) = 1) → χ = 1 := by
    intro N _ χ h
    ext u
    have := h (u : ZMod N).val
    rw [ZMod.natCast_zmod_val] at this
    rw [this, MulChar.one_apply_coe]
  have one_vals : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ = 1 →
      ∀ n : ℕ, χ (n : ZMod N) = 1 := by
    intro N _ χ hp h1 n
    have hN := triv χ hp h1
    subst hN
    rw [h1]
    exact MulChar.one_apply (isUnit_of_subsingleton _)
  constructor
  · intro h'
    exact allone χ2 (fun n => (hall n).symm.trans (one_vals χ1 h1 h' n))
  · intro h'
    exact allone χ1 (fun n => (hall n).trans (one_vals χ2 h2 h' n))

private lemma ev_log_lemma (A B r : ℝ) (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop, A + B * Real.log x ≤ x ^ r := by
  have h1 := ((isLittleO_log_rpow_atTop hr).const_mul_left B).bound (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 := (tendsto_rpow_atTop hr).eventually_ge_atTop (2 * |A|)
  filter_upwards [h1, h2, eventually_gt_atTop 0] with x hx1 hx2 hx0
  have hxr : 0 ≤ x ^ r := Real.rpow_nonneg hx0.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hxr] at hx1
  have e1 := le_abs_self A
  have e2 := le_abs_self (B * Real.log x)
  linarith

theorem ev_exp (A K r c : ℝ) (hA : 0 < A) (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, A * x ^ K ≤ Real.exp (c * x ^ r) := by
  filter_upwards [ev_log_lemma (Real.log A / c) (K / c) r hr, eventually_gt_atTop 0] with x hx hx0
  rw [Real.rpow_def_of_pos hx0, ← Real.exp_log hA, ← Real.exp_add, Real.exp_le_exp]
  have h2 : Real.log A + Real.log x * K = c * (Real.log A / c + K / c * Real.log x) := by
    field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_left hx hc.le

theorem ev_log (A B r : ℝ) (hr : 0 < r) : ∀ᶠ x : ℝ in atTop, A + B * Real.log x ≤ x ^ r :=
  ev_log_lemma A B r hr

theorem ev_rpow_ge (A r : ℝ) (hr : 0 < r) : ∀ᶠ x : ℝ in atTop, A ≤ x ^ r :=
  (tendsto_rpow_atTop hr).eventually_ge_atTop A

end Formalism.MainNotions.ZetaZeroFreeRegion.Br

end

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion.Br

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions Formalism.LFunctionChainParameters Finset
open scoped Pointwise ComplexConjugate

open Classical

instance factQ (D : D7) : Fact D.host.q.Prime := ⟨D.host.hyp.1⟩
instance factD (D : D7) : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩

abbrev MM (D : D7) : Type := D5.E0 × D.R.A

def AD (D : D7) : characterSumData.ArithData D.R.A := UpperTheory.Comparison₂.arith D.host.toHostRaw

def tE (D : D7) : D.R.GG ≃ MM D :=
  Equiv.ofBijective (fun g => (UpperTheory.Comparison₂.toE D.R.toFrame g).toAdd)
    (Multiplicative.toAdd.bijective.comp (UpperTheory.Comparison₂.toE_bij D.R.toFrame).1)

variable (D : D7)

theorem tE_mul (g g' : D.R.GG) : tE D (g * g') = tE D g + tE D g' := by
  show (UpperTheory.Comparison₂.toE D.R.toFrame (g * g')).toAdd = (UpperTheory.Comparison₂.toE D.R.toFrame g).toAdd + (UpperTheory.Comparison₂.toE D.R.toFrame g').toAdd
  rw [map_mul, toAdd_mul]
theorem tE_one : tE D 1 = 0 := by
  show (UpperTheory.Comparison₂.toE D.R.toFrame 1).toAdd = 0
  rw [map_one, toAdd_one]
theorem tE_pow (g : D.R.GG) (i : ℕ) : tE D (g ^ i) = i • tE D g := by
  show (UpperTheory.Comparison₂.toE D.R.toFrame (g ^ i)).toAdd = i • (UpperTheory.Comparison₂.toE D.R.toFrame g).toAdd
  rw [map_pow, toAdd_pow]
theorem tE_symm_add (x y : MM D) : (tE D).symm (x + y) = (tE D).symm x * (tE D).symm y := by
  apply (tE D).injective
  rw [tE_mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
theorem tE_symm_zero : (tE D).symm 0 = 1 := by
  rw [Equiv.symm_apply_eq, tE_one]

def aOf (ψ : Chr D) : AddChar (MM D) ℂ where
  toFun x := ((ψ ((tE D).symm x) : ℂˣ) : ℂ)
  map_zero_eq_one' := by simp [tE_symm_zero]
  map_add_eq_mul' x y := by simp [tE_symm_add]

def cOf (φ : AddChar (MM D) ℂ) : Chr D :=
  MonoidHom.toHomUnits
    { toFun := fun g => φ (tE D g)
      map_one' := by simp [tE_one]
      map_mul' := fun g g' => by simp [tE_mul, AddChar.map_add_eq_mul] }

theorem cOf_apply (φ : AddChar (MM D) ℂ) (g : D.R.GG) : ((cOf D φ g : ℂˣ) : ℂ) = φ (tE D g) := rfl
theorem aOf_apply (ψ : Chr D) (x : MM D) : aOf D ψ x = ((ψ ((tE D).symm x) : ℂˣ) : ℂ) := rfl

def chE : AddChar (MM D) ℂ ≃ Chr D where
  toFun := cOf D
  invFun := aOf D
  left_inv φ := by ext x; simp [aOf_apply, cOf_apply]
  right_inv ψ := by ext g; simp [aOf_apply, cOf_apply]

theorem aOf_cOf (φ : AddChar (MM D) ℂ) : aOf D (cOf D φ) = φ := (chE D).left_inv φ
theorem cOf_aOf (ψ : Chr D) : cOf D (aOf D ψ) = ψ := (chE D).right_inv ψ
theorem cOf_zero : cOf D 0 = 1 := by
  refine MonoidHom.ext fun g => Units.ext ?_
  rw [cOf_apply, AddChar.zero_apply]
  simp
theorem aOf_one : aOf D 1 = 0 := by
  ext x
  rw [aOf_apply, AddChar.zero_apply]
  simp
theorem cOf_eq_one_iff (φ : AddChar (MM D) ℂ) : cOf D φ = 1 ↔ φ = 0 := by
  constructor
  · intro h
    rw [← aOf_cOf D φ, h, aOf_one]
  · intro h
    rw [h, cOf_zero]
theorem aOf_eq_zero_iff (ψ : Chr D) : aOf D ψ = 0 ↔ ψ = 1 := by
  constructor
  · intro h
    rw [← cOf_aOf D ψ, h, cOf_zero]
  · intro h
    rw [h, aOf_one]

theorem exists_prime_over (p : ℕ) (hp : p.Prime) :
    ∃ P : Ideal (𝓞 D.host.E), P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
  haveI hp' : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨Q, -, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 D.host.E)
    (Ideal.span {(p : ℤ)}) ⊥ (Ideal.comap_bot_le_of_injective _ (RingHom.injective_int _))
  exact ⟨Q, hQ, ⟨hc.symm⟩⟩

theorem fieldFacts (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 D.host.E)) (hP : P.IsPrime)
    (hL : P.LiesOver (Ideal.span {(p : ℤ)})) (σ : D.host.E ≃ₐ[ℚ] D.host.E) :
    ((∀ x : 𝓞 D.host.E, σ • x - x ∈ P) ↔
      tE D (D.host.galE σ) ∈ (AD D).inertia p) ∧
    (IsArithFrobAt ℤ σ P ↔
      tE D (D.host.galE σ) - (AD D).frob p ∈ (AD D).inertia p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hP
  haveI := hL
  exact Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.fld D p P σ

theorem frob_spec (p : ℕ) (hp : p.Prime) :
    tE D (frob D p) - (AD D).frob p ∈ (AD D).inertia p := by
  obtain ⟨P, hP, hL⟩ := exists_prime_over D p hp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hP
  haveI := hL
  exact Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.frob_mem D p P

theorem mem_inertiaAt_iff (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 D.host.E)) (hP : P.IsPrime)
    (hL : P.LiesOver (Ideal.span {(p : ℤ)})) (g : D.R.GG) :
    g ∈ inerP D P ↔ tE D g ∈ (AD D).inertia p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hP
  haveI := hL
  exact Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.mem_inerP D p P g

theorem dvd_discr_iff_ram (p : ℕ) (hp : p.Prime) :
    ((p : ℤ) ∣ discr D.host.E) ↔ 1 < (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 D.host.E) :=
  Formalism.MainNotions.GlobalTheoryTheory.jnt_dvd_discr_iff_ram D p hp

theorem unram_iff (p : ℕ) :
    Unram D p ↔ p.Prime ∧ ¬ p ∣ D.host.condN :=
  ⟨fun h => ⟨h.1, Formalism.MainNotions.GlobalTheoryTheory.ConductorDivisibility.not_dvd_condN_of_unram' D p h⟩,
    fun h => Formalism.MainNotions.GlobalTheoryTheory.ConductorDivisibility.jnt_unram D p h.1 h.2⟩

theorem inertia_unram {p : ℕ} (h : Unram D p) : (AD D).inertia p = ⊥ := by
  have hu := (LHost.unramified_spec D.host.condN p (Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.hostN_ne D) h.1
    ((unram_iff D p).mp h).2).1
  show Subgroup.toAddSubgroup' ((LHost.localUnits D.host.condN p).map (UpperTheory.Comparison₂.recH D.host.toHostRaw)) = ⊥
  rw [hu, Subgroup.map_bot]
  rfl

theorem frob_unram {p : ℕ} (h : Unram D p) : tE D (frob D p) = (AD D).frob p := by
  have h1 := frob_spec D p h.1
  rw [inertia_unram D h, AddSubgroup.mem_bot, sub_eq_zero] at h1
  exact h1

instance neZeroN : NeZero D.host.condN :=
  ⟨D.host.condN_pos.ne'⟩

def chi0 (ψ : Chr D) : DirichletCharacter ℂ D.host.condN :=
  LHost.dirChar (UpperTheory.Comparison₂.recH D.host.toHostRaw) (aOf D ψ)

theorem primVal_eq (ψ : Chr D) (n : ℕ) (hn : n ≠ 0) :
    characterSumData.primVal (AD D) (aOf D ψ) n =
      (chi0 D ψ).primitiveCharacter (n : ZMod (chi0 D ψ).conductor) :=
  LHost.primitive_value_primitive _ _ _ _ (aOf D ψ) n (Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.hostN_ne D) hn

def chiP (ψ : Chr D) : Σ N : ℕ+, DirichletCharacter ℂ N :=
  ⟨⟨(chi0 D ψ).conductor, Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero _)⟩,
    (chi0 D ψ).primitiveCharacter⟩

theorem primVal_unram (ψ : Chr D) {p : ℕ} (h : Unram D p) :
    characterSumData.primVal (AD D) (aOf D ψ) p = ((ψ (frob D p) : ℂˣ) : ℂ) := by
  have hp := h.1
  rw [characterSumData.primVal, Nat.Prime.primeFactors hp, Finset.prod_singleton, Nat.Prime.factorization_self hp, one_smul,
    inertia_unram D h, ← frob_unram D h]
  simp [characterSumData.cosetMean, aOf_apply, Finset.sum_filter, Finset.card_filter]

theorem reads0 (ψ : Chr D) : Reads D ψ (chiP D ψ) := by
  exact Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.reads_model D ψ

theorem primitive_reading_exists : adm10 D := primitive_reading_holds D

theorem prim_spec (ψ : Chr D) : Reads D ψ (prim D ψ) :=
  Formalism.MainNotions.GlobalTheoryTheory.ConductorDivisibility.jnt_prim_reads D ψ ⟨_, reads0 D ψ⟩

theorem primitiveCharacter_chi0_eq_one_iff (ψ : Chr D) : (chi0 D ψ).primitiveCharacter = 1 ↔ ψ = 1 := by
  constructor
  · intro h
    by_contra hψ
    exact Formalism.MainNotions.GlobalTheoryTheory.ConductorDivisibility.jnt_reads_ne_one D ψ (chiP D ψ) (reads0 D ψ) hψ h
  · intro h
    subst h
    exact Formalism.MainNotions.GlobalTheoryTheory.ConductorDivisibility.jnt_reads_one D (chiP D 1) (reads0 D 1)

theorem prim_both (ψ : Chr D) :
    (∀ n : ℕ, (prim D ψ).2 (n : ZMod (prim D ψ).1) =
      (chi0 D ψ).primitiveCharacter (n : ZMod (chi0 D ψ).conductor)) ∧
    ((prim D ψ).2 = 1 ↔ (chi0 D ψ).primitiveCharacter = 1) := by
  have hU : ∀ p : ℕ, p.Prime → ¬ p ∣ D.host.condN →
      (prim D ψ).2 (p : ZMod (prim D ψ).1) = (chiP D ψ).2 (p : ZMod (chiP D ψ).1) := by
    intro p hp hpN
    have hu := Formalism.MainNotions.GlobalTheoryTheory.ConductorDivisibility.jnt_unram D p hp hpN
    rw [(prim_spec D ψ).2 p hu, (reads0 D ψ).2 p hu]
  exact prim_unique (prim D ψ).2 (chiP D ψ).2 (prim_spec D ψ).1 (reads0 D ψ).1 D.host.condN
    (Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.hostN_ne D) hU

theorem prim_val (ψ : Chr D) (n : ℕ) (hn : n ≠ 0) :
    (prim D ψ).2 (n : ZMod (prim D ψ).1) = characterSumData.primVal (AD D) (aOf D ψ) n := by
  rw [(prim_both D ψ).1 n, primVal_eq D ψ n hn]

theorem prim_one_iff (ψ : Chr D) : (prim D ψ).2 = 1 ↔ ψ = 1 :=
  (prim_both D ψ).2.trans (primitiveCharacter_chi0_eq_one_iff D ψ)

def ell (φ : AddChar (MM D) ℂ) : ℂ := Lp D (cOf D φ)

theorem GPsi_eq (φ : AddChar (MM D) ℂ) (y : ℝ) :
    characterSumData.GPsi (AD D) (ell D) φ y = Gc D (cOf D φ) y := by
  unfold characterSumData.GPsi Gc gChi
  by_cases h : φ = 0
  · have h1 : (prim D (cOf D φ)).2 = 1 := (prim_one_iff D _).2 ((cOf_eq_one_iff D φ).2 h)
    rw [if_pos h, if_pos h1, G_eq_Gz]
  · have h1 : (prim D (cOf D φ)).2 ≠ 1 := fun h' => h ((cOf_eq_one_iff D φ).1 ((prim_one_iff D _).1 h'))
    rw [if_neg h, if_neg h1]
    unfold sumLamChi ell Lp
    congr 1
    refine Finset.sum_congr rfl (fun n hn => ?_)
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hy0 : 0 ≤ y := by
      by_contra hneg
      rw [Nat.floor_eq_zero.2 (by linarith)] at hn2
      omega
    have hy : (n : ℝ) ≤ y := (Nat.cast_le.2 hn2).trans (Nat.floor_le hy0)
    have hp : 0 ≤ y / n - 1 := by rw [sub_nonneg, le_div_iff₀ hn0]; linarith
    rw [prim_val D _ n (by omega), aOf_cOf, max_eq_left hp]

end Formalism.MainNotions.ZetaZeroFreeRegion.Br

end

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion.Br

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions Formalism.LFunctionChainParameters Finset
open scoped Pointwise ComplexConjugate

open Classical

variable (D : D7)

def tH (t : HH D) : D.R.A := t

theorem inPhi_iff (g : D.R.GG) : D5.InPhi (tE D g) ↔ g ∈ D.R.Psi :=
  LHost.sgn2_toAdd_eq_zero_iff g.1.2

theorem inPhi_symm_iff (x : MM D) : (tE D).symm x ∈ D.R.Psi ↔ D5.InPhi x := by
  rw [← inPhi_iff, Equiv.apply_symm_apply]

theorem tE_cc : tE D (D.R.cc) = D5.cconj := rfl
theorem top_place_of_first_tau (t : HH D) : tE D (D.R.tau1 t) = D5.topPl (tH D t) := rfl
theorem thick_place_of_second_tau (t : HH D) : tE D (D.R.tau2 t) = D5.thickPl (tH D t) := rfl
theorem tE_iner : tE D (iner D) = characterSumData.sgc0 := rfl

theorem tE_rho (t : HH D) (g : D.R.GG) :
    tE D (rho D (D.R.tau1 t) g) = characterSumData.partner (tH D t) (tE D g) := by
  unfold rho characterSumData.partner
  rw [tE_mul, tE_mul, tE_cc, top_place_of_first_tau]

def wM (w : D.R.GG → ℝ) : MM D → ℝ := fun x => w ((tE D).symm x)

theorem wM_partner (w : D.R.GG → ℝ) (t : HH D) (g : D.R.GG) :
    wM D w (characterSumData.partner (tH D t) (tE D g)) = w (rho D (D.R.tau1 t) g) := by
  unfold wM
  rw [← tE_rho, Equiv.symm_apply_apply]

theorem rho_mem (t : HH D) {g : D.R.GG} (hg : g ∉ D.R.Psi) :
    rho D (D.R.tau1 t) g ∈ D.R.Psi := by
  rw [← inPhi_iff, tE_rho]
  exact characterSumData.partner_inPhi _ (fun h => hg ((inPhi_iff D g).1 h))

theorem isInert_iff (p : ℕ) : characterSumData.IsInert (AD D) p ↔ InertK D p := by
  refine (UpperTheory.GL.isInert_iff D.host.toHostAx p).trans ?_
  unfold InertK Host.cls
  refine and_congr_right fun hp => ?_
  rw [primeClass_eq_signal_iff' hp, primeClass_eq_inert_iff_symbols hp]
  constructor
  · rintro ⟨hN, hJ⟩
    rcases D.host.psAt_eq_one_or (hp.coprime_iff_not_dvd.2 hN) with h | h
    · exact Or.inl ⟨hN, hJ, h⟩
    · exact Or.inr ⟨hN, hJ, h⟩
  · rintro (⟨hN, hJ, -⟩ | ⟨hN, hJ, -⟩) <;> exact ⟨hN, hJ⟩

theorem inertK_unram {p : ℕ} (h : InertK D p) : Unram D p := by
  obtain ⟨hp, hN, -⟩ := (UpperTheory.GL.isInert_iff D.host.toHostAx p).1 ((isInert_iff D p).2 h)
  exact (unram_iff D p).2 ⟨hp, hN⟩

theorem term_zero {a W : ℝ} {N M : ℕ} (hW : 0 < W) (hN : a / W ≤ N) (hM : N < M) :
    max (a / (M : ℝ) - W) 0 = 0 := by
  have h2 : (N : ℝ) < M := by exact_mod_cast hM
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hM0 : (0 : ℝ) < M := lt_of_le_of_lt hN0 h2
  have h1 : a ≤ N * W := (div_le_iff₀ hW).mp hN
  have h3 : a / M ≤ W := by
    rw [div_le_iff₀ hM0]
    nlinarith
  exact max_eq_right (by linarith)

theorem gD_spec (i : ℕ) :
    tE D (gD D i) - i • (AD D).frob (AD D).d ∈ (AD D).inertia (AD D).d ∧ ¬ D5.InPhi (tE D (gD D i)) := by
  have h0 : tE D (frob D D.host.d ^ i) - i • (AD D).frob (AD D).d ∈ (AD D).inertia (AD D).d := by
    rw [tE_pow, ← smul_sub]
    exact AddSubgroup.nsmul_mem _ (frob_spec D D.host.d D.host.hyp.2.1) i
  have hs : characterSumData.sgc0 ∈ (AD D).inertia (AD D).d :=
    ((UpperTheory.GL.inertia_d D.host.toHostAx).1 _).2 (Or.inr rfl)
  have hin : iner D ∉ D.R.Psi := by
    rw [Formalism.HC.Frame.mem_Psi_iff]; show (sgc0).2 ≠ 1; decide
  unfold gD
  by_cases hm : frob D D.host.d ^ i ∈ D.R.Psi
  · rw [if_neg (by tauto)]
    constructor
    · rw [tE_mul, tE_iner, add_sub_right_comm]
      exact AddSubgroup.add_mem _ h0 hs
    · rw [inPhi_iff, Subgroup.mul_mem_cancel_left _ hm]
      exact hin
  · rw [if_pos hm]
    exact ⟨h0, by rw [inPhi_iff]; exact hm⟩

section vonMangoldtClassSum
variable (a : ℝ) (w : D.R.GG → ℝ) (hw : ∀ ρ ∈ D.R.Psi, 0 < w ρ) (N : ℕ)
  (hN : ∀ ρ ∈ D.R.Psi, a / w ρ ≤ N) (t : HH D)
include hw hN

theorem primePowerSum_eq_local {p : ℕ} (hp : InertK D p) :
    askP D a w (D.R.tau1 t) p = characterSumData.askP (AD D) N a (tH D t) (wM D w) p := by
  have hU := inertK_unram D hp
  have hfr := frob_unram D hU
  unfold askP characterSumData.askP
  rw [tsum_eq_sum (s := Icc 1 N), Finset.sum_filter]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi1 := (Finset.mem_Icc.1 hi).1
    have e1 : i • (AD D).frob p = tE D (frob D p ^ i) := by rw [tE_pow, hfr]
    rw [e1, wM_partner]
    by_cases hm : frob D p ^ i ∈ D.R.Psi
    · rw [if_neg (by tauto), if_neg (by rw [inPhi_iff]; tauto)]
    · rw [if_pos ⟨hi1, hm⟩, if_pos (by rw [inPhi_iff]; exact hm)]
  · intro i hi
    by_cases hc : 1 ≤ i ∧ frob D p ^ i ∉ D.R.Psi
    · rw [if_pos hc]
      have hiN : N < i := by
        by_contra hcon
        exact hi (Finset.mem_Icc.2 ⟨hc.1, by omega⟩)
      have hpi : N < p ^ i := hiN.trans (Nat.lt_pow_self hp.1.one_lt)
      have := term_zero (a := a) (hw _ (rho_mem D t hc.2)) (hN _ (rho_mem D t hc.2)) hpi
      rwa [Nat.cast_pow] at this
    · rw [if_neg hc]

theorem primePowerSum_eq_zero_of_cutoff_lt {p : ℕ} (hpN : N < p) :
    characterSumData.askP (AD D) N a (tH D t) (wM D w) p = 0 := by
  unfold characterSumData.askP
  refine Finset.sum_eq_zero (fun i hi => ?_)
  obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
  have hi1' := (Finset.mem_Icc.1 hi1).1
  have hpi : N < p ^ i := lt_of_lt_of_le hpN (Nat.le_self_pow (by omega) p)
  have hρ : (tE D).symm (characterSumData.partner (tH D t) (i • (AD D).frob p)) ∈ D.R.Psi := by
    rw [inPhi_symm_iff]; exact characterSumData.partner_inPhi _ hi2
  have := term_zero (a := a) (hw _ hρ) (hN _ hρ) hpi
  rwa [Nat.cast_pow] at this

theorem askD_eq :
    askD D a w (D.R.tau1 t) = characterSumData.askD (AD D) N a (tH D t) (wM D w) := by
  unfold askD characterSumData.askD
  rw [tsum_eq_sum (s := Icc 1 N)]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi1 := (Finset.mem_Icc.1 hi).1
    rw [if_pos hi1]
    obtain ⟨g0, -, huniq⟩ := (UpperTheory.GL.inertia_d D.host.toHostAx).2.2 i
    have hg := gD_spec D i
    rw [Finset.sum_eq_single_of_mem (tE D (gD D i)) (by simp only [mem_filter, mem_univ, true_and]; exact hg)]
    · rw [wM_partner]; rfl
    · intro b hb hne
      simp only [mem_filter, mem_univ, true_and] at hb
      exact absurd ((huniq b hb).trans (huniq _ hg).symm) hne
  · intro i hi
    by_cases hc : 1 ≤ i
    · rw [if_pos hc]
      have hiN : N < i := by
        by_contra hcon
        exact hi (Finset.mem_Icc.2 ⟨hc, by omega⟩)
      have hpi : N < D.host.d ^ i := hiN.trans (Nat.lt_pow_self D.host.hyp.2.1.one_lt)
      have hg : gD D i ∉ D.R.Psi := fun h => (gD_spec D i).2 ((inPhi_iff D _).2 h)
      have := term_zero (a := a) (hw _ (rho_mem D t hg)) (hN _ (rho_mem D t hg)) hpi
      rwa [Nat.cast_pow] at this
    · rw [if_neg hc]

theorem ASK_eq :
    ASKjt D a w (D.R.tau1 t) = characterSumData.ASK (AD D) N a (tH D t) (wM D w) := by
  unfold ASKjt characterSumData.ASK
  rw [askD_eq D a w hw N hN t]
  congr 1
  rw [tsum_eq_sum (s := range (N + 1)), Finset.sum_filter]
  · refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : InertK D p
    · rw [if_pos hp, if_pos ((isInert_iff D p).2 hp), primePowerSum_eq_local D a w hw N hN t hp]
    · rw [if_neg hp, if_neg (fun h => hp ((isInert_iff D p).1 h))]
  · intro p hp
    by_cases hI : InertK D p
    · rw [if_pos hI, primePowerSum_eq_local D a w hw N hN t hI, primePowerSum_eq_zero_of_cutoff_lt D a w hw N hN t (by
        simpa using hp), mul_zero]
    · rw [if_neg hI]

end vonMangoldtClassSum

theorem sum_Phi {β : Type*} [AddCommMonoid β] (F : D.R.GG → β) :
    ∑ x ∈ D5.PhiSet (H := D.R.A), F ((tE D).symm x) = ∑ g ∈ PhiF D, F g := by
  refine Finset.sum_equiv (tE D).symm (fun x => ?_) (fun _ _ => rfl)
  simp only [D5.PhiSet, PhiF, mem_filter, mem_univ, true_and, inPhi_symm_iff]

theorem sum_notPhi {β : Type*} [AddCommMonoid β] (F : D.R.GG → β) :
    ∑ x ∈ univ.filter (fun x : MM D => ¬ D5.InPhi x), F ((tE D).symm x) = ∑ g ∈ notPhiF D, F g := by
  refine Finset.sum_equiv (tE D).symm (fun x => ?_) (fun _ _ => rfl)
  simp only [notPhiF, mem_filter, mem_univ, true_and, inPhi_symm_iff]

theorem card_HA : Fintype.card D.R.A = D.R.n := D.R.card_A

theorem card_PhiSet : (D5.PhiSet (H := D.R.A)).card = D.R.f := by
  have h := D5.Bal.card_G_eq (H := D.R.A)
  have h2 : Fintype.card (MM D) = 4 * D.R.n := by
    rw [Fintype.card_prod, Fintype.card_prod, ZMod.card, card_HA]
  rw [h2] at h
  have h3 : 4 * D.R.n = 2 * (D5.PhiSet (H := D.R.A)).card := by exact_mod_cast h
  unfold Ranks.f
  omega

theorem cOf_chC : cOf D characterSumData.chC = chC D := by
  ext g
  rw [cOf_apply]
  have h1 : (characterSumData.chC : AddChar (MM D) ℂ) (tE D g) = if (tE D g).1.1 = 0 then 1 else -1 := rfl
  rw [h1]
  have h2 : ((chC D g : ℂˣ) : ℂ) = (((g.1.2 : ℤˣ) : ℤ) : ℂ) := rfl
  rw [h2]
  by_cases hg : g ∈ D.R.Psi
  · rw [if_pos (show (tE D g).1.1 = 0 from (inPhi_iff D g).2 hg), (Formalism.HC.Frame.mem_Psi_iff g).1 hg]; simp
  · rw [if_neg (show ¬ (tE D g).1.1 = 0 from fun h => hg ((inPhi_iff D g).1 h))]
    have : g.1.2 = -1 := (Int.units_eq_one_or g.1.2).resolve_left hg
    rw [this]; simp

theorem MAIN_eq (a : ℝ) (w : D.R.GG → ℝ) : characterSumData.MAIN (ell D) a (wM D w) = MAINjt D a w := by
  unfold characterSumData.MAIN MAINjt ell wM
  rw [cOf_chC, card_PhiSet, sum_Phi D (fun g => Real.log (w g))]

theorem De_eq (a : ℝ) (w : D.R.GG → ℝ) (t : HH D) :
    characterSumData.De (AD D) (ell D) a (tH D t) (wM D w) = Dejt D a w (D.R.tau1 t) := by
  unfold characterSumData.De Dejt
  rw [card_PhiSet, ← sum_notPhi]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← finsum_comp_equiv (chE D), finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl (fun φ _ => ?_)
  have e1 : wM D w (characterSumData.partner (tH D t) x) = w (rho D (D.R.tau1 t) ((tE D).symm x)) := by
    have := wM_partner D w t ((tE D).symm x)
    rwa [Equiv.apply_symm_apply] at this
  rw [e1, GPsi_eq]
  have e2 : (((chE D φ) ((tE D).symm x) : ℂˣ) : ℂ) = φ x := by
    show ((cOf D φ ((tE D).symm x) : ℂˣ) : ℂ) = φ x
    rw [cOf_apply, Equiv.apply_symm_apply]
  rw [e2]
  rfl

theorem exists_cut {ι : Type*} [Finite ι] (f : ι → ℝ) : ∃ N : ℕ, ∀ i, f i ≤ N := by
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  exact ⟨⌈M⌉₊, fun i => (hM ⟨i, rfl⟩).trans (Nat.le_ceil M)⟩

theorem balance (a : ℝ) (ha : 0 < a) (w : D.R.GG → ℝ) (hw : ∀ ρ ∈ D.R.Psi, 0 < w ρ) (t : HH D) :
    ((ASKjt D a w (D.R.tau1 t) : ℝ) : ℂ) - MAINjt D a w = Dejt D a w (D.R.tau1 t) := by
  obtain ⟨N, hN⟩ := exists_cut (fun ρ : D.R.GG => a / w ρ)
  rw [ASK_eq D a w hw N (fun ρ _ => hN ρ) t, ← MAIN_eq, ← De_eq]
  exact Deduction.ch_balance (AD D) _ (UpperTheory.Comparison₂.hostFactsS _ D.host.toHostAx)
    (ell D) a (tH D t) (wM D w) ha (fun ρ hρ => hw _ ((inPhi_symm_iff D ρ).2 hρ)) N
    (fun ρ _ => hN _)

theorem a_pos (s : Scale) {a : ℤ} (h : |(a : ℝ) / s.b - s.x| ≤ 1) : (0 : ℝ) < a := by
  have hb : 0 < s.b := Real.exp_pos _
  have hx := s.one_lt_alt
  have h1 := (abs_le.mp h).1
  by_contra hn
  push_neg at hn
  have := div_nonpos_of_nonpos_of_nonneg hn hb.le
  linarith

theorem proposition_eleven_one_at_scale (s : Scale) : Conclusion1 D s := by
  intro η u0 a w hG j hj t ht
  obtain ⟨-, -, ha, hw⟩ := hG
  exact balance D (a t) (a_pos s (ha t ht)) (w j) (fun ρ hρ => (hw j hj ρ hρ).1) t

end Formalism.MainNotions.ZetaZeroFreeRegion.Br

end

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion.Br

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions Formalism.LFunctionChainParameters Finset

variable (D : D7) (s : Scale)

theorem thick_set_lt_level {u : ℕ} (hu : u ∈ D.host.T2) : u < D.R.n0 := by
  have h1 := D.host.second_set_range u hu
  have h2 := D.host.two_le_Lw
  nlinarith

theorem card_T2_le_degree : D.host.T2.card ≤ D.R.n := by
  have : D.host.T2 ⊆ range D.R.n0 := fun u hu => mem_range.2 (thick_set_lt_level D hu)
  have h := card_le_card this
  rw [card_range] at h
  exact h.trans D.R.baseRank_le_rank

def LargeX (x ε c Cd CL : ℝ) : Prop :=
  3 ≤ x ∧ ThickSetMeanBounds.moveCost x Cd CL ≤ x ^ ((1 : ℝ) / 2 + ε) ∧ 8 * x ^ 5 ≤ Real.exp (c * x ^ (ε / 8)) ∧
    48 * x ^ 5 ≤ Real.exp (1 * x ^ (ε / 4)) ∧ 2 ≤ x ^ (3 * ε / 4) ∧ 26 ≤ x ^ (3 * ε / 8)

theorem largeX_ev (ε c Cd CL : ℝ) (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ x : ℝ in Filter.atTop, LargeX x ε c Cd CL := by
  have hA := ev_log (4 * Cd + 3 * Real.log 2) (3 + 3 * CL) ((1 : ℝ) / 2 + ε) (by linarith)
  have hB := ev_exp 8 5 (ε / 8) c (by norm_num) (by linarith) hc
  have hC := ev_exp 48 5 (ε / 4) 1 (by norm_num) (by linarith) one_pos
  have hD := ev_rpow_ge 2 (3 * ε / 4) (by linarith)
  have hE := ev_rpow_ge 26 (3 * ε / 8) (by linarith)
  filter_upwards [hA, hB, hC, hD, hE, Filter.eventually_ge_atTop 3] with x h1 h2 h3 h4 h5 h6
  have h5r : ((5 : ℝ)) = ((5 : ℕ) : ℝ) := by norm_num
  rw [h5r, Real.rpow_natCast] at h2 h3
  refine ⟨h6, ?_, h2, h3, h4, h5⟩
  have hx0 : 0 < x := by linarith
  have hl : Real.log (x + 1) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num) hx0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  unfold ThickSetMeanBounds.moveCost
  nlinarith

theorem rle {x u v : ℝ} (hx : 1 ≤ x) (h : u ≤ v) : x ^ u ≤ x ^ v := Real.rpow_le_rpow_of_exponent_le hx h

theorem windows (C : ℝ) (hC : 0 ≤ C) (hS : SizesAt D s (s.eps / 4)) (hP : PlacesAt D s)
    (h3 : 3 ≤ s.x) (h26 : 26 ≤ s.x ^ (3 * s.eps / 8)) :
    ThickSetMeanBounds.SizeWindows C s.eps s.x D.R.n D.host.TT.card D.host.T2.card D.R.m s.b D.R.k s.a
      (Err D s C) := by
  obtain ⟨hn1, hn2, hm1, hm2, hk1, hk2⟩ := hS
  obtain ⟨hT1, -, hT2⟩ := hP
  have hx1 : 1 ≤ s.x := by linarith
  have hx0 : 0 < s.x := by linarith
  have hε := s.eps_pos
  have hε2 := s.eps_lt
  have hb : 0 < s.b := Real.exp_pos _
  have hxd : s.x * s.delta1 = s.x ^ (1 - s.eps / 8) := by
    unfold Scale.delta1
    rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
  rw [hxd, ← Real.rpow_mul hx0.le] at hm1 hm2
  have hmU : (D.R.m : ℝ) ≤ s.x ^ ((1 : ℝ) / 2 + s.eps / 2) :=
    hm2.trans (rle hx1 (by nlinarith))
  have hmL : s.x ^ ((1 : ℝ) / 2 - s.eps) ≤ (D.R.m : ℝ) :=
    (rle hx1 (by nlinarith)).trans hm1
  refine ⟨h3, hε, hC, by unfold Ranks.n; positivity, hb, by unfold Scale.a; positivity, ?_, hT1, hT2,
    card_T2_le_degree D, hmL, hmU, ?_, ?_, ?_, h26⟩
  · unfold Scale.a; nlinarith [mul_pos hx0 hb]
  · calc s.x * (D.R.m : ℝ) ≤ s.x ^ (1 : ℝ) * s.x ^ ((1 : ℝ) / 2 + s.eps / 2) := by
          rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left hmU hx0.le
      _ = s.x ^ (1 + ((1 : ℝ) / 2 + s.eps / 2)) := (Real.rpow_add hx0 _ _).symm
      _ ≤ s.x ^ ((9 : ℝ) / 2 + 10 * s.eps - s.eps / 4) := rle hx1 (by nlinarith)
      _ ≤ _ := hk1
  · calc (D.R.k : ℝ) ≤ s.x ^ ((9 : ℝ) / 2 + 10 * s.eps + s.eps / 4) := hk2
      _ ≤ s.x ^ ((2 + 8 * s.eps - s.eps / 4) * ((2 : ℕ) : ℝ) + ((1 : ℝ) / 2 - s.eps)) :=
          rle hx1 (by push_cast; nlinarith)
      _ = (s.x ^ (2 + 8 * s.eps - s.eps / 4)) ^ 2 * s.x ^ ((1 : ℝ) / 2 - s.eps) := by
          rw [Real.rpow_add hx0, Real.rpow_mul hx0.le, Real.rpow_natCast]
      _ ≤ (D.R.n : ℝ) ^ 2 * s.x ^ ((1 : ℝ) / 2 - s.eps) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0.le _)
          exact pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) hn1 2
  · apply le_of_eq
    simp only [Err, sizeBudget, budgetNc, rankBudget, bSize, Ranks.f, Scale.b, Scale.L]
    push_cast
    ring

theorem smallCosts (c Cd CL η : ℝ) (hS : SizesAt D s (s.eps / 4)) (hη0 : 0 < η)
    (hη : Real.log η ≤ s.x ^ (s.eps / 4)) (hL : LargeX s.x s.eps c Cd CL) :
    ThickSetMeanBounds.SmallCosts s.x s.eps (D.R.f : ℝ) s.b η (Real.exp (-(c * s.x ^ (s.eps / 8)))) Cd CL := by
  obtain ⟨h3, hmv, he1, he2, h2, -⟩ := hL
  obtain ⟨-, hn2, -⟩ := hS
  have hx1 : 1 ≤ s.x := by linarith
  have hx0 : 0 < s.x := by linarith
  have hε := s.eps_pos
  have hε2 := s.eps_lt
  have hn3 : (D.R.n : ℝ) ≤ s.x ^ 3 := by
    refine hn2.trans ?_
    rw [← Real.rpow_natCast]
    exact rle hx1 (by push_cast; nlinarith)
  have hf : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hn0 : (0 : ℝ) ≤ D.R.n := Nat.cast_nonneg _
  have hfx : (D.R.f : ℝ) * (s.x + 1) ≤ 4 * s.x ^ 4 := by
    rw [hf]
    have : (D.R.n : ℝ) * (s.x + 1) ≤ s.x ^ 3 * (2 * s.x) :=
      mul_le_mul hn3 (by linarith) (by linarith) (by positivity)
    nlinarith
  have hfx0 : 0 ≤ (D.R.f : ℝ) * (s.x + 1) := by rw [hf]; positivity
  refine ⟨hmv, ?_, ?_⟩
  · rw [Real.exp_neg, le_div_iff₀ hx0]
    have hE : 0 < Real.exp (c * s.x ^ (s.eps / 8)) := Real.exp_pos _
    have : 2 * (D.R.f : ℝ) * (s.x + 1) * (Real.exp (c * s.x ^ (s.eps / 8)))⁻¹ * s.x =
        (2 * ((D.R.f : ℝ) * (s.x + 1)) * s.x) / Real.exp (c * s.x ^ (s.eps / 8)) := by
      field_simp
    rw [this, div_le_one hE]
    calc 2 * ((D.R.f : ℝ) * (s.x + 1)) * s.x ≤ 2 * (4 * s.x ^ 4) * s.x := by
          apply mul_le_mul_of_nonneg_right _ hx0.le; linarith
      _ = 8 * s.x ^ 5 := by ring
      _ ≤ _ := he1
  · rw [le_div_iff₀ hx0]
    set E4 := Real.exp (1 * s.x ^ (s.eps / 4)) with hE4
    have hE41 : 1 ≤ E4 := Real.one_le_exp (by rw [one_mul]; exact Real.rpow_nonneg hx0.le _)
    have hηE : η ≤ E4 := by
      rw [← Real.exp_log hη0, hE4, one_mul]; exact Real.exp_le_exp.2 hη
    have hbb : E4 * E4 ≤ s.b := by
      rw [hE4, ← Real.exp_add]
      unfold Scale.b Scale.L
      apply Real.exp_le_exp.2
      have e : s.x ^ s.eps = s.x ^ (s.eps / 4) * s.x ^ (3 * s.eps / 4) := by
        rw [← Real.rpow_add hx0]; congr 1; ring
      rw [e]
      nlinarith [Real.rpow_nonneg hx0.le (s.eps / 4)]
    calc 6 * (D.R.f : ℝ) * (s.x + 1) * (η + 1) * s.x
        = 6 * ((D.R.f : ℝ) * (s.x + 1)) * (η + 1) * s.x := by ring
      _ ≤ 6 * (4 * s.x ^ 4) * (2 * E4) * s.x := by
          apply mul_le_mul_of_nonneg_right _ hx0.le
          apply mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
      _ = (48 * s.x ^ 5) * E4 := by ring
      _ ≤ E4 * E4 := mul_le_mul_of_nonneg_right he2 (by linarith)
      _ ≤ s.b := hbb

end Formalism.MainNotions.ZetaZeroFreeRegion.Br

end

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion.Br

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions Formalism.LFunctionChainParameters Finset
open scoped Pointwise ComplexConjugate

open Classical

variable (D : D7)

def tHe : HH D ≃ D.R.A :=
  Equiv.ofBijective (tH D) Function.bijective_id

theorem tHe_apply (t : HH D) : tHe D t = tH D t := rfl

theorem tH_add (u v : HH D) : tH D (u + v) = tH D u + tH D v := rfl

def TTm : Finset D.R.A := D.host.TT.map (tHe D).toEmbedding

def thickSetModel : Finset D.R.A :=
  (D.host.T2.image (fun u : ℕ => (D.R.dig u))).map (tHe D).toEmbedding

theorem card_TTm : (TTm D).card = D.host.TT.card := Finset.card_map _

theorem card_thick_set_model : (thickSetModel D).card = D.host.T2.card := by
  unfold thickSetModel
  rw [card_map, card_image_of_injOn]
  intro u hu v hv h
  exact D.R.dig_inj (thick_set_lt_level D hu) (thick_set_lt_level D hv) h

def aM (a : HH D → ℤ) : D.R.A → ℝ := fun h => (a ((tHe D).symm h) : ℝ)

def wMM (w : HH D → ℕ → D.R.GG → ℝ) : D.R.A → Fin D.R.m → MM D → ℝ :=
  fun u j => wM D (w ((tHe D).symm u) (j + 1))

theorem thickAt_mem (u0 : HH D) (g : D.R.GG) :
    g ∈ thickAt D u0 ↔ ∃ u ∈ D.host.T2, D.R.tau2 ((D.R.dig u) + u0) = g := by
  unfold thickAt
  simp only [mem_image]

theorem thick_iff (u0 : HH D) (x : MM D) :
    D5.IsThickAt (thickSetModel D) (tH D u0) x ↔ (tE D).symm x ∈ thickAt D u0 := by
  rw [thickAt_mem]
  unfold D5.IsThickAt thickSetModel
  simp only [mem_image, mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨t, ⟨z, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
    refine ⟨u, hu, ?_⟩
    rw [tHe_apply, ← tH_add, ← thick_place_of_second_tau, Equiv.symm_apply_apply]
  · rintro ⟨u, hu, h⟩
    refine ⟨tH D (D.R.dig u), ⟨(D.R.dig u), ⟨u, hu, rfl⟩, rfl⟩, ?_⟩
    rw [← tH_add, ← thick_place_of_second_tau, h, Equiv.apply_symm_apply]

theorem thick_inPhi {T2 : Finset D.R.A} {u0 : D.R.A} {x : MM D}
    (h : D5.IsThickAt T2 u0 x) : D5.InPhi x := by
  unfold D5.IsThickAt at h
  obtain ⟨t, -, rfl⟩ := mem_image.1 h
  rfl

theorem lift_mem (j : Fin D.R.m) : (j : ℕ) + 1 ∈ SizeData₂.lifts D := by
  rw [SizeData₂.lifts, Finset.mem_Icc]
  have := j.isLt
  omega

theorem sum_lifts (m : ℕ) (f : ℕ → ℝ) : ∑ j : Fin m, f (j + 1) = ∑ j ∈ Icc 1 m, f j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [Finset.sum_Icc_succ_top (by omega), ih]

theorem MAIN_re (a : ℝ) (w : D.R.GG → ℝ) :
    (MAINjt D a w).re = a * (Real.log a - 1 - Real.eulerMascheroniConstant + (Lp D (chC D)).re -
      (1 : ℝ) / D.R.f * ∑ ρ ∈ PhiF D, Real.log (w ρ)) := by
  unfold MAINjt
  rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_re]

theorem topExcess_eq (a : HH D → ℤ) (w : HH D → ℕ → D.R.GG → ℝ) (N : ℕ)
    (hw : ∀ u0, ∀ j ∈ SizeData₂.lifts D, ∀ ρ ∈ D.R.Psi, 0 < w u0 j ρ)
    (hN : ∀ u0, ∀ j ∈ SizeData₂.lifts D, ∀ t, ∀ ρ ∈ D.R.Psi, (a t : ℝ) / w u0 j ρ ≤ N) :
    ThickSetMeanBounds.topExcess (AD D) N (ell D) (TTm D) (aM D a) (wMM D w) =
      (1 : ℝ) / D.R.n * ∑ u0 : HH D, ASKtot D a (w u0) -
        (1 : ℝ) / D.R.n * ∑ u0 : HH D, MAINtot D a (w u0) := by
  unfold ThickSetMeanBounds.topExcess
  have hc : (Fintype.card D.R.A : ℝ) = (D.R.n : ℝ) := by rw [card_HA]
  rw [hc, ← mul_sub, ← Finset.sum_sub_distrib, ← Equiv.sum_comp (tHe D)]
  congr 1
  refine Finset.sum_congr rfl (fun u0 _ => ?_)
  unfold TTm ASKtot MAINtot
  rw [Finset.sum_map, ← Finset.sum_sub_distrib, Finset.sum_comm]
  unfold SizeData₂.lifts
  rw [← sum_lifts D.R.m (fun j => ∑ t ∈ D.host.TT, ASKjt D (a t) (w u0 j) (D.R.tau1 t) -
    ∑ t ∈ D.host.TT, (a t : ℝ) * (Real.log (a t) - 1 -
      Real.eulerMascheroniConstant + (Lp D (chC D)).re -
      (1 : ℝ) / D.R.f * ∑ ρ ∈ PhiF D, Real.log (w u0 j ρ)))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have e1 : aM D a ((tHe D).toEmbedding t) = (a t : ℝ) := by
    unfold aM; rw [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
  have e2 : wMM D w (tHe D u0) j = wM D (w u0 (j + 1)) := by
    unfold wMM; rw [Equiv.symm_apply_apply]
  rw [e1, e2, MAIN_eq, MAIN_re, Equiv.coe_toEmbedding, tHe_apply,
    ← ASK_eq D (a t) (w u0 (j + 1)) (hw u0 _ (lift_mem D j)) N
      (fun ρ hρ => hN u0 _ (lift_mem D j) t ρ hρ) t]

theorem cOf_mul (φ φ' : AddChar (MM D) ℂ) : cOf D (φ * φ') = cOf D φ * cOf D φ' := by
  refine MonoidHom.ext fun g => Units.ext ?_
  rw [MonoidHom.mul_apply, Units.val_mul, cOf_apply, cOf_apply, cOf_apply, AddChar.mul_apply]

theorem cOf_psC : cOf D ThickSetMeanBounds.psC = psC D := by
  ext g
  rw [cOf_apply]
  have h1 : (ThickSetMeanBounds.psC : AddChar (MM D) ℂ) (tE D g) = if (tE D g).1.2 = 0 then 1 else -1 := rfl
  rw [h1]
  have h2 : ((psC D g : ℂˣ) : ℂ) = (((g.1.1 : ℤˣ) : ℤ) : ℂ) := rfl
  rw [h2]
  have h3 : (tE D g).1.2 = 0 ↔ g.1.1 = 1 := LHost.sgn2_toAdd_eq_zero_iff g.1.1
  by_cases hg : g.1.1 = 1
  · rw [if_pos (h3.2 hg), hg]; simp
  · rw [if_neg (fun h => hg (h3.1 h))]
    have : g.1.1 = -1 := (Int.units_eq_one_or g.1.1).resolve_left hg
    rw [this]; simp

theorem cOf_chpsC : cOf D ThickSetMeanBounds.chpsC = chC D * psC D := by
  unfold ThickSetMeanBounds.chpsC
  rw [cOf_mul, cOf_chC, cOf_psC]

theorem proposition_eleven_two_at_scale (s : Scale) (C c CL Cd : ℝ) (hC : 0 ≤ C) (hCd0 : 0 ≤ Cd)
    (hCd : ThickSetMeanBounds.DerivInt (AD D) (ell D) Cd)
    (h5 : adm5 D s c) (h6 : adm6 D s CL) (h7 : adm7 D s C)
    (hS : SizesAt D s (s.eps / 4)) (hP : PlacesAt D s) (hL : LargeX s.x s.eps c Cd CL) :
    Conclusion2 s.x s.eps (C + 3) := by
  obtain ⟨η, a, w, hG, hT⟩ := h7
  have hx0 : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hb : 0 < s.b := Real.exp_pos _
  have hX' : 0 < s.X' := Real.exp_pos _
  have hb' : 0 < s.b' := div_pos (mul_pos hx0 hb) hX'
  have hη0 : 0 < η := (hG 0).1
  have hη : Real.log η ≤ s.x ^ (s.eps / 4) := (hG 0).2.1
  have hw : ∀ u0, ∀ j ∈ SizeData₂.lifts D, ∀ ρ ∈ D.R.Psi, 0 < w u0 j ρ :=
    fun u0 j hj ρ hρ => ((hG u0).2.2.2 j hj ρ hρ).1
  obtain ⟨N, hN⟩ := exists_cut
    (fun i : HH D × Fin (D.R.m + 1) × HH D × D.R.GG => (a i.2.2.1 : ℝ) / w i.1 i.2.1 i.2.2.2)
  have hN1 : ∀ u0, ∀ j ∈ SizeData₂.lifts D, ∀ t, ∀ ρ ∈ D.R.Psi, (a t : ℝ) / w u0 j ρ ≤ N := by
    intro u0 j hj t ρ _
    have hj2 := (mem_Icc.1 hj).2
    exact hN (u0, ⟨j, by omega⟩, t, ρ)
  have hyp : ThickSetMeanBounds.GrowthInequalityHypotheses (AD D) (ell D) N (TTm D) (thickSetModel D) (aM D a) (wMM D w) s.x s.eps s.b s.b' η s.X'
      (Real.exp (-(c * s.x ^ (s.eps / 8)))) Cd CL (Err D s C) := by
    refine ⟨hL.1, hb, hη0.le, hX', hb', ?_, (Real.exp_pos _).le, hCd0, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_,
      ThickSetMeanBounds.lipschitz_weight_all _ _ _, hCd, ?_⟩
    · unfold Scale.b' Scale.a
      rw [div_mul_cancel₀ _ hX'.ne']
    · intro t ht
      obtain ⟨t0, ht0, rfl⟩ := mem_map.1 ht
      unfold aM
      rw [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
      exact (hG 0).2.2.1 t0 ht0
    · intro u0 j ρ hρ
      exact hw _ _ (lift_mem D j) _ ((inPhi_symm_iff D ρ).2 hρ)
    · intro u0 j ρ hρ
      have hρ' : D5.IsThickAt (thickSetModel D) (tH D ((tHe D).symm u0)) ρ := by
        rw [← tHe_apply, Equiv.apply_symm_apply]; exact hρ
      exact ((hG _).2.2.2 _ (lift_mem D j) _ ((inPhi_symm_iff D ρ).2 (thick_inPhi D hρ))).2.1
        ((thick_iff D _ ρ).1 hρ')
    · intro u0 j ρ hρ hnt
      refine ((hG _).2.2.2 _ (lift_mem D j) _ ((inPhi_symm_iff D ρ).2 hρ)).2.2 (fun h => hnt ?_)
      have := (thick_iff D _ ρ).2 h
      rwa [← tHe_apply, Equiv.apply_symm_apply] at this
    · intro u0 j t ρ _ _
      exact hN ((tHe D).symm u0, ⟨j + 1, by have := j.2; omega⟩, (tHe D).symm t, (tE D).symm ρ)
    · rw [topExcess_eq D a w N hw hN1]
      unfold TOPineq at hT
      linarith
    · intro φ y hy
      rw [GPsi_eq]
      exact h5 _ y hy
    · intro φ hφ
      rw [GPsi_eq]
      unfold ell
      rcases hφ with rfl | rfl | rfl
      · rw [cOf_psC]; exact h6 _ (by simp)
      · rw [cOf_chC]; exact h6 _ (by simp)
      · rw [cOf_chpsC]; exact h6 _ (by simp)
  have hsm : ThickSetMeanBounds.SmallCosts s.x s.eps (ThickSetMeanBounds.fPl D.R.A) s.b η
      (Real.exp (-(c * s.x ^ (s.eps / 8)))) Cd CL := by
    unfold ThickSetMeanBounds.fPl
    rw [card_PhiSet]
    exact smallCosts D s c Cd CL η hS hη0 hη hL
  have hwin : ThickSetMeanBounds.SizeWindows C s.eps s.x (Fintype.card D.R.A) (TTm D).card (thickSetModel D).card
      D.R.m s.b D.R.k s.a (Err D s C) := by
    have e1 : Fintype.card D.R.A = D.R.n := card_HA D
    rw [e1, card_TTm, card_thick_set_model]
    exact windows D s C hC hS hP hL.1 hL.2.2.2.2.2
  have := UpperTheory.GL.cost_proposition_at_scale (AD D) _ (UpperTheory.Comparison₂.hostFactsS _ D.host.toHostAx) (ell D) N D.R.m (TTm D) (thickSetModel D)
    (aM D a) (wMM D w) C s.x s.eps s.b s.b' η s.X' _ Cd CL (Err D s C) D.R.k s.a hyp hsm hwin
  unfold Conclusion2
  rw [G_eq_Gz]
  exact this

theorem proposition_eleven_two_along_family {ε : ℝ} (h0 : 0 < ε) (Fm : FamP ε) (C c CL : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (h5 : ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ i : Fm.Ix x, adm5 (Fm.D x i) (Fm.L x i).sc c)
    (h6 : ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ i : Fm.Ix x, adm6 (Fm.D x i) (Fm.L x i).sc CL)
    (hS : ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ i : Fm.Ix x,
      SizesAt (Fm.D x i) (Fm.L x i).sc (ε / 4) ∧ PlacesAt (Fm.D x i) (Fm.L x i).sc)
    (hT : ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∃ i : Fm.Ix x, adm7 (Fm.D x i) (Fm.L x i).sc C) :
    ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → Conclusion2 x ε (C + 3) := by
  obtain ⟨x5, H5⟩ := h5
  obtain ⟨x6, H6⟩ := h6
  obtain ⟨xS, HS⟩ := hS
  obtain ⟨xT, HT⟩ := hT
  obtain ⟨Cd, hCd0, hCd⟩ := ThickSetMeanBounds.derivative_integral_all
  obtain ⟨xL, HL⟩ := Filter.eventually_atTop.1 (largeX_ev ε c Cd CL h0 hc)
  refine ⟨max (max (max x5 x6) (max xS xT)) (max xL (Fm.x1 + 1)), fun x hx => ?_⟩
  have hx5 : x5 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hx6 : x6 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxS : xS ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hxT : xT ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hxL : xL ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    linarith
  obtain ⟨i, hi⟩ := HT x hxT
  have ex : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have ee : (Fm.L x i).sc.eps = ε := Fm.L_eps x i
  have := proposition_eleven_two_at_scale (Fm.D x i) (Fm.L x i).sc C c CL Cd hC hCd0 (hCd _ _ _)
    (H5 x hx5 i) (H6 x hx6 i) hi (by rw [ee]; exact (HS x hxS i).1) (HS x hxS i).2
    (by rw [ex, ee]; exact HL x hxL)
  rwa [ex, ee] at this

theorem proposition_eleven_two_small_epsilon (Fm : DFamP) (ε0 : ℝ) (h5 : FamilyPropTwoSix Fm ε0) (h6 : FamilyCharacterSumBounds Fm ε0) (hS : SizesFe Fm ε0)
    (C : ℝ) (hC : 0 < C) (hT : TOPF Fm ε0 C) (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52) (h : ε < ε0) :
    ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → Conclusion2 x ε (C + 3) := by
  obtain ⟨c, x5, hc, -, H5⟩ := h5 ε h0 h1 h
  obtain ⟨CL, x6, -, -, H6⟩ := h6 ε h0 h1 h
  obtain ⟨xS, -, HS⟩ := hS ε h0 h1 h (ε / 4) (by positivity)
  obtain ⟨xT, -, HT⟩ := hT ε h0 h1 h
  exact proposition_eleven_two_along_family h0 (Fm ε h0 h1) C c CL hC.le hc ⟨x5, H5⟩ ⟨x6, H6⟩ ⟨xS, HS⟩ ⟨xT, HT⟩

end Formalism.MainNotions.ZetaZeroFreeRegion.Br

end

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions Formalism.LFunctionChainParameters

theorem ramification_two_and_conjugation_at_q_and_d (D : D7) (s : Scale) : Conclusion1 D s := Br.proposition_eleven_one_at_scale D s

theorem transportEstimate_of_admissible (D : D7) (s : Scale) (_ : admitted D) : Conclusion1 D s := ramification_two_and_conjugation_at_q_and_d D s

theorem prim_eq_one_iff (D : D7) (ψ : Chr D) : (prim D ψ).2 = 1 ↔ ψ = 1 := Br.prim_one_iff D ψ

theorem stmt_holds (D : D7) (s : Scale) : Stmt D s := fun _ => ⟨ramification_two_and_conjugation_at_q_and_d D s, points_property_of_d7⟩

theorem proposition_eleven_two_of_characters : ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (D : D7) (s : Scale) (C c CL : ℝ), 0 ≤ C →
    adm5 D s c → adm6 D s CL → adm7 D s C → SizesAt D s (s.eps / 4) → PlacesAt D s →
    Br.LargeX s.x s.eps c Cd CL → Conclusion2 s.x s.eps (C + 3) := by
  obtain ⟨Cd, hCd0, hCd⟩ := ThickSetMeanBounds.derivative_integral_all
  exact ⟨Cd, hCd0, fun D s C c CL hC h5 h6 h7 hS hP hL =>
    Br.proposition_eleven_two_at_scale D s C c CL Cd hC hCd0 (hCd _ _ _) h5 h6 h7 hS hP hL⟩

theorem proposition_eleven_one_family (Fm : DFamP) : Conclusion1Family Fm :=
  fun _ _ _ _ => ⟨2, by norm_num, fun _ _ _ => ramification_two_and_conjugation_at_q_and_d _ _⟩

theorem proposition_eleven_two_family (Fm : DFamP) (h5 : FamilyPropTwoSix Fm (1 / 52)) (h6 : FamilyCharacterSumBounds Fm (1 / 52)) : Conclusion2Family Fm :=
  fun hS C hC hT ε h0 h1 => Br.proposition_eleven_two_small_epsilon Fm (1 / 52) h5 h6 hS C hC hT ε h0 h1 h1

theorem rh_of (Fm : DFamP) (ε0 : ℝ) (hε0 : 0 < ε0) (h5 : FamilyPropTwoSix Fm ε0) (h6 : FamilyCharacterSumBounds Fm ε0)
    (h7 : FamilyTopBoundAbsolute Fm ε0) (hS : SizesFe Fm ε0) : RiemannHypothesis := by
  obtain ⟨C, hC, hT⟩ := h7
  refine ConditionalMainTheorem.riemann_hypothesis_of_power_bound (C + 3) (min ε0 (1 / 52)) (lt_min hε0 (by norm_num)) (fun ε h0 h => ?_)
  obtain ⟨x0, H⟩ := Br.proposition_eleven_two_small_epsilon Fm ε0 h5 h6 hS C hC hT ε h0 (lt_of_lt_of_le h (min_le_right _ _))
    (lt_of_lt_of_le h (min_le_left _ _))
  refine ⟨x0, fun x hx => ?_⟩
  have := H x hx
  unfold Conclusion2 at this
  rwa [G_eq_Gz] at this

theorem theorem_eleven_three_family (Fm : DFamP) : SlopeLemmaFamily Fm := by
  rintro ⟨ε0, hε0, ⟨-, -, -, -, h5, h6, h7, -⟩, hS⟩
  exact rh_of Fm ε0 hε0 h5 h6 h7 hS

theorem stmtF_holds (Fm : DFamP) : KudlaFamilyStatement Fm := by
  rintro ⟨-, -, -, -, h5, h6, -⟩
  exact ⟨proposition_eleven_one_family Fm, proposition_eleven_two_family Fm h5 h6, points_property_of_d7, theorem_eleven_three_family Fm⟩

theorem chebyshev_bounds_one_fifth (D : D7) : adm1 D := first_hypothesis_of_lifting D (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d D)
theorem second_admissible_holds (D : D7) : adm2 D := second_hypothesis_of_lifting D (UnusedSlot33.second_proposition_every_localisation D)

theorem admissibleModule_iff_lattice_quotients (D : D7) : admitted D ↔ adm8 :=
  ⟨fun h => h.2.2.2.1, fun h => ⟨chebyshev_bounds_one_fifth D, second_admissible_holds D, subgroup_admissible_holds D, h, content_divisibility_clause,
    primitive_reading_holds D, zero_window_bound_holds D⟩⟩

theorem admissible_family_iff_components (Fm : DFamP) (ε0 : ℝ) :
    AdmFe Fm ε0 ↔ FamilyLemmaTwoOne Fm ε0 ∧ FamilyPropTwoSix Fm ε0 ∧ FamilyCharacterSumBounds Fm ε0 ∧ FamilyTopBoundAbsolute Fm ε0 ∧ adm8 := by
  have all : ∀ P : D7 → Prop, (∀ D, P D) → AllLarge Fm ε0 (fun D _ => P D) :=
    fun P hP _ _ _ _ => ⟨2, by norm_num, fun _ _ _ => hP _⟩
  constructor
  · rintro ⟨-, -, -, h4, h5, h6, h7, h8, -⟩
    exact ⟨h4, h5, h6, h7, h8⟩
  · rintro ⟨h4, h5, h6, h7, h8⟩
    exact ⟨all _ chebyshev_bounds_one_fifth, all _ second_admissible_holds, all _ subgroup_admissible_holds, h4, h5, h6, h7, h8, content_divisibility_clause,
      all _ primitive_reading_holds, all _ zero_window_bound_holds⟩

end Formalism.MainNotions.ZetaZeroFreeRegion

end
