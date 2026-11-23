import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SizeWindowBrackets.ChainSlopeWindows.OneLeThresholdMulPowers
import Formalism.SizeWindowBrackets.ChainSlopeWindows.WeightedSlopeExcessDecomposition
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.ZetaZeroFreeRegion
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.RamificationTwoAndConjugationAtQAndD
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum
import Development.AutomorphicArithmetic.ConductorsKronecker.dataField
import Development.AutomorphicArithmetic.ConductorsKronecker.Imports
import Development.AutomorphicArithmetic.ConductorsKronecker.kronecker
import Development.AutomorphicArithmetic.ConductorsKronecker.RecSurj
import Development.AutomorphicArithmetic.ConductorsKronecker.InertiaD
import Development.AutomorphicArithmetic.ConductorsKronecker.ChCond
import Development.AutomorphicArithmetic.ConductorsKronecker.IsInertIff
import Development.AutomorphicArithmetic.PrimitiveCosets.hostFactsS
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChBalance
import Lemmata.GeneralBFactLeftBisAlt.Imports

noncomputable section

namespace Formalism.MainNotions.LinkB

open Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits

def ThickSetChoice (R : Ranks) (Lw : ℕ) (C : ℝ) (T₂ : Finset ℕ) : Prop :=
  (∀ s ∈ T₂, 4 * Lw * s < R.n0) ∧ NoRel T₂ Lw ∧
  (R.n0 : ℝ) * Real.exp (-(C * Real.sqrt (Real.log (R.n0 : ℝ) * Real.log Lw))) / Lw ≤ T₂.card

section BernoulliSumsFrobeniusOrbits

variable {D : D7} {L : SizeData₂ D}

def topsPosT (D : D7) (T : Finset (G.HH D)) (h t0 : G.HH D) : Finset (Fin (addOrderOf h)) :=
  Finset.univ.filter (fun i => t0 + (i : ℕ) • h ∈ T)

def GoodT (L : SizeData₂ D) (T : Finset (G.HH D)) (h t0 : G.HH D) : Prop :=
  G.IsGoodOrbit (addOrderOf h) (topsPosT D T h t0) (G.L2 D L.sc) (G.KG L.sc) (G.rG L.sc) L.sc.delta1
    (G.hG L.sc) L.sc.x

def BadT (X : G.Inst D L) (h t : G.HH D) (T : Finset (G.HH D)) : Prop := ¬ GoodT L T h (X.bs h t)

open Classical in

def ServedOrbitsSecondMoment (X : G.Inst D L) (Cb : ℝ) : Prop :=
  ∀ h : G.HH D, L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf h : ℝ) → ∀ t : G.HH D,
    (∑ T : Finset (G.HH D), if t ∈ T ∧ BadT X h t T then UnusedSlot33.bern L.sc.delta1 T else 0) ≤
      (Cb * L.sc.x ^ (-2 : ℝ)) * L.sc.delta1

open Classical in

def TTChoice (X : G.Inst D L) (Cb : ℝ) (T : Finset (G.HH D)) : Prop :=
  L.sc.delta1 * D.R.n / 2 ≤ (T.card : ℝ) ∧ (T.card : ℝ) ≤ 2 * L.sc.delta1 * D.R.n ∧
  ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p * ((T.filter (fun t => BadT X (G.hP D p) t T)).card : ℝ) ≤
    4 * (Cb * L.sc.x ^ (-2 : ℝ)) * L.sc.delta1 * D.R.n * ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p

open Classical in

theorem large_order_primes_eq_filter (L : SizeData₂ D) : largeOrderResiduePrimes L = (AuxBlock8.primesResidueBelow D L.sc.X').filter
      (fun p => L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (G.hP D p) : ℝ)) := by
  ext p
  simp only [largeOrderResiduePrimes, AuxBlock8.primesResidueBelow, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2, Nat.lt_ceil.mp h1, h3⟩, h4⟩
  · rintro ⟨⟨h1, h2, -, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩

end BernoulliSumsFrobeniusOrbits

section Proviso

variable {D : D7}

theorem gamL_eq (L : SizeData₂ D) (u : D.what₂.Word) : GamL L = (D.mem u).A.GamP := by
  unfold GamL
  rw [← L.Gam_eq u, Real.exp_log (lt_trans one_pos (D.mem u).A.one_lt_gammaP)]

theorem proviso_mono (L : SizeData₂ D) {C0 C0' : ℝ} (h0 : 0 < C0) (h : C0 ≤ C0') (hp : ChProviso_at L C0) :
    ChProviso_at L C0' := fun u =>
  ⟨le_trans (inv_anti₀ h0 h) (hp u).1, le_trans (hp u).2 h⟩

theorem exp_logXu (hDu : StandardLattice.FactDuStar D) (hDs : StandardLattice.FactDstar D) (u : D.what₂.Word) :
    Real.exp (StandardLattice.logXuD D u) = (D.mem u).A.Xu := by
  have hd : (0 : ℝ) < ((D.mem u).A.duStar : ℝ) := by exact_mod_cast (D.mem u).A.duStar_pos
  have hr : 0 < (D.mem u).A.Dstar / ((D.mem u).A.duStar : ℝ) := div_pos (D.mem u).A.Dstar_pos hd
  unfold StandardLattice.logXuD StandardLattice.logXu ColumnsAtT.Xu
  rw [← hDs, ← hDu u, ← D.Dstar_eq u, Real.rpow_def_of_pos hr, mul_comm]

def RankM (D : D7) : Prop :=
  ∀ u : D.what₂.Word, (D.duS u : ℝ) = StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

def RankHyp (D : D7) : Prop :=
  StandardLattice.GBig D ∧ (∀ i, StandardLattice.SplitsF D (D.host.g i)) ∧
    ∀ u : D.what₂.Word, StandardLattice.SplitsF D (D.mem u).A.T ∧ StandardLattice.Mu0Tie D u

theorem rank_formula_of_part_four (Lv : LevelData D) (h : StandardLattice.Conclusion4f D Lv) (hR : RankHyp D) : RankM D :=
  fun u => h hR.1 hR.2.1 u (hR.2.2 u).1 (hR.2.2 u).2

def DataBF {eps : ℝ} (Fm : FamP eps) (CB : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (Δ : ℕ) (w : ℕ → (Fm.D x i).what₂.Tau → ℝ),
    StandardLattice.DataB (Fm.D x i) (Fm.L x i).sc CB Δ w

def RankHypF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, RankHyp (Fm.D x i)

end Proviso

def ChosenExists (CH : ℝ) : Prop :=
  ∃ Fm : DFamP, ∀ ε (h0 : 0 < ε) (h1 : ε < 1 / 52), ChosenEx (Fm ε h0 h1) CH

def ChoicesMade {eps : ℝ} (Fm : FamP eps) (CH C0 Cb : ℝ) : Prop :=
  (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
    ThickSetChoice (Fm.D x i).R (Fm.D x i).host.Lw (Fm.D x i).host.CT2 (Fm.D x i).host.T2 ∧
    TTChoice (Fm.Gx x i) Cb (Fm.D x i).host.TT) ∧
  ShortIntervalPrimes.FamilyPrimesAsPropTwoFive Fm ∧ ChosenCode Fm C0 CH

end Formalism.MainNotions.LinkB

end

noncomputable section

namespace Formalism.MainNotions.LnkBr

open DirichletCharacter Filter

theorem prim_unique {N1 N2 : ℕ} [NeZero N1] [NeZero N2] (χ1 : DirichletCharacter ℂ N1)
    (χ2 : DirichletCharacter ℂ N2) (h1 : χ1.IsPrimitive) (h2 : χ2.IsPrimitive) (M : ℕ) (hM : M ≠ 0)
    (h : ∀ p : ℕ, p.Prime → ¬ p ∣ M → χ1 (p : ZMod N1) = χ2 (p : ZMod N2)) :
    (∀ n : ℕ, χ1 (n : ZMod N1) = χ2 (n : ZMod N2)) ∧ (χ1 = 1 ↔ χ2 = 1) := by
  have hN : N1 * N2 * M ≠ 0 := mul_ne_zero (mul_ne_zero (NeZero.ne N1) (NeZero.ne N2)) hM
  have : NeZero (N1 * N2 * M) := ⟨hN⟩
  have d1 : N1 ∣ N1 * N2 * M := ⟨N2 * M, by ring⟩
  have d2 : N2 ∣ N1 * N2 * M := ⟨N1 * M, by ring⟩
  have d3 : M ∣ N1 * N2 * M := ⟨N1 * N2, by ring⟩
  have key : changeLevel d1 χ1 = changeLevel d2 χ2 := by
    ext u
    obtain ⟨p, -, hpp, hpu⟩ := Nat.forall_exists_prime_gt_and_eq_mod u.isUnit 0
    have hcop : p.Coprime (N1 * N2 * M) := by
      rw [← ZMod.isUnit_iff_coprime, hpu]; exact u.isUnit
    have hpM : ¬ p ∣ M := fun hd => (Nat.Prime.coprime_iff_not_dvd hpp).1 hcop (hd.trans d3)
    rw [changeLevel_eq_cast_of_dvd, changeLevel_eq_cast_of_dvd, ← hpu, ZMod.cast_natCast d1,
      ZMod.cast_natCast d2]
    exact h p hpp hpM
  have c1 : conductor (changeLevel d1 χ1) = N1 := by rw [conductor_changeLevel]; exact h1
  have c2 : conductor (changeLevel d2 χ2) = N2 := by rw [conductor_changeLevel]; exact h2
  have hEq : N1 = N2 := c1.symm.trans ((congrArg conductor key).trans c2)
  subst hEq
  have : χ1 = χ2 := changeLevel_injective d1 key
  subst this
  exact ⟨fun _ => rfl, Iff.rfl⟩

end Formalism.MainNotions.LnkBr

end

noncomputable section

namespace Formalism.MainNotions.LnkBr

open Formalism.MainNotions.ZetaZeroFreeRegion

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions Formalism.LFunctionChainParameters Finset
open scoped Pointwise ComplexConjugate

open Classical

instance factQ (D : D7) : Fact D.host.q.Prime := ⟨D.host.hyp.1⟩
instance factD (D : D7) : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩

abbrev MM (D : D7) : Type := D5.E0 × D.R.A

def AD (D : D7) : characterSumData.ArithData D.R.A := Formalism.MainNotions.arithOf D.host.toHostRaw

def tE (D : D7) : D.R.GG ≃ MM D :=
  Equiv.ofBijective (fun g => (UpperTheory.Comparison₂.toE D.R.toFrame g).toAdd)
    (Multiplicative.toAdd.bijective.comp (UpperTheory.Comparison₂.toE_bij D.R.toFrame).1)

variable (D : D7)

theorem tE_mul (g g' : D.R.GG) : tE D (g * g') = tE D g + tE D g' :=
  congrArg Multiplicative.toAdd (map_mul (UpperTheory.Comparison₂.toE D.R.toFrame) g g')
theorem tE_one : tE D 1 = 0 := congrArg Multiplicative.toAdd (map_one (UpperTheory.Comparison₂.toE D.R.toFrame))
theorem tE_symm_add (x y : MM D) : (tE D).symm (x + y) = (tE D).symm x * (tE D).symm y := by
  apply (tE D).injective; simp [tE_mul]
theorem tE_symm_zero : (tE D).symm 0 = 1 := by
  apply (tE D).injective; simp [tE_one]

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
theorem cOf_zero : cOf D 0 = 1 := by ext g; simp [cOf_apply]
theorem aOf_one : aOf D 1 = 0 := by ext x; simp [aOf_apply]
theorem cOf_eq_one_iff (φ : AddChar (MM D) ℂ) : cOf D φ = 1 ↔ φ = 0 := by
  rw [← cOf_zero D]; exact (chE D).injective.eq_iff

theorem exists_prime_over (p : ℕ) (hp : p.Prime) :
    ∃ P : Ideal (𝓞 D.host.E), P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have := Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices.span_prime hp
  obtain ⟨⟨P, hPp, hPl⟩⟩ :
    Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 D.host.E)) := inferInstance
  exact ⟨P, hPp, hPl⟩

theorem fieldFacts (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 D.host.E)) (hP : P.IsPrime)
    (hL : P.LiesOver (Ideal.span {(p : ℤ)})) (σ : D.host.E ≃ₐ[ℚ] D.host.E) :
    ((∀ x : 𝓞 D.host.E, σ • x - x ∈ P) ↔
      tE D (D.host.galE σ) ∈ (AD D).inertia p) ∧
    (IsArithFrobAt ℤ σ P ↔
      tE D (D.host.galE σ) - (AD D).frob p ∈ (AD D).inertia p) := by
  have := Fact.mk hp
  exact UpperTheory.GL.dataField D.host.toHostAx p P σ

theorem frob_spec (p : ℕ) (hp : p.Prime) :
    tE D (frob D p) - (AD D).frob p ∈ (AD D).inertia p := by
  obtain ⟨P, hP, hL⟩ := exists_prime_over D p hp
  obtain ⟨σ0, hσ0⟩ := (D.host.galE_bijective).2 ((tE D).symm ((AD D).frob p))
  have hex : ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, ∃ P : Ideal (𝓞 D.host.E),
      P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧ IsArithFrobAt ℤ σ P :=
    ⟨σ0, P, hP, hL, ((fieldFacts D p hp P hP hL σ0).2).2 (by
      rw [hσ0, Equiv.apply_symm_apply, sub_self]; exact AddSubgroup.zero_mem _)⟩
  unfold frob
  rw [dif_pos hex]
  obtain ⟨P', hP', hL', hF⟩ := hex.choose_spec
  exact ((fieldFacts D p hp P' hP' hL' _).2).1 hF

theorem dvd_discr_iff_ram (p : ℕ) (hp : p.Prime) :
    ((p : ℤ) ∣ discr D.host.E) ↔ 1 < (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 D.host.E) := by
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have hne := Ideal.ramificationIdxIn_ne_zero (B := 𝓞 D.host.E) (D.host.E ≃ₐ[ℚ] D.host.E)
    (p := Ideal.span {(p : ℤ)})
  rw [← not_iff_not, NumberField.not_dvd_discr_iff_isUnramifiedIn D.host.E (𝓞 D.host.E) hpZ,
    Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  constructor
  · intro H
    obtain ⟨P, hP⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)))
    have := hP.1; have := hP.2
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P (D.host.E ≃ₐ[ℚ] D.host.E),
      H P hP.2]
    omega
  · intro H P _ hlo
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P
      (D.host.E ≃ₐ[ℚ] D.host.E)] at H hne
    omega

theorem unram_iff (p : ℕ) :
    Unram D p ↔ p.Prime ∧ ¬ p ∣ D.host.condN := by
  unfold Unram
  constructor
  · rintro ⟨hp, h⟩
    rw [dvd_discr_iff_ram D p hp, Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices.ram_iff D p hp] at h
    exact ⟨hp, h⟩
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rw [dvd_discr_iff_ram D p hp, Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices.ram_iff D p hp]
    exact h

theorem inertia_unram {p : ℕ} (h : Unram D p) : (AD D).inertia p = ⊥ := by
  obtain ⟨hp, h2⟩ := (unram_iff D p).1 h
  exact (UpperTheory.GL.unram D.host.toHostRaw p ((Nat.Prime.coprime_iff_not_dvd hp).2 h2) hp).1

theorem frob_unram {p : ℕ} (h : Unram D p) : tE D (frob D p) = (AD D).frob p := by
  have := frob_spec D p h.1
  rw [inertia_unram D h, AddSubgroup.mem_bot, sub_eq_zero] at this
  exact this

instance neZeroN : NeZero D.host.condN :=
  ⟨D.host.condN_pos.ne'⟩

def chi0 (ψ : Chr D) : DirichletCharacter ℂ D.host.condN :=
  LHost.dirChar (Formalism.MainNotions.recOf D.host.toHostRaw) (aOf D ψ)

theorem primVal_eq (ψ : Chr D) (n : ℕ) (hn : n ≠ 0) :
    characterSumData.primVal (AD D) (aOf D ψ) n =
      (chi0 D ψ).primitiveCharacter (n : ZMod (chi0 D ψ).conductor) :=
  LHost.primitive_value_primitive _ D.host.q D.host.d (Formalism.MainNotions.recOf D.host.toHostRaw)
    (aOf D ψ) n (D.host.condN_pos.ne') hn

def chiP (ψ : Chr D) : Σ N : ℕ+, DirichletCharacter ℂ N :=
  ⟨⟨(chi0 D ψ).conductor, Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero _)⟩,
    (chi0 D ψ).primitiveCharacter⟩

theorem primVal_unram (ψ : Chr D) {p : ℕ} (h : Unram D p) :
    characterSumData.primVal (AD D) (aOf D ψ) p = ((ψ (frob D p) : ℂˣ) : ℂ) := by
  have h1 := ((LHost.primitive_value_ramified _ D.host.q D.host.d
    (Formalism.MainNotions.recOf D.host.toHostRaw) (aOf D ψ) p 1 h.1 le_rfl).1 (by
      intro x hx
      have hx' : x ∈ (AD D).inertia p := hx
      rw [inertia_unram D h, AddSubgroup.mem_bot] at hx'
      rw [hx', AddChar.map_zero_eq_one]))
  rw [pow_one, pow_one] at h1
  have h2 : characterSumData.primVal (AD D) (aOf D ψ) p = aOf D ψ ((AD D).frob p) := h1
  rw [h2, ← frob_unram D h, aOf_apply, Equiv.symm_apply_apply]

theorem reads0 (ψ : Chr D) : Reads D ψ (chiP D ψ) := by
  refine ⟨DirichletCharacter.primitiveCharacter_isPrimitive _, fun p hp => ?_⟩
  rw [← primVal_unram D ψ hp, primVal_eq D ψ p hp.1.ne_zero]
  rfl

theorem primitive_reading_exists : adm10 D := fun ψ => ⟨_, reads0 D ψ⟩

theorem prim_spec (ψ : Chr D) : Reads D ψ (prim D ψ) := by
  unfold prim
  rw [dif_pos (primitive_reading_exists D ψ)]
  exact (primitive_reading_exists D ψ).choose_spec

theorem primitiveCharacter_chi0_eq_one_iff (ψ : Chr D) : (chi0 D ψ).primitiveCharacter = 1 ↔ ψ = 1 := by
  have e0 : chi0 D 1 = 1 := by
    unfold chi0
    rw [aOf_one]
    ext u
    rw [LHost.dirChar_unit]
    simp
  constructor
  · intro h
    have h1 : chi0 D ψ = 1 := by
      rw [← DirichletCharacter.changeLevel_primitiveCharacter (chi0 D ψ), h,
        DirichletCharacter.changeLevel_one]
    have h2 : aOf D ψ = aOf D 1 :=
      (UpperTheory.GL.rec_surj D.host.toHostAx).2 (h1.trans e0.symm)
    exact (chE D).symm.injective h2
  · rintro rfl
    exact DirichletCharacter.level_one' _ (by
      rw [e0]; exact DirichletCharacter.conductor_one)

theorem prim_both (ψ : Chr D) :
    (∀ n : ℕ, (prim D ψ).2 (n : ZMod (prim D ψ).1) =
      (chi0 D ψ).primitiveCharacter (n : ZMod (chi0 D ψ).conductor)) ∧
    ((prim D ψ).2 = 1 ↔ (chi0 D ψ).primitiveCharacter = 1) := by
  have : NeZero (chi0 D ψ).conductor := ⟨DirichletCharacter.conductor_ne_zero _⟩
  refine prim_unique (prim D ψ).2 (chi0 D ψ).primitiveCharacter (prim_spec D ψ).1
    (DirichletCharacter.primitiveCharacter_isPrimitive _) (discr D.host.E).natAbs
    (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero D.host.E)) (fun p hp hd => ?_)
  have hU : Unram D p := ⟨hp, fun h => hd (Int.natCast_dvd.1 h)⟩
  rw [(prim_spec D ψ).2 p hU]
  exact ((reads0 D ψ).2 p hU).symm

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

theorem inPhi_iff (g : D.R.GG) : D5.InPhi (tE D g) ↔ g ∈ D.R.Psi :=
  LHost.sgn2_toAdd_eq_zero_iff g.1.2

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

theorem cOf_mul (φ φ' : AddChar (MM D) ℂ) : cOf D (φ * φ') = cOf D φ * cOf D φ' := by
  ext g; simp [cOf_apply]

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

end Formalism.MainNotions.LnkBr

end

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.D5 Formalism.FrobeniusOrbits Formalism.LFunctionChainParameters.LHost Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds

theorem Xpp_eq (s : Scale) (n : ℕ) (hn : (1 : ℝ) ≤ n) : s.X'' n = s.x * n * s.X' := by
  obtain ⟨hx, hb, ha, hX, hb'⟩ := sc_pos s
  have hn0 : (0 : ℝ) < n := by linarith
  unfold Scale.X'' Scale.w'' Scale.b'
  field_simp

section Chars

open DirichletCharacter

theorem log_deriv_L_one_congr_primitive {N1 N2 : ℕ} [NeZero N1] [NeZero N2] (χ1 : DirichletCharacter ℂ N1)
    (χ2 : DirichletCharacter ℂ N2) (h1 : χ1.IsPrimitive) (h2 : χ2.IsPrimitive)
    (h : ∀ n : ℕ, n ≠ 0 → χ1 (n : ZMod N1) = χ2 (n : ZMod N2)) :
    GlobalTheoryTheory.logDerivativeAtOne χ1 = GlobalTheoryTheory.logDerivativeAtOne χ2 := by
  have hN : N1 * N2 ≠ 0 := mul_ne_zero (NeZero.ne N1) (NeZero.ne N2)
  have : NeZero (N1 * N2) := ⟨hN⟩
  have d1 : N1 ∣ N1 * N2 := ⟨N2, rfl⟩
  have d2 : N2 ∣ N1 * N2 := ⟨N1, by ring⟩
  have key : changeLevel d1 χ1 = changeLevel d2 χ2 := by
    ext u
    obtain ⟨p, -, hpp, hpu⟩ := Nat.forall_exists_prime_gt_and_eq_mod u.isUnit 0
    rw [changeLevel_eq_cast_of_dvd, changeLevel_eq_cast_of_dvd, ← hpu, ZMod.cast_natCast d1,
      ZMod.cast_natCast d2]
    exact h p hpp.ne_zero
  have c1 : conductor (changeLevel d1 χ1) = N1 := by rw [conductor_changeLevel]; exact h1
  have c2 : conductor (changeLevel d2 χ2) = N2 := by rw [conductor_changeLevel]; exact h2
  have hEq : N1 = N2 := c1.symm.trans ((congrArg conductor key).trans c2)
  subst hEq
  have : χ1 = χ2 := changeLevel_injective d1 key
  subst this
  rfl

end Chars

open Formalism.MainNotions.ZetaZeroFreeRegion Formalism.MainNotions.LnkBr in

theorem char_at {D : D7} (L : SizeData₂ D) (x eps c6 C5 : ℝ) : Char_at L x eps c6 C5 := by
  intro e AD' he hAD
  subst he
  obtain rfl := eq_of_heq hAD
  refine ⟨Formalism.MainNotions.LnkBr.ell D, ?_, ?_, ?_, ?_⟩
  · intro ψ _ N _ χ hχ hv
    show Lp D (cOf D ψ) = _
    unfold Lp
    refine (log_deriv_L_one_congr_primitive χ (prim D (cOf D ψ)).2 hχ (prim_spec D _).1 (fun n hn => ?_)).symm
    rw [hv n hn, prim_val D _ n hn, aOf_cOf]
    rfl
  · rw [L.logDerivative_at_one_eq]
    show _ = (Lp D (cOf D Formalism.LFunctionChainParameters.characterSumData.chC)).re
    rw [cOf_chC, Lp_chC_eq]
    rfl
  · intro hT ψ y hy
    have h1 := GPsi_eq D ψ y
    have h2 := hT _ (prim D (cOf D ψ)).2 (GlobalTheoryTheory.ConductorDivisibility.jnt_prim_isCharED D (cOf D ψ)) y hy
    calc ‖GPsi (Formalism.MainNotions.arithOf D.host.toHostRaw) (Formalism.MainNotions.LnkBr.ell D) ψ y‖ = ‖Gc D (cOf D ψ) y‖ := congrArg _ h1
      _ ≤ _ := h2
  · intro hQ ψ hψ
    obtain ⟨B1, B2, B3⟩ := hQ
    have h1 := GPsi_eq D ψ x
    have key : ‖Gc D (cOf D ψ) x‖ ≤ x ^ ((1 : ℝ) / 2 + eps) ∧ ‖Lp D (cOf D ψ)‖ ≤ C5 * Real.log x := by
      rcases hψ with rfl | rfl | rfl
      · rw [cOf_psC]; exact B1 _ _ (GlobalTheoryTheory.ConductorDivisibility.jnt_induces_ps D _ (prim_spec D _))
      · rw [cOf_chC]; exact B2 _ _ (GlobalTheoryTheory.ConductorDivisibility.jnt_induces_ch D _ (prim_spec D _))
      · rw [cOf_chpsC]; exact B3 _ _ (GlobalTheoryTheory.ConductorDivisibility.jnt_induces_chps D _ (prim_spec D _))
    exact ⟨(congrArg norm h1).trans_le key.1, key.2⟩

theorem charF {eps : ℝ} (Fm : FamP eps) : CharF Fm :=
  fun c6 C5 => ⟨0, fun x _ i => char_at (Fm.L x i) x eps c6 C5⟩

end Formalism.MainNotions.Lnk

end

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.HN Formalism.LFunctionChainParameters.MatrixLatticeEstimates NumberField Matrix Module

def FrameReal_at (D : D7) (sg de eB : ℝ) : Prop :=
  ∃ (κ₁ : Type) (_ : Fintype κ₁) (_ : DecidableEq κ₁) (v : InfinitePlace D.what₂.LL)
    (Y : ∀ u, Matrix (D.div.Nu u).ι (D.div.Nu u).ι ℂ) (Y' : Matrix D.div.RR.ι D.div.RR.ι ℂ)
    (Ball : ∀ u, Matrix (D.div.RR.ι ⊕ κ₁) (D.div.Nu u).ι ℂ) (γ : D.what₂.Word → ℝ)
    (ιf : D.what₂.Word → Type) (_ : ∀ u, Fintype (ιf u)) (_ : ∀ u, DecidableEq (ιf u))
    (Bf : ∀ u, Matrix (D.div.RR.ι ⊕ κ₁) (ιf u) ℂ) (Vr : ∀ u, Matrix (ιf u) (D.div.Nu u).ι ℂ) (η0 η1 e0 : ℝ),
    LatGeom D.div.RR.dualB D.div.RR.dualX D.div.RR.dualL (fun u => (D.div.Nu u).b) (fun u => (D.div.Nu u).X)
      (fun u => (D.div.Nu u).L) D.div.Bk D.div.h v Y Y' Ball D.what₂.delp ∧
    (∀ u, 0 < γ u) ∧ (∀ u, Ball u = Bf u * Vr u) ∧ (∀ u, (Vr u)ᴴ * Vr u = 1) ∧
    (∀ u, Fintype.card (ιf u) = D.duS u) ∧
    -1 ≤ η0 ∧ η0 ≤ sg / 2 ∧ η1 ≤ sg / 2 ∧ 0 ≤ e0 ∧ Real.sqrt e0 ≤ sg / 2 ∧ 2 * e0 ≤ eB ∧
    ∑ u, ((Fintype.card (ιf u) : ℝ) - (Fintype.card (D.div.Nu u).ι : ℝ)) ≤ de * RsG ιf ∧
    InputSG Bf γ D.what₂.Dstar η0 η1 e0

theorem rank_eq_card {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K)
    (h : Submodule.span K (A.L : Set A.V) = ⊤) : A.rank = Fintype.card A.ι := by
  unfold HLat.rank Formalism.HN.rkK
  rw [h, finrank_top, Module.finrank_eq_card_basis A.b]

theorem frame_at_of {D : D7} (L : SizeData₂ D) (C0 CH sg de eB : ℝ) (hsgx : sg = L.sc.x ^ (-CH)) (hsg20 : sg ≤ 1 / 20)
    (hde0 : 0 ≤ de) (hde4 : de ≤ 1 / 4) (hC0 : 1 ≤ C0)
    (hR : FrameReal_at D sg de eB) (hP : ChProviso_at L C0) (hCo : ChCode_at L C0 CH) (hFull : D.NuFull)
    (hLat : Lat_at D) : Frame_at D (5 * sg + 3 * Real.sqrt de) eB := by
  obtain ⟨κ₁, i1, i2, v, Y, Y', Ball, γ, ιf, i3, i4, Bf, Vr, η0, η1, e0, hG, hγ, hBV, hV, hcard, h0, h0', h1, he0,
    hse, heB, hcor, hS⟩ := hR
  have hx0 : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hsg0 : 0 < sg := by rw [hsgx]; exact Real.rpow_pos_of_pos hx0 _
  have hD0 : 0 < D.what₂.Dstar := by rw [← D.Dstar_eq D.u₀]; exact (D.mem D.u₀).A.Dstar_pos
  have hG2 : 0 < GamL L ^ 2 := pow_pos (Real.exp_pos _) 2
  refine ⟨5 * sg + 3 * Real.sqrt de, 2 * e0, by positivity, le_refl _, by linarith, heB, fun HH hHH hpos => ?_⟩
  have hRs : D.what₂.Dstar / sg ≤ RsG ιf := by
    refine word_count_bound_holds D.what₂.Word ιf D.what₂.Dstar sg C0 (GamL L) hD0 hsg0 (by linarith) (Real.exp_pos _) ?_ ?_
    · have h := hCo
      unfold ChCode_at at h
      rw [hsgx, Real.rpow_neg hx0.le, div_inv_eq_mul]
      exact h
    · intro u
      have h := (hP u).1
      rw [le_div_iff₀ hD0] at h
      rw [hcard u]
      calc D.what₂.Dstar * (GamL L ^ 2)⁻¹ / C0 = (C0⁻¹ * D.what₂.Dstar) * (GamL L ^ 2)⁻¹ := by
            rw [div_eq_mul_inv]; ring
        _ ≤ ((D.duS u : ℝ) * GamL L ^ 2) * (GamL L ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hG2.le)
        _ = (D.duS u : ℝ) := by rw [mul_assoc, mul_inv_cancel₀ hG2.ne', mul_one]
  have hc : ∀ u, (Fintype.card (D.div.Nu u).ι : ℝ) = ((D.div.Nu u).rank : ℝ) := fun u => by
    rw [rank_eq_card (D.div.Nu u) (hFull u).2]
  have hdpos : ∀ u, (0 : ℝ) < ((D.div.Nu u).rank : ℝ) := fun u => Nat.cast_pos.mpr (hLat.1 u).1
  have hRpos : (0 : ℝ) < ∑ u, ((D.div.Nu u).rank : ℝ) :=
    Finset.sum_pos (fun u _ => hdpos u) Finset.univ_nonempty
  have hs : sFrame D.div.Nu D.div.h * (∑ u, ((D.div.Nu u).rank : ℝ)) =
      ∑ u, ((D.div.Nu u).rank : ℝ) * ((D.div.Nu u).mu - D.div.h u) := by
    unfold sFrame Rsum dU
    rw [Nat.cast_sum, div_mul_cancel₀ _ hRpos.ne']
  have hsup : ∀ u, (D.div.Nu u).muMax - D.div.h u ≤
      Finset.univ.sup' Finset.univ_nonempty (fun u => (D.div.Nu u).muMax - D.div.h u) := fun u =>
    Finset.le_sup' (fun u => (D.div.Nu u).muMax - D.div.h u) (Finset.mem_univ u)
  have hsle : sFrame D.div.Nu D.div.h ≤
      Finset.univ.sup' Finset.univ_nonempty (fun u => (D.div.Nu u).muMax - D.div.h u) := by
    have h2 : ∑ u, ((D.div.Nu u).rank : ℝ) * ((D.div.Nu u).mu - D.div.h u) ≤
        ∑ u, ((D.div.Nu u).rank : ℝ) *
          Finset.univ.sup' Finset.univ_nonempty (fun u => (D.div.Nu u).muMax - D.div.h u) :=
      Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left
        (le_trans (by have := (hLat.1 u).2; linarith) (hsup u)) (hdpos u).le)
    rw [← hs, ← Finset.sum_mul, mul_comm] at h2
    exact le_of_mul_le_mul_left h2 hRpos
  have hNum : LatNum D.div.RR.dualB D.div.RR.dualX D.div.RR.dualL (fun u => (D.div.Nu u).b)
      (fun u => (D.div.Nu u).X) (fun u => (D.div.Nu u).L) D.div.h (sFrame D.div.Nu D.div.h)
      (uFrame D.div.Nu D.div.h) HH := by
    refine ⟨?_, ?_, ?_, hHH, hpos.le⟩
    · simp only [hc]
      exact le_of_eq hs
    · unfold uFrame; linarith
    · intro u
      have := hsup u
      unfold uFrame
      show (D.div.Nu u).muMax - D.div.h u ≤ _
      linarith
  exact joint_a_ramified_holds D.what₂.LL (Module.Dual D.what₂.LL D.div.RR.V) D.div.RR.ι κ₁ D.what₂.Word
    (fun u => (D.div.Nu u).V) (fun u => (D.div.Nu u).ι) D.div.RR.dualB D.div.RR.dualX D.div.RR.dualL
    (fun u => (D.div.Nu u).b) (fun u => (D.div.Nu u).X) (fun u => (D.div.Nu u).L) D.div.Bk D.div.h v Y Y' Ball γ ιf Bf Vr
    _ _ HH D.what₂.delp D.what₂.Dstar sg η0 η1 e0 de hG hNum hγ hBV hV hD0 hsg0 hsg20 hRs h0 h0' h1 he0 hse hde0 hde4
    hcor hS

def FrameRealF {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∃ de eB : ℝ, 0 ≤ de ∧ de ≤ 1 / 4 ∧ 0 ≤ eB ∧ eB ≤ 1 / 4 ∧
    (3 * Real.sqrt de + 4 * Real.sqrt eB) * x ^ CH ≤ 1 ∧ ∀ i : Fm.Ix x, FrameReal_at (Fm.D x i) (x ^ (-CH)) de eB

theorem frameF_of {eps : ℝ} (Fm : FamP eps) (CH C0 : ℝ) (hCH : 0 < CH) (hC0 : 1 ≤ C0)
    (hReal : FrameRealF Fm CH) (hLat : LatF Fm) (cPr : ChosenProviso Fm C0) (cCo : ChosenCode Fm C0 CH)
    (hNF : NuFullF Fm) : FrameF Fm CH := by
  obtain ⟨a0, hReal⟩ := hReal
  obtain ⟨a1, hLat⟩ := hLat
  obtain ⟨a2, cPr⟩ := cPr
  obtain ⟨a3, cCo⟩ := cCo
  obtain ⟨a4, hNF⟩ := hNF
  refine ⟨Fm.x1 + 1 + |a0| + |a1| + |a2| + |a3| + |a4| + (20 : ℝ) ^ (1 / CH), fun x hx => ?_⟩
  have hpos := Fm.one_lt_family_threshold
  have h20 : (0 : ℝ) < (20 : ℝ) ^ (1 / CH) := Real.rpow_pos_of_pos (by norm_num) _
  have b0 := abs_nonneg a0
  have b1 := abs_nonneg a1
  have b2 := abs_nonneg a2
  have b3 := abs_nonneg a3
  have b4 := abs_nonneg a4
  have hx1 : Fm.x1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have e0 : x ≥ a0 := by linarith [le_abs_self a0]
  have e1 : x ≥ a1 := by linarith [le_abs_self a1]
  have e2 : x ≥ a2 := by linarith [le_abs_self a2]
  have e3 : x ≥ a3 := by linarith [le_abs_self a3]
  have e4 : x ≥ a4 := by linarith [le_abs_self a4]
  have e5 : (20 : ℝ) ^ (1 / CH) ≤ x := by linarith
  have hxC : (20 : ℝ) ≤ x ^ CH := by
    calc (20 : ℝ) = ((20 : ℝ) ^ (1 / CH)) ^ CH := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hCH.ne', Real.rpow_one]
      _ ≤ x ^ CH := Real.rpow_le_rpow h20.le e5 hCH.le
  have hxCpos : 0 < x ^ CH := by linarith
  have hsg : x ^ (-CH) = (x ^ CH)⁻¹ := Real.rpow_neg hx0.le CH
  have hsg20 : x ^ (-CH) ≤ 1 / 20 := by
    rw [hsg, one_div]; exact inv_anti₀ (by norm_num) hxC
  obtain ⟨de, eB, d0, d4, f0, f4, hnum, hR⟩ := hReal x e0
  refine ⟨5 * x ^ (-CH) + 3 * Real.sqrt de, eB, by positivity, f0, f4, ?_, fun i => ?_⟩
  · have h5 : 5 * x ^ (-CH) * x ^ CH = 5 := by rw [hsg, mul_assoc, inv_mul_cancel₀ hxCpos.ne', mul_one]
    calc (5 * x ^ (-CH) + 3 * Real.sqrt de + 4 * Real.sqrt eB) * x ^ CH
        = 5 * x ^ (-CH) * x ^ CH + (3 * Real.sqrt de + 4 * Real.sqrt eB) * x ^ CH := by ring
      _ ≤ 5 + 1 := by rw [h5]; linarith
      _ = 6 := by norm_num
  · exact frame_at_of (Fm.L x i) C0 CH (x ^ (-CH)) de eB (by rw [Fm.L_x x i hx1]) hsg20 d0 d4 hC0 (hR i)
      (cPr x e2 i) (cCo x e3 i) (hNF x e4 i) (hLat x e1 i)

end Formalism.MainNotions.Lnk

end

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.HN Formalism.LFunctionChainParameters.MatrixLatticeEstimates NumberField Matrix Module

def MatReal_at (D : D7) (sg de eB : ℝ) : Prop :=
  ∃ (κ₁ : Type) (_ : Fintype κ₁) (_ : DecidableEq κ₁) (v : InfinitePlace D.what₂.LL)
    (Y : ∀ u, Matrix (D.div.Nu u).ι (D.div.Nu u).ι ℂ) (Y' : Matrix D.div.RR.ι D.div.RR.ι ℂ)
    (Ball : ∀ u, Matrix (D.div.RR.ι ⊕ κ₁) (D.div.Nu u).ι ℂ) (γ : D.what₂.Word → ℝ)
    (ιf : D.what₂.Word → Type) (_ : ∀ u, Fintype (ιf u)) (_ : ∀ u, DecidableEq (ιf u))
    (Bf : ∀ u, Matrix (D.div.RR.ι ⊕ κ₁) (ιf u) ℂ) (Vr : ∀ u, Matrix (ιf u) (D.div.Nu u).ι ℂ) (η0 η1 e0 : ℝ),
    (∀ u, IsUnit (Y u).det) ∧ IsUnit Y'.det ∧
    (1 - D.what₂.delp) * (Fintype.card (D.div.RR.ι ⊕ κ₁) : ℝ) ≤ (Fintype.card D.div.RR.ι : ℝ) ∧
    (∀ u (k : D.div.RR.ι) (j : (D.div.Nu u).ι), Ball u (Sum.inl k) j =
      (Y'⁻¹ * (LinearMap.toMatrix (D.div.Nu u).b D.div.RR.dualB (D.div.Bk u)).map v.embedding * Y u) k j) ∧
    (∀ u, 0 < γ u) ∧ (∀ u, Ball u = Bf u * Vr u) ∧ (∀ u, (Vr u)ᴴ * Vr u = 1) ∧
    (∀ u, Fintype.card (ιf u) = D.duS u) ∧
    -1 ≤ η0 ∧ η0 ≤ sg / 2 ∧ η1 ≤ sg / 2 ∧ 0 ≤ e0 ∧ Real.sqrt e0 ≤ sg / 2 ∧ 2 * e0 ≤ eB ∧
    ∑ u, ((Fintype.card (ιf u) : ℝ) - (Fintype.card (D.div.Nu u).ι : ℝ)) ≤ de * RsG ιf ∧
    InputSG Bf γ D.what₂.Dstar η0 η1 e0

theorem cc_full (D : D7) (hRR : D.RRFull) :
    D.div.RR.dualL.FG ∧ Submodule.span D.what₂.LL (D.div.RR.dualL : Set (Module.Dual D.what₂.LL D.div.RR.V)) = ⊤ := by
  haveI : FiniteDimensional D.what₂.LL D.div.RR.V := Module.Finite.of_basis D.div.RR.b
  exact ⟨Formalism.HN.DualPolygon.dualLat_fg D.div.RR.L hRR.2, Formalism.HN.DualPolygon.dualLat_span D.div.RR.L hRR.1 hRR.2⟩

theorem frameReal_at_of (D : D7) (sg de eB : ℝ) (hRR : D.RRFull) (hNu : D.NuFull)
    (hrk : ∀ u, 0 < (D.div.Nu u).rank) (hOne : D.div.OneMapIntoCC)
    (hht : ∀ u, D.div.Bk u ≠ 0 →
      htMap (D.div.Nu u).b (D.div.Nu u).X D.div.RR.dualB D.div.RR.dualX (D.div.Bk u) ≤ D.div.h u)
    (hd0 : 0 ≤ D.what₂.delp) (hd1 : D.what₂.delp < 1) (hM : MatReal_at D sg de eB) : FrameReal_at D sg de eB := by
  obtain ⟨κ₁, i1, i2, v, Y, Y', Ball, γ, ιf, i3, i4, Bf, Vr, η0, η1, e0, hY, hY', hcard, hblock, hrest⟩ := hM
  have hsum : 0 < ∑ u, Fintype.card (D.div.Nu u).ι :=
    Finset.sum_pos (fun u _ => by rw [← rank_eq_card (D.div.Nu u) (hNu u).2]; exact hrk u) Finset.univ_nonempty
  exact ⟨κ₁, i1, i2, v, Y, Y', Ball, γ, ιf, i3, i4, Bf, Vr, η0, η1, e0,
    ⟨Formalism.HN.DualPolygon.dualFrame_unit D.div.RR.X D.div_good.1, D.div_good.2, hY, hY', (cc_full D hRR).1, (cc_full D hRR).2,
      fun u => (hNu u).1, fun u => (hNu u).2, hsum, hOne, hht, hd0, hd1, hcard, hblock⟩, hrest⟩

def MatRealF {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∃ de eB : ℝ, 0 ≤ de ∧ de ≤ 1 / 4 ∧ 0 ≤ eB ∧ eB ≤ 1 / 4 ∧
    (3 * Real.sqrt de + 4 * Real.sqrt eB) * x ^ CH ≤ 1 ∧ ∀ i : Fm.Ix x, MatReal_at (Fm.D x i) (x ^ (-CH)) de eB

theorem frameRealF_of {eps : ℝ} (Fm : FamP eps) (Cabs CH : ℝ) (lD : LinkDIV Fm Cabs CH) (lI : LinkIRR Fm)
    (hNF : NuFullF Fm) (hRk : J.MuRank Fm) (hM : MatRealF Fm CH) : FrameRealF Fm CH := by
  obtain ⟨C, a0, lD⟩ := lD
  obtain ⟨a1, lI⟩ := lI
  obtain ⟨a2, hNF⟩ := hNF
  obtain ⟨a3, hRk⟩ := hRk
  obtain ⟨a4, hM⟩ := hM
  refine ⟨1 + |a0| + |a1| + |a2| + |a3| + |a4|, fun x hx => ?_⟩
  have b0 := abs_nonneg a0
  have b1 := abs_nonneg a1
  have b2 := abs_nonneg a2
  have b3 := abs_nonneg a3
  have b4 := abs_nonneg a4
  have hx0 : 0 < x := by linarith
  have e0 : x ≥ a0 := by linarith [le_abs_self a0]
  have e1 : x ≥ a1 := by linarith [le_abs_self a1]
  have e2 : x ≥ a2 := by linarith [le_abs_self a2]
  have e3 : x ≥ a3 := by linarith [le_abs_self a3]
  have e4 : x ≥ a4 := by linarith [le_abs_self a4]
  obtain ⟨de, eB, d0, d4, f0, f4, hnum, hR⟩ := hM x e4
  refine ⟨de, eB, d0, d4, f0, f4, hnum, fun i => ?_⟩
  obtain ⟨hOne, -, -, -, hRR, hht, -⟩ := lD x e0 i
  have hlt : (Fm.D x i).what₂.delp < 1 := by
    have h1 := (lI x e1 i).2
    have h2 := Real.exp_lt_exp.mpr (show -(x ^ (Fm.ez / 7)) < 0 by
      have := Real.rpow_pos_of_pos hx0 (Fm.ez / 7); linarith)
    rw [Real.exp_zero] at h2
    linarith
  exact frameReal_at_of (Fm.D x i) _ de eB hRR (hNF x e2 i) (hRk x e3 i) hOne hht (lI x e1 i).1 hlt (hR i)

def MatS_at (D : D7) (η0 η1 e0 de : ℝ) : Prop :=
  ∃ (κ₁ : Type) (_ : Fintype κ₁) (_ : DecidableEq κ₁) (v : InfinitePlace D.what₂.LL)
    (Y : ∀ u, Matrix (D.div.Nu u).ι (D.div.Nu u).ι ℂ) (Y' : Matrix D.div.RR.ι D.div.RR.ι ℂ)
    (Ball : ∀ u, Matrix (D.div.RR.ι ⊕ κ₁) (D.div.Nu u).ι ℂ) (γ : D.what₂.Word → ℝ)
    (ιf : D.what₂.Word → Type) (_ : ∀ u, Fintype (ιf u)) (_ : ∀ u, DecidableEq (ιf u))
    (Bf : ∀ u, Matrix (D.div.RR.ι ⊕ κ₁) (ιf u) ℂ) (Vr : ∀ u, Matrix (ιf u) (D.div.Nu u).ι ℂ),
    (∀ u, IsUnit (Y u).det) ∧ IsUnit Y'.det ∧
    (1 - D.what₂.delp) * (Fintype.card (D.div.RR.ι ⊕ κ₁) : ℝ) ≤ (Fintype.card D.div.RR.ι : ℝ) ∧
    (∀ u (k : D.div.RR.ι) (j : (D.div.Nu u).ι), Ball u (Sum.inl k) j =
      (Y'⁻¹ * (LinearMap.toMatrix (D.div.Nu u).b D.div.RR.dualB (D.div.Bk u)).map v.embedding * Y u) k j) ∧
    (∀ u, 0 < γ u) ∧ (∀ u, Ball u = Bf u * Vr u) ∧ (∀ u, (Vr u)ᴴ * Vr u = 1) ∧
    (∀ u, Fintype.card (ιf u) = D.duS u) ∧
    ∑ u, ((Fintype.card (ιf u) : ℝ) - (Fintype.card (D.div.Nu u).ι : ℝ)) ≤ de * RsG ιf ∧
    InputSG Bf γ D.what₂.Dstar η0 η1 e0

def MatSF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ η0 η1 e0 de : ℝ,
    -1 ≤ η0 ∧ η0 ≤ Real.exp (-(x ^ (eps / 8))) ∧ η1 ≤ Real.exp (-(x ^ (eps / 8))) ∧
    0 ≤ e0 ∧ Real.sqrt e0 ≤ Real.exp (-(x ^ (eps / 8))) ∧ 0 ≤ de ∧ Real.sqrt de ≤ Real.exp (-(x ^ (eps / 8))) ∧
    MatS_at (Fm.D x i) η0 η1 e0 de

theorem le_sq_of_sqrt_le {y E : ℝ} (hy : 0 ≤ y) (h : Real.sqrt y ≤ E) : y ≤ E ^ 2 := by
  calc y = Real.sqrt y ^ 2 := (Real.sq_sqrt hy).symm
    _ ≤ E ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg y) h 2

theorem matRealF_of {eps : ℝ} (Fm : FamP eps) (CH : ℝ) (hCH : 0 ≤ CH) (h : MatSF Fm) : MatRealF Fm CH := by
  have heps := fam_eps_pos Fm
  obtain ⟨a0, h⟩ := h
  obtain ⟨a1, hev⟩ := ev_pow_le_exp 1 (eps / 8) (CH + 1) one_pos (by positivity)
  refine ⟨18 + |a0| + |a1|, fun x hx => ?_⟩
  have b0 := abs_nonneg a0
  have b1 := abs_nonneg a1
  have hx18 : (18 : ℝ) ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have e0' : x ≥ a0 := by linarith [le_abs_self a0]
  have e1' : x ≥ a1 := by linarith [le_abs_self a1]
  have hp := hev x e1' (by linarith)
  rw [one_mul] at hp
  set E : ℝ := Real.exp (-(x ^ (eps / 8))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hxC : 0 < x ^ CH := Real.rpow_pos_of_pos hx0 _
  have hxC1 : 1 ≤ x ^ CH := Real.one_le_rpow (by linarith) hCH
  have hsg : x ^ (-CH) = (x ^ CH)⁻¹ := Real.rpow_neg hx0.le CH

  have hkey : E * (x ^ CH * x) ≤ 1 := by
    have h1 : x ^ (CH + 1) = x ^ CH * x := by rw [Real.rpow_add hx0, Real.rpow_one]
    rw [h1] at hp
    have h2 : E * Real.exp (x ^ (eps / 8)) = 1 := by rw [hE, ← Real.exp_add]; simp
    calc E * (x ^ CH * x) ≤ E * Real.exp (x ^ (eps / 8)) := mul_le_mul_of_nonneg_left hp hE0.le
      _ = 1 := h2
  have hEx : E * x ^ CH ≤ 1 / 18 := by
    have h3 : E * x ^ CH * 18 ≤ E * x ^ CH * x := mul_le_mul_of_nonneg_left hx18 (by positivity)
    have h4 : E * x ^ CH * x = E * (x ^ CH * x) := by ring
    linarith
  have hE18 : E ≤ 1 / 18 := by
    have : E * 1 ≤ E * x ^ CH := mul_le_mul_of_nonneg_left hxC1 hE0.le
    linarith
  have hEsg : E ≤ x ^ (-CH) / 2 := by
    rw [hsg]
    have h5 : E = (E * x ^ CH) * (x ^ CH)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hxC.ne', mul_one]
    have h6 : (E * x ^ CH) * (x ^ CH)⁻¹ ≤ (1 / 18) * (x ^ CH)⁻¹ :=
      mul_le_mul_of_nonneg_right hEx (inv_nonneg.mpr hxC.le)
    have h7 : 0 ≤ (x ^ CH)⁻¹ := inv_nonneg.mpr hxC.le
    rw [h5]
    linarith
  have hs1 : Real.sqrt (E ^ 2) = E := Real.sqrt_sq hE0.le
  have hs2 : Real.sqrt (2 * E ^ 2) ≤ 2 * E := by
    calc Real.sqrt (2 * E ^ 2) ≤ Real.sqrt ((2 * E) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg E])
      _ = 2 * E := Real.sqrt_sq (by positivity)
  refine ⟨E ^ 2, 2 * E ^ 2, by positivity, by nlinarith, by positivity, by nlinarith, ?_, fun i => ?_⟩
  · rw [hs1]
    calc (3 * E + 4 * Real.sqrt (2 * E ^ 2)) * x ^ CH ≤ (3 * E + 4 * (2 * E)) * x ^ CH :=
          mul_le_mul_of_nonneg_right (by linarith) hxC.le
      _ = 11 * (E * x ^ CH) := by ring
      _ ≤ 1 := by linarith
  · obtain ⟨η0, η1, e0, de, g1, g2, g3, g4, g5, g6, g7, κ₁, i1, i2, v, Y, Y', Ball, γ, ιf, i3, i4, Bf, Vr, m1, m2, m3, m4,
      m5, m6, m7, m8, m9, m10⟩ := h x e0' i
    have hRs : 0 ≤ RsG ιf := by unfold RsG; exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    exact ⟨κ₁, i1, i2, v, Y, Y', Ball, γ, ιf, i3, i4, Bf, Vr, η0, η1, e0, m1, m2, m3, m4, m5, m6, m7, m8, g1,
      le_trans g2 hEsg, le_trans g3 hEsg, g4, le_trans g5 hEsg, by have := le_sq_of_sqrt_le g4 g5; linarith,
      le_trans m9 (mul_le_mul_of_nonneg_right (le_sq_of_sqrt_le g6 g7) hRs), m10⟩

def MatK_at (D : D7) (η0 e0 : ℝ) : Prop :=
  ∃ (v : InfinitePlace D.what₂.LL)
    (Y : ∀ u, Matrix (D.div.Nu u).ι (D.div.Nu u).ι ℂ) (Y' : Matrix D.div.RR.ι D.div.RR.ι ℂ)
    (Ball : ∀ u, Matrix (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) (D.div.Nu u).ι ℂ) (γ : D.what₂.Word → ℝ)
    (Bf : ∀ u, Matrix (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) (Fin (D.duS u)) ℂ)
    (Vr : ∀ u, Matrix (Fin (D.duS u)) (D.div.Nu u).ι ℂ),
    (∀ u, IsUnit (Y u).det) ∧ IsUnit Y'.det ∧
    (∀ u (k : D.div.RR.ι) (j : (D.div.Nu u).ι), Ball u (Sum.inl k) j =
      (Y'⁻¹ * (LinearMap.toMatrix (D.div.Nu u).b D.div.RR.dualB (D.div.Bk u)).map v.embedding * Y u) k j) ∧
    (∀ u, 0 < γ u) ∧ (∀ u, Ball u = Bf u * Vr u) ∧ (∀ u, (Vr u)ᴴ * Vr u = 1) ∧
    (∀ u u', u ≠ u' → Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq (KpG Bf γ u u') ≤
      (1 + η0) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar) ∧
    (∀ u, Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq (KdG Bf γ u - 1) ≤ e0 * (D.duS u : ℝ))

theorem matS_at_of (D : D7) (η0 η1 e0 de : ℝ) (hd0 : 0 ≤ D.what₂.delp)
    (hall : (D.what₂.Dall : ℝ) ≤ (1 + η1) * D.what₂.Dstar)
    (hram : ∀ u, (D.duS u : ℝ) - ((D.mem u).A.du : ℝ) ≤ de * (D.duS u : ℝ))
    (hK : MatK_at D η0 e0) : MatS_at D η0 η1 e0 de := by
  obtain ⟨v, Y, Y', Ball, γ, Bf, Vr, m1, m2, m4, m5, m6, m7, k1, k2⟩ := hK
  have hκ : Fintype.card D.div.RR.ι = D.what₂.Drows := by
    rw [← Module.finrank_eq_card_basis D.div.RR.b, D.RRV_finrank]
  have hle : D.what₂.Drows ≤ D.what₂.Dall := by
    have h1 := D.what₂.D_eq
    have h2 : (0 : ℝ) ≤ (D.what₂.Dall : ℝ) := Nat.cast_nonneg _
    have h3 : (D.what₂.Drows : ℝ) ≤ (D.what₂.Dall : ℝ) := by rw [h1]; nlinarith
    exact_mod_cast h3
  have hα : Fintype.card (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) = D.what₂.Dall := by
    rw [Fintype.card_sum, Fintype.card_fin, hκ]; omega
  have hι : ∀ u, Fintype.card (D.div.Nu u).ι = (D.mem u).A.du := fun u => by
    rw [← Module.finrank_eq_card_basis (D.div.Nu u).b, D.NuV_finrank u]
  refine ⟨Fin (D.what₂.Dall - D.what₂.Drows), inferInstance, inferInstance, v, Y, Y', Ball, γ, fun u => Fin (D.duS u),
    fun _ => inferInstance, fun _ => inferInstance, Bf, Vr, m1, m2, ?_, m4, m5, m6, m7, fun u => Fintype.card_fin _, ?_,
    ?_, ?_, ?_⟩
  · rw [hα, hκ, D.what₂.D_eq]
  · unfold RsG
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun u _ => ?_)
    rw [Fintype.card_fin, hι u]
    exact hram u
  · intro u u' huu
    rw [Fintype.card_fin, Fintype.card_fin]
    exact k1 u u' huu
  · intro u
    rw [Fintype.card_fin]
    exact k2 u
  · rw [hα]; exact hall

def MatKF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ η0 e0 : ℝ, -1 ≤ η0 ∧ η0 ≤ Real.exp (-(x ^ (eps / 8))) ∧
    0 ≤ e0 ∧ Real.sqrt e0 ≤ Real.exp (-(x ^ (eps / 8))) ∧ MatK_at (Fm.D x i) η0 e0

def RamShareF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ de : ℝ, 0 ≤ de ∧ Real.sqrt de ≤ Real.exp (-(x ^ (eps / 8))) ∧
    ∀ u, ((Fm.D x i).duS u : ℝ) - (((Fm.D x i).mem u).A.du : ℝ) ≤ de * ((Fm.D x i).duS u : ℝ)

theorem matSF_of {eps : ℝ} (Fm : FamP eps) (C0 : ℝ) (lS : LinkS Fm C0) (cPr : ChosenProviso Fm C0) (lI : LinkIRR Fm)
    (hK : MatKF Fm) (hR : RamShareF Fm) : MatSF Fm := by
  obtain ⟨a0, lS⟩ := lS
  obtain ⟨a1, cPr⟩ := cPr
  obtain ⟨a2, lI⟩ := lI
  obtain ⟨a3, hK⟩ := hK
  obtain ⟨a4, hR⟩ := hR
  refine ⟨|a0| + |a1| + |a2| + |a3| + |a4|, fun x hx i => ?_⟩
  have b0 := abs_nonneg a0
  have b1 := abs_nonneg a1
  have b2 := abs_nonneg a2
  have b3 := abs_nonneg a3
  have b4 := abs_nonneg a4
  have e0' : x ≥ a0 := by linarith [le_abs_self a0]
  have e1' : x ≥ a1 := by linarith [le_abs_self a1]
  have e2' : x ≥ a2 := by linarith [le_abs_self a2]
  have e3' : x ≥ a3 := by linarith [le_abs_self a3]
  have e4' : x ≥ a4 := by linarith [le_abs_self a4]
  obtain ⟨_t0, η1, _t1, _, _, s3, _, hS⟩ := lS x e0' i
  obtain ⟨η0, e0, k1, k2, k3, k4, hKi⟩ := hK x e3' i
  obtain ⟨de, r1, r2, r3⟩ := hR x e4' i
  exact ⟨η0, η1, e0, de, k1, k2, s3, k3, k4, r1, r2,
    matS_at_of (Fm.D x i) η0 η1 e0 de (lI x e2' i).1 (hS (cPr x e1' i)).2.2 r3 hKi⟩

theorem frameRealF_of' {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 : ℝ) (hCH : 0 ≤ CH) (lD : LinkDIV Fm Cabs CH)
    (lI : LinkIRR Fm) (lS : LinkS Fm C0) (cPr : ChosenProviso Fm C0) (hNF : NuFullF Fm) (hRk : J.MuRank Fm)
    (hK : MatKF Fm) (hR : RamShareF Fm) : FrameRealF Fm CH :=
  frameRealF_of Fm Cabs CH lD lI hNF hRk (matRealF_of Fm CH hCH (matSF_of Fm C0 lS cPr lI hK hR))

def RamRank_at (D : D7) : Prop :=
  ∀ u, ((D.mem u).A.du : ℝ) = (D.duS u : ℝ) * (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f

theorem ramShare_at_of {D : D7} (L : SizeData₂ D) (hT : L.TuGe) (hR : RamRank_at D) (hb3 : 3 ≤ L.sc.b) :
    ∀ u, (D.duS u : ℝ) - ((D.mem u).A.du : ℝ) ≤ (2 * (D.R.f : ℝ) / L.sc.b) * (D.duS u : ℝ) := by
  intro u
  have hb0 : 0 < L.sc.b := by linarith
  have hm : (1 : ℝ) ≤ (D.R.m : ℝ) / 2 := by
    have : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
    linarith
  have hTb : L.sc.b ≤ ((D.mem u).A.T : ℝ) := by
    calc L.sc.b = L.sc.b ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ L.sc.b ^ ((D.R.m : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) hm
      _ ≤ _ := hT u
  have hT0 : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by linarith
  have hf0 : (0 : ℝ) ≤ 2 * (D.R.f : ℝ) := by positivity
  by_cases h0 : D.duS u = 0
  · have h1 := hR u
    rw [h0] at h1 ⊢
    simp only [Nat.cast_zero, zero_mul] at h1
    rw [h1]; simp
  · have hdM : (0 : ℝ) < (D.duS u : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
    obtain ⟨-, -, -, h4⟩ := Formalism.LFunctionChainParameters.UnitWeightPartition.deficit_bounds D.R.f ((D.mem u).A.T : ℝ) (D.duS u : ℝ)
      ((D.mem u).A.du : ℝ) hdM (by linarith) (hR u)
    have h5 : 2 * (D.R.f : ℝ) / ((D.mem u).A.T : ℝ) ≤ 2 * (D.R.f : ℝ) / L.sc.b :=
      div_le_div_of_nonneg_left hf0 hb0 hTb
    have h6 : (D.duS u : ℝ) - ((D.mem u).A.du : ℝ) =
        (1 - ((D.mem u).A.du : ℝ) / (D.duS u : ℝ)) * (D.duS u : ℝ) := by
      field_simp
    rw [h6]
    exact mul_le_mul_of_nonneg_right (le_trans h4 h5) hdM.le

def RamRankF {eps : ℝ} (Fm : FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, RamRank_at (Fm.D x i)

theorem ramShareF_of {eps : ℝ} (Fm : FamP eps) (hTu : TuSize Fm) (hR : RamRankF Fm) : RamShareF Fm := by
  have heps := fam_eps_pos Fm
  obtain ⟨a0, hTu⟩ := hTu
  obtain ⟨a1, hR⟩ := hR
  obtain ⟨a2, hev⟩ := ev_pow_le_exp (1 / 2) eps 6 (by norm_num) heps
  have hδ : 0 < 7 * eps / 8 := by positivity
  refine ⟨Fm.x1 + 3 + |a0| + |a1| + |a2| + (4 : ℝ) ^ (1 / (7 * eps / 8)), fun x hx i => ?_⟩
  have hpos := Fm.one_lt_family_threshold
  have h4p : (0 : ℝ) < (4 : ℝ) ^ (1 / (7 * eps / 8)) := Real.rpow_pos_of_pos (by norm_num) _
  have b0 := abs_nonneg a0
  have b1 := abs_nonneg a1
  have b2 := abs_nonneg a2
  have hx1 : Fm.x1 < x := by linarith
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have e0' : x ≥ a0 := by linarith [le_abs_self a0]
  have e1' : x ≥ a1 := by linarith [le_abs_self a1]
  have e2' : x ≥ a2 := by linarith [le_abs_self a2]
  have e3' : (4 : ℝ) ^ (1 / (7 * eps / 8)) ≤ x := by linarith
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hb : (Fm.L x i).sc.b = Real.exp (x ^ eps) := by
    show Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) = _
    rw [hsx, hse]
  have hxe : 1 ≤ x ^ eps := Real.one_le_rpow (by linarith) heps.le

  have h4 : (4 : ℝ) ≤ x ^ (7 * eps / 8) := by
    calc (4 : ℝ) = ((4 : ℝ) ^ (1 / (7 * eps / 8))) ^ (7 * eps / 8) := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one]
      _ ≤ x ^ (7 * eps / 8) := Real.rpow_le_rpow h4p.le e3' hδ.le
  have hsplit : x ^ eps = x ^ (eps / 8) * x ^ (7 * eps / 8) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hd0 : 0 < x ^ (eps / 8) := Real.rpow_pos_of_pos hx0 _
  have h4x : 4 * x ^ (eps / 8) ≤ x ^ eps := by
    rw [hsplit]; nlinarith
  have hb3 : 3 ≤ (Fm.L x i).sc.b := by
    rw [hb]
    have h1 : x ^ eps + 1 ≤ Real.exp (x ^ eps) := Real.add_one_le_exp _
    have h2 : (4 : ℝ) ≤ x ^ eps := by
      have : 1 ≤ x ^ (eps / 8) := Real.one_le_rpow (by linarith) (by positivity)
      linarith
    linarith
  have hb0 : 0 < (Fm.L x i).sc.b := by linarith
  have hf : (2 : ℝ) * ((Fm.D x i).R.f : ℝ) ≤ Real.exp (1 / 2 * x ^ eps) := by
    have hk : ((Fm.D x i).R.k : ℝ) ≤ x ^ (5 : ℝ) := by
      have := winC (L := Fm.L x i) (Fm.sizes x hx1 i).2.2.1
      rwa [hsx] at this
    have hfk : ((Fm.D x i).R.f : ℝ) ≤ ((Fm.D x i).R.k : ℝ) := by exact_mod_cast (Fm.D x i).R.f_le_k
    have h6 : x ^ (6 : ℝ) = x ^ (5 : ℝ) * x := by
      rw [show (6 : ℝ) = 5 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]
    have h5p : 0 < x ^ (5 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have := hev x e2' (by linarith)
    rw [h6] at this
    nlinarith
  refine ⟨2 * ((Fm.D x i).R.f : ℝ) / (Fm.L x i).sc.b, by positivity, ?_,
    ramShare_at_of (Fm.L x i) (hTu x e0' i).1 (hR x e1' i) hb3⟩
  have hE0 : 0 ≤ Real.exp (-(x ^ (eps / 8))) := (Real.exp_pos _).le
  rw [← Real.sqrt_sq hE0]
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ hb0, hb, sq, ← Real.exp_add, ← Real.exp_add]
  refine le_trans hf (Real.exp_le_exp.mpr ?_)
  linarith

theorem frameRealF_of'' {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 : ℝ) (hCH : 0 ≤ CH) (lD : LinkDIV Fm Cabs CH)
    (lI : LinkIRR Fm) (lS : LinkS Fm C0) (cPr : ChosenProviso Fm C0) (hNF : NuFullF Fm) (hRk : J.MuRank Fm)
    (hTu : TuSize Fm) (hRam : RamRankF Fm) (hK : MatKF Fm) : FrameRealF Fm CH :=
  frameRealF_of' Fm Cabs CH C0 hCH lD lI lS cPr hNF hRk hK (ramShareF_of Fm hTu hRam)

end Formalism.MainNotions.Lnk

end

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.LFunctionChainParameters.MatrixLatticeEstimates Matrix NumberField
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)

theorem finrank_Cu (D : D7) (u : D.what₂.Word) : Module.finrank ℂ (D.s.Cu u) = D.duS u := by
  unfold D7.duS
  exact LinearEquiv.finrank_eq (D.s_Cu u)

def eC (D : D7) (u : D.what₂.Word) : OrthonormalBasis (Fin (D.duS u)) ℂ (D.s.Cu u) :=
  (stdOrthonormalBasis ℂ (D.s.Cu u)).reindex (finCongr (finrank_Cu D u))

abbrev RowIx (D : D7) : Type := D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)

def PMat (D : D7) (f : OrthonormalBasis (RowIx D) ℂ D.s.HH) (u : D.what₂.Word) :
    Matrix (RowIx D) (Fin (D.duS u)) ℂ :=
  fun a j => inner ℂ (f a) (D.s.Pu u (eC D u j))

def opMat (D : D7) {u u' : D.what₂.Word} (A : D.s.Cu u' →L[ℂ] D.s.Cu u) : Matrix (Fin (D.duS u)) (Fin (D.duS u')) ℂ :=
  fun i j => inner ℂ (eC D u i) (A (eC D u' j))

structure IsIdOrConj (ε : ℂ →+* ℂ) : Prop where
  norm : ∀ z, ‖ε z‖ = ‖z‖
  star : ∀ z, ε (star z) = star (ε z)
  real : ∀ r : ℝ, ε (r : ℂ) = r

theorem hs_opMat (D : D7) {u u' : D.what₂.Word} (A : D.s.Cu u' →L[ℂ] D.s.Cu u) (ε : ℂ →+* ℂ) (hε : IsIdOrConj ε) :
    hsSq ((opMat D A).map ε) = S.hsNormSq A := by
  unfold hsSq S.hsNormSq S.hsInner
  rw [Finset.sum_comm]
  have h1 : ∀ j : Fin (D.duS u'), ∑ i, ‖((opMat D A).map ε) i j‖ ^ 2 = ‖A (eC D u' j)‖ ^ 2 := by
    intro j
    simp only [Matrix.map_apply, hε.norm, opMat]
    exact (eC D u).sum_sq_norm_inner_right (A (eC D u' j))
  simp only [h1]
  rw [Complex.re_sum]
  have h2 : ∀ l, (inner ℂ (A (stdOrthonormalBasis ℂ (D.s.Cu u') l)) (A (stdOrthonormalBasis ℂ (D.s.Cu u') l))).re =
      ‖A (stdOrthonormalBasis ℂ (D.s.Cu u') l)‖ ^ 2 := fun l => by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  simp only [h2]
  rw [← Equiv.sum_comp (finCongr (finrank_Cu D u'))
    (fun j => ‖A (eC D u' j)‖ ^ 2)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  unfold eC
  rw [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply]

theorem gram_PMat (D : D7) (f : OrthonormalBasis (RowIx D) ℂ D.s.HH) (u u' : D.what₂.Word) :
    (PMat D f u)ᴴ * PMat D f u' = fun i j => inner ℂ (D.s.Pu u (eC D u i)) (D.s.Pu u' (eC D u' j)) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, PMat]
  rw [← f.sum_inner_mul_inner (D.s.Pu u (eC D u i)) (D.s.Pu u' (eC D u' j))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← inner_conj_symm (D.s.Pu u (eC D u i)) (f a)]
  rfl

theorem conjT_map {m n : Type} (A : Matrix m n ℂ) (ε : ℂ →+* ℂ) (hε : IsIdOrConj ε) : (A.map ε)ᴴ = (Aᴴ).map ε := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, hε.star]

theorem sqrt_inv_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Real.sqrt (a⁻¹ * b⁻¹) = (a * b) ^ (-(1 / 2 : ℝ)) := by
  rw [← mul_inv, Real.sqrt_eq_rpow, Real.inv_rpow (mul_pos ha hb).le, Real.rpow_neg (mul_pos ha hb).le]

theorem opMat_KD (D : D7) (u u' : D.what₂.Word) (i : Fin (D.duS u)) (j : Fin (D.duS u')) :
    opMat D (S.KD D u u') i j = (((S.c0 D.s u * S.c0 D.s u') ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      inner ℂ (D.s.Pu u (eC D u i)) (D.s.Pu u' (eC D u' j)) := by
  unfold opMat S.KD S.Kmat
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

theorem kp_eq (D : D7) (f : OrthonormalBasis (RowIx D) ℂ D.s.HH) (ε : ℂ →+* ℂ) (hε : IsIdOrConj ε)
    (hc : ∀ u, 0 < S.c0 D.s u) (u u' : D.what₂.Word) :
    KpG (fun u => (PMat D f u).map ε) (fun u => (S.c0 D.s u)⁻¹) u u' = (opMat D (S.KD D u u')).map ε := by
  unfold KpG
  rw [conjT_map _ ε hε, ← Matrix.map_mul, gram_PMat, sqrt_inv_mul (hc u) (hc u')]
  ext i j
  rw [Matrix.smul_apply, Matrix.map_apply, opMat_KD, map_mul, hε.real, smul_eq_mul]
  rfl

theorem opMat_sub_id (D : D7) (u : D.what₂.Word) (A : D.s.Cu u →L[ℂ] D.s.Cu u) (ε : ℂ →+* ℂ) :
    (opMat D (A - ContinuousLinearMap.id ℂ (D.s.Cu u))).map ε = (opMat D A).map ε - 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, opMat, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    inner_sub_right, map_sub]
  congr 1
  rw [orthonormal_iff_ite.mp (eC D u).orthonormal i j, Matrix.one_apply]
  split_ifs <;> simp

def BlockReal_at (D : D7) : Prop :=
  ∃ (ε : ℂ →+* ℂ) (_ : IsIdOrConj ε) (f : OrthonormalBasis (RowIx D) ℂ D.s.HH) (v : InfinitePlace D.what₂.LL)
    (Y : ∀ u, Matrix (D.div.Nu u).ι (D.div.Nu u).ι ℂ) (Y' : Matrix D.div.RR.ι D.div.RR.ι ℂ)
    (Vr : ∀ u, Matrix (Fin (D.duS u)) (D.div.Nu u).ι ℂ),
    (∀ u, IsUnit (Y u).det) ∧ IsUnit Y'.det ∧ (∀ u, (Vr u)ᴴ * Vr u = 1) ∧
    ∀ u (k : D.div.RR.ι) (j : (D.div.Nu u).ι), ((PMat D f u).map ε * Vr u) (Sum.inl k) j =
      (Y'⁻¹ * (LinearMap.toMatrix (D.div.Nu u).b D.div.RR.dualB (D.div.Bk u)).map v.embedding * Y u) k j

def UnfoldingConstantsPos (D : D7) : Prop := ∀ u, 0 < S.c0 D.s u

theorem matK_at_of {D : D7} (L : SizeData₂ D) (η0 e0 : ℝ) (hB : BlockReal_at D) (hc : UnfoldingConstantsPos D)
    (h1 : ∀ u u', u ≠ u' → L.hsSq u u' ≤ (1 + η0) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar)
    (h2 : ∀ u, hsDiagFull D u ≤ e0 * (D.duS u : ℝ)) : MatK_at D η0 e0 := by
  obtain ⟨ε, hε, f, v, Y, Y', Vr, b1, b2, b3, b4⟩ := hB
  refine ⟨v, Y, Y', fun u => (PMat D f u).map ε * Vr u, fun u => (S.c0 D.s u)⁻¹, fun u => (PMat D f u).map ε, Vr,
    b1, b2, b4, fun u => inv_pos.mpr (hc u), fun _ => rfl, b3, fun u u' huu => ?_, fun u => ?_⟩
  · rw [kp_eq D f ε hε hc, hs_opMat D _ ε hε]
    exact h1 u u' huu
  · unfold KdG
    rw [kp_eq D f ε hε hc, ← opMat_sub_id, hs_opMat D _ ε hε]
    exact h2 u

def iotaC (D : D7) (u : D.what₂.Word) : D.what₂.Mu u →ₗ[ℂ] D.s.Cu u :=
  (D.s_Cu u).symm.toLinearMap ∘ₗ
    (Submodule.inclusion (inf_le_left : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0)) ∘ₗ (D.eMu u).toLinearMap

theorem besS_eq (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) (F : D.what₂.EE) :
    D.besS u φ F = inner ℂ (D.sEE F) (D.s.Pu u (iotaC D u φ)) := rfl

theorem iotaC_inner (D : D7) (u : D.what₂.Word) (φ ψ : D.what₂.Mu u) :
    inner ℂ (iotaC D u φ) (iotaC D u ψ) = inner ℂ φ ψ := by
  rw [D.s_Cu_isom u, D.eMu_isom u]
  unfold iotaC
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

theorem card_RRι (D : D7) : Fintype.card D.div.RR.ι = D.what₂.Drows := by
  rw [← Module.finrank_eq_card_basis D.div.RR.b, D.RRV_finrank]

def oE (D : D7) : OrthonormalBasis D.div.RR.ι ℂ D.what₂.EE :=
  D.what₂.onb.reindex (Fintype.equivOfCardEq (by rw [Fintype.card_fin, card_RRι]))

theorem finrank_Mu (D : D7) (u : D.what₂.Word) : Module.finrank ℂ (D.what₂.Mu u) = Fintype.card (D.div.Nu u).ι :=
  Module.finrank_eq_card_basis (Module.Basis.mk (D.jN_basis u).1 (le_of_eq (D.jN_basis u).2.symm))

def oM (D : D7) (u : D.what₂.Word) : OrthonormalBasis (D.div.Nu u).ι ℂ (D.what₂.Mu u) :=
  (stdOrthonormalBasis ℂ (D.what₂.Mu u)).reindex
    (Fintype.equivOfCardEq (by rw [Fintype.card_fin, finrank_Mu]))

theorem sEE_inner (D : D7) (x y : D.what₂.EE) : inner ℂ (D.sEE x) (D.sEE y) = inner ℂ y x := by
  have hI : (starRingEnd ℂ) (RCLike.I : ℂ) = -(RCLike.I : ℂ) := RCLike.conj_I
  have hn : ‖(RCLike.I : ℂ)‖ = 1 := by simp
  have hII : (RCLike.I : ℂ) * (RCLike.I : ℂ) = -1 := by simp
  have e1 : D.sEE x + D.sEE y = D.sEE (x + y) := (map_add _ _ _).symm
  have e2 : D.sEE x - D.sEE y = D.sEE (x - y) := (map_sub _ _ _).symm
  have e3 : D.sEE x - (RCLike.I : ℂ) • D.sEE y = D.sEE (x + (RCLike.I : ℂ) • y) := by
    rw [map_add, map_smulₛₗ, hI, neg_smul, sub_eq_add_neg]
  have e4 : D.sEE x + (RCLike.I : ℂ) • D.sEE y = D.sEE (x - (RCLike.I : ℂ) • y) := by
    rw [map_sub, map_smulₛₗ, hI, neg_smul, sub_neg_eq_add]
  have f3 : ‖y - (RCLike.I : ℂ) • x‖ = ‖x + (RCLike.I : ℂ) • y‖ := by
    have : y - (RCLike.I : ℂ) • x = (-(RCLike.I : ℂ)) • (x + (RCLike.I : ℂ) • y) := by
      rw [smul_add, smul_smul, neg_mul, hII, neg_neg, one_smul, neg_smul]; abel
    rw [this, norm_smul, norm_neg, hn, one_mul]
  have f4 : ‖y + (RCLike.I : ℂ) • x‖ = ‖x - (RCLike.I : ℂ) • y‖ := by
    have : y + (RCLike.I : ℂ) • x = (RCLike.I : ℂ) • (x - (RCLike.I : ℂ) • y) := by
      rw [smul_sub, smul_smul, hII, neg_smul, one_smul]; abel
    rw [this, norm_smul, hn, one_mul]
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (D.sEE x) (D.sEE y), inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) y x,
    e1, e2, e3, e4, D.sEE.norm_map, D.sEE.norm_map, D.sEE.norm_map, D.sEE.norm_map, f3, f4, add_comm y x,
    norm_sub_rev y x]

theorem rows_orthonormal (D : D7) (V : D.what₂.EE ≃ₗᵢ[ℂ] D.what₂.EE) :
    Orthonormal ℂ (fun k : D.div.RR.ι => D.sEE (V (oE D k))) := by
  rw [orthonormal_iff_ite]
  intro k k'
  rw [sEE_inner, V.inner_map_map, orthonormal_iff_ite.mp (oE D).orthonormal k' k]
  by_cases h : k = k'
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

theorem Drows_le (D : D7) : D.what₂.Drows ≤ D.what₂.Dall := by
  have h := (rows_orthonormal D (LinearIsometryEquiv.refl ℂ _)).linearIndependent.fintype_card_le_finrank
  rwa [card_RRι, D.s_HH] at h

theorem exists_rowBasis (D : D7) (V : D.what₂.EE ≃ₗᵢ[ℂ] D.what₂.EE) :
    ∃ f : OrthonormalBasis (RowIx D) ℂ D.s.HH, ∀ k, f (Sum.inl k) = D.sEE (V (oE D k)) := by
  have hcard : Module.finrank ℂ D.s.HH = Fintype.card (RowIx D) := by
    rw [D.s_HH, Fintype.card_sum, card_RRι, Fintype.card_fin]
    have := Drows_le D
    omega
  have hv : Orthonormal ℂ ((Set.range (Sum.inl : D.div.RR.ι → RowIx D)).restrict
      (Sum.elim (fun k => D.sEE (V (oE D k))) (fun _ => 0))) := by
    have h0 := rows_orthonormal D V
    rw [orthonormal_iff_ite] at h0 ⊢
    intro a b
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨k, hk⟩ := ha
    obtain ⟨k', hk'⟩ := hb
    subst hk; subst hk'
    show inner ℂ (D.sEE (V (oE D k))) (D.sEE (V (oE D k'))) = _
    rw [h0 k k']
    by_cases h : k = k'
    · subst h; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg (fun h' => h (Sum.inl_injective (congrArg Subtype.val h')))]
  obtain ⟨f, hf⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨f, fun k => by rw [hf (Sum.inl k) ⟨k, rfl⟩]; rfl⟩

open Module in

def bN (D : D7) (u : D.what₂.Word) : Basis (D.div.Nu u).ι ℂ (D.what₂.Mu u) :=
  Basis.mk (D.jN_basis u).1 (le_of_eq (D.jN_basis u).2.symm)

open Module in

def bE (D : D7) : Basis D.div.RR.ι ℂ D.what₂.EE := Basis.mk D.jEE_basis.1 (le_of_eq D.jEE_basis.2.symm)

theorem bN_apply (D : D7) (u : D.what₂.Word) (j : (D.div.Nu u).ι) : bN D u j = D.jN u ((D.div.Nu u).b j) := by
  unfold bN; rw [Module.Basis.mk_apply]

theorem bE_apply (D : D7) (k : D.div.RR.ι) : bE D k = D.jEE (D.div.RR.b k) := by
  unfold bE; rw [Module.Basis.mk_apply]

theorem bes_sum_left (D : D7) (u : D.what₂.Word) (F : D.what₂.EE) {ι : Type} (t : Finset ι) (c : ι → ℂ)
    (g : ι → D.what₂.Mu u) : D.besS u (∑ i ∈ t, c i • g i) F = ∑ i ∈ t, c i * D.besS u (g i) F := by
  simp only [besS_eq, map_sum, map_smul, inner_sum, inner_smul_right]

theorem bes_sum_right (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) {ι : Type} (t : Finset ι) (c : ι → ℂ)
    (g : ι → D.what₂.EE) : D.besS u φ (∑ i ∈ t, c i • g i) = ∑ i ∈ t, c i * D.besS u φ (g i) := by
  simp only [besS_eq, map_sum, map_smulₛₗ, sum_inner, inner_smul_left, Complex.conj_conj]

def Vr0 (D : D7) (U : ∀ u, D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u) (u : D.what₂.Word) :
    Matrix (Fin (D.duS u)) (D.div.Nu u).ι ℂ :=
  fun i j => inner ℂ (eC D u i) (iotaC D u (U u (oM D u j)))

theorem vr_gram (D : D7) (U : ∀ u, D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u) (u : D.what₂.Word) :
    (Vr0 D U u)ᴴ * Vr0 D U u = 1 := by
  ext j j'
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Vr0]
  have h : ∀ i, star (inner ℂ (eC D u i) (iotaC D u (U u (oM D u j)))) *
      inner ℂ (eC D u i) (iotaC D u (U u (oM D u j'))) =
      inner ℂ (iotaC D u (U u (oM D u j))) (eC D u i) * inner ℂ (eC D u i) (iotaC D u (U u (oM D u j'))) := by
    intro i
    rw [← inner_conj_symm (iotaC D u (U u (oM D u j))) (eC D u i)]
    rfl
  simp only [h]
  rw [(eC D u).sum_inner_mul_inner, iotaC_inner, (U u).inner_map_map,
    orthonormal_iff_ite.mp (oM D u).orthonormal j j', Matrix.one_apply]

theorem pm_vr (D : D7) (f : OrthonormalBasis (RowIx D) ℂ D.s.HH) (U : ∀ u, D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u)
    (u : D.what₂.Word) (a : RowIx D) (j : (D.div.Nu u).ι) :
    (PMat D f u * Vr0 D U u) a j = inner ℂ (f a) (D.s.Pu u (iotaC D u (U u (oM D u j)))) := by
  rw [Matrix.mul_apply]
  conv_rhs => rw [← (eC D u).sum_repr' (iotaC D u (U u (oM D u j)))]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right, PMat, Vr0]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem block_eq (D : D7) (hRat : D.BuRational) (V : D.what₂.EE ≃ₗᵢ[ℂ] D.what₂.EE)
    (U : ∀ u, D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u) (a : D.what₂.Word → ℂ) (ha : ∀ u, a u ≠ 0)
    (hU : ∀ u φ F, D.what₂.Bu u φ F = a u * D.besS u (U u φ) (V F)) (u : D.what₂.Word) :
    (fun (k : D.div.RR.ι) (j : (D.div.Nu u).ι) => D.besS u (U u (oM D u j)) (V (oE D k))) =
      ((bE D).toMatrix (oE D))ᵀ *
        (LinearMap.toMatrix (D.div.Nu u).b D.div.RR.dualB (D.div.Bk u)).map D.what₂.embLL *
        ((a u)⁻¹ • (bN D u).toMatrix (oM D u)) := by
  have hbase : ∀ (k' : D.div.RR.ι) (j' : (D.div.Nu u).ι), D.besS u (U u (bN D u j')) (V (bE D k')) =
      (a u)⁻¹ * D.what₂.embLL (LinearMap.toMatrix (D.div.Nu u).b D.div.RR.dualB (D.div.Bk u) k' j') := by
    intro k' j'
    rw [LinearMap.toMatrix_apply]
    have h1 : D.div.RR.dualB.repr (D.div.Bk u ((D.div.Nu u).b j')) k' =
        D.div.Bk u ((D.div.Nu u).b j') (D.div.RR.b k') := Module.Basis.dualBasis_repr _ _ _
    rw [h1, ← hRat u, hU u, ← mul_assoc, inv_mul_cancel₀ (ha u), one_mul, bN_apply, bE_apply]
  ext k j
  have e1 : oM D u j = ∑ j', (bN D u).repr (oM D u j) j' • bN D u j' := ((bN D u).sum_repr _).symm
  have e2 : oE D k = ∑ k', (bE D).repr (oE D k) k' • bE D k' := ((bE D).sum_repr _).symm
  conv_lhs => rw [e1, e2]
  simp only [map_sum, map_smul]
  rw [bes_sum_left]
  simp only [bes_sum_right, hbase]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  simp only [Matrix.transpose_apply, Module.Basis.toMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem det_toMatrix_unit {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (b b' : Module.Basis ι ℂ M) : IsUnit (b.toMatrix b').det :=
  Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip b b')

theorem det_map_unit {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (ε : ℂ →+* ℂ) (h : IsUnit A.det) :
    IsUnit (A.map ε).det := by
  have h1 : (A.map ε).det = ε A.det := by
    rw [RingHom.map_det]; rfl
  rw [h1]; exact h.map ε

theorem blockReal_at_of (D : D7) (h : BesselId D) : BlockReal_at D := by
  obtain ⟨hRat, V, hV⟩ := h
  choose a ha U hU using hV
  obtain ⟨f, hf⟩ := exists_rowBasis D V
  have key : ∀ (ε : ℂ →+* ℂ), IsIdOrConj ε →
      (∀ z, (InfinitePlace.mk D.what₂.embLL).embedding z = ε (D.what₂.embLL z)) → BlockReal_at D := by
    intro ε hε hv
    have hZ : IsUnit ((((bE D).toMatrix (oE D))ᵀ).map ε).det := by
      apply det_map_unit
      rw [Matrix.det_transpose]
      exact det_toMatrix_unit (bE D) (oE D).toBasis
    refine ⟨ε, hε, f, InfinitePlace.mk D.what₂.embLL,
      fun u => ((a u)⁻¹ • (bN D u).toMatrix (oM D u)).map ε, ((((bE D).toMatrix (oE D))ᵀ).map ε)⁻¹,
      fun u => (Vr0 D U u).map ε, fun u => ?_, Matrix.isUnit_nonsing_inv_det _ hZ, fun u => ?_, fun u k j => ?_⟩
    · apply det_map_unit
      rw [Matrix.det_smul]
      exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero (ha u))).pow _).mul (det_toMatrix_unit (bN D u) (oM D u).toBasis)
    · rw [conjT_map _ ε hε, ← Matrix.map_mul, vr_gram]
      ext i j
      rw [Matrix.map_apply, Matrix.one_apply]
      split_ifs <;> simp
    · rw [Matrix.nonsing_inv_nonsing_inv _ hZ, ← Matrix.map_mul, Matrix.map_apply, pm_vr, hf k, ← besS_eq]
      have hM : (LinearMap.toMatrix (D.div.Nu u).b D.div.RR.dualB (D.div.Bk u)).map
          (InfinitePlace.mk D.what₂.embLL).embedding =
          ((LinearMap.toMatrix (D.div.Nu u).b D.div.RR.dualB (D.div.Bk u)).map D.what₂.embLL).map ε := by
        ext k' j'
        simp only [Matrix.map_apply, hv]
      rw [hM, ← Matrix.map_mul, ← Matrix.map_mul, ← block_eq D hRat V U a ha hU u]
      rfl
  rcases InfinitePlace.embedding_mk_eq D.what₂.embLL with h | h
  · exact key (RingHom.id ℂ) ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ (fun z => by rw [h]; rfl)
  · exact key (starRingEnd ℂ) ⟨fun z => by simp, fun z => by simp, fun r => Complex.conj_ofReal r⟩
      (fun z => by rw [h]; rfl)

theorem weightConst_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ S.c0 D.s u := by
  unfold S.c0 S.dimPi
  exact div_nonneg (mul_pos (D.s.volN_pos u) (D.s.volH_pos u)).le
    (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))

theorem hs_neg_id (D : D7) (u : D.what₂.Word) :
    S.hsNormSq (0 - ContinuousLinearMap.id ℂ (D.s.Cu u)) = (D.duS u : ℝ) := by
  unfold S.hsNormSq S.hsInner
  have h : ∀ l, inner ℂ ((0 - ContinuousLinearMap.id ℂ (D.s.Cu u)) (stdOrthonormalBasis ℂ (D.s.Cu u) l))
      ((0 - ContinuousLinearMap.id ℂ (D.s.Cu u)) (stdOrthonormalBasis ℂ (D.s.Cu u) l)) = (1 : ℂ) := by
    intro l
    simp only [zero_sub, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, inner_neg_neg]
    rw [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ (D.s.Cu u)).orthonormal l l, if_pos rfl]
  simp only [h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, finrank_Cu]
  simp

theorem unfolding_constant_pos_of_diagonal (D : D7) (u : D.what₂.Word) (e0 : ℝ) (he : e0 < 1) (hd : 0 < D.duS u)
    (h2 : hsDiagFull D u ≤ e0 * (D.duS u : ℝ)) : 0 < S.c0 D.s u := by
  rcases (weightConst_nonneg D u).lt_or_eq with h | h
  · exact h
  · exfalso
    have hK : S.KD D u u = 0 := by
      unfold S.KD S.Kmat
      rw [← h, mul_zero, Real.zero_rpow (by norm_num)]
      simp
    unfold hsDiagFull at h2
    rw [hK, hs_neg_id] at h2
    have hd' : (0 : ℝ) < (D.duS u : ℝ) := by exact_mod_cast hd
    nlinarith

theorem matKF_of {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 : ℝ) (hC0 : 0 < C0) (lS : LinkS Fm C0)
    (cPr : ChosenProviso Fm C0) (lD : LinkDIV Fm Cabs CH) : MatKF Fm := by
  obtain ⟨a0, lS⟩ := lS
  obtain ⟨a1, cPr⟩ := cPr
  obtain ⟨C, a2, lD⟩ := lD
  refine ⟨max (max a0 a1) (max a2 1), fun x hx i => ?_⟩
  have e0' : x ≥ a0 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have e1' : x ≥ a1 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have e2' : x ≥ a2 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have e3' : (1 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨eta0, eta1, e0, he0, h0, -, hse, hS⟩ := lS x e0' i
  have hP := cPr x e1' i
  obtain ⟨s1, s2, -⟩ := hS hP
  have hBes : BesselId (Fm.D x i) := (lD x e2' i).2.2.2.1
  have hD0 : 0 < (Fm.D x i).what₂.Dstar := by
    rw [← (Fm.D x i).Dstar_eq (Fm.D x i).u₀]; exact ((Fm.D x i).mem (Fm.D x i).u₀).A.Dstar_pos
  have hexp : Real.exp (-(x ^ (eps / 8))) < 1 := by
    have hpos : 0 < x ^ (eps / 8) := Real.rpow_pos_of_pos (by linarith) _
    have h := Real.exp_lt_exp.mpr (show -(x ^ (eps / 8)) < 0 by linarith)
    rwa [Real.exp_zero] at h
  have he1 : e0 < 1 := by
    have h1 : Real.sqrt e0 < 1 := lt_of_le_of_lt hse hexp
    have h2 := (Real.sqrt_lt' one_pos).mp h1
    simpa using h2
  have hdu : ∀ u, 0 < (Fm.D x i).duS u := by
    intro u
    have h1 := (hP u).1
    have h2 : 0 < C0⁻¹ := inv_pos.mpr hC0
    rcases Nat.eq_zero_or_pos ((Fm.D x i).duS u) with h | h
    · rw [h] at h1; simp at h1; linarith
    · exact h
  refine ⟨max eta0 0, e0, by have := le_max_right eta0 0; linarith, max_le h0 (Real.exp_pos _).le, he0, hse,
    matK_at_of (Fm.L x i) _ _ (blockReal_at_of _ hBes) (fun u => unfolding_constant_pos_of_diagonal _ u e0 he1 (hdu u) (s2 u))
      (fun u u' huu => le_trans (s1 u u' huu) ?_) s2⟩
  have hq : 0 ≤ ((Fm.D x i).duS u : ℝ) * ((Fm.D x i).duS u' : ℝ) / (Fm.D x i).what₂.Dstar :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hD0.le
  have hm : (1 + eta0) * (((Fm.D x i).duS u : ℝ) * ((Fm.D x i).duS u' : ℝ) / (Fm.D x i).what₂.Dstar) ≤
      (1 + max eta0 0) * (((Fm.D x i).duS u : ℝ) * ((Fm.D x i).duS u' : ℝ) / (Fm.D x i).what₂.Dstar) :=
    mul_le_mul_of_nonneg_right (by have := le_max_left eta0 0; linarith) hq
  calc (1 + eta0) * ((Fm.D x i).duS u : ℝ) * ((Fm.D x i).duS u' : ℝ) / (Fm.D x i).what₂.Dstar
      = (1 + eta0) * (((Fm.D x i).duS u : ℝ) * ((Fm.D x i).duS u' : ℝ) / (Fm.D x i).what₂.Dstar) := by ring
    _ ≤ _ := hm
    _ = _ := by ring

end Formalism.MainNotions.Lnk

end

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions

theorem dall_pos {D : D7} (u : D.what₂.Word) (e0 : ℝ) (he : e0 < 1) (hd : 0 < D.duS u)
    (h : hsDiagFull D u ≤ e0 * (D.duS u : ℝ)) : 0 < D.what₂.Dall := by
  by_contra hcon
  have h0 : D.what₂.Dall = 0 := by omega
  have hfr : Module.finrank ℂ D.s.HH = 0 := by rw [D.s_HH, h0]
  haveI : Subsingleton D.s.HH := Module.finrank_zero_iff.mp hfr
  have hK : S.KD D u u = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    have hP : D.s.Pu u x = 0 := Subsingleton.elim _ _
    simp [S.KD, S.Kmat, hP]
  have hfin : Module.finrank ℂ (D.s.Cu u) = D.duS u := by
    unfold D7.duS
    exact LinearEquiv.finrank_eq (D.s_Cu u)
  have hval : hsDiagFull D u = (D.duS u : ℝ) := by
    unfold hsDiagFull S.hsNormSq S.hsInner
    rw [hK, zero_sub]
    simp [hfin]
  rw [hval] at h
  have hd' : (0 : ℝ) < (D.duS u : ℝ) := by exact_mod_cast hd
  nlinarith

theorem rrRankF_of {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 : ℝ) (hC0 : 0 < C0) (lS : LinkS Fm C0)
    (cPr : ChosenProviso Fm C0) (lI : LinkIRR Fm) (lD : LinkDIV Fm Cabs CH) : RRRankF Fm := by
  have heps := fam_eps_pos Fm
  obtain ⟨a0, lS⟩ := lS
  obtain ⟨a1, cPr⟩ := cPr
  obtain ⟨a2, lI⟩ := lI
  obtain ⟨C, a3, lD⟩ := lD
  refine ⟨1 + |a0| + |a1| + |a2| + |a3|, fun x hx i => ?_⟩
  have b0 := abs_nonneg a0
  have b1 := abs_nonneg a1
  have b2 := abs_nonneg a2
  have b3 := abs_nonneg a3
  have hx0 : 0 < x := by linarith
  have e0' : x ≥ a0 := by linarith [le_abs_self a0]
  have e1 : x ≥ a1 := by linarith [le_abs_self a1]
  have e2 : x ≥ a2 := by linarith [le_abs_self a2]
  have e3 : x ≥ a3 := by linarith [le_abs_self a3]
  obtain ⟨eta0, eta1, e0, he0, -, -, hse, hS⟩ := lS x e0' i
  have hP := cPr x e1 i
  obtain ⟨-, hdiag, -⟩ := hS hP
  have hexp : ∀ y : ℝ, 0 < y → Real.exp (-y) < 1 := fun y hy => by
    have h := Real.exp_lt_exp.mpr (show -y < 0 by linarith)
    rwa [Real.exp_zero] at h
  have hs1 : Real.sqrt e0 < 1 := lt_of_le_of_lt hse (hexp _ (Real.rpow_pos_of_pos hx0 _))
  have he1 : e0 < 1 := by
    have h1 := Real.sq_sqrt he0
    have h2 := Real.sqrt_nonneg e0
    nlinarith
  have hdu : 0 < (Fm.D x i).duS (Fm.D x i).u₀ := by
    by_contra hcon
    have hz : (Fm.D x i).duS (Fm.D x i).u₀ = 0 := by omega
    have h1 := (hP (Fm.D x i).u₀).1
    rw [hz] at h1
    have h2 : (0 : ℝ) < C0⁻¹ := inv_pos.mpr hC0
    simp at h1
    linarith
  have hDall := dall_pos (Fm.D x i).u₀ e0 he1 hdu (hdiag _)
  have hdel : (Fm.D x i).what₂.delp < 1 := lt_of_le_of_lt (lI x e2 i).2 (hexp _ (Real.rpow_pos_of_pos hx0 _))
  have hDr : (0 : ℝ) < ((Fm.D x i).what₂.Drows : ℝ) := by
    rw [(Fm.D x i).what₂.D_eq]
    exact mul_pos (by linarith) (by exact_mod_cast hDall)
  have hrk := D7.RRFull.rank (lD x e3 i).2.2.2.2.1
  have : 0 < (Fm.D x i).what₂.Drows := by exact_mod_cast hDr
  rw [← hrk] at this
  exact this

end Formalism.MainNotions.Lnk

end

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.LFunctionChainParameters

variable {D : D7} (L : SizeData₂ D)

def lE (w : D.what₂.places.Pl) : ℝ := SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)

open Classical in

def suppT (u : D.what₂.Word) : Finset D.what₂.places.Pl :=
  L.supp.filter (fun w => D.what₂.places.resChar w = (D.mem u).A.T)

theorem sz_eq (w : D.what₂.places.Pl) (y : ℝ) : SizeData₂.sz w y = 2 * (lE w * y) := by
  unfold SizeData₂.sz lE; ring

open Classical in
theorem Ga_eq : L.Ga = UnitWeightPartition.Ga L.supp (SizeData₂.lifts D) lE L.gainD L.tau := by
  unfold SizeData₂.Ga UnitWeightPartition.Ga
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun w _ => sz_eq w _)

open Classical in
theorem Fo_eq : L.Fo = UnitWeightPartition.Fo L.supp (SizeData₂.lifts D) lE L.F := by
  unfold SizeData₂.Fo UnitWeightPartition.Fo
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun w _ => sz_eq w _)

open Classical in
theorem Ee_eq' (u : D.what₂.Word) : L.Ee u = UnitWeightPartition.Ee L.supp (SizeData₂.lifts D) lE (L.E u) := by
  unfold SizeData₂.Ee UnitWeightPartition.Ee
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun w _ => sz_eq w _)

open Classical in

def Places_at (C : ℝ) : Prop :=
  ∀ u, ∃ (sg' : D.what₂.places.Pl → ℝ) (de muMu muMaxMu PT Rd LT RX : ℝ),
    UnitWeightPartition.HypLow L.supp (suppT L u) (SizeData₂.lifts D) lE L.gainD L.F (L.E u) L.tau L.io (fun w => (L.lenMN u w : ℝ)) sg'
      (D.duS u : ℝ) ((D.div.Nu u).rank : ℝ) de muMu (D.div.Nu u).mu PT Rd ∧
    UnitWeightPartition.HypLow2 L.supp lE L.tau L.io (D.R.f : ℝ) ((D.mem u).A.T : ℝ) de L.sc.b ((D.fm u).lat 0).mu muMu (IOsum L)
      PT LT Rd RX ∧
    UnitWeightPartition.HypHigh L.supp (SizeData₂.lifts D) lE L.gainD L.F (L.E u) L.tau sg' ((D.fm u).lat 0).muMax muMaxMu
      (D.div.Nu u).muMax ∧
    LT ≤ C * D.host.TT.card * D.R.m * (L.sc.a / D.R.k + L.sc.b') * Real.log ((D.mem u).A.T : ℝ) ∧
    RX ≤ C * L.sc.X'' D.R.n

open Classical in

theorem slopesN_at_of (C : ℝ) (hC : 4 ≤ C) (hio : 0 ≤ IOsum L) (h : Places_at L C) : SlopesN_at L C := by
  intro u
  obtain ⟨sg', de, muMu, muMaxMu, PT, Rd, LT, RX, h1, h2, h3, h4, h5⟩ := h u
  have hlow := UnitWeightPartition.lower_bound_simplified _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2
  have hhigh := UnitWeightPartition.claimHigh_valid _ _ _ _ _ _ _ _ _ _ _ h3
  rw [← Ga_eq L, ← Fo_eq L, ← Ee_eq' L u] at hlow hhigh
  have hB : 0 ≤ C * D.R.m * L.B0 := mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) (loss_bound_nonneg L)
  refine ⟨by linarith, ?_⟩
  unfold LoU
  have h6 : 4 * IOsum L ≤ C * IOsum L := mul_le_mul_of_nonneg_right hC hio
  linarith

def PlacesF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C x0 : ℝ, 4 ≤ C ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ IOsum (Fm.L x i) ∧ Places_at (Fm.L x i) C

theorem slopesNF_of {eps : ℝ} (Fm : FamP eps) (h : PlacesF Fm) : SlopesNF Fm := by
  obtain ⟨C, x0, hC, h⟩ := h
  exact ⟨C, x0, by linarith, fun x hx i => slopesN_at_of _ C hC (h x hx i).1 (h x hx i).2⟩

end Formalism.MainNotions.Lnk

end

section FullLattices

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions

section General

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem int_smul (d : 𝓞 K) (v : V) : d • v = (algebraMap (𝓞 K) K d) • v := (algebraMap_smul K d v).symm

theorem algMap_ne {d : 𝓞 K} (hd : d ≠ 0) : algebraMap (𝓞 K) K d ≠ 0 := by
  intro h
  exact hd ((injective_iff_map_eq_zero (algebraMap (𝓞 K) K)).mp (IsFractionRing.injective (𝓞 K) K) d h)

theorem exists_mul_mem (L : Submodule (𝓞 K) V) (v : V) (hv : v ∈ Submodule.span K (L : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ L := by
  first | exact Bl.general_b_fact_left''''''''.goal1 .. | (apply Bl.general_b_fact_left''''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left''''''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_left''''''''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left''''''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_left''''''''.goal1 <;> first | assumption | infer_instance)

end General

def NuCommens (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u, (L.NuLat u).FG ∧ ∃ c : 𝓞 D.what₂.LL, c ≠ 0 ∧ ∀ y ∈ DV.MramL D u, c • y ∈ L.NuLat u

def MramSpan (D : D7) : Prop :=
  ∀ u, Submodule.span D.what₂.LL (DV.MramL D u : Set (D.div.Nu u).V) = ⊤

theorem mramSpan (D : D7) : MramSpan D := by
  intro u
  rw [eq_top_iff]
  intro x _
  have hx : D.nuIn u x ∈ Submodule.span D.what₂.LL (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V) := by
    rw [((D.fm u).lat_good 0).2.2]; trivial
  obtain ⟨d, hd, hm⟩ := exists_mul_mem _ _ hx
  have hmem : d • x ∈ DV.MramL D u := by
    show (D.nuIn u) (d • x) ∈ ((D.fm u).lat 0).L
    rw [int_smul d x, map_smul, ← int_smul]
    exact hm
  have e : x = (algebraMap (𝓞 D.what₂.LL) D.what₂.LL d)⁻¹ • (d • x) := by
    rw [int_smul d x, smul_smul, inv_mul_cancel₀ (algMap_ne hd), one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem Iu_ne_zero (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) : DV.Iu D L u ≠ 0 := by
  unfold DV.Iu
  rw [Finset.prod_ne_zero_iff]
  intro w _
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr (D.plEq w).ne_bot)

theorem nuFull_of {D : D7} {L : SizeData₂ D} (hN' : DV.NprimeDef D L) (hc : NuCommens D L) : D.NuFull := by
  intro u
  obtain ⟨hfg, c, hc0, hcM⟩ := hc u
  constructor
  ·
    obtain ⟨d, hd, hI⟩ := (DV.Iu D L u).isFractional
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    let f : (D.div.Nu u).V →ₗ[𝓞 D.what₂.LL] (D.div.Nu u).V := LinearMap.lsmul (𝓞 D.what₂.LL) (D.div.Nu u).V d
    have hinj : Function.Injective f := by
      intro x y hxy
      have h1 : d • x = d • y := hxy
      rw [int_smul d x, int_smul d y] at h1
      exact smul_right_injective _ (algMap_ne hd0) h1
    have hle : (D.div.Nu u).L.map f ≤ L.NuLat u := by
      rw [hN' u, Submodule.map_span_le]
      rintro x ⟨a, ha, y, hy, rfl⟩
      obtain ⟨z, hz⟩ := hI a ha
      show d • (a • y) ∈ L.NuLat u
      have e : d • (a • y) = z • y := by
        rw [int_smul z y, hz, smul_assoc]
      rw [e]
      exact (L.NuLat u).smul_mem _ hy
    have : Module.Finite (𝓞 D.what₂.LL) (L.NuLat u) := Module.Finite.iff_fg.2 hfg
    have : IsNoetherian (𝓞 D.what₂.LL) (L.NuLat u) := inferInstance
    have h2 := (IsNoetherian.noetherian (((D.div.Nu u).L.map f).comap (L.NuLat u).subtype)).map (L.NuLat u).subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h2
    exact Submodule.fg_of_fg_map_injective f hinj h2
  ·
    obtain ⟨a0, ha0, ha⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (Iu_ne_zero D L u)
    rw [eq_top_iff, ← mramSpan D u, Submodule.span_le]
    intro y hy
    have hmem : (algebraMap (𝓞 D.what₂.LL) D.what₂.LL a0) • (c • y) ∈ (D.div.Nu u).L := by
      rw [hN' u]
      exact Submodule.subset_span ⟨_, ha, c • y, hcM y hy, rfl⟩
    have e : y = ((algebraMap (𝓞 D.what₂.LL) D.what₂.LL a0) * (algebraMap (𝓞 D.what₂.LL) D.what₂.LL c))⁻¹ •
        ((algebraMap (𝓞 D.what₂.LL) D.what₂.LL a0) • (c • y)) := by
      rw [int_smul c y, smul_smul, smul_smul, mul_assoc,
        inv_mul_cancel₀ (mul_ne_zero (algMap_ne ha0) (algMap_ne hc0)), one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

def NuCommensF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, NuCommens (Fm.D x i) (Fm.L x i)

theorem nuFullF_of {eps : ℝ} (Fm : FamP eps) (h : NuCommensF Fm) : NuFullF Fm := by
  obtain ⟨x0, h⟩ := h
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have h0 : x ≥ x0 := (le_max_left _ _).trans hx
  have h1 : Fm.x1 < x := by
    have := (le_max_right x0 (Fm.x1 + 1)).trans hx
    linarith
  exact nuFull_of (Fm.nprimeDef x h1 i) (h x h0 i)

end Formalism.MainNotions.Lnk

end

end FullLattices

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.D5 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

variable {eps : ℝ}

def Carries (Fm : FamP eps) {x : ℝ} (i : Fm.Ix x) (av bv : ℕ → ℤ) : Prop :=
  ∀ t : (Fm.D x i).host.TT, (Fm.L x i).aT t = av (t : (Fm.D x i).R.A).val ∧
    (Fm.L x i).bT t = bv (t : (Fm.D x i).R.A).val

def AdmWt (Fm : FamP eps) {x : ℝ} (i0 : Fm.Ix x) (av bv : ℕ → ℤ) : Prop :=
  ∀ t ∈ Fm.TTn x, aWin (Fm.L x i0) (av t) ∧ (Fm.L x i0).sc.b' ≤ (bv t : ℝ) ∧ (bv t : ℝ) ≤ Fm.bTop x

def AskIs {D : D7} (L : SizeData₂ D) (A : ℝ) : Prop :=
  ∀ (e : Formalism.HC.Frame) (m : ℕ) (AD : ArithData e.A) (N : ℕ) (TT : Finset e.A) (a : e.A → ℝ)
    (w : Fin m → E0 × e.A → ℝ), Reads L e m TT a w → HEq AD (arithOf D.host.toHostRaw) →
    (∀ j t ρ, t ∈ TT → InPhi ρ → a t / w j ρ ≤ N) →
    (∑ t ∈ TT, ∑ j : Fin m, Formalism.LFunctionChainParameters.characterSumData.ASK AD N (a t) t (w j)) = A

def EstimatesAtScale (Fm : FamP eps) (x Cord e K : ℝ) : Prop :=
  ∃ (P : Par) (ι κ τ U Ω : Type) (_ : Fintype Ω) (π : Ω → ℝ) (Ps s sB : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (BAD : ℕ → τ → Prop) (Sig : ℕ → Ω → ℝ) (io : U → ℕ → Ω → ℝ) (D : U → Ω → LD ι κ τ)
    (i0 : Fm.Ix x) (av bv : Ω → ℕ → ℤ),
    P.x = x ∧ P.ε = eps ∧ P.Cord = Cord ∧ Windows P e K ∧
    WindowSettingHypotheses P π Ps s sB J TT BAD Sig io D ∧
    (∀ o, AdmWt Fm i0 (av o) (bv o)) ∧
    ∀ o (i : Fm.Ix x), Carries Fm i (av o) (bv o) →
      J.card = (Fm.D x i).R.m ∧ TT.card = (Fm.D x i).host.TT.card ∧
      ∃ υ : U, (D υ o).Ga J = (Fm.L x i).Ga ∧ (∑ p ∈ s, Real.log p * io υ p o) = IOsum (Fm.L x i) ∧
        AskIs (Fm.L x i) ((D υ o).ASK P.d Ps J TT)

def SmallOrderPrimes (Fm : FamP eps) : Prop :=
  ∀ Cord : ℝ, 0 ≤ Cord → ∃ e K x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → EstimatesAtScale Fm x Cord e K

theorem lossF_of_core (Fm : FamP eps) (h : SmallOrderPrimes Fm) : LossF Fm 0 := by
  obtain ⟨Cord, hC0, hJ⟩ := joint_bound_eventually
  obtain ⟨e, K, x0, hx⟩ := h Cord hC0
  have heps : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]
    exact (Fm.L 0 i).sc.eps_pos
  have heps4 : eps < 1 / 4 := by
    obtain ⟨i⟩ := Fm.Ix_zero
    have := (Fm.L 0 i).sc.eps_lt
    rw [Fm.L_eps 0 i] at this
    linarith
  obtain ⟨x1, hJ'⟩ := hJ eps e K heps heps4
  refine ⟨3 * |K| + 13, max x0 (max x1 (Fm.x1 + 1)), by positivity, fun x hxx hw => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_max_left _ _) hxx
  have e1 : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hxx
  have e2 : Fm.x1 < x := by
    have := le_trans (le_trans (le_max_right x1 (Fm.x1 + 1)) (le_max_right _ _)) hxx
    linarith
  obtain ⟨P, ι, κ, τ, U, Ω, iΩ, π, Ps, s, sB, J, TT, BAD, Sig, io, D, i0, av, bv, hPx, hPe, hPC, hW, hS, hadm,
    hties⟩ := hx x e0 hw
  obtain ⟨o, -, hc1, hc2⟩ := hJ' P hPe hPC (by rw [hPx]; exact e1) hW ι κ τ U Ω π Ps s sB J TT BAD Sig io D hS
  refine ⟨i0, av o, bv o, hadm o, fun i hi => ?_⟩
  obtain ⟨hJc, hTc, υ, hGa, hIo, hAsk⟩ := hties o i hi
  have hPC0 : 0 ≤ P.C := hW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hPCK : P.C ≤ K := hW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb : P.b = (Fm.L x i).sc.b := by
    show Real.exp (P.x ^ P.ε) = Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    rw [hPx, hPe, Fm.L_x x i e2, Fm.L_eps x i]
  have hU : unitU P J.card TT.card =
      ((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b := by
    unfold unitU; rw [hJc, hTc, hb]
  have hU0 : 0 ≤ ((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.exp_pos _).le
  have hone : (Fm.L x i).sc.x ^ ((0 : ℝ) * (Fm.L x i).sc.eps) = 1 := by rw [zero_mul, Real.rpow_zero]
  have hKabs : K ≤ |K| := le_abs_self K
  have hbig : (3 * P.C + 13) * (((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b) ≤
      (3 * |K| + 13) * (Fm.D x i).host.TT.card * (Fm.D x i).R.m * (Fm.L x i).sc.b *
        (Fm.L x i).sc.x ^ ((0 : ℝ) * (Fm.L x i).sc.eps) := by
    rw [hone, mul_one]
    have := mul_le_mul_of_nonneg_right (show 3 * P.C + 13 ≤ 3 * |K| + 13 by linarith) hU0
    simpa [mul_assoc] using this
  have hsmall : ((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b ≤
      (3 * P.C + 13) * (((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b) := by
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 3 * P.C + 13 by linarith) hU0
    linarith
  constructor
  · have h2 := hc2 υ
    rw [hIo, hU] at h2
    linarith
  · intro e' m' AD N TT' a w hr hAD hcut
    rw [hAsk e' m' AD N TT' a w hr hAD hcut]
    have h1 := hc1 υ
    rw [hGa, hU] at h1
    linarith

theorem lossF_mono (Fm : FamP eps) {eL eL' : ℝ} (hle : eL ≤ eL') (h : LossF Fm eL) : LossF Fm eL' := by
  obtain ⟨C, x0, hC, hx⟩ := h
  refine ⟨C, x0, hC, fun x hxx hw => ?_⟩
  obtain ⟨i0, av, bv, hadm, hl⟩ := hx x hxx hw
  refine ⟨i0, av, bv, hadm, fun i hi => ?_⟩
  obtain ⟨h1, h2⟩ := hl i hi
  have hsx := (Fm.L x i).sc.one_lt_alt
  have hpow : (Fm.L x i).sc.x ^ (eL * (Fm.L x i).sc.eps) ≤ (Fm.L x i).sc.x ^ (eL' * (Fm.L x i).sc.eps) :=
    Real.rpow_le_rpow_of_exponent_le hsx.le (mul_le_mul_of_nonneg_right hle (Fm.L x i).sc.eps_pos.le)
  have hU0 : 0 ≤ C * ((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (Real.exp_pos _).le
  have hm := mul_le_mul_of_nonneg_left hpow hU0
  exact ⟨le_trans h1 hm, fun e m AD N TT a w hr hAD hcut => le_trans (h2 e m AD N TT a w hr hAD hcut) hm⟩

theorem tops_clause {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (Cb m : ℝ) (hCb : 0 ≤ Cb) (hm : 0 ≤ m)
    (h1 : ChTT_at L) (h2 : ChBad_at X Cb) :
    ∑ p ∈ largeOrderResiduePrimes L, 4 * m * L.sc.a * (Real.log p / p) * ((badTops X p).card : ℝ) ≤
      32 * (Cb * L.sc.x ^ (-2 : ℝ)) * m * L.sc.a * D.host.TT.card * ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have ha : 0 ≤ L.sc.a := (sc_a_pos L.sc).le
  have hβ : 0 ≤ Cb * L.sc.x ^ (-2 : ℝ) := mul_nonneg hCb (Real.rpow_nonneg hx.le _)
  have hS : 0 ≤ ∑ p ∈ largeOrderResiduePrimes L, Real.log (p : ℝ) / p :=
    Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have e1 : ∑ p ∈ largeOrderResiduePrimes L, 4 * m * L.sc.a * (Real.log p / p) * ((badTops X p).card : ℝ) =
      4 * m * L.sc.a * ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p * ((badTops X p).card : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e1]
  have h3 : L.sc.delta1 * D.R.n ≤ 2 * (D.host.TT.card : ℝ) := by have := h1.1; linarith
  have h4 : 4 * (Cb * L.sc.x ^ (-2 : ℝ)) * L.sc.delta1 * D.R.n * ∑ p ∈ largeOrderResiduePrimes L, Real.log (p : ℝ) / p ≤
      8 * (Cb * L.sc.x ^ (-2 : ℝ)) * D.host.TT.card * ∑ p ∈ largeOrderResiduePrimes L, Real.log (p : ℝ) / p := by
    apply mul_le_mul_of_nonneg_right _ hS
    have := mul_le_mul_of_nonneg_left h3 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hβ)
    linarith
  have h5 := mul_le_mul_of_nonneg_left (le_trans h2 h4) (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hm) ha)
  calc _ ≤ 4 * m * L.sc.a * (8 * (Cb * L.sc.x ^ (-2 : ℝ)) * D.host.TT.card *
        ∑ p ∈ largeOrderResiduePrimes L, Real.log (p : ℝ) / p) := h5
    _ = _ := by ring

theorem ioP_le {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (p : ℕ)
    (hS : ∀ t0 ∈ G.VV X K (G.aL L) (G.bL L) p,
      G.Sv X K (G.aL L) (G.bL L) p t0 ≤ 2 * (D.R.m : ℝ) * (G.Nv X p t0 : ℝ) * L.sc.a / p)
    (hSig : 0 ≤ G.Sig X K (G.aL L) (G.bL L) p) :
    G.ioP X K (G.aL L) (G.bL L) p ≤
      2 * G.Sig X K (G.aL L) (G.bL L) p * (2 * ((D.R.m : ℝ) * D.host.TT.card * L.sc.a) / p) := by
  have ha : 0 ≤ L.sc.a := (sc_a_pos L.sc).le
  have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  unfold G.ioP
  split_ifs with h
  · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hSig)
    apply Finset.sup'_le
    intro t0 ht0
    refine le_trans (hS t0 ht0) ?_
    have hN : (G.Nv X p t0 : ℝ) ≤ (D.host.TT.card : ℝ) := by
      unfold G.Nv G.topsOn
      exact_mod_cast Finset.card_filter_le _ _
    apply div_le_div_of_nonneg_right _ hp
    have h1 : (D.R.m : ℝ) * (G.Nv X p t0 : ℝ) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) :=
      mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg _)
    have h2 := mul_le_mul_of_nonneg_right h1 ha
    linarith
  · exact mul_nonneg (mul_nonneg (by norm_num) hSig)
      (div_nonneg (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ha)) hp)

section Points

variable (Fm : FamP eps) (x : ℝ) (i0 : Fm.Ix x)

def winAz : Finset ℤ :=
  Finset.Icc ⌈(Fm.L x i0).sc.a⌉ ⌊(Fm.L x i0).sc.a + (Fm.L x i0).sc.a /
    (((Fm.D x i0).R.k : ℝ) * (Fm.L x i0).sc.x ^ (Scale.A / 2))⌋

def winBz : Finset ℤ := Finset.Icc ⌈(Fm.L x i0).sc.b'⌉ ⌊Fm.bTop x⌋

abbrev Wt : Type := (t : ↥(Fm.TTn x)) → ↥(winAz Fm x i0) × ↥(winBz Fm x i0)

variable {Fm x i0}

def avOf (o : Wt Fm x i0) (n : ℕ) : ℤ := if h : n ∈ Fm.TTn x then ((o ⟨n, h⟩).1 : ℤ) else 0

def bvOf (o : Wt Fm x i0) (n : ℕ) : ℤ := if h : n ∈ Fm.TTn x then ((o ⟨n, h⟩).2 : ℤ) else 0

theorem admissible_weight_of_vector (o : Wt Fm x i0) : AdmWt Fm i0 (avOf o) (bvOf o) := by
  intro t ht
  simp only [avOf, bvOf, dif_pos ht]
  have h1 := Finset.mem_Icc.mp (o ⟨t, ht⟩).1.2
  have h2 := Finset.mem_Icc.mp (o ⟨t, ht⟩).2.2
  exact ⟨⟨Int.ceil_le.mp h1.1, Int.le_floor.mp h1.2⟩, Int.ceil_le.mp h2.1, Int.le_floor.mp h2.2⟩

theorem wt_nonempty (hx : Fm.x1 < x) : Nonempty (Wt Fm x i0) :=
  ⟨fun τ => (⟨(Fm.L x i0).aT ((eqTT Fm x i0).symm τ), Finset.mem_Icc.mpr
      ⟨Int.ceil_le.mpr ((Fm.L x i0).aT_win _).1, Int.le_floor.mpr ((Fm.L x i0).aT_win _).2⟩⟩,
    ⟨(Fm.L x i0).bT ((eqTT Fm x i0).symm τ), Finset.mem_Icc.mpr
      ⟨Int.ceil_le.mpr ((Fm.L x i0).bT_ge _), Int.le_floor.mpr (Fm.bT_le x hx i0 _)⟩⟩)⟩

theorem exists_carrier (hCov : Fm.CoverAll) (hx : Fm.x1 < x) (o : Wt Fm x i0) :
    ∃ i : Fm.Ix x, Carries Fm i (avOf o) (bvOf o) := by
  obtain ⟨i, -, hi⟩ := hCov x hx i0 0 (avOf o) (bvOf o) (by unfold Ranks.n; positivity) (admissible_weight_of_vector o)
  exact ⟨i, hi⟩

open Classical in

def StatementsAtPoints (Fm : FamP eps) (x : ℝ) (i0 : Fm.Ix x) (P : Par) {ι κ τ : Type} (Ps s sB : Finset ℕ) (J : Finset κ)
    (TT : Finset τ) (BAD : ℕ → τ → Prop) (Sig : ℕ → Wt Fm x i0 → ℝ) (ioP : Fm.Ix x → ℕ → ℝ)
    (ld : Fm.Ix x → LD ι κ τ) : Prop :=
  TT.Nonempty ∧ (∀ p ∈ Ps, p.Prime ∧ p ≠ 2) ∧
  (∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ P.Y) ∧ (∀ p ∈ s, ∀ o, 0 ≤ Sig p o) ∧
  (∀ p ∈ s, (∑ o, Sig p o) / (Fintype.card (Wt Fm x i0) : ℝ) ≤ P.s₀) ∧
  (∀ p ∈ sB, p.Prime ∧ (p : ℝ) ≤ P.Xp) ∧
  (∑ p ∈ sB, 4 * (J.card : ℝ) * P.a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ) ≤
    32 * P.β * (J.card : ℝ) * P.a * TT.card * ∑ p ∈ sB, Real.log p / p) ∧
  ∀ (o : Wt Fm x i0) (i : Fm.Ix x), Carries Fm i (avOf o) (bvOf o) →
    (∀ p ∈ s, ioP i p ≤ 2 * Sig p o * (2 * ((J.card : ℝ) * TT.card * P.a) / p)) ∧
    ParametersHyp P Ps J TT (ld i) ∧ FirstHyp P Ps (ld i).cl ∧
    (∀ p ∈ Ps, (ld i).cl p = PClass.second → p ∈ s ∧ P.θ < Sig p o) ∧
    (∀ p ∈ Ps, (ld i).cl p = PClass.served → ∀ t ∈ TT \ (ld i).TTp p, p ∈ sB ∧ BAD p t) ∧
    J.card = (Fm.D x i).R.m ∧ TT.card = (Fm.D x i).host.TT.card ∧
    (ld i).Ga J = (Fm.L x i).Ga ∧ (∑ p ∈ s, Real.log p * ioP i p) = IOsum (Fm.L x i) ∧
    AskIs (Fm.L x i) ((ld i).ASK P.d Ps J TT)

open Classical in
theorem estimates_at_scale_of_points (hCov : Fm.CoverAll) (hx : Fm.x1 < x) (P : Par) {ι κ τ : Type} (Ps s sB : Finset ℕ) (J : Finset κ)
    (TT : Finset τ) (BAD : ℕ → τ → Prop) (Sig : ℕ → Wt Fm x i0 → ℝ) (ioP : Fm.Ix x → ℕ → ℝ)
    (ld : Fm.Ix x → LD ι κ τ) (Cord e K : ℝ)
    (hP : P.x = x ∧ P.ε = eps ∧ P.Cord = Cord ∧ Windows P e K)
    (h : StatementsAtPoints Fm x i0 P Ps s sB J TT BAD Sig ioP ld) : EstimatesAtScale Fm x Cord e K := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, hpt⟩ := h
  have := wt_nonempty (i0 := i0) hx
  have hcard : (0 : ℝ) < (Fintype.card (Wt Fm x i0) : ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨P, ι, κ, τ, {σ : Wt Fm x i0 → Fm.Ix x // ∀ o, Carries Fm (σ o) (avOf o) (bvOf o)}, Wt Fm x i0, inferInstance,
    fun _ => 1 / (Fintype.card (Wt Fm x i0) : ℝ), Ps, s, sB, J, TT, BAD, Sig, fun υ p o => ioP (υ.1 o) p,
    fun υ o => ld (υ.1 o), i0, avOf, bvOf, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2, ?_, admissible_weight_of_vector, ?_⟩
  · refine ⟨g1, g2, fun _ => by positivity, ?_, g3, g4, ?_, ?_, g6, g7, ?_⟩
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    · intro p hp
      have := g5 p hp
      rw [← Finset.mul_sum, one_div, inv_mul_eq_div]
      exact this
    · intro υ p hp o
      exact (hpt o (υ.1 o) (υ.2 o)).1 p hp
    · intro υ o
      obtain ⟨-, a2, a3, a4, a5, -⟩ := hpt o (υ.1 o) (υ.2 o)
      exact ⟨a2, a3, a4, a5⟩
  · intro o i hi
    obtain ⟨-, -, -, -, -, a6, a7, a8, a9, a10⟩ := hpt o i hi
    refine ⟨a6, a7, ⟨fun o' => if h : o' = o then i else (exists_carrier hCov hx o').choose, fun o' => ?_⟩, ?_⟩
    · by_cases h : o' = o
      · simp only [dif_pos h]; rw [h]; exact hi
      · simp only [dif_neg h]; exact (exists_carrier hCov hx o').choose_spec
    · simp only [dif_pos rfl]
      exact ⟨a8, a9, a10⟩

end Points

def StatementsAtPointsLargeScales (Fm : FamP eps) : Prop :=
  ∀ Cord : ℝ, 0 ≤ Cord → ∃ e K x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → ∃ (i0 : Fm.Ix x) (P : Par) (ι κ τ : Type) (Ps s sB : Finset ℕ)
    (J : Finset κ) (TT : Finset τ) (BAD : ℕ → τ → Prop) (Sig : ℕ → Wt Fm x i0 → ℝ) (ioP : Fm.Ix x → ℕ → ℝ)
    (ld : Fm.Ix x → LD ι κ τ),
    (P.x = x ∧ P.ε = eps ∧ P.Cord = Cord ∧ Windows P e K) ∧ StatementsAtPoints Fm x i0 P Ps s sB J TT BAD Sig ioP ld

theorem estimates_of_points_family (Fm : FamP eps) (hCov : Fm.CoverAll) (h : StatementsAtPointsLargeScales Fm) : SmallOrderPrimes Fm := by
  intro Cord hC
  obtain ⟨e, K, x0, hx⟩ := h Cord hC
  refine ⟨e, K, max x0 (Fm.x1 + 1), fun x hxx hw => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_max_left _ _) hxx
  have e1 : Fm.x1 < x := by have := le_trans (le_max_right x0 (Fm.x1 + 1)) hxx; linarith
  obtain ⟨i0, P, ι, κ, τ, Ps, s, sB, J, TT, BAD, Sig, ioP, ld, hP, hpts⟩ := hx x e0 hw
  exact estimates_at_scale_of_points hCov e1 P Ps s sB J TT BAD Sig ioP ld Cord e K hP hpts

end Formalism.MainNotions.Lnk

end

noncomputable section

namespace Formalism.MainNotions

open Formalism.MainNotions.Lnk

end Formalism.MainNotions

end
