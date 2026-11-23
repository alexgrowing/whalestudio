import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingTermCoefEqResidueCardZpow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnipotentLevelNilpotent
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAtOfSubsingleton
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BandMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherTer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherMore

namespace ResidueCardinalityNilpotence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.CompanionTheory.ResCardPlace

theorem resCard_Kw : ∀ {D : D7} (w : Pl D.host.E), GlobalTheory.SplitWeil.resCard (Kw w) = Ideal.absNorm w.asIdeal := by
  intro D w
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (Kw w))
    (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
  have hO : (ValuativeRel.valuation (Kw w)).integer = (w.adicCompletionIntegers D.host.E).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  have h := Formalism.UG.P.tjcosets_card_residue w
  rw [Formalism.UG.qV] at h
  rw [← h]
  exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (RingEquiv.subringCongr hO)).toEquiv

end GlobalTheory.CompanionTheory.ResCardPlace

end

section

open GlobalTheory.SumSize GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.CompanionTheory.VolVal

open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj ValuativeRel Matrix

section Unip

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

def Rises (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) : Prop := ∀ r s, ℓ s < ℓ r + j → X r s = 0

theorem Rises.mono {ℓ : ι → ℕ} {i j : ℕ} {X : Matrix ι ι k} (h : Rises ℓ j X) (hij : i ≤ j) : Rises ℓ i X :=
  _root_.GlobalTheory.BandMonotonicity.band_mono h hij

theorem Rises.add {ℓ : ι → ℕ} {j : ℕ} {X Y : Matrix ι ι k} (h : Rises ℓ j X) (h' : Rises ℓ j Y) : Rises ℓ j (X + Y) :=
  _root_.GlobalTheory.BandLemmaFirst.main h h'

theorem Rises.neg {ℓ : ι → ℕ} {j : ℕ} {X : Matrix ι ι k} (h : Rises ℓ j X) : Rises ℓ j (-X) :=
  _root_.GlobalTheory.BandLemmaSecond.main h

theorem Rises.mul {ℓ : ι → ℕ} {i j : ℕ} {X Y : Matrix ι ι k} (h : Rises ℓ i X) (h' : Rises ℓ j Y) :
    Rises ℓ (i + j) (X * Y) :=
  _root_.GlobalTheory.BandLemmaThird.main h h'

theorem rises_one (ℓ : ι → ℕ) : Rises ℓ 0 (1 : Matrix ι ι k) := fun r s hs => by
  rw [Matrix.one_apply_ne]
  rintro rfl
  omega

theorem Rises.pow {ℓ : ι → ℕ} {X : Matrix ι ι k} (h : Rises ℓ 1 X) (j : ℕ) : Rises ℓ j (X ^ j) := by
  induction j with
  | zero => simpa using rises_one ℓ
  | succ j ih => rw [pow_succ]; exact ih.mul h

theorem Rises.eq_zero {ℓ : ι → ℕ} {X : Matrix ι ι k} (h : Rises ℓ (Finset.univ.sup ℓ + 1) X) : X = 0 := by
  ext r s
  have : ℓ s ≤ Finset.univ.sup ℓ := Finset.le_sup (f := ℓ) (Finset.mem_univ s)
  exact h r s (by omega)

theorem Rises.pow_eq_zero {ℓ : ι → ℕ} {X : Matrix ι ι k} (h : Rises ℓ 1 X) : X ^ (Finset.univ.sup ℓ + 1) = 0 :=
  (h.pow _).eq_zero

def UT (k : Type*) [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι] (ℓ : ι → ℕ) : Subgroup (GL ι k) where
  carrier := {g | Rises ℓ 1 (g.val - 1)}
  one_mem' := fun r s _ => by simp
  mul_mem' := by
    intro g h hg hh
    have e : (g * h).val - 1 = (g.val - 1) * (h.val - 1) + (g.val - 1) + (h.val - 1) := by
      rw [Units.val_mul]; noncomm_ring
    show Rises ℓ 1 _
    rw [e]
    exact ((Rises.mul hg hh).mono (by omega) |>.add hg).add hh
  inv_mem' := by
    intro g hg
    have hg' : Rises ℓ 1 (g.val - 1) := hg
    set X := g.val - 1 with hX
    have hd := hg'.pow_eq_zero
    set d := Finset.univ.sup ℓ + 1 with hdd
    have hs : g.val * ∑ i ∈ Finset.range d, (-X) ^ i = 1 := by
      have e : g.val = 1 - (-X) := by rw [hX]; noncomm_ring
      rw [e, mul_neg_geom_sum, neg_pow, hd, mul_zero, sub_zero]
    have hi : (g⁻¹).val = ∑ i ∈ Finset.range d, (-X) ^ i := by
      have h1 : (g⁻¹).val * g.val = 1 := by rw [← Units.val_mul]; simp
      calc (g⁻¹).val = (g⁻¹).val * (g.val * ∑ i ∈ Finset.range d, (-X) ^ i) := by rw [hs, mul_one]
        _ = _ := by rw [← mul_assoc, h1, one_mul]
    show Rises ℓ 1 _
    have hd0 : d = (d - 1) + 1 := by omega
    rw [hi, hd0, Finset.sum_range_succ', pow_zero, add_sub_cancel_right]
    have : ∀ n : ℕ, Rises ℓ 1 (∑ i ∈ Finset.range n, (-X) ^ (i + 1)) := by
      intro n
      induction n with
      | zero => intro r s _; simp
      | succ n ih =>
        rw [Finset.sum_range_succ]
        exact ih.add ((hg'.neg.pow (n + 1)).mono (by omega))
    exact this _

theorem UT_pow_eq_zero {ℓ : ι → ℕ} {g : GL ι k} (h : g ∈ UT k ℓ) : (g.val - 1) ^ (Finset.univ.sup ℓ + 1) = 0 :=
  Rises.pow_eq_zero h

end Unip

section Sym

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def step (n : Type*) (c : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * ((c + 1) / 2) + 1) fun i => 2 * (i.val + 1)

theorem N_le_UT {p : ℕ} (hp : (c + 1) / 2 ≤ p) (hp' : p ≤ (c + 1) / 2 + 1) : N k n c p ≤ UT k (step n c) := by
  refine (Subgroup.closure_le _).2 fun g hg r s hs => ?_
  have : g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := hg r s (by
    rcases r with r | r <;> rcases s with s | s <;> simp only [lev, step, Sum.elim_inl, Sum.elim_inr] at hs ⊢ <;> omega)
  rw [Matrix.sub_apply, this, sub_self]

theorem symN_le_UT : symN k n c ≤ UT k (step n c) :=
  sup_le (N_le_UT le_rfl (by omega)) (N_le_UT (by omega) (by omega))

end Sym

end GlobalTheory.CompanionTheory.VolVal

namespace GlobalTheory.CompanionTheory.VolVal

open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj ValuativeRel Matrix

section Root

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι]

def intM (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : Type) [Fintype ι] [DecidableEq ι] : AddSubgroup (Matrix ι ι k) where
  carrier := {X | ∀ i j, X i j ∈ 𝒪[k]}
  zero_mem' := fun _ _ => zero_mem _
  add_mem' := fun h h' i j => add_mem (h i j) (h' i j)
  neg_mem' := fun h i j => neg_mem (h i j)

theorem intM_mul {X Y : Matrix ι ι k} (hX : X ∈ intM k ι) (hY : Y ∈ intM k ι) : X * Y ∈ intM k ι := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun t _ => mul_mem (hX i t) (hY t j)

theorem intM_one : (1 : Matrix ι ι k) ∈ intM k ι := fun i j => by
  by_cases h : i = j
  · subst h; simpa using one_mem _
  · rw [Matrix.one_apply_ne h]; exact zero_mem _

theorem int_of_pow {g : GL ι k} {d m : ℕ} (hν : (g.val - 1) ^ d = 0) (h0 : (m : k) ≠ 0) (hm : ((m : k))⁻¹ ∈ 𝒪[k])
    (hg : (g ^ m).val ∈ intM k ι) : g.val ∈ intM k ι := by
  have h1 := GlobalTheory.UnipVol.smul_mem_of_pow (A := Matrix ι ι k) (V := Matrix ι ι k) (intM k ι) (g.val - 1) hν m
    (fun x hx i j => by
      have e : x i j = ((m : k))⁻¹ * ((m • x) i j) := by
        rw [Matrix.smul_apply, nsmul_eq_mul, inv_mul_cancel_left₀ h0]
      rw [e]
      exact mul_mem hm (hx i j))
    (fun x hx => by
      have e : (1 + (g.val - 1)) ^ m = (g ^ m).val := by
        rw [add_sub_cancel, Units.val_pow_eq_pow_val]
      rw [e, smul_eq_mul, sub_mul, one_mul]
      exact (intM k ι).sub_mem (intM_mul hg hx) hx)
    1 intM_one
  have h2 := (intM k ι).add_mem h1 intM_one
  rw [smul_eq_mul, mul_one, sub_add_cancel] at h2
  exact h2

theorem mem_KO_of_pow {ℓ : ι → ℕ} {g : GL ι k} (hU : g ∈ UT k ℓ) {m : ℕ} (h0 : (m : k) ≠ 0)
    (hm : ((m : k))⁻¹ ∈ 𝒪[k]) (hg : g ^ m ∈ KO k ι) : g ∈ KO k ι := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff _).1 hg
  refine (mem_KO_iff _).2 ⟨int_of_pow (UT_pow_eq_zero hU) h0 hm h1, ?_⟩
  refine int_of_pow (g := g⁻¹) (UT_pow_eq_zero (inv_mem hU)) h0 hm ?_
  rw [inv_pow]
  exact h2

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem relIndex_eq {p : ℕ} (hp : p.Prime) (hu : ∀ m : ℕ, m.Coprime p → (m : k) ≠ 0 ∧ ((m : k))⁻¹ ∈ 𝒪[k])
    (C : Subgroup (GL (n ⊕ Fin c) k)) (h0 : (KO k (n ⊕ Fin c)).relIndex (symN k n c ⊓ C) ≠ 0) :
    ∃ a, (KO k (n ⊕ Fin c)).relIndex (symN k n c ⊓ C) = p ^ a := by
  haveI : ((KO k (n ⊕ Fin c)).subgroupOf (symN k n c ⊓ C)).FiniteIndex := ⟨h0⟩
  refine GlobalTheory.UnipVol.index_eq_prime_pow _ hp fun g m hm hg => ?_
  rw [Subgroup.mem_subgroupOf] at hg ⊢
  exact mem_KO_of_pow (symN_le_UT g.2.1) (hu m hm).1 (hu m hm).2 (by simpa using hg)

theorem invVol_eq {p : ℕ} (hp : p.Prime) (hu : ∀ m : ℕ, m.Coprime p → (m : k) ≠ 0 ∧ ((m : k))⁻¹ ∈ 𝒪[k])
    (C : Subgroup (GL (n ⊕ Fin c) k)) : ∃ a b : ℕ, invVol C = (a : ℚ) / (p : ℚ) ^ b := by
  by_cases h0 : (KO k (n ⊕ Fin c)).relIndex (symN k n c ⊓ C) = 0
  · exact ⟨0, 0, by simp [invVol, h0]⟩
  · obtain ⟨b, hb⟩ := relIndex_eq hp hu C h0
    exact ⟨_, b, by rw [invVol, hb]; push_cast; rfl⟩

end Root

end GlobalTheory.CompanionTheory.VolVal

namespace GlobalTheory.CompanionTheory.VolVal

open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj ValuativeRel Matrix
open Formalism.BasicNotions Formalism.L2.DIV IsDedekindDomain NumberField
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

section Place

variable {D : D7}

theorem unit_Kw (P : Pl D.host.E) {p : ℕ} (hp : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (m : ℕ) (hm : m.Coprime p) :
    (m : Kw P) ≠ 0 ∧ ((m : Kw P))⁻¹ ∈ 𝒪[Kw P] := by
  have hnm : ((m : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := GlobalTheory.UnipVol.natCast_notMem hp hm
  have h1 : P.intValuation ((m : ℕ) : 𝓞 D.host.E) = 1 := (P.intValuation_eq_one_iff).2 hnm
  haveI : (Valued.v : Valuation (Kw P) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (valuation (Kw P)) (Valued.v : Valuation (Kw P) (WithZero (Multiplicative ℤ)))
  have h2 : (Valued.v : Valuation (Kw P) (WithZero (Multiplicative ℤ))) (m : Kw P) = 1 := by
    have e0 : (m : Kw P) = algebraMap D.host.E (Kw P) ((m : ℕ) : D.host.E) := (map_natCast _ m).symm
    have : (Valued.v : Valuation (Kw P) (WithZero (Multiplicative ℤ))) (algebraMap D.host.E (Kw P) ((m : ℕ) : D.host.E)) =
        P.valuation D.host.E ((m : ℕ) : D.host.E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := D.host.E) P ((m : ℕ) : D.host.E)
    rw [e0, this]
    have h3 := P.valuation_of_algebraMap (K := D.host.E) ((m : ℕ) : 𝓞 D.host.E)
    have e1 : algebraMap (𝓞 D.host.E) D.host.E ((m : ℕ) : 𝓞 D.host.E) = ((m : ℕ) : D.host.E) := map_natCast _ m
    rw [← e1, h3, h1]
  have h4 : valuation (Kw P) (m : Kw P) = 1 := (e.eq_one_iff_eq_one).2 h2
  refine ⟨fun h => ?_, ?_⟩
  · rw [h, map_zero] at h4
    exact zero_ne_one h4
  · rw [Valuation.mem_integer_iff, map_inv₀, h4, inv_one]

end Place

end GlobalTheory.CompanionTheory.VolVal

namespace GlobalTheory.CompanionTheory.VolVal

open Formalism.DivisionValues (vw lw)
open IsDedekindDomain NumberField

section Val

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def QL (w : HeightOneSpectrum (𝓞 K)) (r : ℚ) (a : ℝ) : Prop := r = 0 ∨ -a ≤ (vw w (r : K) : ℝ)

theorem QL.mono {w : HeightOneSpectrum (𝓞 K)} {r : ℚ} {a a' : ℝ} (h : QL w r a) (ha : a ≤ a') : QL w r a' :=
  h.imp_right fun h => (neg_le_neg ha).trans h

theorem QL.mul {w : HeightOneSpectrum (𝓞 K)} {r r' : ℚ} {a a' : ℝ} (h : QL w r a) (h' : QL w r' a') :
    QL w (r * r') (a + a') := by
  rcases h with rfl | h
  · exact Or.inl (zero_mul _)
  rcases h' with rfl | h'
  · exact Or.inl (mul_zero _)
  by_cases h0 : r = 0
  · exact Or.inl (by simp [h0])
  by_cases h0' : r' = 0
  · exact Or.inl (by simp [h0'])
  refine Or.inr ?_
  rw [Rat.cast_mul, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (by exact_mod_cast h0) (by exact_mod_cast h0'), Int.cast_add]
  linarith

theorem QL.prod {w : HeightOneSpectrum (𝓞 K)} {ι : Type} (s : Finset ι) (f : ι → ℚ) (a : ι → ℝ)
    (h : ∀ i ∈ s, QL w (f i) (a i)) : QL w (∏ i ∈ s, f i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inr (by simp [Formalism.DivisionValues.ValuationRepresentative.vw_one])
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem vw_nat_nonneg (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : 0 ≤ vw w (n : K) := by
  have := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w (n : 𝓞 K)
  simpa using this

theorem vw_nat_eq_zero (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (h : (n : 𝓞 K) ∉ w.asIdeal) : vw w (n : K) = 0 := by
  have h0 : (n : 𝓞 K) ≠ 0 := fun e => h (e ▸ zero_mem _)
  have h1 := Formalism.EigenvalueLevelCeiling.intValuation_eq_exp' w _ h0
  rw [(w.intValuation_eq_one_iff).2 h, ← WithZero.exp_zero] at h1
  have h2 := WithZero.exp_injective h1
  have h3 : (((n : ℕ) : 𝓞 K) : K) = (n : K) := by simp
  rw [h3] at h2
  omega

theorem vw_npow (w : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) (n : ℕ) : vw w (x ^ n) = n * vw w x := by
  induction n with
  | zero => simp [Formalism.DivisionValues.ValuationRepresentative.vw_one]
  | succ n ih =>
    rw [pow_succ, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ hx) hx, ih]
    push_cast
    ring

theorem vw_zpow (w : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) (z : ℤ) : vw w (x ^ z) = z * vw w x := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [zpow_natCast, vw_npow w hx]
  · rw [zpow_neg, zpow_natCast, Formalism.DivisionValues.ValuationRepresentative.vw_inv, vw_npow w hx]
    push_cast
    ring

theorem ql_zpow (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : q ≠ 0) {z : ℤ} {A : ℝ} (h : |(z : ℝ)| ≤ A) :
    QL w ((q : ℚ) ^ z) (A * vw w (q : K)) := by
  refine Or.inr ?_
  have hq' : (q : K) ≠ 0 := by exact_mod_cast hq
  have e : (((q : ℚ) ^ z : ℚ) : K) = (q : K) ^ z := by push_cast; rfl
  rw [e, vw_zpow w hq']
  have hv : (0 : ℝ) ≤ (vw w (q : K) : ℝ) := by exact_mod_cast vw_nat_nonneg w q
  push_cast
  have := (abs_le.1 h).1
  nlinarith

theorem ql_away (w : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : (p : 𝓞 K) ∉ w.asIdeal) (a b : ℕ) :
    QL w ((a : ℚ) / (p : ℚ) ^ b) 0 := by
  by_cases ha : a = 0
  · exact Or.inl (by simp [ha])
  refine Or.inr ?_
  have hp0 : (p : K) ≠ 0 := by
    intro e
    have : p = 0 := by exact_mod_cast e
    exact hp (by simp [this])
  have ha' : (a : K) ≠ 0 := by exact_mod_cast ha
  have e : (((a : ℚ) / (p : ℚ) ^ b : ℚ) : K) = (a : K) * ((p : K) ^ b)⁻¹ := by
    push_cast; rw [div_eq_mul_inv]
  rw [e, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ ha' (inv_ne_zero (pow_ne_zero _ hp0)), Formalism.DivisionValues.ValuationRepresentative.vw_inv, vw_npow w hp0,
    vw_nat_eq_zero w hp]
  have : (0 : ℝ) ≤ (vw w (a : K) : ℝ) := by exact_mod_cast vw_nat_nonneg w a
  simpa using this

theorem finite_vw_ne (n : ℕ) (hn : n ≠ 0) : {w : HeightOneSpectrum (𝓞 K) | vw w (n : K) ≠ 0}.Finite := by
  have h0 : Ideal.span {(n : 𝓞 K)} ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  by_contra h
  refine hw (vw_nat_eq_zero w fun h' => h ?_)
  exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h')

end Val

end GlobalTheory.CompanionTheory.VolVal

namespace GlobalTheory.CompanionTheory.VolVal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.FunObj.AaCoef
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

section Factors

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem givenLevel_KO (t : T) (P : Pl D.host.E) {j : ℕ} (hj : 0 < j) :
    givenLevel G t P ((locGrid G t P).m, j) = KO (Kw P) _ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  have key : ∀ a, 0 < a → givenLevel G t P (a, j + 1) = KO (Kw P) _ := by
    rintro (_ | a) h
    · omega
    · rfl
  exact key _ (by have := D.R.two_le_m; show 0 < D.R.m; omega)

theorem card_le (t : T) (P : Pl D.host.E) {j : ℕ} (hj : j < D.R.m) :
    topRank (locGrid G t P) j + (D.R.m - 1 - j) ≤ bigN D := by
  have h := topRank_add (G := bareGrid P) one_le_sLen j
  have hr := rank_le_bigN P hj
  have hm : (bareGrid P).m = D.R.m := rfl
  show topRank (bareGrid P) j + (D.R.m - 1 - j) ≤ bigN D
  omega

theorem factor_stair (t : T) (P : Pl D.host.E) (hs : 1 ≤ (locGrid G t P).s) (e : ℕ) (g : (locGrid G t P).VertexGroup) {j : ℕ}
    (h0 : 0 < j) (hj : j < (locGrid G t P).m) (hg : g ((locGrid G t P).m, j) = stair (locGrid G t P) (unifAt P) e j) : ∃ z : ℤ,
    invVol (conjLevel hs (givenLevel G t P) g hj) = (resCard (Kw P) : ℚ) ^ z ∧
      |z| ≤ (bigN D : ℤ) * ((D.R.m : ℤ) * ((e : ℤ) * (D.R.m : ℤ))) := by
  have hJ : conjLevel hs (givenLevel G t P) g hj = conjLevel hs (fun _ => KO _ _) g hj := by
    simp only [conjLevel, givenLevel_KO G t P h0]
  rw [hJ, conjLevel_KO, hg, toFrame_stair]
  let f : Fin (topRank (locGrid G t P) j) ⊕ Fin ((locGrid G t P).m - 1 - j) → ℤ :=
    Sum.elim (fun _ => 0) fun p => ((e * (p.val + 1) : ℕ) : ℤ)
  obtain ⟨z, hz, hzb⟩ := invVol_diag_zpow (unifAt P) (isUnif_unifAt P) f
  have e1 : (Sum.elim (fun _ => 1) fun p : Fin ((locGrid G t P).m - 1 - j) => unifAt P ^ (e * (p.val + 1))) =
      fun r => unifAt P ^ f r := by
    funext r
    rcases r with r | r
    · simp [f]
    · simp only [Sum.elim_inr, f]
      rw [zpow_natCast]
  rw [e1]
  refine ⟨z, hz, hzb.trans ?_⟩
  have hm : (locGrid G t P).m = D.R.m := rfl
  have hj' : j < D.R.m := hj
  have hc : (Fintype.card (Fin (topRank (locGrid G t P) j) ⊕ Fin ((locGrid G t P).m - 1 - j)) : ℤ) ≤ bigN D := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hm]
    exact_mod_cast card_le G t P hj'
  have hs : ∑ r, |f r| ≤ (D.R.m : ℤ) * ((e : ℤ) * (D.R.m : ℤ)) := by
    rw [Fintype.sum_sum_type]
    have h1 : ∑ a : Fin (topRank (locGrid G t P) j), |f (Sum.inl a)| = 0 :=
      Finset.sum_eq_zero fun a _ => by simp [f]
    rw [h1, zero_add]
    have h2 : ∀ p : Fin ((locGrid G t P).m - 1 - j), |f (Sum.inr p)| ≤ (e : ℤ) * (D.R.m : ℤ) := fun p => by
      have hp : p.val < D.R.m - 1 - j := p.2
      have : p.val + 1 ≤ D.R.m := by omega
      simp only [f, Sum.elim_inr]
      rw [abs_of_nonneg (by positivity)]
      push_cast
      have h3 : ((p.val : ℤ) + 1) ≤ D.R.m := by exact_mod_cast this
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    calc ∑ p, |f (Sum.inr p)| ≤ ∑ _p : Fin ((locGrid G t P).m - 1 - j), (e : ℤ) * (D.R.m : ℤ) :=
          Finset.sum_le_sum fun p _ => h2 p
      _ = (((locGrid G t P).m - 1 - j : ℕ) : ℤ) * ((e : ℤ) * (D.R.m : ℤ)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by rw [hm]; omega) (by positivity)
  exact mul_le_mul hc hs (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)

end Factors

end GlobalTheory.CompanionTheory.VolVal

namespace GlobalTheory.CompanionTheory.VolVal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.FunObj.AaCoef
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

section Coef

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

variable (G) in

def expAt (P : Pl D.host.E) : ℝ := (D.R.m : ℝ) ^ 3 * bigN D * cosExp G P

variable (G) in

def dlF (w : PlL D) : ℝ := ∑ P ∈ G.pl.W0, expAt G P * vw w ((resCard (Kw P) : ℕ) : D.what₂.LL)

theorem coefficient_local_term_at_split_place {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {P : Pl D.host.E} (hP : P ∈ G.pl.W0)
    (hl : P ∈ locPl G t) {β : CosFam G t} (hβ : β ∈ S.supp t Φ) (w : PlL D) :
    QL w (S.term t Φ β ⟨P, hl⟩).coef (expAt G P * vw w ((resCard (Kw P) : ℕ) : D.what₂.LL)) := by
  classical
  have hs : 1 ≤ (locGrid G t P).s := one_le_sLen
  have hkeep : keepAt G P = false := by simp [keepAt, hP]
  have hdep : depthAt G P = cosExp G P := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨h1, h2⟩ := depthAt_w G hv
    rw [h1, h2]
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := ((Good.locGrid_isGood hL G W t hde hc).1 P hl).square 0 hm 0 hm
  haveI := (isUnitVol_unitVol P).1
  have hT := isTensor_Tflip hL W S.B t Φ hde hc hl
  rw [hdep] at hT
  have hO := oneCoset hs (psiAt W P) (unitVol P) (givenLevel G t P) (Tflip W S.B t Φ P) (unifAt P) (cosExp G P) D.R.m_even
    (isUnif_unifAt P) h00.cond hT (fun j hj _ => givenLevel_KO G t P hj)
  have hb := hβ ⟨P, hl⟩
  have hb' : β ⟨P, hl⟩ ∈ unfSupport (psiAt W P) (unitVol P) false
      (Reps.through hs (givenLevel G t P) (stair (locGrid G t P) (unifAt P) (cosExp G P))) (Tflip W S.B t Φ P) := by
    have : keepAt G (⟨P, hl⟩ : locPl G t).1 = false := hkeep
    rw [this] at hb
    exact hb
  have hβ' := funext (hO _ hb')
  have hz : ∀ i : Fin ((locGrid G t P).m - 2), ∃ z : ℤ,
      invVol (conjLevel hs (givenLevel G t P) ((repsAt G t P).elt (β ⟨P, hl⟩)) (j := i + 1) (by omega)) =
        (resCard (Kw P) : ℚ) ^ z ∧ |z| ≤ (bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ))) := fun i =>
    factor_stair G t P hs (cosExp G P) _ (Nat.succ_pos _) _ (by
      rw [hβ']
      exact through_elt _ (by omega))
  choose z hz hzb using hz
  have hq : resCard (Kw P) ≠ 0 := by
    have := resCard_ne_zero (k := Kw P)
    exact_mod_cast this
  set v : ℝ := (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ) with hv
  have hv0 : 0 ≤ v := by
    have := vw_nat_nonneg w (resCard (Kw P)) (K := D.what₂.LL)
    rw [hv]
    exact_mod_cast this
  set B : ℝ := (bigN D : ℝ) * ((D.R.m : ℝ) * ((cosExp G P : ℝ) * (D.R.m : ℝ))) with hB
  have hQ : QL w (∏ i : Fin ((locGrid G t P).m - 2), (resCard (Kw P) : ℚ) ^ z i)
      (∑ _i : Fin ((locGrid G t P).m - 2), B * v) := QL.prod _ _ _ fun i _ =>
    ql_zpow w hq (by
      have := hzb i
      rw [hB]
      exact_mod_cast this)
  have e : (S.term t Φ β ⟨P, hl⟩).coef = ∏ i : Fin ((locGrid G t P).m - 2), (resCard (Kw P) : ℚ) ^ z i := by
    refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ => hz i)
    rfl
  rw [e]
  refine hQ.mono ?_
  have hm2 : (((locGrid G t P).m - 2 : ℕ) : ℝ) ≤ D.R.m := by
    have : (locGrid G t P).m - 2 ≤ D.R.m := by show D.R.m - 2 ≤ D.R.m; omega
    exact_mod_cast this
  have hB0 : 0 ≤ B := by positivity
  calc ∑ _i : Fin ((locGrid G t P).m - 2), B * v = (((locGrid G t P).m - 2 : ℕ) : ℝ) * (B * v) := by simp
    _ ≤ (D.R.m : ℝ) * (B * v) := mul_le_mul_of_nonneg_right hm2 (by positivity)
    _ = expAt G P * v := by rw [hB, expAt]; ring

theorem coef_away (S : GridChoice W U) (t : T) (Φ : G.Datum) {P : Pl D.host.E} (hl : P ∈ locPl G t) (β : CosFam G t)
    (w : PlL D) (hw : ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) : QL w (S.term t Φ β ⟨P, hl⟩).coef 0 := by
  have hs : 1 ≤ (locGrid G t P).s := one_le_sLen
  have hp := Formalism.EigenvalueLevelCeiling.plc_prime P
  have hpm := Formalism.EigenvalueLevelCeiling.plc_mem P
  have hQ := QL.prod (w := w) (Finset.univ : Finset (Fin ((locGrid G t P).m - 2)))
    (fun i => invVol (conjLevel hs (givenLevel G t P) ((repsAt G t P).elt (β ⟨P, hl⟩)) (j := i + 1) (by omega)))
    (fun _ => 0) (fun i _ => by
      obtain ⟨a, b, e⟩ := invVol_eq hp (unit_Kw P hpm)
        (conjLevel hs (givenLevel G t P) ((repsAt G t P).elt (β ⟨P, hl⟩)) (j := i + 1) (by omega))
      rw [e]
      exact ql_away w hw a b)
  have e : (S.term t Φ β ⟨P, hl⟩).coef = ∏ i : Fin ((locGrid G t P).m - 2),
      invVol (conjLevel hs (givenLevel G t P) ((repsAt G t P).elt (β ⟨P, hl⟩)) (j := i + 1) (by omega)) := rfl
  rw [e]
  simpa using hQ

theorem coef_QL {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {w : PlL D} (hA : Away G t w)
    {β : CosFam G t} (hβ : β ∈ S.supp t Φ) : QL w (∏ v, (S.term t Φ β v).coef) (dlF G w) := by
  classical
  have key : ∀ v : locPl G t, QL w (S.term t Φ β v).coef
      (if v.1 ∈ G.pl.W0 then expAt G v.1 * vw w ((resCard (Kw v.1) : ℕ) : D.what₂.LL) else 0) := by
    rintro ⟨P, hl⟩
    by_cases hP : P ∈ G.pl.W0
    · rw [if_pos hP]
      exact coefficient_local_term_at_split_place hL S t Φ hde hc hP hl hβ w
    · rw [if_neg hP]
      have hQ : P ∈ L.Q t := by
        rcases Finset.mem_union.1 hl with h | h
        · exact absurd h hP
        · exact h
      refine coef_away S t Φ hl β w ?_
      rcases hA P hQ with h | h
      · exfalso
        rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
        · exact G.pl.levelPlace_ne_basePlace t P hQ h
        · exact hP (by
            rw [G.pl.w_Q t P hQ h]
            exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h)))
      · exact h _ (Formalism.EigenvalueLevelCeiling.plc_prime P) (Formalism.EigenvalueLevelCeiling.plc_mem P)
  have h1 := QL.prod (w := w) Finset.univ _ _ fun v _ => key v
  refine h1.mono (le_of_eq ?_)
  rw [Finset.sum_coe_sort (locPl G t) fun P =>
    ((if P ∈ G.pl.W0 then expAt G P * vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) else 0 : ℝ)),
    Finset.sum_ite_mem, dlF]
  congr 1
  exact Finset.inter_eq_right.2 Finset.subset_union_left

end Coef

end GlobalTheory.CompanionTheory.VolVal

namespace GlobalTheory.CompanionTheory.VolVal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.FunObj.AaCoef
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

section Loss

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem resCard_ne (P : Pl D.host.E) : resCard (Kw P) ≠ 0 := by
  have := resCard_ne_zero (k := Kw P)
  exact_mod_cast this

theorem absNorm_le_sq (P : Pl D.host.E) : Ideal.absNorm P.asIdeal ≤ Ideal.absNorm (P.under (𝓞 D.host.F)).asIdeal ^ 2 := by
  have h1 : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (P.under (𝓞 D.host.F)).asIdeal ≤ P.asIdeal :=
    Ideal.map_le_iff_le_comap.2 le_rfl
  have h2 : Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (P.under (𝓞 D.host.F)).asIdeal) =
      Ideal.absNorm (P.under (𝓞 D.host.F)).asIdeal ^ 2 := by
    rw [Ideal.absNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E, D.sp.cm.deg2]
  have hp : 0 < Ideal.absNorm (P.under (𝓞 D.host.F)).asIdeal ^ 2 :=
    pow_pos (Nat.pos_of_ne_zero fun h => (P.under (𝓞 D.host.F)).ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) _
  exact Nat.le_of_dvd hp (h2 ▸ Ideal.absNorm_dvd_absNorm_of_le h1)

theorem log_absNorm_le (P : Pl D.host.E) :
    Real.log (Ideal.absNorm P.asIdeal) ≤ 2 * Real.log (Ideal.absNorm (P.under (𝓞 D.host.F)).asIdeal) := by
  have h0 : 0 < Ideal.absNorm P.asIdeal := Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : (Ideal.absNorm P.asIdeal : ℝ) ≤ (Ideal.absNorm (P.under (𝓞 D.host.F)).asIdeal : ℝ) ^ 2 := by
    exact_mod_cast absNorm_le_sq P
  have h2 := Real.log_le_log (by exact_mod_cast h0) h1
  rwa [Real.log_pow, Nat.cast_ofNat] at h2

theorem sig_nonneg : 0 ≤ sig G := Finset.sum_nonneg fun v _ =>
  mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

theorem expAt_nonneg (P : Pl D.host.E) : 0 ≤ expAt G P := by
  unfold expAt; positivity

theorem sum_expAt_le : ∑ P ∈ G.pl.W0, expAt G P * Real.log (resCard (Kw P) : ℕ) ≤
    2 * ((D.R.m : ℝ) ^ 3 * bigN D) * sig G := by
  classical
  have hinj : Set.InjOn G.pl.w (G.pl.S0 : Set (Pl D.host.F)) := fun v hv v' hv' h =>
    (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))
  rw [Places.W0, Finset.sum_image hinj, sig, Finset.mul_sum]
  refine Finset.sum_le_sum fun v hv => ?_
  obtain ⟨h1, -⟩ := depthAt_w G hv
  rw [expAt, h1, GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]
  have h2 := log_absNorm_le (G.pl.w v)
  rw [G.pl.under_w hv] at h2
  have h3 : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 3 * bigN D * (G.pl.depth sc v : ℝ) := by positivity
  calc (D.R.m : ℝ) ^ 3 * bigN D * (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm (G.pl.w v).asIdeal : ℕ)
      ≤ (D.R.m : ℝ) ^ 3 * bigN D * (G.pl.depth sc v : ℝ) * (2 * Real.log (Ideal.absNorm v.asIdeal)) :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = _ := by ring

theorem m_le_bigN : D.R.m ≤ bigN D := by
  unfold bigN
  nlinarith [Nat.zero_le D.R.k, Nat.zero_le D.R.t, Nat.zero_le (sLen D), Nat.zero_le D.R.m]

theorem loss_dlF {C b : ℝ} (hC : 2 ≤ C) (hb : 1 ≤ b) (hf : 1 ≤ D.R.f) :
    Loss (dlF G) (D.R.m * bOne G C b) := by
  classical
  refine ⟨fun w => Finset.sum_nonneg fun P _ => mul_nonneg (expAt_nonneg G P) ?_, ?_, fun s => ?_⟩
  · exact_mod_cast vw_nat_nonneg w _
  · refine ((G.pl.W0.finite_toSet.biUnion fun P _ =>
      finite_vw_ne (K := D.what₂.LL) (resCard (Kw P)) (resCard_ne P))).subset fun w hw => ?_
    by_contra h
    refine hw (Finset.sum_eq_zero fun P hP => ?_)
    have : vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) = 0 := by
      by_contra h'
      exact h (Set.mem_biUnion hP h')
    simp [this]
  · have h1 : ∑ w ∈ s, lw w * dlF G w =
        ∑ P ∈ G.pl.W0, expAt G P * ∑ w ∈ s, lw w * (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ) := by
      simp only [dlF, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun w _ => by ring
    have h2 : ∑ w ∈ s, lw w * dlF G w ≤ ∑ P ∈ G.pl.W0, expAt G P * Real.log (resCard (Kw P) : ℕ) := by
      rw [h1]
      exact Finset.sum_le_sum fun P _ => mul_le_mul_of_nonneg_left
        (Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le s _ (resCard_ne P)) (expAt_nonneg G P)
    refine h2.trans ((sum_expAt_le G).trans ?_)
    have hX := sig_nonneg G
    have hL : 0 ≤ Real.log b := Real.log_nonneg hb
    have hmN : (D.R.m : ℝ) ≤ bigN D := by exact_mod_cast m_le_bigN
    have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
    have hm0 : (0 : ℝ) ≤ D.R.m := by positivity
    have hN0 : (0 : ℝ) ≤ bigN D := by positivity
    have h3 : (2 : ℝ) ≤ C * D.R.f * b := by
      have : (1 : ℝ) ≤ D.R.f * b := one_le_mul_of_one_le_of_one_le hf' hb
      nlinarith
    have h4 : 2 * sig G ≤ (C * D.R.f * b) * (Real.log b + sig G) :=
      mul_le_mul h3 (by linarith) hX (by linarith)
    have h5 : (D.R.m : ℝ) ^ 3 * bigN D ≤ (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 := by
      have : (D.R.m : ℝ) ^ 2 * bigN D * D.R.m ≤ (D.R.m : ℝ) ^ 2 * bigN D * bigN D :=
        mul_le_mul_of_nonneg_left hmN (by positivity)
      nlinarith
    have h6 : 2 * ((D.R.m : ℝ) ^ 3 * bigN D) * sig G ≤ (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (2 * sig G) := by
      have := mul_le_mul_of_nonneg_right h5 (by linarith : (0 : ℝ) ≤ 2 * sig G)
      linarith
    have h7 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2)
    refine h6.trans (h7.trans (le_of_eq ?_))
    rw [bOne]
    ring

end Loss

end GlobalTheory.CompanionTheory.VolVal

namespace GlobalTheory.CompanionTheory.VolVal

open Formalism.BasicNotions Formalism.L2.DIV

theorem finCoefK : GlobalTheory.FunPr.Hypotheses₂ → FinCoefK := by
  intro _
  refine ⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ => ?_⟩⟩⟩
  have hL := s.core.lev
  have hde := Test.pde_ne_q s
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hf : 1 ≤ D.R.f := by
    have h1 : D.R.m ≤ D.R.f := D.R.m_le_f
    have h2 := D.R.two_le_m
    omega
  refine ⟨dlF ch.G, loss_dlF ch.G hC hb hf, fun t w hA Φ β hβ => ?_⟩
  have hq := coef_QL hL ch.S.toGridChoice t Φ hde (GlobalTheory.RowTest.guard_of_qGuard s.guard t) hA hβ
  refine ⟨((∏ v, (ch.S.term t Φ β v).coef : ℚ) : D.what₂.LL), ?_, ?_⟩
  · rw [map_ratCast]
    push_cast
    rfl
  · rcases hq with h | h
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr h

end GlobalTheory.CompanionTheory.VolVal

end
end

end ResidueCardinalityNilpotence
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.finite_coefficient_bound : GlobalTheory.FunPr.Hypotheses₂ → FinCoefK := by
  first | exact @ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.finCoefK | exact ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.finCoefK | (intros; apply ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.finCoefK <;> assumption)

end
