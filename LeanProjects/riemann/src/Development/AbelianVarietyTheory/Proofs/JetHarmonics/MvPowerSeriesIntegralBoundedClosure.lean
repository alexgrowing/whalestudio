import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt

noncomputable section

open GlobalTheory.ConvSer

namespace GlobalTheory.BddAlg

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type}

def Le (c : ℝ) (S : MvPowerSeries σ K) : Prop := ∀ ν, ‖MvPowerSeries.coeff ν S‖ ≤ c

omit [IsUltrametricDist K] in
theorem Le.nonneg {c : ℝ} {S : MvPowerSeries σ K} (h : Le c S) : 0 ≤ c :=
  (norm_nonneg _).trans (h 0)

theorem Le.add {c d : ℝ} {S T : MvPowerSeries σ K} (h : Le c S) (h' : Le d T) :
    Le (max c d) (S + T) := fun ν => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (h ν) (h' ν))

theorem Le.sub {c d : ℝ} {S T : MvPowerSeries σ K} (h : Le c S) (h' : Le d T) :
    Le (max c d) (S - T) := fun ν => by
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (h ν) ?_)
  rw [norm_neg]; exact h' ν

theorem Le.mul {c d : ℝ} {S T : MvPowerSeries σ K} (h : Le c S) (h' : Le d T) :
    Le (c * d) (S * T) := fun ν => by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg h.nonneg h'.nonneg) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (h _) (h' _) (norm_nonneg _) h.nonneg

omit [IsUltrametricDist K] in
theorem le_C (a : K) : Le ‖a‖ (MvPowerSeries.C a : MvPowerSeries σ K) := fun ν => by
  classical
  rw [MvPowerSeries.coeff_C]
  split_ifs <;> simp

theorem intg_add {S T : MvPowerSeries σ K} (h : Intg S) (h' : Intg T) : Intg (S + T) := by
  have := Le.add (c := 1) (d := 1) h h'
  rwa [max_self] at this

theorem intg_sub {S T : MvPowerSeries σ K} (h : Intg S) (h' : Intg T) : Intg (S - T) := by
  have := Le.sub (c := 1) (d := 1) h h'
  rwa [max_self] at this

theorem intg_mul {S T : MvPowerSeries σ K} (h : Intg S) (h' : Intg T) : Intg (S * T) := by
  have := Le.mul (c := 1) (d := 1) h h'
  rwa [one_mul] at this

theorem bdd_add {S T : MvPowerSeries σ K} (h : Bdd S) (h' : Bdd T) : Bdd (S + T) := by
  obtain ⟨c, h⟩ := h
  obtain ⟨d, h'⟩ := h'
  exact ⟨_, Le.add h h'⟩

theorem bdd_sub {S T : MvPowerSeries σ K} (h : Bdd S) (h' : Bdd T) : Bdd (S - T) := by
  obtain ⟨c, h⟩ := h
  obtain ⟨d, h'⟩ := h'
  exact ⟨_, Le.sub h h'⟩

theorem bdd_mul {S T : MvPowerSeries σ K} (h : Bdd S) (h' : Bdd T) : Bdd (S * T) := by
  obtain ⟨c, h⟩ := h
  obtain ⟨d, h'⟩ := h'
  exact ⟨_, Le.mul h h'⟩

omit [IsUltrametricDist K] in
theorem bdd_C (a : K) : Bdd (MvPowerSeries.C a : MvPowerSeries σ K) := ⟨_, le_C a⟩

omit [IsUltrametricDist K] in
theorem intg_C {a : K} (ha : ‖a‖ ≤ 1) : Intg (MvPowerSeries.C a : MvPowerSeries σ K) :=
  fun ν => (le_C a ν).trans ha

omit [IsUltrametricDist K] in
theorem intg_one : Intg (1 : MvPowerSeries σ K) := by
  have := intg_C (σ := σ) (a := (1 : K)) (by simp)
  rwa [map_one] at this

omit [IsUltrametricDist K] in
theorem intg_zero : Intg (0 : MvPowerSeries σ K) := fun ν => by simp

omit [IsUltrametricDist K] in
theorem bdd_of_intg {S : MvPowerSeries σ K} (h : Intg S) : Bdd S := ⟨1, h⟩

theorem intg_prod {ι : Type} (t : Finset ι) (f : ι → MvPowerSeries σ K)
    (h : ∀ i ∈ t, Intg (f i)) : Intg (∏ i ∈ t, f i) :=
  Finset.prod_induction f Intg (fun _ _ => intg_mul) intg_one h

theorem bdd_prod {ι : Type} (t : Finset ι) (f : ι → MvPowerSeries σ K)
    (h : ∀ i ∈ t, Bdd (f i)) : Bdd (∏ i ∈ t, f i) :=
  Finset.prod_induction f Bdd (fun _ _ => bdd_mul) (bdd_of_intg intg_one) h

theorem intg_pow {S : MvPowerSeries σ K} (h : Intg S) (n : ℕ) : Intg (S ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact intg_one
  | succ n ih => rw [pow_succ]; exact intg_mul ih h

theorem bdd_pow {S : MvPowerSeries σ K} (h : Bdd S) (n : ℕ) : Bdd (S ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact bdd_of_intg intg_one
  | succ n ih => rw [pow_succ]; exact bdd_mul ih h

omit [IsUltrametricDist K] in
theorem small_X (i : σ) : Small (MvPowerSeries.X i : MvPowerSeries σ K) := by
  classical
  refine ⟨fun ν => ?_, by simp⟩
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem norm_finsum_le {ι : Type} {c : ℝ} (hc : 0 ≤ c) (f : ι → K) (h : ∀ i, ‖f i‖ ≤ c) :
    ‖∑ᶠ i, f i‖ ≤ c := by
  classical
  rw [finsum_def]
  split_ifs with hf
  · exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc fun i _ => h i
  · simpa using hc

theorem Le.subst {ρ : Type} [Fintype ρ] {a : ρ → MvPowerSeries σ K} {S : MvPowerSeries ρ K}
    {c : ℝ} (ha : ∀ j, Intg (a j)) (h0 : ∀ j, MvPowerSeries.constantCoeff (a j) = 0)
    (hS : Le c S) : Le c (MvPowerSeries.subst a S) := fun ν => by
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero h0)]
  refine norm_finsum_le hS.nonneg _ fun d => ?_
  rw [smul_eq_mul, norm_mul]
  have h1 : Intg (d.prod fun s e => a s ^ e) :=
    intg_prod _ _ fun i _ => intg_pow (ha i) _
  exact (mul_le_mul (hS d) (h1 ν) (norm_nonneg _) hS.nonneg).trans (mul_one c).le

theorem bdd_eval₂ {k ι : Type} [CommRing k] (φ : k →+* K) (a : ι → MvPowerSeries σ K)
    (A : MvPolynomial ι k) (ha : ∀ j, Bdd (a j)) :
    Bdd (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A) := by
  induction A using MvPolynomial.induction_on with
  | C r => rw [MvPolynomial.eval₂_C]; exact bdd_C _
  | add p q hp hq => rw [MvPolynomial.eval₂_add]; exact bdd_add hp hq
  | mul_X p n hp => rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]; exact bdd_mul hp (ha n)

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
omit [IsUltrametricDist K] in
private lemma nonneg_of_le' {c : ℝ} {S : MvPowerSeries σ K}
    (h : _root_.GlobalTheory.BddAlg.Le c S) : 0 ≤ c :=
  (norm_nonneg _).trans (h 0)

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
omit [IsUltrametricDist K] in
private lemma le_one_one : _root_.GlobalTheory.BddAlg.Le 1 (1 : MvPowerSeries σ K) :=
  fun ν => by
    classical
    rw [MvPowerSeries.coeff_one]
    split_ifs <;> simp

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
private lemma le_mul' {c d : ℝ} {S T : MvPowerSeries σ K}
    (hS : _root_.GlobalTheory.BddAlg.Le c S) (hT : _root_.GlobalTheory.BddAlg.Le d T) :
    _root_.GlobalTheory.BddAlg.Le (c * d) (S * T) := fun ν => by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (nonneg_of_le' hS) (nonneg_of_le' hT)) fun p _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hS _) (hT _) (norm_nonneg _) (nonneg_of_le' hS)

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
private lemma le_one_finset_prod_of_le_one {ι : Type*} (t : Finset ι) (f : ι → MvPowerSeries σ K)
    (h : ∀ i ∈ t, _root_.GlobalTheory.BddAlg.Le 1 (f i)) :
    _root_.GlobalTheory.BddAlg.Le 1 (∏ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact le_one_one
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    have := le_mul' (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    rwa [one_mul] at this

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
private lemma le_pow' {c : ℝ} {S : MvPowerSeries σ K}
    (hS : _root_.GlobalTheory.BddAlg.Le c S) (n : ℕ) : _root_.GlobalTheory.BddAlg.Le (c ^ n) (S ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact le_one_one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact le_mul' ih hS

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
private lemma le_subst_of_le_one_of_constantCoeff_zero {ρ : Type} [Fintype ρ] {a : ρ → MvPowerSeries σ K}
    {S : MvPowerSeries ρ K} {c : ℝ} (ha : ∀ j, _root_.GlobalTheory.BddAlg.Le 1 (a j))
    (h0 : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) (hS : _root_.GlobalTheory.BddAlg.Le c S) :
    _root_.GlobalTheory.BddAlg.Le c (MvPowerSeries.subst a S) := fun e => by
  have hsub : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  rw [MvPowerSeries.coeff_subst hsub, finsum_eq_sum _ (MvPowerSeries.coeff_subst_finite hsub S e)]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (nonneg_of_le' hS)
    fun d _ => ?_
  rw [smul_eq_mul, norm_mul]
  have hp : _root_.GlobalTheory.BddAlg.Le 1 (d.prod fun s n => a s ^ n) := by
    have := le_one_finset_prod_of_le_one d.support (fun s => a s ^ d s) fun s _ => by
      simpa using le_pow' (ha s) (d s)
    exact this
  calc ‖MvPowerSeries.coeff d S‖ * ‖MvPowerSeries.coeff e (d.prod fun s n => a s ^ n)‖
      ≤ c * 1 := mul_le_mul (hS d) (hp e) (norm_nonneg _) (nonneg_of_le' hS)
    _ = c := mul_one c

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
omit [IsUltrametricDist K] in
private lemma bdd_iff_exists_le {S : MvPowerSeries σ K} :
    _root_.GlobalTheory.ConvSer.Bdd S ↔ ∃ c, _root_.GlobalTheory.BddAlg.Le c S := Iff.rfl

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
private lemma le_add' {c : ℝ} {S T : MvPowerSeries σ K}
    (hS : _root_.GlobalTheory.BddAlg.Le c S) (hT : _root_.GlobalTheory.BddAlg.Le c T) :
    _root_.GlobalTheory.BddAlg.Le c (S + T) := fun ν => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hS ν) (hT ν))

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
omit [IsUltrametricDist K] in
private lemma le_neg' {c : ℝ} {S : MvPowerSeries σ K}
    (hS : _root_.GlobalTheory.BddAlg.Le c S) : _root_.GlobalTheory.BddAlg.Le c (-S) := fun ν => by
  rw [map_neg, norm_neg]
  exact hS ν

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
private lemma le_sub' {c : ℝ} {S T : MvPowerSeries σ K}
    (hS : _root_.GlobalTheory.BddAlg.Le c S) (hT : _root_.GlobalTheory.BddAlg.Le c T) :
    _root_.GlobalTheory.BddAlg.Le c (S - T) := by
  rw [sub_eq_add_neg]
  exact le_add' hS (le_neg' hT)

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
private lemma le_one_mul_of_le_one {S T : MvPowerSeries σ K} (hS : _root_.GlobalTheory.BddAlg.Le 1 S)
    (hT : _root_.GlobalTheory.BddAlg.Le 1 T) : _root_.GlobalTheory.BddAlg.Le 1 (S * T) := by
  have := le_mul' hS hT
  rwa [one_mul] at this

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
omit [IsUltrametricDist K] in
private lemma le_mono {c d : ℝ} {S : MvPowerSeries σ K}
    (h : _root_.GlobalTheory.BddAlg.Le c S) (hcd : c ≤ d) : _root_.GlobalTheory.BddAlg.Le d S :=
  fun ν => (h ν).trans hcd

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
private lemma bdd_add_jet_harmonics {S T : MvPowerSeries σ K} (hS : _root_.GlobalTheory.ConvSer.Bdd S)
    (hT : _root_.GlobalTheory.ConvSer.Bdd T) : _root_.GlobalTheory.ConvSer.Bdd (S + T) := by
  obtain ⟨c, hc⟩ := bdd_iff_exists_le.mp hS
  obtain ⟨d, hd⟩ := bdd_iff_exists_le.mp hT
  exact bdd_iff_exists_le.mpr ⟨max c d, le_add' (le_mono hc (le_max_left c d))
    (le_mono hd (le_max_right c d))⟩

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
private lemma bdd_sub' {S T : MvPowerSeries σ K} (hS : _root_.GlobalTheory.ConvSer.Bdd S)
    (hT : _root_.GlobalTheory.ConvSer.Bdd T) : _root_.GlobalTheory.ConvSer.Bdd (S - T) := by
  obtain ⟨c, hc⟩ := bdd_iff_exists_le.mp hS
  obtain ⟨d, hd⟩ := bdd_iff_exists_le.mp hT
  exact bdd_iff_exists_le.mpr ⟨max c d, le_sub' (le_mono hc (le_max_left c d))
    (le_mono hd (le_max_right c d))⟩

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
private lemma bdd_mul_of_bdd {S T : MvPowerSeries σ K} (hS : _root_.GlobalTheory.ConvSer.Bdd S)
    (hT : _root_.GlobalTheory.ConvSer.Bdd T) : _root_.GlobalTheory.ConvSer.Bdd (S * T) := by
  obtain ⟨c, hc⟩ := bdd_iff_exists_le.mp hS
  obtain ⟨d, hd⟩ := bdd_iff_exists_le.mp hT
  exact bdd_iff_exists_le.mpr ⟨c * d, le_mul' hc hd⟩

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
omit [IsUltrametricDist K] in
private lemma le_norm_C (a : K) :
    _root_.GlobalTheory.BddAlg.Le ‖a‖ (MvPowerSeries.C a : MvPowerSeries σ K) := fun ν => by
  classical
  rw [MvPowerSeries.coeff_C]
  split_ifs <;> simp

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
omit [IsUltrametricDist K] in
private lemma le_one_X (i : σ) :
    _root_.GlobalTheory.BddAlg.Le 1 (MvPowerSeries.X i : MvPowerSeries σ K) := fun ν => by
  classical
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
private lemma le_finset_sum {ι : Type*} {c : ℝ} (hc : 0 ≤ c) (t : Finset ι)
    (f : ι → MvPowerSeries σ K) (h : ∀ i ∈ t, _root_.GlobalTheory.BddAlg.Le c (f i)) :
    _root_.GlobalTheory.BddAlg.Le c (∑ i ∈ t, f i) := fun ν => by
  rw [map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc fun i hi => h i hi ν

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in
omit [IsUltrametricDist K] in
private lemma le_zero_series {c : ℝ} (hc : 0 ≤ c) :
    _root_.GlobalTheory.BddAlg.Le c (0 : MvPowerSeries σ K) :=
  fun ν => by simp [hc]

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} in

theorem _root_.GlobalTheory.BddAlg.bdd_alg : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (σ : Type), (∀ S T : MvPowerSeries σ K, _root_.GlobalTheory.ConvSer.Intg S → _root_.GlobalTheory.ConvSer.Intg T → _root_.GlobalTheory.ConvSer.Intg (S + T) ∧ _root_.GlobalTheory.ConvSer.Intg (S - T) ∧ _root_.GlobalTheory.ConvSer.Intg (S * T)) ∧ (∀ S T : MvPowerSeries σ K, _root_.GlobalTheory.ConvSer.Bdd S → _root_.GlobalTheory.ConvSer.Bdd T → _root_.GlobalTheory.ConvSer.Bdd (S + T) ∧ _root_.GlobalTheory.ConvSer.Bdd (S - T) ∧ _root_.GlobalTheory.ConvSer.Bdd (S * T)) ∧ (∀ (S : MvPowerSeries σ K) (n : ℕ), (_root_.GlobalTheory.ConvSer.Intg S → _root_.GlobalTheory.ConvSer.Intg (S ^ n)) ∧ (_root_.GlobalTheory.ConvSer.Bdd S → _root_.GlobalTheory.ConvSer.Bdd (S ^ n)) ∧ (_root_.GlobalTheory.ConvSer.Intg S → _root_.GlobalTheory.ConvSer.Bdd S)) ∧ (∀ a : K, _root_.GlobalTheory.ConvSer.Bdd (MvPowerSeries.C a : MvPowerSeries σ K) ∧ (‖a‖ ≤ 1 → _root_.GlobalTheory.ConvSer.Intg (MvPowerSeries.C a : MvPowerSeries σ K)) ∧ (‖a‖ < 1 → _root_.GlobalTheory.ConvSer.Small (MvPowerSeries.C a : MvPowerSeries σ K))) ∧ (∀ i : σ, _root_.GlobalTheory.ConvSer.Small (MvPowerSeries.X i : MvPowerSeries σ K)) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → MvPowerSeries σ K), ((∀ i ∈ t, _root_.GlobalTheory.ConvSer.Intg (f i)) → _root_.GlobalTheory.ConvSer.Intg (∏ i ∈ t, f i) ∧ _root_.GlobalTheory.ConvSer.Intg (∑ i ∈ t, f i)) ∧ ((∀ i ∈ t, _root_.GlobalTheory.ConvSer.Bdd (f i)) → _root_.GlobalTheory.ConvSer.Bdd (∏ i ∈ t, f i) ∧ _root_.GlobalTheory.ConvSer.Bdd (∑ i ∈ t, f i))) ∧ (∀ (ρ : Type) [Fintype ρ] (a : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, _root_.GlobalTheory.ConvSer.Intg (a j)) → (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → (_root_.GlobalTheory.ConvSer.Intg S → _root_.GlobalTheory.ConvSer.Intg (MvPowerSeries.subst a S)) ∧ (_root_.GlobalTheory.ConvSer.Bdd S → _root_.GlobalTheory.ConvSer.Bdd (MvPowerSeries.subst a S))) ∧ (∀ (a : MvPowerSeries σ K) (f : PowerSeries K), _root_.GlobalTheory.ConvSer.Intg a → MvPowerSeries.constantCoeff a = 0 → (_root_.GlobalTheory.ConvSer.Intg f → _root_.GlobalTheory.ConvSer.Intg (f.subst a)) ∧ (_root_.GlobalTheory.ConvSer.Bdd f → _root_.GlobalTheory.ConvSer.Bdd (f.subst a))) ∧ (∀ (k ι : Type) [CommRing k] (φ : k →+* K) (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k), (∀ j, _root_.GlobalTheory.ConvSer.Bdd (a j)) → _root_.GlobalTheory.ConvSer.Bdd (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A)) ∧ (∀ f : PowerSeries K, (_root_.GlobalTheory.ConvSer.Intg f ↔ ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1) ∧ (_root_.GlobalTheory.ConvSer.Bdd f ↔ ∃ C : ℝ, ∀ n, ‖PowerSeries.coeff n f‖ ≤ C)) := by
  intro K _ _ σ
  have hsubst : ∀ (ρ : Type) [Fintype ρ] (a : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K),
      (∀ j, _root_.GlobalTheory.ConvSer.Intg (a j)) → (∀ j, MvPowerSeries.constantCoeff (a j) = 0) →
      (_root_.GlobalTheory.ConvSer.Intg S → _root_.GlobalTheory.ConvSer.Intg (MvPowerSeries.subst a S)) ∧
      (_root_.GlobalTheory.ConvSer.Bdd S → _root_.GlobalTheory.ConvSer.Bdd (MvPowerSeries.subst a S)) := by
    intro ρ _ a S ha h0
    refine ⟨fun hS => le_subst_of_le_one_of_constantCoeff_zero ha h0 hS, fun hS => ?_⟩
    obtain ⟨c, hc⟩ := bdd_iff_exists_le.mp hS
    exact bdd_iff_exists_le.mpr ⟨c, le_subst_of_le_one_of_constantCoeff_zero ha h0 hc⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hsubst, ?_, ?_, ?_⟩
  · intro S T hS hT
    exact ⟨le_add' hS hT, le_sub' hS hT, le_one_mul_of_le_one hS hT⟩
  · intro S T hS hT
    exact ⟨bdd_add_jet_harmonics hS hT, bdd_sub' hS hT, bdd_mul_of_bdd hS hT⟩
  · intro S n
    refine ⟨fun hS => ?_, fun hS => ?_, fun hS => bdd_iff_exists_le.mpr ⟨1, hS⟩⟩
    · have := le_pow' (c := 1) hS n
      rwa [one_pow] at this
    · obtain ⟨c, hc⟩ := bdd_iff_exists_le.mp hS
      exact bdd_iff_exists_le.mpr ⟨c ^ n, le_pow' hc n⟩
  · intro a
    refine ⟨bdd_iff_exists_le.mpr ⟨‖a‖, le_norm_C a⟩,
      fun ha => le_mono (le_norm_C a) ha, fun ha => ?_⟩
    refine ⟨le_mono (le_norm_C a) ha.le, ?_⟩
    rw [MvPowerSeries.constantCoeff_C]
    exact ha
  · intro i
    refine ⟨le_one_X i, ?_⟩
    rw [MvPowerSeries.constantCoeff_X, norm_zero]
    exact one_pos
  · intro ι t f
    classical
    refine ⟨fun h => ⟨le_one_finset_prod_of_le_one t f h, le_finset_sum zero_le_one t f h⟩,
      fun h => ⟨?_, ?_⟩⟩
    · induction t using Finset.induction_on with
      | empty =>
        rw [Finset.prod_empty]
        exact bdd_iff_exists_le.mpr ⟨1, le_one_one⟩
      | insert b t hb ih =>
        rw [Finset.prod_insert hb]
        exact bdd_mul_of_bdd (h b (Finset.mem_insert_self _ _))
          (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    · induction t using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty]
        exact bdd_iff_exists_le.mpr ⟨0, le_zero_series le_rfl⟩
      | insert b t hb ih =>
        rw [Finset.sum_insert hb]
        exact bdd_add_jet_harmonics (h b (Finset.mem_insert_self _ _))
          (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
  · intro a f ha h0
    exact hsubst Unit (fun _ => a) f (fun _ => ha) (fun _ => h0)
  · intro k ι _ φ a A ha
    induction A using MvPolynomial.induction_on with
    | C r =>
      rw [MvPolynomial.eval₂_C, RingHom.comp_apply]
      exact bdd_iff_exists_le.mpr ⟨_, le_norm_C (φ r)⟩
    | add p q hp hq =>
      rw [MvPolynomial.eval₂_add]
      exact bdd_add_jet_harmonics hp hq
    | mul_X p j hp =>
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      exact bdd_mul_of_bdd hp (ha j)
  · intro f
    have key : ∀ c : ℝ, _root_.GlobalTheory.BddAlg.Le c f ↔ ∀ n, ‖PowerSeries.coeff n f‖ ≤ c := by
      intro c
      constructor
      · intro h n
        have := h (Finsupp.single () n)
        exact this
      · intro h ν
        rw [← PowerSeries.coeff_def (s := ν) (n := ν ()) rfl]
        exact h _
    exact ⟨key 1, bdd_iff_exists_le.trans (exists_congr key)⟩

end GlobalTheory.BddAlg
