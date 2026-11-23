import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitLoc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyDeepSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLeOfCompleteHomogeneousLe

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace PositivityTheory.ThK.SplitLoc.Unr

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL

section Alg
open PowerSeries

abbrev polys : Subring (PowerSeries ℂ) := (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ).range

def conv (P : Polynomial ℂ) (n : ℕ) (f : ℤ → ℂ) (m : ℤ) : ℂ := ∑ j ∈ Finset.range (n + 1), P.coeff j * f (m - j)

theorem coeff_prod_mk {n : ℕ} (f : Fin n → ℕ → ℂ) (m : ℕ) :
    coeff m (∏ i, (mk (f i) : PowerSeries ℂ)) = ∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i, f i (a i) := by
  rw [coeff_prod]
  simp only [coeff_mk]
  refine Finset.sum_bij' (fun l _ => (l : Fin n → ℕ))
    (fun a _ => Finsupp.equivFunOnFinite.symm a) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simpa [Finset.mem_piAntidiag, Finset.mem_finsuppAntidiag] using hl
  · intro a ha
    simpa [Finset.mem_piAntidiag, Finset.mem_finsuppAntidiag] using ha
  · intro l _
    simp
  · intro a _
    simp
  · intro l _
    rfl

theorem mem_polys_of_coeff {f : PowerSeries ℂ} (N : ℕ) (h : ∀ t, N ≤ t → coeff t f = 0) : f ∈ polys := by
  refine ⟨trunc N f, ?_⟩
  ext t
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, coeff_trunc]
  split_ifs with ht
  · rfl
  · exact (h t (not_lt.mp ht)).symm

theorem linear_mul_piece_mem_polys (γ : ℂ) (M b : ℕ) :
    (1 - C γ * X) * mk (fun t => if min t M = b then γ ^ (t - M) else 0) ∈ polys := by
  refine mem_polys_of_coeff (M + 1) fun t ht => ?_
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have h1 : min (s + 1) M = M := by omega
  have h2 : min s M = M := by omega
  have h3 : s + 1 - M = s - M + 1 := by omega
  rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_mk, coeff_mk, h1, h2, h3]
  split_ifs
  · ring
  · ring

theorem gen_mem_polys {n : ℕ} (γ : Fin n → ℂ) (M : ℕ) (T : (Fin n → ℕ) → ℂ)
    (hT : ∀ a, T a = (∏ i, γ i ^ (a i - M)) * T (fun i => min (a i) M)) :
    (∏ i, (1 - C (γ i) * X)) * mk (fun t => ∑ a ∈ Finset.piAntidiag Finset.univ t, T a) ∈ polys := by
  classical
  have key : (mk (fun t => ∑ a ∈ Finset.piAntidiag Finset.univ t, T a) : PowerSeries ℂ) =
      ∑ b ∈ Fintype.piFinset (fun _ : Fin n => Finset.range (M + 1)),
        C (T b) * ∏ i, mk (fun t => if min t M = b i then γ i ^ (t - M) else 0) := by
    ext t
    rw [coeff_mk, map_sum]
    simp only [coeff_C_mul, coeff_prod_mk, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (fun i => min (a i) M)]
    · rw [hT a, mul_comm]
      simp
    · intro b _ hb
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (Ne.symm hi)), mul_zero]
    · intro h
      exact absurd (Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (by omega)) h
  rw [key, Finset.mul_sum]
  refine Subring.sum_mem _ fun b _ => ?_
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  refine Subring.mul_mem _ ⟨Polynomial.C (T b), by simp⟩ ?_
  exact Subring.prod_mem _ fun i _ => linear_mul_piece_mem_polys _ _ _

theorem gen_geom {n : ℕ} (γ : Fin n → ℂ) :
    (∏ i, (1 - C (γ i) * X)) * mk (fun t => ∑ a ∈ Finset.piAntidiag Finset.univ t, ∏ i, γ i ^ a i) = 1 := by
  have key : (mk (fun t => ∑ a ∈ Finset.piAntidiag Finset.univ t, ∏ i, γ i ^ a i) : PowerSeries ℂ) =
      ∏ i, mk (fun t => γ i ^ t) := by
    ext t
    rw [coeff_mk, GlobalTheory.CompleteHomogeneousBound.coeff_prod_geom]
  rw [key, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [mul_comm, GlobalTheory.CompleteHomogeneousBound.geom_mul_linear]

theorem conv_natCast {P : Polynomial ℂ} {n : ℕ} (hP : P.natDegree ≤ n) {f : ℤ → ℂ} (hf : ∀ m < 0, f m = 0) (t : ℕ) :
    conv P n f t = coeff t ((P : PowerSeries ℂ) * mk fun s => f s) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Polynomial.coeff_coe, coeff_mk]
  unfold conv
  have h1 : ∑ j ∈ Finset.range (n + 1), P.coeff j * f ((t : ℤ) - j) =
      ∑ j ∈ Finset.range (n + t + 1), P.coeff j * f ((t : ℤ) - j) := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => ?_
    rw [Finset.mem_range] at hj
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  have h2 : ∑ j ∈ Finset.range (t + 1), P.coeff j * f ((t : ℤ) - j) =
      ∑ j ∈ Finset.range (n + t + 1), P.coeff j * f ((t : ℤ) - j) := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => ?_
    rw [Finset.mem_range] at hj
    rw [hf _ (by omega), mul_zero]
  rw [h1, ← h2]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [Nat.cast_sub (by omega)]

theorem conv_neg {P : Polynomial ℂ} {n : ℕ} {f : ℤ → ℂ} (hf : ∀ m < 0, f m = 0) {m : ℤ} (hm : m < 0) :
    conv P n f m = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [hf _ (by omega), mul_zero]

theorem hasSum_conv {P : Polynomial ℂ} {n : ℕ} (hP : P.natDegree ≤ n) {f : ℤ → ℂ} {S : ℂ} (hf : HasSum f S) :
    HasSum (conv P n f) (P.eval 1 * S) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.sum_mul]
  refine hasSum_sum fun j _ => ?_
  rw [one_pow, mul_one]
  exact ((Equiv.subRight (j : ℤ)).hasSum_iff.mpr hf).mul_left _

theorem summable_geom_coeff {n : ℕ} (γ : Fin n → ℂ) (hγ : ∀ i, ‖γ i‖ < 1) :
    Summable fun t : ℕ => ‖∑ a ∈ Finset.piAntidiag Finset.univ t, ∏ i, γ i ^ a i‖ := by
  have h := GlobalTheory.CompleteHomogeneousBound.weightedSummable_prod 1 Finset.univ
    (fun i => (mk fun t => γ i ^ t : PowerSeries ℂ))
    (fun i _ => (GlobalTheory.CompleteHomogeneousBound.weightedSummable_geom_iff 1 (γ i)).mpr (by simpa using hγ i))
  unfold GlobalTheory.CompleteHomogeneousBound.WeightedSummable at h
  simpa [GlobalTheory.CompleteHomogeneousBound.coeff_prod_geom] using h

end Alg

section ZetaNonvanishing₂
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def dShell (n : ℕ) (m : ℤ) : Set (GL (Fin n) k) := {g | ord k (gdet g) = m}

def wt {n : ℕ} (d : ℕ) (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) : ℂ := (ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)

def cst (d : ℕ) (ϖ : kˣ) (ν : kˣ →* ℂˣ) : ℂ := (ν ϖ : ℂ) * (resCard k : ℂ) ^ (-(d : ℂ) / 2)

def scal (n : ℕ) (u : kˣ) : GL (Fin n) k := diagGL fun _ => u

theorem ord_one_eq : ord k 1 = 0 := ord_eq_zero (by simp)

theorem ord_prod_eq {ι : Type} (s : Finset ι) (f : ι → kˣ) : ord k (∏ i ∈ s, f i) = ∑ i ∈ s, ord k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ord_one_eq]
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ord_mul, ih]

theorem ord_zpow_eq (u : kˣ) (m : ℤ) : ord k (u ^ m) = m * ord k u := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := congrArg Multiplicative.toAdd (map_zpow o u m)
  rw [toAdd_zpow, smul_eq_mul] at h
  exact h

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem shellSet_eq_cell {n : ℕ} (ϖ : kˣ) (e : Fin n → ℤ) : shellSet ϖ e = GlobalTheory.GLDoubling.cell k (Fin n) ϖ e := by
  have h : (diagGL fun i => ϖ ^ e i) = GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ e :=
    Units.ext (by rw [GlobalTheory.GLDoubling.val_torusElt, diagGL_val]; simp)
  rw [shellSet, h, GlobalTheory.GLDoubling.cell]

theorem ord_of_mem_shellSet {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {e : Fin n → ℤ} {g : GL (Fin n) k}
    (hg : g ∈ shellSet ϖ e) : ord k (gdet g) = ∑ i, e i := by
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
  rw [gdet_mul, gdet_mul, ord_mul, ord_mul, ord_eq_zero (valuation_gdet_of_mem_KO hx),
    ord_eq_zero (valuation_gdet_of_mem_KO hy), zero_add, add_zero, gdet, det_diagGL, ord_prod_eq]
  exact Finset.sum_congr rfl fun i _ => by rw [ord_zpow_eq, ord_eq_one hϖ, mul_one]

theorem dShell_eq_iUnion {ϖ : kˣ} (hϖ : IsUnif ϖ) (n : ℕ) (m : ℤ) :
    dShell (k := k) n m = ⋃ e : {e : Fin n → ℤ // Antitone e ∧ ∑ i, e i = m}, shellSet ϖ e.1 := by
  ext g
  rw [Set.mem_iUnion]
  constructor
  · intro hg
    have h : g ∈ ⋃ e : {e : Fin n → ℤ // Antitone e}, GlobalTheory.GLDoubling.cell k (Fin n) ϖ e := by
      rw [GlobalTheory.GLDoubling.iUnion_cell hϖ]; trivial
    obtain ⟨e, he⟩ := Set.mem_iUnion.1 h
    rw [← shellSet_eq_cell] at he
    exact ⟨⟨e.1, e.2, (ord_of_mem_shellSet hϖ he).symm.trans hg⟩, he⟩
  · rintro ⟨e, he⟩
    exact (ord_of_mem_shellSet hϖ he).trans e.2.2

theorem isOpen_shellSet {n : ℕ} (ϖ : kˣ) (e : Fin n → ℤ) : IsOpen (shellSet ϖ e) := by
  rw [shellSet_eq_cell]; exact GlobalTheory.GLDoubling.isOpen_cell ϖ e

theorem isCompact_shellSet {n : ℕ} (ϖ : kˣ) (e : Fin n → ℤ) : IsCompact (shellSet ϖ e) := by
  rw [shellSet_eq_cell]; exact GlobalTheory.GLDoubling.isCompact_cell ϖ e

theorem isOpen_dShell (n : ℕ) (m : ℤ) : IsOpen (dShell (k := k) n m) := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  rw [dShell_eq_iUnion hϖ]
  exact isOpen_iUnion fun e => isOpen_shellSet ϖ e.1

open GlobalTheory.IwahoriInj in

theorem le_of_mem_shellSet {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {e : Fin n → ℤ} {g : GL (Fin n) k}
    (hg : g ∈ shellSet ϖ e) {a : ℤ} (ha : ∀ i j, Deep a (g.val i j)) (i : Fin n) : a ≤ e i := by
  obtain ⟨x, hx, y, hy, h⟩ := mem_shellSet.1 hg
  have h1 : (diagGL fun i => ϖ ^ e i) = x⁻¹ * g * y⁻¹ := by rw [h]; group
  have hx' : ∀ i j, Deep 0 ((x⁻¹).val i j) := fun i j => deep_zero_iff.2 (((mem_KO_iff x).1 hx).2 i j)
  have hy' : ∀ i j, Deep 0 ((y⁻¹).val i j) := fun i j => deep_zero_iff.2 (((mem_KO_iff y).1 hy).2 i j)
  have h2 : Deep a ((x⁻¹ * g * y⁻¹).val i i) := by
    rw [Units.val_mul, Units.val_mul, mul_apply]
    refine Deep.sum fun l _ => ?_
    have h3 : Deep a (((x⁻¹).val * g.val) i l) := by
      rw [mul_apply]
      exact Deep.sum fun r _ => ((hx' i r).mul (ha r l)).mono (by omega)
    exact (h3.mul (hy' l i)).mono (by omega)
  rw [← h1, diagGL_val, diagonal_apply_eq, Deep, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ] at h2
  exact (zpow_le_zpow_iff_right_of_lt_one₀ unif_pos uniformizer_lt_one).1 h2

theorem finsum_eq_of_hasSum {ι : Type} {f : ι → ℂ} {S : ℂ} (h : HasSum f S) {s : Set ι} (hs : s.Finite)
    (hz : ∀ i ∉ s, f i = 0) : ∑ᶠ i, f i = S := by
  rw [finsum_eq_sum_of_support_subset (s := hs.toFinset) f
    fun e he => by by_contra h; exact he (hz e (by simpa using h))]
  exact (hasSum_sum_of_ne_finset_zero fun e he => hz e (by simpa using he)).unique h

theorem finite_exponents (n : ℕ) (a m : ℤ) : {e : Fin n → ℤ | ∑ i, e i = m ∧ ∀ i, a ≤ e i}.Finite := by
  refine (Set.Finite.pi' (t := fun _ : Fin n => Set.Icc a (m - n * a + a)) fun _ => Set.finite_Icc _ _).subset ?_
  rintro e ⟨h1, h2⟩ i
  refine ⟨h2 i, ?_⟩
  have h3 := Finset.single_le_sum (f := fun j => e j - a) (s := Finset.univ) (fun j _ => sub_nonneg.2 (h2 j))
    (Finset.mem_univ i)
  simp only [Finset.sum_sub_distrib, h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  linarith

variable [MeasurableSpace k] [BorelSpace k]

def Jm (n : ℕ) (φ : Matrix (Fin n) (Fin n) k → ℂ) (m : ℤ) : ℂ :=
  ∫ g in dShell n m, φ g.val ∂haarVol (KO k (Fin n))

theorem measurableSet_dShell (n : ℕ) (m : ℤ) : MeasurableSet (dShell (k := k) n m) := by
  exact (isOpen_dShell n m).measurableSet

theorem wt_of_mem {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (d : ℕ) {n : ℕ} {m : ℤ} {g : GL (Fin n) k}
    (hg : g ∈ dShell n m) : wt d ν g = cst d ϖ ν ^ m := by
  have hm : ord k (gdet g) = m := hg
  have hu : valuation k ((gdet g / ϖ ^ m : kˣ) : k) = 1 := by
    refine ord_eq_zero_iff.1 ?_
    have h := ord_mul k (gdet g / ϖ ^ m) (ϖ ^ m)
    rw [div_mul_cancel, ord_zpow_eq, ord_eq_one hϖ, hm] at h
    omega
  have hϖd : apow ϖ ((d : ℂ) / 2) = (resCard k : ℂ) ^ (-(d : ℂ) / 2) := by
    rw [apow, GlobalTheory.GLDoubling.nabs_unif hϖ, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), ← Complex.cpow_neg, neg_div]
  let w : kˣ →* ℂ :=
    { toFun := fun x => (ν x : ℂ) * apow x ((d : ℂ) / 2)
      map_one' := by simp
      map_mul' := fun x y => by rw [map_mul, apow_mul, Units.val_mul]; ring }
  have h1 : w (gdet g / ϖ ^ m) = 1 := by
    show (ν _ : ℂ) * apow _ _ = 1
    rw [hν _ hu, apow_of_valuation_eq_one hu]; simp
  have h2 : w ϖ = cst d ϖ ν := by
    show (ν _ : ℂ) * apow _ _ = _
    rw [hϖd, cst]
  show w (gdet g) = _
  rw [← div_mul_cancel (gdet g) (ϖ ^ m), map_mul, h1, one_mul, map_zpow, h2]

theorem integrableOn_dShell {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) (m : ℤ) :
    IntegrableOn (fun g : GL (Fin n) k => φ g.val) (dShell n m) (haarVol (KO k (Fin n))) := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  obtain ⟨N, M, hN, -⟩ := GlobalTheory.SBUniform.exists_bound_period k (Fin n) φ hφ
  have hc : Continuous fun g : GL (Fin n) k => φ g.val := hφ.1.continuous.comp Units.continuous_val
  have hK := (finite_exponents n (-(N : ℤ)) m).isCompact_biUnion fun e _ => isCompact_shellSet ϖ e
  refine (hc.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero (measurableSet_dShell n m) ?_
  rintro g ⟨hg, hg'⟩
  by_contra h
  rw [dShell_eq_iUnion hϖ] at hg
  obtain ⟨e, he⟩ := Set.mem_iUnion.1 hg
  exact hg' (Set.mem_biUnion (x := e.1) ⟨e.2.2, le_of_mem_shellSet hϖ he (hN _ h)⟩ he)

theorem zCoeff_eq {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (d : ℕ) {n : ℕ}
    {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) (m : ℤ) :
    zCoeff n d ϖ ν φ m = cst d ϖ ν ^ m * Jm n φ m := by
  obtain ⟨N, M, hN, -⟩ := GlobalTheory.SBUniform.exists_bound_period k (Fin n) φ hφ
  have hsh : ∀ e : {e : Fin n → ℤ // Antitone e ∧ ∑ i, e i = m},
      shell (haarVol (KO k (Fin n))) ϖ ν ((d : ℂ) / 2) φ e.1 =
        cst d ϖ ν ^ m * ∫ g in shellSet ϖ e.1, φ g.val ∂haarVol (KO k (Fin n)) := fun e => by
    rw [shell, ← integral_const_mul]
    refine setIntegral_congr_fun (isOpen_shellSet ϖ e.1).measurableSet fun g hg => ?_
    have h := wt_of_mem hϖ hν d (g := g) (m := m) ((ord_of_mem_shellSet hϖ hg).trans e.2.2)
    show _ = cst d ϖ ν ^ m * φ g.val
    rw [← h, wt]; ring
  have hdis : Pairwise (Function.onFun Disjoint
      fun e : {e : Fin n → ℤ // Antitone e ∧ ∑ i, e i = m} => shellSet ϖ e.1) := fun a b hab => by
    have h := GlobalTheory.GLDoubling.pairwise_disjoint_cell (N := n) hϖ (i := ⟨a.1, a.2.1⟩) (j := ⟨b.1, b.2.1⟩)
      fun h => hab (Subtype.ext (Subtype.mk.inj h))
    simpa only [Function.onFun, shellSet_eq_cell] using h
  have hint := integrableOn_dShell hφ m
  rw [dShell_eq_iUnion hϖ] at hint
  have hsum := hasSum_integral_iUnion
    (s := fun e : {e : Fin n → ℤ // Antitone e ∧ ∑ i, e i = m} => shellSet ϖ e.1)
    (fun e => (isOpen_shellSet ϖ e.1).measurableSet) hdis hint
  rw [← dShell_eq_iUnion hϖ] at hsum
  have hfin : {e : {e : Fin n → ℤ // Antitone e ∧ ∑ i, e i = m} | ∀ i, -(N : ℤ) ≤ e.1 i}.Finite :=
    ((finite_exponents n (-(N : ℤ)) m).preimage Subtype.val_injective.injOn).subset fun e he => ⟨e.2.2, he⟩
  rw [zCoeff, finsum_congr hsh]
  refine finsum_eq_of_hasSum (hsum.mul_left (cst d ϖ ν ^ m)) hfin fun e he => ?_
  rw [setIntegral_eq_zero_of_forall_eq_zero, mul_zero]
  intro g hg
  by_contra h
  exact he (le_of_mem_shellSet hϖ hg (hN _ h))

theorem Jm_mul_left {n : ℕ} (φ : Matrix (Fin n) (Fin n) k → ℂ) (g₁ : GL (Fin n) k) (m : ℤ) :
    Jm n (fun x => φ (g₁.val * x)) m = Jm n φ (m + ord k (gdet g₁)) := by
  rw [Jm, Jm, ← integral_indicator (measurableSet_dShell _ _), ← integral_indicator (measurableSet_dShell _ _),
    ← integral_mul_left_eq_self ((dShell n (m + ord k (gdet g₁))).indicator fun g => φ g.val) g₁]
  congr 1
  funext g
  have h : g₁ * g ∈ dShell n (m + ord k (gdet g₁)) ↔ g ∈ dShell n m := by
    show ord k (gdet (g₁ * g)) = _ ↔ ord k (gdet g) = m
    rw [gdet_mul, ord_mul]; omega
  by_cases hg : g ∈ dShell n m
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (h.2 hg), Units.val_mul]
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt h.1 hg)]

theorem Jm_mul_right {n : ℕ} (φ : Matrix (Fin n) (Fin n) k → ℂ) (g₁ : GL (Fin n) k) (m : ℤ) :
    Jm n (fun x => φ (x * g₁.val)) m = Jm n φ (m + ord k (gdet g₁)) := by
  rw [Jm, Jm, ← integral_indicator (measurableSet_dShell _ _), ← integral_indicator (measurableSet_dShell _ _),
    ← integral_mul_right_eq_self ((dShell n (m + ord k (gdet g₁))).indicator fun g => φ g.val) g₁]
  congr 1
  funext g
  have h : g * g₁ ∈ dShell n (m + ord k (gdet g₁)) ↔ g ∈ dShell n m := by
    show ord k (gdet (g * g₁)) = _ ↔ ord k (gdet g) = m
    rw [gdet_mul, ord_mul]; omega
  by_cases hg : g ∈ dShell n m
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (h.2 hg), Units.val_mul]
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt h.1 hg)]

theorem exists_normal {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) :
    ∃ N M : ℕ, (∀ x, φ ((scal n (ϖ ^ N)⁻¹).val * x) ≠ 0 → ∀ i j, x i j ∈ 𝒪[k]) ∧
      ∀ x y : Matrix (Fin n) (Fin n) k, (∀ i j, valuation k (y i j) ≤ valuation k (ϖ : k) ^ M) →
        φ ((scal n (ϖ ^ N)⁻¹).val * (x + y)) = φ ((scal n (ϖ ^ N)⁻¹).val * x) := by
  obtain ⟨N, M, hN, hM⟩ := GlobalTheory.SBUniform.exists_bound_period k (Fin n) φ hφ
  have hval : ∀ (x : Matrix (Fin n) (Fin n) k) i j,
      valuation k (((scal n (ϖ ^ N)⁻¹).val * x) i j) = uniformizer k ^ (-(N : ℤ)) * valuation k (x i j) := by
    intro x i j
    rw [scal, diagGL_val, diagonal_mul, map_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow,
      hϖ, _root_.zpow_neg, zpow_natCast]
  have hpos : 0 < uniformizer k := GlobalTheory.IwahoriInj.unif_pos
  refine ⟨N, M + N, fun x hx i j => ?_, fun x y hy => ?_⟩
  · have h : valuation k _ ≤ _ := hN _ hx i j
    rw [hval] at h
    exact (mul_le_iff_le_one_right (zpow_pos hpos _)).1 h
  · rw [Matrix.mul_add]
    refine hM _ _ fun i j => ?_
    show valuation k _ ≤ _
    rw [hval]
    refine (mul_le_mul_right (hy i j) _).trans_eq ?_
    rw [hϖ, ← zpow_natCast, ← zpow_add₀ hpos.ne']
    congr 1
    push_cast
    ring

section Hermite
open GlobalTheory.SatakeBound

theorem sum_comp_surj {G H : Type*} [AddGroup G] [AddGroup H] [Fintype G] [Fintype H] (π : G →+ H)
    (hπ : Function.Surjective π) {r : ℕ} (hr : Nat.card G = r * Nat.card H) (F : H → ℂ) :
    ∑ c, F (π c) = r * ∑ d, F d := by
  classical
  have h1 : ∀ d, (Finset.univ.filter fun c => π c = d).card = (Finset.univ.filter fun c => π c = 0).card := fun d =>
    AddMonoidHom.card_fiber_eq_of_mem_range π (hπ d) (hπ 0)
  have h2 := Finset.card_eq_sum_card_fiberwise (f := π) (s := Finset.univ) (t := Finset.univ)
    fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)
  simp only [h1, Finset.sum_const, smul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
  have h3 : (Finset.univ.filter fun c => π c = 0).card = r :=
    Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := H)) (by rw [← h2, hr, mul_comm])
  rw [← Finset.sum_fiberwise' Finset.univ π F, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_const, h1, h3, nsmul_eq_mul]

theorem span_pow_le_min {R : Type} [CommRing R] (p : R) (m M : ℕ) :
    Ideal.span {p ^ m} ≤ Ideal.span {p ^ min m M} :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow p (min_le_left m M))

def hermRed {R : Type} [CommRing R] {n : ℕ} (p : R) (a : Fin n → ℕ) (M : ℕ) :
    HermIdx p a →+ HermIdx p fun i => min (a i) M where
  toFun c i j := Ideal.Quotient.factor (span_pow_le_min p (a i) M) (c i j)
  map_zero' := by funext i j; simp
  map_add' c c' := by funext i j; simp

theorem hermRed_surjective {R : Type} [CommRing R] {n : ℕ} (p : R) (a : Fin n → ℕ) (M : ℕ) :
    Function.Surjective (hermRed p a M) := fun d => by
  choose c hc using fun i j => Ideal.Quotient.factor_surjective (span_pow_le_min p (a i) M) (d i j)
  exact ⟨c, funext fun i => funext fun j => hc i j⟩

theorem dvd_out_sub_out {R : Type} [CommRing R] (p : R) (m M : ℕ) (x : R ⧸ Ideal.span {p ^ m}) :
    p ^ M ∣ x.out - (Ideal.Quotient.factor (span_pow_le_min p m M) x).out := by
  rcases le_total m M with h | h
  · have key : ∀ m' (_ : m = m') (H : Ideal.span {p ^ m} ≤ Ideal.span {p ^ m'}),
        (Ideal.Quotient.factor H x).out = x.out := fun m' e H => by
      subst e
      rw [Ideal.Quotient.factor_eq]; rfl
    rw [key _ (min_eq_left h).symm, sub_self]
    exact dvd_zero _
  · have h1 : p ^ min m M ∣ x.out - (Ideal.Quotient.factor (span_pow_le_min p m M) x).out := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, Ideal.Quotient.mk_out,
        ← Ideal.Quotient.factor_mk (span_pow_le_min p m M), Ideal.Quotient.mk_out]
    exact (pow_dvd_pow p (le_min h le_rfl)).trans h1

theorem dvd_hermMat_sub {R : Type} [CommRing R] {n : ℕ} (p : R) (a : Fin n → ℕ) (M : ℕ) (c : HermIdx p a)
    (i j : Fin n) : p ^ M ∣ hermMat p a c i j - hermMat p _ (hermRed p a M c) i j := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [hermMat_lt _ h, hermMat_lt _ h]
    exact dvd_out_sub_out p (a i) M _
  · rw [hermMat_diag, hermMat_diag]
    rcases le_total (a i) M with h | h
    · rw [min_eq_left h, sub_self]; exact dvd_zero _
    · rw [min_eq_right h]; exact dvd_sub (pow_dvd_pow p h) dvd_rfl
  · rw [hermMat_gt _ h, hermMat_gt _ h, sub_self]; exact dvd_zero _

omit [MeasurableSpace k] [BorelSpace k] in

theorem finite_hermIdx {p : 𝒪[k]} (hp : Irreducible p) {n : ℕ} (a : Fin n → ℕ) : Finite (HermIdx p a) := by
  have hq := GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k
  exact Nat.finite_of_card_ne_zero (by rw [card_hermIdx hp]; positivity)

omit [MeasurableSpace k] [BorelSpace k] in

theorem exists_hermGL {p : 𝒪[k]} (hp : Irreducible p) {n : ℕ} {g : GL (Fin n) k} (hg : ∀ i j, g.val i j ∈ 𝒪[k]) :
    ∃ (a : Fin n → ℕ) (c : HermIdx p a), (hermGL hp a c)⁻¹ * g ∈ KO k (Fin n) := by
  obtain ⟨b, hb, w, hw, e⟩ := iwasawa_blockTriangular k (Fin n) Fin.val g
  have hb' : ∀ i j, b.val i j ∈ 𝒪[k] := fun i j => by
    rw [eq_mul_inv_of_mul_eq e.symm, Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => mul_mem (hg _ _) (((mem_KO_iff _).1 hw).2 _ _)
  let B : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨b.val i j, hb' i j⟩
  have hB : b.val = (algebraMap 𝒪[k] k).mapMatrix B := rfl
  have h1 : ∀ i j, j < i → B i j = 0 := fun i j h => Subtype.ext (hb h)
  have hd : B.det ≠ 0 := fun h => b.det_ne_zero (by rw [hB, ← RingHom.map_det, h, map_zero])
  rw [Matrix.det_of_isUpperTriangular (M := B) fun _ _ h => h1 _ _ h, Finset.prod_ne_zero_iff] at hd
  obtain ⟨a, c, U, hU⟩ := exists_hermMat hp B h1 fun i => hd i (Finset.mem_univ i)
  have : hermGL hp a c = b * Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) U := by
    apply Units.ext
    rw [val_hermGL, hU, map_mul, ← hB]
    rfl
  refine ⟨a, c, ?_⟩
  rw [this, e, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  exact mul_mem (inv_mem (MonoidHom.mem_range.2 ⟨U, rfl⟩)) hw

omit [MeasurableSpace k] [BorelSpace k] in

theorem ord_gdet_of_mem_coset {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {a : Fin n → ℕ} {c : HermIdx _ a} {g : GL (Fin n) k}
    (hg : (hermGL hϖ.irreducible a c)⁻¹ * g ∈ KO k (Fin n)) : ord k (gdet g) = (∑ i, a i : ℕ) := by
  have h1 : ∀ m : ℕ, ord k (ϖ ^ m) = m := fun m => by
    induction m with
    | zero => exact ord_eq_zero (by simp)
    | succ m ih => rw [pow_succ, ord_mul, ih, ord_eq_one hϖ]; simp
  have h2 : gdet (hermGL hϖ.irreducible a c) = ϖ ^ ∑ i, a i := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, val_hermGL, ← RingHom.map_det, det_hermMat, map_pow,
      Units.val_pow_eq_pow_val]
    rfl
  rw [← mul_inv_cancel_left (hermGL hϖ.irreducible a c) g, gdet_mul, ord_mul, h2, h1,
    ord_eq_zero (valuation_gdet_of_mem_KO hg), add_zero]

omit [MeasurableSpace k] [BorelSpace k] in

theorem int_of_mem_coset {p : 𝒪[k]} (hp : Irreducible p) {n : ℕ} {a : Fin n → ℕ} {c : HermIdx p a} {g : GL (Fin n) k}
    (hg : (hermGL hp a c)⁻¹ * g ∈ KO k (Fin n)) (i j : Fin n) : g.val i j ∈ 𝒪[k] := by
  rw [← mul_inv_cancel_left (hermGL hp a c) g, Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => mul_mem (hermMat p a c i l).2 (((mem_KO_iff _).1 hg).1 _ _)

theorem Jm_eq_inter {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hs : ∀ x, φ x ≠ 0 → ∀ i j, x i j ∈ 𝒪[k]) (m : ℤ) :
    Jm n φ m = ∫ g in dShell n m ∩ {g | ∀ i j, g.val i j ∈ 𝒪[k]}, φ g.val ∂haarVol (KO k (Fin n)) := by
  have ho : IsOpen {g : GL (Fin n) k | ∀ i j, g.val i j ∈ 𝒪[k]} :=
    (isOpen_intMatrix (k := k) (m := Fin n) (n := Fin n)).preimage (Units.continuous_val (M := Matrix (Fin n) (Fin n) k))
  rw [← setIntegral_indicator ho.measurableSet, Jm]
  congr 1
  exact (Set.indicator_eq_self.2 fun g hg => hs _ hg).symm

def cosetInt {n : ℕ} (φ : Matrix (Fin n) (Fin n) k → ℂ) (x : Matrix (Fin n) (Fin n) k) : ℂ :=
  ∫ w in (KO k (Fin n) : Set (GL (Fin n) k)), φ (x * w.val) ∂haarVol (KO k (Fin n))

theorem setIntegral_coset {n : ℕ} (φ : Matrix (Fin n) (Fin n) k → ℂ) (h : GL (Fin n) k) :
    ∫ g in {g | h⁻¹ * g ∈ KO k (Fin n)}, φ g.val ∂haarVol (KO k (Fin n)) = cosetInt φ h.val := by
  have ho : IsOpen {g | h⁻¹ * g ∈ KO k (Fin n)} := isOpen_KO.preimage (continuous_const_mul h⁻¹)
  rw [cosetInt, ← integral_indicator ho.measurableSet, ← integral_indicator isOpen_KO.measurableSet,
    ← integral_mul_left_eq_self _ h]
  congr 1
  funext g
  by_cases hg : g ∈ KO k (Fin n)
  · rw [Set.indicator_of_mem (by simpa using hg), Set.indicator_of_mem hg, Units.val_mul]
  · rw [Set.indicator_of_notMem (by simpa using hg), Set.indicator_of_notMem hg]

theorem Jm_eq_sum {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : Continuous φ)
    (hs : ∀ x, φ x ≠ 0 → ∀ i j, x i j ∈ 𝒪[k]) [∀ a : Fin n → ℕ, Fintype (HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) a)] (t : ℕ) :
    Jm n φ t = ∑ a ∈ Finset.piAntidiag Finset.univ t, ∑ c, cosetInt φ (hermGL hϖ.irreducible a c).val := by
  classical
  have hU : dShell n t ∩ {g : GL (Fin n) k | ∀ i j, g.val i j ∈ 𝒪[k]} =
      ⋃ x ∈ (Finset.piAntidiag Finset.univ t).sigma fun a => (Finset.univ : Finset (HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) a)),
        {g | (hermGL hϖ.irreducible x.1 x.2)⁻¹ * g ∈ KO k (Fin n)} := by
    ext g
    simp only [Set.mem_iUnion, Finset.mem_sigma, Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true,
      Set.mem_ofPred_eq, Set.mem_inter_iff, dShell, exists_prop]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨a, c, h⟩ := exists_hermGL hϖ.irreducible h2
      exact ⟨⟨a, c⟩, by exact_mod_cast (ord_gdet_of_mem_coset hϖ h).symm.trans h1, h⟩
    · rintro ⟨⟨a, c⟩, h1, h⟩
      exact ⟨(ord_gdet_of_mem_coset hϖ h).trans (congrArg Nat.cast h1), int_of_mem_coset _ h⟩
  rw [Jm_eq_inter hs, hU, integral_biUnion_finset, Finset.sum_sigma]
  · simp only [setIntegral_coset]
  · exact fun x _ => (isOpen_KO.preimage (continuous_const_mul _)).measurableSet
  · intro x _ y _ hxy
    refine Set.disjoint_left.2 fun g h1 h2 => hxy (hermGL_injective hϖ.irreducible ?_)
    exact (QuotientGroup.eq.2 h1).trans (QuotientGroup.eq.2 h2).symm
  · intro x _
    have hc : IsCompact {g | (hermGL hϖ.irreducible x.1 x.2)⁻¹ * g ∈ KO k (Fin n)} :=
      (Homeomorph.mulLeft (hermGL hϖ.irreducible x.1 x.2)⁻¹).isCompact_preimage.2 isCompact_KO
    exact (hφ.comp Units.continuous_val).continuousOn.integrableOn_compact hc

theorem cosetInt_congr {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} {M : ℕ}
    (hp : ∀ x y : Matrix (Fin n) (Fin n) k, (∀ i j, valuation k (y i j) ≤ valuation k (ϖ : k) ^ M) → φ (x + y) = φ x)
    {B B' : Matrix (Fin n) (Fin n) 𝒪[k]} (h : ∀ i j, (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) ^ M ∣ B i j - B' i j) :
    cosetInt φ ((algebraMap 𝒪[k] k).mapMatrix B) = cosetInt φ ((algebraMap 𝒪[k] k).mapMatrix B') := by
  refine setIntegral_congr_fun isOpen_KO.measurableSet fun w hw => ?_
  have e : (algebraMap 𝒪[k] k).mapMatrix B * w.val =
      (algebraMap 𝒪[k] k).mapMatrix B' * w.val + (algebraMap 𝒪[k] k).mapMatrix (B - B') * w.val := by
    rw [map_sub, sub_mul, add_sub_cancel]
  show φ _ = φ _
  rw [e]
  refine hp _ _ fun i j => ?_
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  have h1 := (Valuation.integer.integers (valuation k)).le_of_dvd (h i l)
  rw [map_pow, map_pow] at h1
  rw [map_mul]
  exact (mul_le_of_le_one_right' (((mem_KO_iff _).1 hw).1 l j)).trans h1

end Hermite

theorem Jm_hnf {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _)
    (hs : ∀ x, φ x ≠ 0 → ∀ i j, x i j ∈ 𝒪[k]) (M : ℕ)
    (hp : ∀ x y : Matrix (Fin n) (Fin n) k, (∀ i j, valuation k (y i j) ≤ valuation k (ϖ : k) ^ M) → φ (x + y) = φ x) :
    ∃ T : (Fin n → ℕ) → ℂ,
      (∀ a, T a = (∏ i : Fin n, ((resCard k : ℂ) ^ (n - 1 - (i : ℕ))) ^ (a i - M)) * T (fun i => min (a i) M)) ∧
      (∀ m : ℤ, m < 0 → Jm n φ m = 0) ∧ ∀ t : ℕ, Jm n φ t = ∑ a ∈ Finset.piAntidiag Finset.univ t, T a := by
  classical
  have hfin : ∀ a : Fin n → ℕ, Finite (GlobalTheory.SatakeBound.HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) a) :=
    finite_hermIdx hϖ.irreducible
  let _ : ∀ a : Fin n → ℕ, Fintype (GlobalTheory.SatakeBound.HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) a) := fun a => Fintype.ofFinite _
  refine ⟨fun a => ∑ c, cosetInt φ (GlobalTheory.SatakeBound.hermGL hϖ.irreducible a c).val, fun a => ?_, fun m hm => ?_,
    Jm_eq_sum hϖ hφ.1.continuous hs⟩
  · have hr : Nat.card (GlobalTheory.SatakeBound.HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) a) =
        (∏ i : Fin n, (resCard k ^ (n - 1 - (i : ℕ))) ^ (a i - M)) *
          Nat.card (GlobalTheory.SatakeBound.HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) fun i => min (a i) M) := by
      rw [GlobalTheory.SatakeBound.card_hermIdx hϖ.irreducible, GlobalTheory.SatakeBound.card_hermIdx hϖ.irreducible,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add]
      congr 1
      omega
    have key := sum_comp_surj _ (hermRed_surjective _ a M) hr
      fun d => cosetInt φ (GlobalTheory.SatakeBound.hermGL hϖ.irreducible _ d).val
    push_cast at key
    refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) key
    exact cosetInt_congr hϖ hp (dvd_hermMat_sub _ a M c)
  · rw [Jm_eq_inter hs, show dShell n m ∩ {g : GL (Fin n) k | ∀ i j, g.val i j ∈ 𝒪[k]} = ∅ from ?_,
      setIntegral_empty]
    refine Set.eq_empty_of_forall_notMem fun g hg => ?_
    obtain ⟨a, c, h⟩ := exists_hermGL hϖ.irreducible hg.2
    have h1 := (ord_gdet_of_mem_coset hϖ h).symm.trans hg.1
    omega

theorem Jm_indicator (n : ℕ) (t : ℕ) :
    Jm n (Set.indicator {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} 1) t =
      ∑ a ∈ Finset.piAntidiag Finset.univ t, ∏ i : Fin n, ((resCard k : ℂ) ^ (n - 1 - (i : ℕ))) ^ a i := by
  classical
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hfin : ∀ a : Fin n → ℕ, Finite (GlobalTheory.SatakeBound.HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) a) :=
    finite_hermIdx hϖ.irreducible
  let _ : ∀ a : Fin n → ℕ, Fintype (GlobalTheory.SatakeBound.HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) a) := fun a => Fintype.ofFinite _
  have hC : IsClopen {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} :=
    ⟨isCompact_intMatrix.isClosed, isOpen_intMatrix⟩
  have hc : Continuous (Set.indicator {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix (Fin n) (Fin n) k → ℂ)) :=
    (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hC).isLocallyConstant.continuous
  rw [Jm_eq_sum hϖ hc fun x hx => Set.mem_of_indicator_ne_zero hx]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 : ∀ c, cosetInt (Set.indicator {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} 1)
      (GlobalTheory.SatakeBound.hermGL hϖ.irreducible a c).val = 1 := fun c => by
    rw [cosetInt, setIntegral_congr_fun isOpen_KO.measurableSet (g := fun _ => (1 : ℂ))]
    · simp [Measure.real, haarVol_self isOpen_KO le_rfl]
    · intro w hw
      have h2 : (GlobalTheory.SatakeBound.hermGL hϖ.irreducible a c).val * w.val ∈
          {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} :=
        int_of_mem_coset hϖ.irreducible (c := c) (g := GlobalTheory.SatakeBound.hermGL hϖ.irreducible a c * w)
          (by simpa using hw)
      exact Set.indicator_of_mem h2 _
  simp only [h1, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one,
    GlobalTheory.SatakeBound.card_hermIdx hϖ.irreducible]
  push_cast
  rfl

end ZetaNonvanishing₂

section Cont
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem conv_shift (P : Polynomial ℂ) (n : ℕ) (f : ℤ → ℂ) (a : ℂ) (o m : ℤ) :
    conv P n (fun m => a * f (m + o)) m = a * conv P n f (m + o) := by
  simp only [conv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show m - (j : ℤ) + o = m + o - j by ring]
  ring

theorem conv_add (P : Polynomial ℂ) (n : ℕ) (f g : ℤ → ℂ) (c : ℂ) (m : ℤ) :
    conv P n (fun m => f m + c * g m) m = conv P n f m + c * conv P n g m := by
  simp only [conv, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem finsum_conv_shift (P : Polynomial ℂ) (n : ℕ) (f : ℤ → ℂ) (a : ℂ) (o : ℤ) :
    ∑ᶠ m, conv P n (fun m => a * f (m + o)) m = a * ∑ᶠ m, conv P n f m := by
  simp only [conv_shift]
  rw [← finsum_comp_equiv (Equiv.addRight o) (f := conv P n f), ← smul_eq_mul a, smul_finsum]
  rfl

theorem conv_finite_of_polys {P : Polynomial ℂ} {n : ℕ} (hP : P.natDegree ≤ n) {f : ℤ → ℂ} (hf : ∀ m < 0, f m = 0)
    (h : (P : PowerSeries ℂ) * PowerSeries.mk (fun s : ℕ => f s) ∈ polys) : (Function.support (conv P n f)).Finite := by
  obtain ⟨Q, hQ⟩ := h
  refine (Set.finite_Icc (0 : ℤ) Q.natDegree).subset fun m hm => ?_
  by_contra hc
  apply hm
  rcases lt_or_ge m 0 with h0 | h0
  · exact conv_neg hf h0
  · obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [conv_natCast hP hf, ← hQ, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe]
    refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
    by_contra hl
    exact hc ⟨h0, by exact_mod_cast not_lt.1 hl⟩

omit [MeasurableSpace k] [BorelSpace k] in

theorem resCard_cast_ne_zero : (resCard k : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[k])).ne'

omit [MeasurableSpace k] [BorelSpace k] in

theorem cst_ne_zero (d : ℕ) (ϖ : kˣ) (ν : kˣ →* ℂˣ) : cst d ϖ ν ≠ 0 := by
  refine mul_ne_zero (ν ϖ).ne_zero fun h => ?_
  exact resCard_cast_ne_zero (k := k) ((Complex.cpow_eq_zero_iff _ _).1 h).1

omit [MeasurableSpace k] [BorelSpace k] in

theorem invL_eq_prod (n d : ℕ) (ϖ : kˣ) (ν : kˣ →* ℂˣ) :
    invL n d ϖ ν = ∏ i : Fin n,
      (1 - Polynomial.C (cst d ϖ ν * (resCard k : ℂ) ^ (n - 1 - (i : ℕ))) * Polynomial.X) := by
  rw [Fin.prod_univ_eq_prod_range
    (fun i => (1 - Polynomial.C (cst d ϖ ν * (resCard k : ℂ) ^ (n - 1 - i)) * Polynomial.X)) n,
    Finset.prod_range_reflect (fun i => (1 - Polynomial.C (cst d ϖ ν * (resCard k : ℂ) ^ i) * Polynomial.X)) n, invL]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sub_eq_add_neg (i : ℂ), Complex.cpow_add _ _ resCard_cast_ne_zero, Complex.cpow_natCast, cst, neg_div]
  congr 3
  ring

omit [MeasurableSpace k] [BorelSpace k] in

theorem natDegree_invL_le (n d : ℕ) (ϖ : kˣ) (ν : kˣ →* ℂˣ) : (invL n d ϖ ν).natDegree ≤ n := by
  rw [invL]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 fun i _ => ?_).trans (by simp)
  compute_degree

omit [MeasurableSpace k] [BorelSpace k] in

theorem coe_invL (n d : ℕ) (ϖ : kˣ) (ν : kˣ →* ℂˣ) :
    (invL n d ϖ ν : PowerSeries ℂ) = ∏ i : Fin n,
      (1 - PowerSeries.C (cst d ϖ ν * (resCard k : ℂ) ^ (n - 1 - (i : ℕ))) * PowerSeries.X) := by
  rw [invL_eq_prod, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_sub, map_one, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_X]

omit [MeasurableSpace k] [BorelSpace k] in

theorem sb_mul_left {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) (g : GL (Fin n) k) :
    (fun x => φ (g.val * x)) ∈ SB (Matrix (Fin n) (Fin n) k) := by
  simpa using comp_mul_mem_SB g 1 hφ

omit [MeasurableSpace k] [BorelSpace k] in

theorem sb_mul_right {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) (g : GL (Fin n) k) :
    (fun x => φ (x * g.val)) ∈ SB (Matrix (Fin n) (Fin n) k) := by
  simpa using comp_mul_mem_SB 1 g hφ

omit [MeasurableSpace k] [BorelSpace k] in

theorem sb_indicator_sq (n : ℕ) :
    Set.indicator {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix (Fin n) (Fin n) k → ℂ) ∈ SB _ := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have he : {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} =
      Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => (𝒪[k] : Set k) := by
    ext X
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  have hc : IsCompact {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} := by
    rw [he]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => Model.isCompact_int
  have ho : IsOpen {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} := by
    rw [he]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => Model.isOpen_int
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) ⟨hc.isClosed, ho⟩).isLocallyConstant

theorem zCoeff_of_shift {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (d : ℕ) {n : ℕ}
    {φ ψ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) (hψ : ψ ∈ SB _) {o : ℤ}
    (h : ∀ m, Jm n ψ m = Jm n φ (m + o)) :
    zCoeff n d ϖ ν ψ = fun m => (cst d ϖ ν ^ o)⁻¹ * zCoeff n d ϖ ν φ (m + o) := by
  funext m
  have hc := cst_ne_zero d ϖ ν
  have hco := zpow_ne_zero o hc
  rw [zCoeff_eq hϖ hν d hψ, zCoeff_eq hϖ hν d hφ, h, zpow_add₀ hc]
  field_simp

theorem conv_finite_normal {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (n d : ℕ)
    {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) (hs : ∀ x, φ x ≠ 0 → ∀ i j, x i j ∈ 𝒪[k]) (M : ℕ)
    (hp : ∀ x y : Matrix (Fin n) (Fin n) k, (∀ i j, valuation k (y i j) ≤ valuation k (ϖ : k) ^ M) → φ (x + y) = φ x) :
    (Function.support (conv (invL n d ϖ ν) n (zCoeff n d ϖ ν φ))).Finite := by
  obtain ⟨T, hT, h0, hJ⟩ := Jm_hnf hϖ hφ hs M hp
  refine conv_finite_of_polys (natDegree_invL_le n d ϖ ν)
    (fun m hm => by rw [zCoeff_eq hϖ hν d hφ, h0 m hm, mul_zero]) ?_
  have key := gen_mem_polys (fun i : Fin n => cst d ϖ ν * (resCard k : ℂ) ^ (n - 1 - (i : ℕ))) M
    (fun a => cst d ϖ ν ^ (∑ i, a i) * T a) (fun a => by
      have e : ∑ i, a i = ∑ i, (a i - M) + ∑ i, min (a i) M := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by omega
      rw [hT a, e, pow_add]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring)
  rw [coe_invL]
  convert key using 3
  funext t
  rw [zCoeff_eq hϖ hν d hφ, hJ, zpow_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_piAntidiag.1 ha).1]

theorem conv_finite {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (n d : ℕ)
    {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) :
    (Function.support (conv (invL n d ϖ ν) n (zCoeff n d ϖ ν φ))).Finite := by
  obtain ⟨N, M, hs, hp⟩ := exists_normal hϖ hφ
  have h₀ := sb_mul_left hφ (scal n (ϖ ^ N)⁻¹)
  have hf := conv_finite_normal hϖ hν n d h₀ hs M hp
  rw [zCoeff_of_shift hϖ hν d hφ h₀ (Jm_mul_left φ _)] at hf
  refine (hf.image (· + ord k (gdet (scal n (ϖ ^ N)⁻¹)))).subset fun m hm => ?_
  refine ⟨m - ord k (gdet (scal n (ϖ ^ N)⁻¹)), ?_, sub_add_cancel _ _⟩
  rw [Function.mem_support, conv_shift, sub_add_cancel]
  exact mul_ne_zero (inv_ne_zero (zpow_ne_zero _ (cst_ne_zero d ϖ ν))) hm

theorem zetaUnr_eq_conv (n d : ℕ) (ϖ : kˣ) (ν : kˣ →* ℂˣ) (φ : Matrix (Fin n) (Fin n) k → ℂ) :
    zetaUnr n d ϖ ν φ = ∑ᶠ m, conv (invL n d ϖ ν) n (zCoeff n d ϖ ν φ) m := rfl

theorem zetaUnr_add {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (n d : ℕ)
    {φ ψ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) (hψ : ψ ∈ SB _) (c : ℂ) :
    zetaUnr n d ϖ ν (fun x => φ x + c * ψ x) = zetaUnr n d ϖ ν φ + c * zetaUnr n d ϖ ν ψ := by
  have hs : (fun x => φ x + c * ψ x) ∈ SB (Matrix (Fin n) (Fin n) k) :=
    (SB _).add_mem hφ ((SB _).smul_mem c hψ)
  have hz : zCoeff n d ϖ ν (fun x => φ x + c * ψ x) =
      fun m => zCoeff n d ϖ ν φ m + c * zCoeff n d ϖ ν ψ m := by
    funext m
    rw [zCoeff_eq hϖ hν d hs, zCoeff_eq hϖ hν d hφ, zCoeff_eq hϖ hν d hψ]
    unfold Jm
    rw [integral_add (integrableOn_dShell hφ m) ((integrableOn_dShell hψ m).const_mul c), integral_const_mul]
    ring
  rw [zetaUnr_eq_conv, zetaUnr_eq_conv, zetaUnr_eq_conv, hz]
  simp only [conv_add]
  rw [finsum_add_distrib (conv_finite hϖ hν n d hφ)
    ((conv_finite hϖ hν n d hψ).subset fun m hm => right_ne_zero_of_mul hm), ← smul_eq_mul c, smul_finsum]
  rfl

theorem zetaUnr_const_mul (n d : ℕ) (ϖ : kˣ) (ν : kˣ →* ℂˣ) (φ : Matrix (Fin n) (Fin n) k → ℂ) (c : ℂ) :
    zetaUnr n d ϖ ν (fun x => c * φ x) = c * zetaUnr n d ϖ ν φ := by
  have hz : zCoeff n d ϖ ν (fun x => c * φ x) = fun m => c * zCoeff n d ϖ ν φ (m + 0) := by
    funext m
    rw [add_zero, zCoeff, zCoeff, ← smul_eq_mul c, smul_finsum]
    refine finsum_congr fun a => ?_
    simp only [shell, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _
  rw [zetaUnr_eq_conv, zetaUnr_eq_conv, hz, finsum_conv_shift]

theorem zetaUnr_mul_left {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (n d : ℕ)
    {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) (g₁ : GL (Fin n) k) :
    zetaUnr n d ϖ ν (fun x => φ (g₁.val * x)) = (wt d ν g₁)⁻¹ * zetaUnr n d ϖ ν φ := by
  rw [zetaUnr_eq_conv, zetaUnr_eq_conv, zCoeff_of_shift hϖ hν d hφ (sb_mul_left hφ g₁) (Jm_mul_left φ g₁),
    finsum_conv_shift, wt_of_mem hϖ hν d (m := ord k (gdet g₁)) rfl]

theorem zetaUnr_mul_right {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (n d : ℕ)
    {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) (g₁ : GL (Fin n) k) :
    zetaUnr n d ϖ ν (fun x => φ (x * g₁.val)) = (wt d ν g₁)⁻¹ * zetaUnr n d ϖ ν φ := by
  rw [zetaUnr_eq_conv, zetaUnr_eq_conv, zCoeff_of_shift hϖ hν d hφ (sb_mul_right hφ g₁) (Jm_mul_right φ g₁),
    finsum_conv_shift, wt_of_mem hϖ hν d (m := ord k (gdet g₁)) rfl]

theorem zetaUnr_indicator {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (n d : ℕ) :
    zetaUnr n d ϖ ν (Set.indicator {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} 1) = 1 := by
  have hφ := sb_indicator_sq (k := k) n
  obtain ⟨_, -, h0, -⟩ := Jm_hnf hϖ hφ (fun x hx => by
      by_contra hc
      exact hx (Set.indicator_of_notMem (s := {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]}) hc _)) 0
    (fun x y hy => by
      have hy' : ∀ i j, y i j ∈ 𝒪[k] := fun i j => by simpa [Valuation.mem_integer_iff] using hy i j
      by_cases hx : x ∈ {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]}
      · have hxy : x + y ∈ {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} :=
          fun i j => add_mem (hx i j) (hy' i j)
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxy]
        rfl
      · have hxy : x + y ∉ {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} := fun h =>
          hx fun i j => by simpa using sub_mem (h i j) (hy' i j)
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxy])
  have hf : ∀ m < 0, zCoeff n d ϖ ν (Set.indicator {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} 1) m = 0 :=
    fun m hm => by rw [zCoeff_eq hϖ hν d hφ, h0 m hm, mul_zero]
  have key : (invL n d ϖ ν : PowerSeries ℂ) * PowerSeries.mk (fun s : ℕ =>
      zCoeff n d ϖ ν (Set.indicator {X : Matrix (Fin n) (Fin n) k | ∀ i j, X i j ∈ 𝒪[k]} 1) s) = 1 := by
    rw [coe_invL]
    convert gen_geom (fun i : Fin n => cst d ϖ ν * (resCard k : ℂ) ^ (n - 1 - (i : ℕ))) using 3
    funext t
    rw [zCoeff_eq hϖ hν d hφ, Jm_indicator, zpow_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [(Finset.mem_piAntidiag.1 ha).1]
  rw [zetaUnr_eq_conv, finsum_eq_single _ ((0 : ℕ) : ℤ), conv_natCast (natDegree_invL_le n d ϖ ν) hf, key]
  · simp
  · intro m hm
    rcases lt_or_ge m 0 with h | h
    · exact conv_neg hf h
    · obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le h
      rw [conv_natCast (natDegree_invL_le n d ϖ ν) hf, key, PowerSeries.coeff_one, if_neg]
      exact fun ht => hm (by rw [ht])

theorem summable_antidiag_of_growth {n : ℕ} (Q : Fin n → ℝ) (hQ : ∀ i, 1 ≤ Q i) {r : ℝ} (hr : 0 ≤ r)
    (hrQ : ∀ i, r * Q i < 1) (M : ℕ) (T : (Fin n → ℕ) → ℂ)
    (hT : ∀ a, T a = (∏ i, (Q i : ℂ) ^ (a i - M)) * T (fun i => min (a i) M)) :
    Summable fun t : ℕ => r ^ t * ‖∑ a ∈ Finset.piAntidiag Finset.univ t, T a‖ := by
  classical
  set B : ℝ := ∑ b ∈ Fintype.piFinset (fun _ : Fin n => Finset.range (M + 1)), ‖T b‖ with hB
  have hQ0 : ∀ i, 0 ≤ Q i := fun i => zero_le_one.trans (hQ i)
  have hBle : ∀ a : Fin n → ℕ, ‖T (fun i => min (a i) M)‖ ≤ B := fun a =>
    Finset.single_le_sum (f := fun b => ‖T b‖) (fun _ _ => norm_nonneg _)
      (Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (Nat.lt_succ_of_le (min_le_right _ _)))
  have hTle : ∀ a : Fin n → ℕ, ‖T a‖ ≤ (∏ i, Q i ^ a i) * B := fun a => by
    rw [hT a, norm_mul, norm_prod]
    refine mul_le_mul ?_ (hBle a) (norm_nonneg _) (Finset.prod_nonneg fun i _ => pow_nonneg (hQ0 i) _)
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (hQ0 i)]
    exact pow_le_pow_right₀ (hQ i) (Nat.sub_le _ _)
  have hs := (summable_geom_coeff (fun i => ((r * Q i : ℝ) : ℂ)) fun i => by
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hr (hQ0 i))]; exact hrQ i).mul_right B
  refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hr _) (norm_nonneg _)) (fun t => ?_) hs
  have h1 : (∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) t, ∏ i, ((r * Q i : ℝ) : ℂ) ^ a i) =
      ((∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) t, ∏ i, (r * Q i) ^ a i : ℝ) : ℂ) := by
    push_cast; rfl
  rw [h1, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun a _ =>
    Finset.prod_nonneg fun i _ => pow_nonneg (mul_nonneg hr (hQ0 i)) _), Finset.sum_mul]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hr _)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  have ht : ∑ i, a i = t := (Finset.mem_piAntidiag.1 ha).1
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ht, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hTle a) (pow_nonneg hr _)

theorem summable_Jm {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) {r : ℝ}
    (hr : 0 < r) (hrq : ∀ i : Fin n, r * (resCard k : ℝ) ^ (n - 1 - (i : ℕ)) < 1) :
    Summable fun m : ℤ => r ^ m * ‖Jm n φ m‖ := by
  obtain ⟨N, M, hs, hp⟩ := exists_normal hϖ hφ
  set g₁ : GL (Fin n) k := scal n (ϖ ^ N)⁻¹ with hg₁
  have h0 : (fun x => φ (g₁.val * x)) ∈ SB _ := by
    simpa using comp_mul_mem_SB g₁ 1 hφ
  obtain ⟨T, hT, hneg, hnat⟩ := Jm_hnf hϖ h0 hs M hp
  have hq : (1 : ℝ) ≤ resCard k := by
    have : 1 < resCard k := Finite.one_lt_card
    exact_mod_cast this.le
  have h1 := summable_antidiag_of_growth (fun i : Fin n => (resCard k : ℝ) ^ (n - 1 - (i : ℕ)))
    (fun i => one_le_pow₀ hq) hr.le hrq M T (fun a => by rw [hT a]; push_cast; rfl)
  have h2 : Summable fun m : ℤ => r ^ m * ‖Jm n (fun x => φ (g₁.val * x)) m‖ := by
    refine Summable.of_nat_of_neg_add_one ?_ ?_
    · refine h1.congr fun t => ?_
      rw [hnat t, zpow_natCast]
    · refine summable_zero.congr fun t => ?_
      rw [hneg _ (by omega), norm_zero, mul_zero]
  set e : ℤ := ord k (gdet g₁)
  rw [← (Equiv.addRight e).summable_iff]
  refine (h2.mul_left (r ^ e)).congr fun m => ?_
  simp only [Function.comp_apply, Equiv.coe_addRight]
  rw [Jm_mul_left, zpow_add₀ hr.ne']
  ring

theorem zetaUnr_eq_integral {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (hu : ‖(ν ϖ : ℂ)‖ = 1)
    {n d : ℕ} (hn : 2 * n < d + 2) {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) :
    Integrable (fun g : GL (Fin n) k => φ g.val * wt d ν g) (haarVol (KO k (Fin n))) ∧
      (invL n d ϖ ν).eval 1 * ∫ g, φ g.val * wt d ν g ∂haarVol (KO k (Fin n)) = zetaUnr n d ϖ ν φ := by
  set μ : Measure (GL (Fin n) k) := haarVol (KO k (Fin n)) with hμ
  set c := cst d ϖ ν with hc
  have hq : (1 : ℝ) < resCard k := by
    have : 1 < resCard k := Finite.one_lt_card
    exact_mod_cast this
  have hq0 : (0 : ℝ) < resCard k := zero_lt_one.trans hq
  have hcn : ‖c‖ = (resCard k : ℝ) ^ (-(d : ℝ) / 2) := by
    have h : (resCard k : ℂ) ^ (-(d : ℂ) / 2) = (((resCard k : ℝ) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hq0.le]; push_cast; rfl
    rw [hc, cst, norm_mul, hu, one_mul, h, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq0.le _)]
  have hc0 : 0 < ‖c‖ := hcn ▸ Real.rpow_pos_of_pos hq0 _
  have hrq : ∀ i : Fin n, ‖c‖ * (resCard k : ℝ) ^ (n - 1 - (i : ℕ)) < 1 := fun i => by
    rw [hcn, ← Real.rpow_natCast, ← Real.rpow_add hq0]
    refine Real.rpow_lt_one_of_one_lt_of_neg hq ?_
    have hi := i.2
    have : 2 * (n - 1 - (i : ℕ)) < d := by omega
    have : (2 : ℝ) * ((n - 1 - (i : ℕ) : ℕ) : ℝ) < d := by exact_mod_cast this
    linarith
  have hψ : (fun x => ((‖φ x‖ : ℝ) : ℂ)) ∈ SB _ :=
    ⟨hφ.1.comp (fun z : ℂ => ((‖z‖ : ℝ) : ℂ)), hφ.2.comp_left (g := fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) (by simp)⟩
  have hsum := summable_Jm hϖ hψ hc0 hrq
  have hmeas := measurableSet_dShell (k := k) n
  have heq : ∀ m : ℤ, Set.EqOn (fun g : GL (Fin n) k => φ g.val * wt d ν g) (fun g => c ^ m * φ g.val) (dShell n m) :=
    fun m g hg => by
      simp only [wt_of_mem hϖ hν d hg, hc, mul_comm]
  have hint : ∀ m : ℤ, IntegrableOn (fun g : GL (Fin n) k => φ g.val * wt d ν g) (dShell n m) μ := fun m =>
    IntegrableOn.congr_fun ((integrableOn_dShell hφ m).const_mul (c ^ m)) (heq m).symm (hmeas m)
  have hnorm : ∀ m : ℤ, ∫ g in dShell n m, ‖φ g.val * wt d ν g‖ ∂μ =
      ‖c‖ ^ m * ‖Jm n (fun x => ((‖φ x‖ : ℝ) : ℂ)) m‖ := fun m => by
    rw [setIntegral_congr_fun (g := fun g : GL (Fin n) k => ‖c‖ ^ m * ‖φ g.val‖) (hmeas m) (fun g hg => by
      have := heq m hg
      simp only at this ⊢
      rw [this, norm_mul, norm_zpow]), integral_const_mul, Jm, integral_complex_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  have hU : (⋃ m : ℤ, dShell (k := k) n m) = Set.univ :=
    Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨ord k (gdet g), rfl⟩
  have hI : IntegrableOn (fun g : GL (Fin n) k => φ g.val * wt d ν g) (⋃ m : ℤ, dShell n m) μ :=
    integrableOn_iUnion_of_summable_integral_norm hint (hsum.congr fun m => (hnorm m).symm)
  have hdisj : Pairwise (Function.onFun Disjoint (dShell (k := k) n)) := fun a b hab =>
    Set.disjoint_left.2 fun g ha hb => hab (Eq.trans (Eq.symm ha) hb)
  have hS := hasSum_integral_iUnion hmeas hdisj hI
  rw [hU] at hI hS
  rw [Measure.restrict_univ] at hS
  refine ⟨integrableOn_univ.1 hI, ?_⟩
  have hz : (fun m : ℤ => ∫ g in dShell n m, φ g.val * wt d ν g ∂μ) = zCoeff n d ϖ ν φ := by
    funext m
    rw [zCoeff_eq hϖ hν d hφ, setIntegral_congr_fun (hmeas m) (heq m), integral_const_mul, Jm]
  rw [hz] at hS
  rw [zetaUnr_eq_conv]
  exact (hasSum_conv (natDegree_invL_le n d ϖ ν) hS).tsum_eq.symm.trans (tsum_eq_finsum (conv_finite hϖ hν n d hφ))

end Cont

section SBfun
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sb_comp_right {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] {X : Matrix A D k}
    {R : Matrix D A k} (hXR : X * R = 1) {Φ : Matrix A D k → ℂ} (hΦ : Φ ∈ SB _) :
    (fun g : Matrix A A k => Φ (g * X)) ∈ SB _ := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨hl, hc⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  have h1 : Continuous fun g : Matrix A A k => g * X := continuous_id.matrix_mul continuous_const
  have h2 : Continuous fun Y : Matrix A D k => Y * R := continuous_id.matrix_mul continuous_const
  have hli : Function.LeftInverse (fun Y : Matrix A D k => Y * R) (fun g : Matrix A A k => g * X) := fun g => by
    simp only [Matrix.mul_assoc, hXR, Matrix.mul_one]
  exact ⟨hl.comp_continuous h1, hc.comp_isClosedEmbedding (hli.isClosedEmbedding h2 h1)⟩

theorem exists_stab {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] {Φ : Matrix A D k → ℂ}
    (hΦ : Φ ∈ SB _) : ∃ U : Subgroup (GL D k), IsOpen (U : Set (GL D k)) ∧ ∀ u ∈ U, ∀ X, Φ (X * u.val) = Φ X := by
  obtain ⟨hl, hc⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  have hK : IsCompact (tsupport Φ) := hc
  let U : Subgroup (GL D k) :=
    { carrier := {u | ∀ X, Φ (X * u.val) = Φ X}
      one_mem' := fun X => by rw [Units.val_one, Matrix.mul_one]
      mul_mem' := fun {u v} hu hv X => by rw [Units.val_mul, ← Matrix.mul_assoc, hv, hu]
      inv_mem' := fun {u} hu X => by
        rw [← hu (X * (u⁻¹).val), Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] }
  have hev : ∀ᶠ u in nhds (1 : GL D k), ∀ X ∈ tsupport Φ, Φ (X * u.val) = Φ X := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have h1 : IsLocallyConstant fun z : GL D k × Matrix A D k => Φ (z.2 * z.1.val) :=
      hl.comp_continuous (continuous_snd.matrix_mul (Units.continuous_val.comp continuous_fst))
    have h2 : IsLocallyConstant fun z : GL D k × Matrix A D k => Φ z.2 :=
      hl.comp_continuous continuous_snd
    filter_upwards [h1.eventually_eq (1, x), h2.eventually_eq (1, x)] with z e1 e2
    rw [e1, e2, Units.val_one, Matrix.mul_one]
  have hinv : Filter.Tendsto (fun u : GL D k => u⁻¹) (nhds 1) (nhds 1) := by
    have := (continuous_inv (G := GL D k)).tendsto 1
    rwa [inv_one] at this
  have hU : (U : Set (GL D k)) ∈ nhds (1 : GL D k) := by
    filter_upwards [hev, hinv.eventually hev] with u hu hu' X
    by_cases hx : X ∈ tsupport Φ
    · exact hu X hx
    by_cases hxu : X * u.val ∈ tsupport Φ
    · have := hu' _ hxu
      rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxu]
  exact ⟨U, U.isOpen_of_mem_nhds hU, fun u hu => hu⟩

theorem continuous_invT {D : Type} [Fintype D] [DecidableEq D] : Continuous (invT : GL D k → GL D k) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem indicator_int_mem_SB {A D : Type} [Fintype A] [Fintype D] :
    Set.indicator {X : Matrix A D k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix A D k → ℂ) ∈ SB _ := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  classical
  have hK := isCompact_intMatrix (k := k) (m := A) (n := D)
  have hcl : IsClopen {X : Matrix A D k | ∀ i j, X i j ∈ 𝒪[k]} := ⟨hK.isClosed, isOpen_intMatrix⟩
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.indicator (LocallyConstant.const (Matrix A D k) (1 : ℂ)) hcl).isLocallyConstant

end SBfun

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem int_mul {A B C : Type} [Fintype B] {M : Matrix A B k} {R : Matrix B C k} (hM : ∀ i j, M i j ∈ 𝒪[k])
    (hR : ∀ i j, R i j ∈ 𝒪[k]) : ∀ i j, (M * R) i j ∈ 𝒪[k] := fun i j =>
  Subring.sum_mem _ fun l _ => mul_mem (hM i l) (hR l j)

theorem indicator_int_mul {A B C : Type} [Fintype B] [Fintype C] [DecidableEq B] {M : Matrix B C k} {R : Matrix C B k}
    (hM : ∀ i j, M i j ∈ 𝒪[k]) (hR : ∀ i j, R i j ∈ 𝒪[k]) (hMR : M * R = 1) (g : Matrix A B k) :
    Set.indicator {X : Matrix A C k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix A C k → ℂ) (g * M) =
      Set.indicator {X : Matrix A B k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix A B k → ℂ) g := by
  have key : (∀ i j, (g * M) i j ∈ 𝒪[k]) ↔ ∀ i j, g i j ∈ 𝒪[k] := by
    refine ⟨fun h => ?_, fun h => int_mul h hM⟩
    have := int_mul h hR
    rwa [Matrix.mul_assoc, hMR, Matrix.mul_one] at this
  by_cases hg : ∀ i j, g i j ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (show g * M ∈ {X : Matrix A C k | ∀ i j, X i j ∈ 𝒪[k]} from key.2 hg),
      Set.indicator_of_mem (show g ∈ {X : Matrix A B k | ∀ i j, X i j ∈ 𝒪[k]} from hg)]
    rfl
  · rw [Set.indicator_of_notMem (show g * M ∉ {X : Matrix A C k | ∀ i j, X i j ∈ 𝒪[k]} from fun h => hg (key.1 h)),
      Set.indicator_of_notMem (show g ∉ {X : Matrix A B k | ∀ i j, X i j ∈ 𝒪[k]} from hg)]

section Frames
variable {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem upperProjection_mul_transpose (σ : A ⊕ A' ≃ D) : X0 k σ * (X0 k σ)ᵀ = 1 := by
  ext i j
  simp [X0, Matrix.mul_apply, Matrix.one_apply, σ.injective.eq_iff]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem Y0_mul_transpose (σ : A ⊕ A' ≃ D) : Y0 k σ * (Y0 k σ)ᵀ = 1 := by
  ext i j
  simp [Y0, Matrix.mul_apply, Matrix.one_apply, σ.injective.eq_iff]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem invT_mul_transpose (h : GL D k) : (invT h).val * h.valᵀ = 1 := by
  rw [invT_val, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem upperProjection_integral (σ : A ⊕ A' ≃ D) : ∀ i j, X0 k σ i j ∈ 𝒪[k] := fun i j => by
  simp only [X0, of_apply]; split_ifs <;> simp

theorem lowerProjection_integral (σ : A ⊕ A' ≃ D) : ∀ i j, Y0 k σ i j ∈ 𝒪[k] := fun i j => by
  simp only [Y0, of_apply]; split_ifs <;> simp

end Frames

variable [MeasurableSpace k] [BorelSpace k]

theorem pUnr_eq (a a' : ℕ) (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ)
    (h : GL (Fin (a + a')) k) : pUnr a a' ϖ ν β Φ h = (β (gdet h) : ℂ) * apow (gdet h) (-(a : ℂ) / 2) *
      zetaUnr a (a + a') ϖ ν (fun g => Φ (g * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val))) := by
  rw [← zetaUnr_const_mul]
  unfold pUnr
  congr 1
  funext g
  simp only [omA, map_one, inv_one, Units.val_one, apow_one, Matrix.one_mul, Fintype.card_fin, mul_one, one_mul]
  congr 2
  exact Matrix.mul_assoc _ _ _

end Main

section Main2
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem transpose_mul_invT {D : Type} [Fintype D] [DecidableEq D] (h : GL D k) : h.valᵀ * (invT h).val = 1 := by
  rw [invT_val, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

theorem norm_nu {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ} (hS : HidaSetting a a' ϖ α β ν) (x : kˣ) : ‖(ν x : ℂ)‖ = 1 := by
  rw [hS.quot, MonoidHom.div_apply, Units.val_div_eq_div_val, norm_div, hS.unitα, hS.unitβ, div_one]

theorem isUnram_nu {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ} (hS : HidaSetting a a' ϖ α β ν) (hα : IsUnram α)
    (hβ : IsUnram β) : IsUnram ν := fun x hx => by
  rw [hS.quot, MonoidHom.div_apply, hα x hx, hβ x hx, div_one]

def blkAGL {a a' : ℕ} (b : GL (Fin (a + a')) k) (dA : kˣ) (h : (dA : k) = (blkA b).det) : GL (Fin a) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (blkA b) (by rw [← h]; exact dA.ne_zero)

def blkDGL {a a' : ℕ} (b : GL (Fin (a + a')) k) (dD : kˣ) (h : (dD : k) = (blkD b).det) : GL (Fin a') k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (blkD b) (by rw [← h]; exact dD.ne_zero)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem gdet_blkAGL {a a' : ℕ} (b : GL (Fin (a + a')) k) (dA : kˣ) (h : (dA : k) = (blkA b).det) :
    gdet (blkAGL b dA h) = dA :=
  Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, h]; rfl)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem gdet_blkDGL {a a' : ℕ} (b : GL (Fin (a + a')) k) (dD : kˣ) (h : (dD : k) = (blkD b).det) :
    gdet (blkDGL b dD h) = dD :=
  Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, h]; rfl)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem gdet_of_isBlockUpper {a a' : ℕ} {b : GL (Fin (a + a')) k} (hb : IsBlockUpper b) {dA dD : kˣ}
    (h1 : (dA : k) = (blkA b).det) (h2 : (dD : k) = (blkD b).det) : gdet b = dA * dD := by
  refine Units.ext ?_
  rw [Units.val_mul, h1, h2, Matrix.GeneralLinearGroup.val_det_apply,
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  rw [show (b : Matrix (Fin (a + a')) (Fin (a + a')) k).submatrix finSumFinEquiv finSumFinEquiv =
    Matrix.fromBlocks (blkA b) (Matrix.of fun i j => (b : Matrix (Fin (a + a')) (Fin (a + a')) k)
      (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))) 0 (blkD b) from ?_,
    Matrix.det_fromBlocks_zero₂₁]
  ext (i | i) (j | j) <;> simp [blkA, blkD] <;> exact hb _ _

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem upperProjection_inverse_transpose_block {a a' : ℕ} {b : GL (Fin (a + a')) k} (hb : IsBlockUpper b) {dA : kˣ}
    (h1 : (dA : k) = (blkA b).det) :
    (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT b).val : Matrix (Fin a) (Fin (a + a')) k) =
      (invT (blkAGL b dA h1)).val * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) := by
  have key : ((blkAGL b dA h1).val)ᵀ * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) =
      X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * b.valᵀ := by
    ext i j
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
    · simp [X0, Matrix.mul_apply, blkAGL, blkA, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
    · simp [X0, Matrix.mul_apply, blkAGL, blkA, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
      exact (hb j i).symm
  calc (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT b).val : Matrix (Fin a) (Fin (a + a')) k)
      = (invT (blkAGL b dA h1)).val * (((blkAGL b dA h1).val)ᵀ * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))) * (invT b).val := by
        rw [← Matrix.mul_assoc (invT (blkAGL b dA h1)).val, invT_mul_transpose, Matrix.one_mul]
    _ = (invT (blkAGL b dA h1)).val * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) := by
        rw [key, Matrix.mul_assoc, Matrix.mul_assoc, transpose_mul_invT, Matrix.mul_one]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem lowerProjection_blockUpper {a a' : ℕ} {b : GL (Fin (a + a')) k} (hb : IsBlockUpper b) {dD : kˣ}
    (h2 : (dD : k) = (blkD b).det) :
    (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * b.val : Matrix (Fin a') (Fin (a + a')) k) =
      (blkDGL b dD h2).val * Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) := by
  ext i j
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
  · simp [Y0, Matrix.mul_apply, blkDGL, blkD, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
    exact hb i j
  · simp [Y0, Matrix.mul_apply, blkDGL, blkD, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem upperProjection_inverse_transpose_right_inverse {a a' : ℕ} (h : GL (Fin (a + a')) k) :
    (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val : Matrix (Fin a) (Fin (a + a')) k) *
      (h.valᵀ * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))ᵀ) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (invT h).val, invT_mul_transpose, Matrix.one_mul, upperProjection_mul_transpose]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem lowerProjection_mul_right_inverse {a a' : ℕ} (h : GL (Fin (a + a')) k) :
    (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val : Matrix (Fin a') (Fin (a + a')) k) *
      ((h⁻¹).val * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))ᵀ) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc h.val, Units.mul_inv, Matrix.one_mul, Y0_mul_transpose]

theorem wt_ne_zero {n : ℕ} (d : ℕ) (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) : wt d ν g ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)

theorem onto_of_irred (hI : IndIrred) {a a' : ℕ} {α β : kˣ →* ℂˣ} (hα : ∀ x, ‖(α x : ℂ)‖ = 1)
    (hβ : ∀ x, ‖(β x : ℂ)‖ = 1) {X : Type} [TopologicalSpace X] (p : (X → ℂ) → GL (Fin (a + a')) k → ℂ)
    (hlin : ∀ Φ ∈ SB X, ∀ Φ₁ ∈ SB X, ∀ c : ℂ, p (Φ + c • Φ₁) = p Φ + c • p Φ₁)
    (hin : ∀ Φ ∈ SB X, p Φ ∈ indSp a a' α β)
    (heq : ∀ Φ ∈ SB X, ∀ h₁, ∃ Φ' ∈ SB X, p Φ' = rtr h₁ (p Φ))
    (hne : ∃ Φ ∈ SB X, p Φ ≠ 0) : ∀ F ∈ indSp a a' α β, ∃ Φ ∈ SB X, p Φ = F := by
  have h0 : p 0 = 0 := by
    have := hlin 0 (SB X).zero_mem 0 (SB X).zero_mem 1
    simpa using this
  let N : Submodule ℂ (GL (Fin (a + a')) k → ℂ) :=
    { carrier := {F | ∃ Φ ∈ SB X, p Φ = F}
      add_mem' := by
        rintro _ _ ⟨Φ, hΦ, rfl⟩ ⟨Φ₁, hΦ₁, rfl⟩
        exact ⟨Φ + (1 : ℂ) • Φ₁, (SB X).add_mem hΦ ((SB X).smul_mem _ hΦ₁), by rw [hlin _ hΦ _ hΦ₁, one_smul]⟩
      zero_mem' := ⟨0, (SB X).zero_mem, h0⟩
      smul_mem' := by
        rintro c _ ⟨Φ, hΦ, rfl⟩
        exact ⟨0 + c • Φ, (SB X).add_mem (SB X).zero_mem ((SB X).smul_mem _ hΦ), by
          rw [hlin _ (SB X).zero_mem _ hΦ, h0, zero_add]⟩ }
  have hle : N ≤ indSp a a' α β := by
    rintro _ ⟨Φ, hΦ, rfl⟩
    exact hin Φ hΦ
  have hst : ∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N := by
    rintro h₁ _ ⟨Φ, hΦ, rfl⟩
    exact heq Φ hΦ h₁
  rcases hI k a a' α β hα hβ N hle hst with h | h
  · obtain ⟨Φ, hΦ, hne⟩ := hne
    have hm : p Φ ∈ N := ⟨Φ, hΦ, rfl⟩
    rw [h] at hm
    exact absurd ((Submodule.mem_bot ℂ).1 hm) hne
  · intro F hF
    rw [← h] at hF
    exact hF

variable [MeasurableSpace k] [BorelSpace k]
variable {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ}

theorem pUnr'_eq (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) {Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ}
    (hΨ : Ψ ∈ SB _) (h : GL (Fin (a + a')) k) : pUnr' a a' ϖ ν α Ψ h = (α (gdet h) : ℂ) * apow (gdet h) ((a' : ℂ) / 2) *
      zetaUnr a' (a + a') ϖ ν (fun g => Ψ (g * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val : Matrix (Fin a') (Fin (a + a')) k))) := by
  have hb := zetaUnr_eq_integral hS.unif hν (norm_nu hS ϖ) (n := a') (d := a + a') (by have := hS.lt; omega)
    (sb_comp_right (lowerProjection_mul_right_inverse h) hΨ)
  have e : smallF (haarVol (KO k (Fin a'))) ν Ψ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val) =
      ∫ g, Ψ (g.val * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val : Matrix (Fin a') (Fin (a + a')) k)) * wt (a + a') ν g
        ∂haarVol (KO k (Fin a')) := by
    unfold smallF
    congr 1
    funext g
    simp only [wt, Fintype.card_fin]
    ring
  show (invL a' (a + a') ϖ ν).eval 1 * smallP _ _ ν α Ψ h = _
  unfold smallP
  rw [e, ← hb.2, Fintype.card_fin]
  ring

end Main2

section Clauses
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ}

theorem p_lin (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) : ∀ Φ ∈ SB _, ∀ Φ₁ ∈ SB _, ∀ c : ℂ,
    pUnr a a' ϖ ν β (Φ + c • Φ₁) = pUnr a a' ϖ ν β Φ + c • pUnr a a' ϖ ν β Φ₁ := by
  intro Φ hΦ Φ₁ hΦ₁ c
  funext h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pUnr_eq]
  rw [mul_left_comm c, ← mul_add, ← zetaUnr_add hS.unif hν _ _ (sb_comp_right (upperProjection_inverse_transpose_right_inverse h) hΦ)
    (sb_comp_right (upperProjection_inverse_transpose_right_inverse h) hΦ₁)]

theorem p'_lin (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) : ∀ Ψ ∈ SB _, ∀ Ψ₁ ∈ SB _, ∀ c : ℂ,
    pUnr' a a' ϖ ν α (Ψ + c • Ψ₁) = pUnr' a a' ϖ ν α Ψ + c • pUnr' a a' ϖ ν α Ψ₁ := by
  intro Ψ hΨ Ψ₁ hΨ₁ c
  funext h
  have h2 : Ψ + c • Ψ₁ ∈ SB _ := (SB _).add_mem hΨ ((SB _).smul_mem c hΨ₁)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [pUnr'_eq hS hν h2, pUnr'_eq hS hν hΨ, pUnr'_eq hS hν hΨ₁, mul_left_comm c, ← mul_add,
    ← zetaUnr_add hS.unif hν _ _ (sb_comp_right (lowerProjection_mul_right_inverse h) hΨ) (sb_comp_right (lowerProjection_mul_right_inverse h) hΨ₁)]
  rfl

theorem p_mem (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) (hβ : IsUnram β) :
    ∀ Φ ∈ SB _, pUnr a a' ϖ ν β Φ ∈ indSp a a' α β := by
  intro Φ hΦ
  refine ⟨?_, fun b h hb dA dD h1 h2 => ?_⟩
  · obtain ⟨U, hUo, hU⟩ := exists_stab hΦ
    refine ⟨U.comap invT ⊓ KO k _, (hUo.preimage continuous_invT).inter isOpen_KO, fun u hu h => ?_⟩
    have hu1 : invT u ∈ U := Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hu).1
    have hu2 : u ∈ KO k _ := (Subgroup.mem_inf.1 hu).2
    have hv := valuation_gdet_of_mem_KO hu2
    have e : (fun g : Matrix (Fin a) (Fin a) k => Φ (g * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT (h * u)).val))) =
        fun g => Φ (g * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val)) := by
      funext g
      rw [map_mul, Units.val_mul, show g * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * ((invT h).val * (invT u).val)) =
        (g * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val)) * (invT u).val by simp only [Matrix.mul_assoc], hU _ hu1]
    rw [pUnr_eq, pUnr_eq, e, gdet_mul, map_mul, apow_mul, hβ _ hv, apow_of_valuation_eq_one hv]
    simp
  · have hdet := gdet_of_isBlockUpper hb h1 h2
    have e : (fun g : Matrix (Fin a) (Fin a) k => Φ (g * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT (b * h)).val))) =
        fun g => (fun y => Φ (y * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val))) (g * (invT (blkAGL b dA h1)).val) := by
      funext g
      simp only [map_mul, Units.val_mul]
      rw [← Matrix.mul_assoc (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))), upperProjection_inverse_transpose_block hb h1]
      simp only [Matrix.mul_assoc]
    rw [pUnr_eq, pUnr_eq, e, zetaUnr_mul_right hS.unif hν _ _ (sb_comp_right (upperProjection_inverse_transpose_right_inverse h) hΦ), gdet_mul, hdet]
    simp only [indFac, wt, gdet_invT, gdet_blkAGL, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      apow_mul, apow_inv, hS.quot, MonoidHom.div_apply, Units.val_div_eq_div_val]
    have hA : apow dA ((a' : ℂ) / 2) = apow dA (-(a : ℂ) / 2) * apow dA (((a + a' : ℕ) : ℂ) / 2) := by
      rw [← apow_add]; congr 1; push_cast; ring
    rw [hA, apow_neg]
    have h3 := apow_ne_zero dA (((a + a' : ℕ) : ℂ) / 2)
    have h4 : (β dA : ℂ) ≠ 0 := Units.ne_zero _
    have h5 : (α dA : ℂ) ≠ 0 := Units.ne_zero _
    field_simp

end Clauses

section Clauses2
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ}

theorem p'_mem (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) (hα : IsUnram α) :
    ∀ Ψ ∈ SB _, pUnr' a a' ϖ ν α Ψ ∈ indSp a a' α β := by
  intro Ψ hΨ
  refine ⟨?_, fun b h hb dA dD h1 h2 => ?_⟩
  · obtain ⟨U, hUo, hU⟩ := exists_stab hΨ
    refine ⟨U ⊓ KO k _, hUo.inter isOpen_KO, fun u hu h => ?_⟩
    have hu1 : u ∈ U := (Subgroup.mem_inf.1 hu).1
    have hv := valuation_gdet_of_mem_KO (Subgroup.mem_inf.1 hu).2
    have e : (fun g : Matrix (Fin a') (Fin a') k => Ψ (g * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (h * u).val))) =
        fun g => Ψ (g * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val)) := by
      funext g
      rw [Units.val_mul, show g * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (h.val * u.val)) = (g * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val)) * u.val by
        simp only [Matrix.mul_assoc], hU _ hu1]
    rw [pUnr'_eq hS hν hΨ, pUnr'_eq hS hν hΨ, e, gdet_mul, map_mul, apow_mul, hα _ hv, apow_of_valuation_eq_one hv]
    simp
  · have hdet := gdet_of_isBlockUpper hb h1 h2
    have e : (fun g : Matrix (Fin a') (Fin a') k => Ψ (g * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (b * h).val))) =
        fun g => (fun y => Ψ (y * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val))) (g * (blkDGL b dD h2).val) := by
      funext g
      simp only [Units.val_mul]
      rw [← Matrix.mul_assoc (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))), lowerProjection_blockUpper hb h2]
      simp only [Matrix.mul_assoc]
    rw [pUnr'_eq hS hν hΨ, pUnr'_eq hS hν hΨ, e,
      zetaUnr_mul_right hS.unif hν _ _ (sb_comp_right (lowerProjection_mul_right_inverse h) hΨ), gdet_mul, hdet]
    simp only [indFac, wt, gdet_blkDGL, map_mul, Units.val_mul, apow_mul, hS.quot, MonoidHom.div_apply,
      Units.val_div_eq_div_val]
    have hD : apow dD ((a' : ℂ) / 2) = apow dD (-(a : ℂ) / 2) * apow dD (((a + a' : ℕ) : ℂ) / 2) := by
      rw [← apow_add]; congr 1; push_cast; ring
    rw [hD]
    have h3 := apow_ne_zero dD (((a + a' : ℕ) : ℂ) / 2)
    have h4 : (β dD : ℂ) ≠ 0 := Units.ne_zero _
    have h5 : (α dD : ℂ) ≠ 0 := Units.ne_zero _
    field_simp

theorem p_inv (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) :
    ∀ Φ ∈ SB _, ∀ g, pUnr a a' ϖ ν β (omA ν β g 1 Φ) = pUnr a a' ϖ ν β Φ := by
  intro Φ hΦ g
  funext h
  have e1 : omA ν β 1 h (omA ν β g 1 Φ) = omA ν β g 1 (omA ν β 1 h Φ) := by
    rw [← omA_mul, ← omA_mul, one_mul, mul_one, mul_one, one_mul]
  have hΦ' := omA_mem_SB ν β 1 h hΦ
  have e2 : (fun x : Matrix (Fin a) (Fin a) k => omA ν β g 1 (omA ν β 1 h Φ) (x * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) =
      fun x => wt (a + a') ν g⁻¹ * (fun y => omA ν β 1 h Φ (y * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) ((g⁻¹).val * x) := by
    funext x
    simp only [omA, wt, map_one, map_inv, Units.val_inv_eq_inv_val, Units.val_one, apow_one, apow_inv, mul_one,
      Fintype.card_fin, Matrix.mul_one, Matrix.mul_assoc]
    congr 1
    rw [neg_div]
  unfold pUnr
  rw [e1]
  refine (congrArg (zetaUnr a (a + a') ϖ ν) e2).trans ?_
  rw [zetaUnr_const_mul, zetaUnr_mul_left hS.unif hν _ _ (sb_comp_right (upperProjection_mul_transpose _) hΦ') g⁻¹,
    ← mul_assoc, mul_inv_cancel₀ (wt_ne_zero _ _ _), one_mul]
  rfl

theorem p'_inv (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) :
    ∀ Ψ ∈ SB _, ∀ g, pUnr' a a' ϖ ν α (omB ν α g 1 Ψ) = pUnr' a a' ϖ ν α Ψ := by
  intro Ψ hΨ g
  funext h
  have hΨ' := omB_mem_SB ν α g 1 hΨ
  have hg : gdet (invT g)⁻¹ = gdet g := by
    rw [show gdet (invT g)⁻¹ = (gdet (invT g))⁻¹ from map_inv _ _, gdet_invT, inv_inv]
  have e2 : (fun x : Matrix (Fin a') (Fin a') k => omB ν α g 1 Ψ (x * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val))) =
      fun x => wt (a + a') ν (invT g)⁻¹ * (fun y => Ψ (y * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val))) (((invT g)⁻¹).val * x) := by
    funext x
    simp only [omB, wt, hg, invT_inv_val, map_one, Units.val_one, apow_one, mul_one, Fintype.card_fin,
      Matrix.mul_one, Matrix.mul_assoc]
  rw [pUnr'_eq hS hν hΨ', pUnr'_eq hS hν hΨ, e2, zetaUnr_const_mul,
    zetaUnr_mul_left hS.unif hν _ _ (sb_comp_right (lowerProjection_mul_right_inverse h) hΨ) (invT g)⁻¹,
    ← mul_assoc (wt _ _ _), mul_inv_cancel₀ (wt_ne_zero _ _ _), one_mul]

theorem p_equiv : ∀ Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ, ∀ h₁,
    pUnr a a' ϖ ν β (omA ν β 1 h₁ Φ) = rtr h₁ (pUnr a a' ϖ ν β Φ) := by
  intro Φ h₁
  funext h
  unfold pUnr rtr
  rw [← omA_mul, one_mul]

theorem p'_equiv : ∀ Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ, ∀ h₁,
    pUnr' a a' ϖ ν α (omB ν α 1 h₁ Ψ) = rtr h₁ (pUnr' a a' ϖ ν α Ψ) := by
  intro Ψ h₁
  funext h
  simp only [pUnr', rtr, Pi.smul_apply, smul_eq_mul]
  rw [smallP_eq, smallP_eq, ← omB_mul, one_mul]

theorem p_unit (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) (hβ : IsUnram β) :
    ∀ h ∈ KO k (Fin (a + a')), pUnr a a' ϖ ν β (Set.indicator {X : Matrix (Fin a) (Fin (a + a')) k | ∀ i j, X i j ∈ 𝒪[k]} 1) h = 1 := by
  intro h hh
  have hv := valuation_gdet_of_mem_KO hh
  have hK := (mem_KO_iff h).1 hh
  have hK' := (mem_KO_iff (invT h)).1 (invT_mem_KO hh)
  have e : (fun g : Matrix (Fin a) (Fin a) k =>
      Set.indicator {X : Matrix (Fin a) (Fin (a + a')) k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix (Fin a) (Fin (a + a')) k → ℂ) (g * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val))) =
      Set.indicator {X : Matrix (Fin a) (Fin a) k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix (Fin a) (Fin a) k → ℂ) := by
    funext g
    exact indicator_int_mul (int_mul (upperProjection_integral _) hK'.1) (int_mul (fun i j => hK.1 j i) (fun i j => upperProjection_integral _ j i))
      (upperProjection_inverse_transpose_right_inverse h) g
  rw [pUnr_eq, e, zetaUnr_indicator hS.unif hν, hβ _ hv, apow_of_valuation_eq_one hv]
  simp

theorem p'_unit (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) (hα : IsUnram α) :
    ∀ h ∈ KO k (Fin (a + a')), pUnr' a a' ϖ ν α (Set.indicator {Y : Matrix (Fin a') (Fin (a + a')) k | ∀ i j, Y i j ∈ 𝒪[k]} 1) h = 1 := by
  intro h hh
  have hv := valuation_gdet_of_mem_KO hh
  have hK := (mem_KO_iff h).1 hh
  have e : (fun g : Matrix (Fin a') (Fin a') k =>
      Set.indicator {X : Matrix (Fin a') (Fin (a + a')) k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix (Fin a') (Fin (a + a')) k → ℂ) (g * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val))) =
      Set.indicator {X : Matrix (Fin a') (Fin a') k | ∀ i j, X i j ∈ 𝒪[k]} (1 : Matrix (Fin a') (Fin a') k → ℂ) := by
    funext g
    exact indicator_int_mul (int_mul (lowerProjection_integral _) hK.1) (int_mul hK.2 (fun i j => lowerProjection_integral _ j i)) (lowerProjection_mul_right_inverse h) g
  rw [pUnr'_eq hS hν indicator_int_mem_SB, e, zetaUnr_indicator hS.unif hν, hα _ hv, apow_of_valuation_eq_one hv]
  simp

end Clauses2
end PositivityTheory.ThK.SplitLoc.Unr

namespace PositivityTheory.ThK.SplitLoc

open Unr GlobalTheory.SplitFlip GlobalTheory.SplitWeil

theorem unrMaps_of (hI : IndIrred) : UnrMaps := by
  intro k _ _ _ _ _ _ a a' ϖ α β ν hS hα hβ
  have hν := isUnram_nu hS hα hβ
  have hp1 := p_lin hS hν
  have hp2 := p'_lin hS hν
  have hp3 := p_mem hS hν hβ
  have hp4 := p'_mem hS hν hα
  have hu := p_unit hS hν hβ
  have hu' := p'_unit hS hν hα
  refine ⟨hp1, hp2, hp3, hp4, p_inv hS hν, p'_inv hS hν, fun Φ _ h₁ => p_equiv Φ h₁, fun Ψ _ h₁ => p'_equiv Ψ h₁,
    ?_, ?_, hu, hu'⟩
  · refine onto_of_irred hI hS.unitα hS.unitβ _ hp1 hp3 (fun Φ hΦ h₁ => ⟨_, omA_mem_SB ν β 1 h₁ hΦ, p_equiv Φ h₁⟩)
      ⟨_, indicator_int_mem_SB, fun h0 => ?_⟩
    simpa [hu 1 (one_mem _)] using congrFun h0 1
  · refine onto_of_irred hI hS.unitα hS.unitβ _ hp2 hp4 (fun Ψ hΨ h₁ => ⟨_, omB_mem_SB ν α 1 h₁ hΨ, p'_equiv Ψ h₁⟩)
      ⟨_, indicator_int_mem_SB, fun h0 => ?_⟩
    simpa [hu' 1 (one_mem _)] using congrFun h0 1

end PositivityTheory.ThK.SplitLoc
