import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IopIso
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DetIdealsKernelNormOne

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IL

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions MeasureTheory
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB
open scoped Pointwise ENNReal Function

variable {D : Car} {N N' : ℕ}

def unionFd (M La : AddSubgroup (VC D N N')) (s : Set (VC D N N')) : Set (VC D N N') :=
  ⋃ q : La ⧸ M.addSubgroupOf La, (Quotient.out q : La) +ᵥ s

theorem out_mem (M La : AddSubgroup (VC D N N')) (g : La) :
    (((g + Quotient.out (QuotientAddGroup.mk (-g) : La ⧸ M.addSubgroupOf La) : La)) : VC D N N') ∈ M := by
  have h : (QuotientAddGroup.mk (-g) : La ⧸ M.addSubgroupOf La) =
      QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk (-g) : La ⧸ M.addSubgroupOf La)) :=
    (Quotient.out_eq _).symm
  rw [QuotientAddGroup.eq, neg_neg] at h
  exact AddSubgroup.mem_addSubgroupOf.mp h

theorem out_inj (M La : AddSubgroup (VC D N N')) {q q' : La ⧸ M.addSubgroupOf La}
    (h : (Quotient.out q : La) = Quotient.out q') : q = q' := by
  exact Quotient.out_injective h

theorem mem_vadd_iff {La : AddSubgroup (VC D N N')} (g : La) (s : Set (VC D N N')) (x : VC D N N') :
    x ∈ g +ᵥ s ↔ x - (g : VC D N N') ∈ s := by
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add]
  rfl

theorem unionFd_fd {M La : AddSubgroup (VC D N N')} (hle : M ≤ La)
    [Finite (La ⧸ M.addSubgroupOf La)] {s : Set (VC D N N')}
    (hs : IsAddFundamentalDomain La s volume) :
    IsAddFundamentalDomain M (unionFd M La s) volume where
  nullMeasurableSet := NullMeasurableSet.iUnion fun q => hs.nullMeasurableSet_vadd _
  ae_covers := by
    filter_upwards [hs.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    refine ⟨⟨_, out_mem M La g⟩, Set.mem_iUnion.2 ⟨QuotientAddGroup.mk (-g), ?_⟩⟩
    rw [mem_vadd_iff]
    convert hg using 1
    simp only [AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_add]
    abel
  aedisjoint := by
    intro a b hab
    change volume ((a +ᵥ unionFd M La s) ∩ (b +ᵥ unionFd M La s)) = 0
    let a' : La := ⟨a, hle a.2⟩
    let b' : La := ⟨b, hle b.2⟩
    have hsub : (a +ᵥ unionFd M La s) ∩ (b +ᵥ unionFd M La s) ⊆
        ⋃ q : La ⧸ M.addSubgroupOf La, ⋃ q' : La ⧸ M.addSubgroupOf La,
          ((a' + Quotient.out q) +ᵥ s) ∩ ((b' + Quotient.out q') +ᵥ s) := by
      rintro x ⟨hxa, hxb⟩
      obtain ⟨u, hu, rfl⟩ := Set.mem_vadd_set.1 hxa
      obtain ⟨u', hu', hu'e⟩ := Set.mem_vadd_set.1 hxb
      obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hu
      obtain ⟨q', hq'⟩ := Set.mem_iUnion.1 hu'
      refine Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨q', ⟨?_, ?_⟩⟩⟩
      · rw [mem_vadd_iff] at hq ⊢
        convert hq using 1
        simp only [a', AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_add]
        abel
      · rw [mem_vadd_iff] at hq' ⊢
        convert hq' using 1
        rw [← hu'e]
        simp only [b', AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_add]
        abel
    refine measure_mono_null hsub (measure_iUnion_null fun q => measure_iUnion_null fun q' => ?_)
    by_cases he : a' + Quotient.out q = b' + Quotient.out q'
    · exfalso
      have h2 := congrArg (fun z : La => (z : VC D N N')) he
      simp only [a', b', AddSubgroup.coe_add] at h2
      have hqq : q = q' := by
        rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq,
          AddSubgroup.mem_addSubgroupOf]
        have : ((-Quotient.out q + Quotient.out q' : La) : VC D N N') = (a : VC D N N') - b := by
          simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
          rw [eq_sub_iff_add_eq]
          rw [← sub_eq_zero] at h2 ⊢
          rw [← neg_eq_zero, ← h2]
          abel
        rw [this]
        exact M.sub_mem a.2 b.2
      subst hqq
      apply hab
      simp only [add_left_inj] at h2
      exact Subtype.ext h2
    · exact hs.aedisjoint he

theorem pieces_disj {M La : AddSubgroup (VC D N N')} {s : Set (VC D N N')}
    (hs : IsAddFundamentalDomain La s volume) :
    Pairwise (AEDisjoint volume on fun q : La ⧸ M.addSubgroupOf La => (Quotient.out q : La) +ᵥ s) := by
  intro q q' hqq'
  exact hs.aedisjoint (fun h => hqq' (out_inj M La h))

theorem lint_unionFd {M La : AddSubgroup (VC D N N')} [Countable La]
    [Fintype (La ⧸ M.addSubgroupOf La)]
    {s : Set (VC D N N')} (hs : IsAddFundamentalDomain La s volume) (f : VC D N N' → ℝ≥0∞)
    (hf : ∀ g : La, ∀ x, f (g +ᵥ x) = f x) :
    ∫⁻ x in unionFd M La s, f x =
      (Fintype.card (La ⧸ M.addSubgroupOf La) : ℝ≥0∞) * ∫⁻ x in s, f x := by
  unfold unionFd
  rw [MeasureTheory.lintegral_iUnion₀ (fun q => hs.nullMeasurableSet.vadd _) (pieces_disj hs)]
  have h1 : ∀ q : La ⧸ M.addSubgroupOf La,
      ∫⁻ x in (Quotient.out q : La) +ᵥ s, f x = ∫⁻ x in s, f x :=
    fun q => (hs.vadd _).setLIntegral_eq hs f hf
  simp only [h1, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem vol_unionFd {M La : AddSubgroup (VC D N N')} [Countable La]
    [Fintype (La ⧸ M.addSubgroupOf La)]
    {s : Set (VC D N N')} (hs : IsAddFundamentalDomain La s volume) :
    volume (unionFd M La s) = (Fintype.card (La ⧸ M.addSubgroupOf La) : ℝ≥0∞) * volume s := by
  unfold unionFd
  rw [MeasureTheory.measure_iUnion₀ (pieces_disj hs) (fun q => hs.nullMeasurableSet.vadd _)]
  simp only [MeasureTheory.measure_vadd, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem avg_sub {M La : AddSubgroup (VC D N N')} [Countable La] [Countable M] (hle : M ≤ La)
    [Finite (La ⧸ M.addSubgroupOf La)] {s t : Set (VC D N N')}
    (hs : IsAddFundamentalDomain La s volume) (ht : IsAddFundamentalDomain M t volume)
    (f : VC D N N' → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfc : Continuous f)
    (hper : ∀ g ∈ La, ∀ x, f (x + g) = f x) :
    ⨍ x in t, f x = ⨍ x in s, f x := by
  haveI := Fintype.ofFinite (La ⧸ M.addSubgroupOf La)
  have hu := unionFd_fd hle hs
  have hperM : ∀ (g : M) (x : VC D N N'), f (g +ᵥ x) = f x := fun g x => by
    show f ((g : VC D N N') + x) = f x
    rw [add_comm]
    exact hper _ (hle g.2) x
  have hperL : ∀ (g : La) (x : VC D N N'), ENNReal.ofReal (f (g +ᵥ x)) = ENNReal.ofReal (f x) :=
    fun g x => by
      show ENNReal.ofReal (f ((g : VC D N N') + x)) = ENNReal.ofReal (f x)
      rw [add_comm, hper _ g.2 x]
  have hvol : volume t = volume (unionFd M La s) := ht.measure_eq hu
  have hint : ∫ x in t, f x = ∫ x in unionFd M La s, f x := ht.setIntegral_eq hu hperM
  have hlin : ∫⁻ x in unionFd M La s, ENNReal.ofReal (f x) =
      (Fintype.card (La ⧸ M.addSubgroupOf La) : ℝ≥0∞) * ∫⁻ x in s, ENNReal.ofReal (f x) :=
    lint_unionFd hs _ hperL
  have hI : ∀ u : Set (VC D N N'), ∫ x in u, f x = (∫⁻ x in u, ENNReal.ofReal (f x)).toReal :=
    fun u => MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
      hfc.aestronglyMeasurable
  have hn : (Fintype.card (La ⧸ M.addSubgroupOf La) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, MeasureTheory.measureReal_def,
    MeasureTheory.measureReal_def, hvol, vol_unionFd hs, hint, hI, hlin, hI,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, smul_eq_mul, smul_eq_mul, mul_inv,
    show ∀ a b c : ℝ, a⁻¹ * b * (a * c) = (a⁻¹ * a) * b * c from fun a b c => by ring,
    inv_mul_cancel₀ hn, one_mul]

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IL

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IL

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions MeasureTheory Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB
open scoped Pointwise ENNReal Function

variable {D : Car} {N N' : ℕ}

def crD (T : Tor D) (A B : VC D N N' → ℂ) (z : VC D N N') : ℂ :=
  A z * starRingEnd ℂ (B z) * (Real.exp (-Real.pi * (Hf D T z z).re) : ℂ)

private theorem Hf_swap_eq_conj (T : Tor D) (x y : VC D N N') :
    Hf D T y x = starRingEnd ℂ (Hf D T x y) := by
  unfold Formalism.L2.Ker.Cd.TaylorLogMetric.Hf
  rw [map_div₀, Complex.conj_ofReal]
  congr 1
  simp only [map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem re_Hf_add' (T : Tor D) (z x : VC D N N') :
    (Hf D T (z + x) (z + x)).re =
      (Hf D T z z).re + 2 * (Hf D T z x).re + (Hf D T x x).re := by
  have hadd : Hf D T (z + x) (z + x) = Hf D T z z + Hf D T z x + Hf D T x z + Hf D T x x := by
    unfold Formalism.L2.Ker.Cd.TaylorLogMetric.Hf
    simp only [Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  rw [hadd, Hf_swap_eq_conj T z x]
  simp only [Complex.add_re, Complex.conj_re]
  ring

theorem exp_mul_conj (w : ℂ) :
    Complex.exp w * starRingEnd ℂ (Complex.exp w) = ((Real.exp (2 * w.re) : ℝ) : ℂ) := by
  rw [← Complex.exp_conj, ← Complex.exp_add, Complex.add_conj, Complex.ofReal_exp]

theorem crD_U (T : Tor D) (A B : VC D N N' → ℂ) (y z : VC D N N') :
    crD T (U D T y A) (U D T y B) z = crD T A B (z + y) := by
  simp only [crD, Formalism.L2.Ker.Cd.TaylorLogMetric.U]
  rw [re_Hf_add' T z y]
  set e : ℂ := -(Real.pi : ℂ) * Hf D T z y - (Real.pi : ℂ) * Hf D T y y / 2 with he
  have h := exp_mul_conj e
  have hre : 2 * e.re = -Real.pi * (2 * (Hf D T z y).re + (Hf D T y y).re) := by
    rw [he]
    simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_re, Complex.neg_im]
    ring
  calc A (z + y) * Complex.exp e * starRingEnd ℂ (B (z + y) * Complex.exp e) *
        ((Real.exp (-Real.pi * (Hf D T z z).re) : ℝ) : ℂ)
      = A (z + y) * starRingEnd ℂ (B (z + y)) * (Complex.exp e * starRingEnd ℂ (Complex.exp e)) *
        ((Real.exp (-Real.pi * (Hf D T z z).re) : ℝ) : ℂ) := by rw [map_mul]; ring
    _ = _ := by
      rw [h, hre, mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 3
      ring

theorem crD_smul (T : Tor D) (c c' : ℂ) (A B : VC D N N' → ℂ) (z : VC D N N') :
    crD T (fun w => c * A w) (fun w => c' * B w) z = c * starRingEnd ℂ c' * crD T A B z := by
  unfold crD
  simp only [map_mul]
  ring

def ep (T : Tor D) (x y : VC D N N') : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ))

private theorem Hf_add_leftColumnData (T : Tor D) (z y x : VC D N N') :
    Hf D T (z + y) x = Hf D T z x + Hf D T y x := by
  unfold Formalism.L2.Ker.Cd.TaylorLogMetric.Hf
  rw [← add_div]
  congr 1
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem mul_exp_mul_exp_eq_of_add_eq (g a b c d e : ℂ) (h : a + b = c + (d + e)) :
    g * Complex.exp a * Complex.exp b = Complex.exp c * (g * Complex.exp d * Complex.exp e) := by
  rw [mul_assoc g, ← Complex.exp_add, h, Complex.exp_add, Complex.exp_add]
  ring

theorem aU_eig (T : Tor D) {La₁ : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La₁) {y : VC D N N'} (hy : y ∈ La₁) (x z : VC D N N') :
    al D T y * U D T y (U D T x G) z = ep T x y * U D T x G z := by
  have key : ∀ w, al D T y * U D T y G w = G w := fun w => hG.2 y hy w
  have hc : starRingEnd ℂ (Hf D T x y) = Hf D T x y - 2 * (((Hf D T x y).im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  have hcomm : U D T y (U D T x G) z = ep T x y * U D T x (U D T y G) z := by
    simp only [Formalism.L2.Ker.Cd.TaylorLogMetric.U, ep]
    rw [Hf_add_leftColumnData, Hf_add_leftColumnData, Hf_swap_eq_conj T x y, hc, show z + y + x = z + x + y by abel]
    apply mul_exp_mul_exp_eq_of_add_eq
    ring
  calc al D T y * U D T y (U D T x G) z
      = ep T x y * ((al D T y * U D T y G (z + x)) *
          Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2)) := by
        rw [hcomm]
        simp only [Formalism.L2.Ker.Cd.TaylorLogMetric.U]
        ring
    _ = ep T x y * U D T x G z := by rw [key]; rfl

def trm (T : Tor D) (G : VC D N N' → ℂ) (x : VC D N N') : VC D N N' → ℂ :=
  fun z => al D T x * U D T x G z

theorem al_mul_conj (T : Tor D) (y : VC D N N') : al D T y * starRingEnd ℂ (al D T y) = 1 := by
  unfold Formalism.L2.Ker.Cd.TaylorLogMetric.al
  rw [map_zpow₀, map_neg, map_one, ← mul_zpow]
  norm_num

theorem crD_shift (T : Tor D) {La₁ : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La₁) {y : VC D N N'} (hy : y ∈ La₁) (x x' z : VC D N N') :
    crD T (trm T G x) (trm T G x') (z + y) =
      ep T x y * starRingEnd ℂ (ep T x' y) * crD T (trm T G x) (trm T G x') z := by
  have hUt : ∀ x₀, U D T y (trm T G x₀) =
      fun w => (starRingEnd ℂ (al D T y) * ep T x₀ y) * trm T G x₀ w := by
    intro x₀
    funext w
    have h1 := aU_eig T hG hy x₀ w
    have h2 := al_mul_conj T y
    have hlin : U D T y (trm T G x₀) w = al D T x₀ * U D T y (U D T x₀ G) w := by
      simp only [Formalism.L2.Ker.Cd.TaylorLogMetric.U, trm]
      ring
    rw [hlin]
    simp only [trm]
    linear_combination (al D T x₀ * starRingEnd ℂ (al D T y)) * h1 -
      (al D T x₀ * U D T y (U D T x₀ G) w) * h2
  rw [← crD_U T (trm T G x) (trm T G x') y z, hUt x, hUt x',
    crD_smul T (starRingEnd ℂ (al D T y) * ep T x y) (starRingEnd ℂ (al D T y) * ep T x' y)
      (trm T G x) (trm T G x') z, map_mul, Complex.conj_conj]
  have h2 := al_mul_conj T y
  linear_combination (ep T x y * starRingEnd ℂ (ep T x' y) * crD T (trm T G x) (trm T G x') z) * h2

private theorem Hf_sub_left' (T : Tor D) (x x' y : VC D N N') :
    Hf D T (x - x') y = Hf D T x y - Hf D T x' y := by
  unfold Formalism.L2.Ker.Cd.TaylorLogMetric.Hf
  rw [← sub_div]
  congr 1
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem ep_mul_conj (T : Tor D) (x x' y : VC D N N') :
    ep T x y * starRingEnd ℂ (ep T x' y) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((Hf D T (x - x') y).im : ℂ)) := by
  unfold ep
  rw [← Complex.exp_conj, ← Complex.exp_add, Hf_sub_left' T x x' y, Complex.sub_im]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem ep_eq_one_iff (t : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = 1 ↔ ∃ n : ℤ, t = n := by
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h3 : (t : ℂ) = n := by
      apply mul_left_cancel₀ h2
      rw [hn]
      ring
    exact_mod_cast h3
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

theorem int_shift {M : AddSubgroup (VC D N N')} [Countable M] {t : Set (VC D N N')}
    (ht : IsAddFundamentalDomain M t volume) (f : VC D N N' → ℂ)
    (hper : ∀ m ∈ M, ∀ z, f (z + m) = f z) (x : VC D N N') :
    ∫ z in t, f (z + x) = ∫ z in t, f z := by
  have hmp := MeasureTheory.measurePreserving_add_right
    (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')) x
  have ht' : IsAddFundamentalDomain M ((fun z => z + x) ⁻¹' t) volume :=
    ht.preimage_of_equiv hmp.quasiMeasurePreserving Function.bijective_id
      (fun g z => add_assoc (g : VC D N N') z x)
  calc ∫ z in t, f (z + x) = ∫ z in (fun z => z + x) ⁻¹' t, f (z + x) := by
        refine ht.setIntegral_eq ht' (fun g z => ?_)
        show f ((g : VC D N N') + z + x) = f (z + x)
        rw [show (g : VC D N N') + z + x = z + x + g by abel, hper _ g.2]
    _ = ∫ z in t, f z := hmp.setIntegral_preimage_emb (measurableEmbedding_addRight x) f t

theorem int_zero_of_char {M : AddSubgroup (VC D N N')} [Countable M] {t : Set (VC D N N')}
    (ht : IsAddFundamentalDomain M t volume) (f : VC D N N' → ℂ)
    (hper : ∀ m ∈ M, ∀ z, f (z + m) = f z) (y : VC D N N') (lam : ℂ) (hlam : lam ≠ 1)
    (hy : ∀ z, f (z + y) = lam * f z) :
    ∫ z in t, f z = 0 := by
  have h := int_shift ht f hper y
  simp_rw [hy] at h
  rw [MeasureTheory.integral_const_mul] at h
  have h2 : (lam - 1) * ∫ z in t, f z = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hlam)

theorem intOn_of_full {M : AddSubgroup (VC D N N')} (hM : FullLat M) {t : Set (VC D N N')}
    (ht : IsAddFundamentalDomain M t volume) (f : VC D N N' → ℂ) (hf : Continuous f)
    (hper : ∀ m ∈ M, ∀ z, f (z + m) = f z) : IntegrableOn f t volume := by
  let L : Submodule ℤ (VC D N N') := M.toIntSubmodule
  haveI : DiscreteTopology L := hM.1
  haveI : IsZLattice ℝ L := ⟨by simpa [L] using hM.2⟩
  haveI : Countable M := by
    haveI := hM.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  have hb : Submodule.span ℤ (Set.range b) = L := Module.Basis.ofZLatticeBasis_span ℝ L _
  have hs0 : IsAddFundamentalDomain M (ZSpan.fundamentalDomain b) volume := by
    have h := ZSpan.isAddFundamentalDomain b (MeasureTheory.volume : MeasureTheory.Measure (VC D N N'))
    rw [hb] at h
    exact h
  have hcpt : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hf.continuousOn
  have hbd : ∀ z, ‖f z‖ ≤ C := by
    intro z
    obtain ⟨m, hm, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b z
    have hmM : (m : VC D N N') ∈ M := hb.le m.2
    have h3 := hC _ (subset_closure hm)
    rwa [show m +ᵥ z = z + (m : VC D N N') from add_comm _ _, hper _ hmM] at h3
  have hfin : volume t ≠ ⊤ := by
    rw [ht.measure_eq hs0]
    exact ((ZSpan.fundamentalDomain_isBounded b).measure_lt_top).ne
  exact MeasureTheory.Measure.integrableOn_of_bounded (M := C) hfin hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbd)

theorem countable_of_full {M : AddSubgroup (VC D N N')} (hM : FullLat M) : Countable M := by
  haveI := hM.1
  exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance

theorem fd_of_full {M : AddSubgroup (VC D N N')} (hM : FullLat M) :
    ∃ t : Set (VC D N N'), IsAddFundamentalDomain M t volume := by
  let L : Submodule ℤ (VC D N N') := M.toIntSubmodule
  haveI : DiscreteTopology L := hM.1
  haveI : IsZLattice ℝ L := ⟨by simpa [L] using hM.2⟩
  let b := Module.Free.chooseBasis ℤ L
  refine ⟨ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L), ?_⟩
  have h := ZSpan.isAddFundamentalDomain (b.ofZLatticeBasis ℝ L)
    (MeasureTheory.volume : MeasureTheory.Measure (VC D N N'))
  rw [Module.Basis.ofZLatticeBasis_span] at h
  exact h

theorem full_inf {La₁ La₂ : AddSubgroup (VC D N N')} (h₁ : FullLat La₁) (h₂ : FullLat La₂)
    [Finite (La₂ ⧸ La₁.addSubgroupOf La₂)] : FullLat (La₁ ⊓ La₂) := by
  refine ⟨?_, ?_⟩
  · haveI : DiscreteTopology (La₁ : Set (VC D N N')) := h₁.1
    exact DiscreteTopology.of_subset this (fun v hv => (AddSubgroup.mem_inf.mp hv).1)
  · rw [eq_top_iff, ← h₂.2, Submodule.span_le]
    intro v hv
    have hn : (La₁.addSubgroupOf La₂).index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
    have hmem : (La₁.addSubgroupOf La₂).index • (⟨v, hv⟩ : La₂) ∈ La₁.addSubgroupOf La₂ :=
      AddSubgroup.nsmul_index_mem _ _
    have h1 : (La₁.addSubgroupOf La₂).index • v ∈ La₁ := by
      rw [AddSubgroup.mem_addSubgroupOf] at hmem
      simpa using hmem
    have h2 : (La₁.addSubgroupOf La₂).index • v ∈ La₂ := La₂.nsmul_mem hv _
    have h3 : (La₁.addSubgroupOf La₂).index • v ∈
        Submodule.span ℝ ((La₁ ⊓ La₂ : AddSubgroup (VC D N N')) : Set (VC D N N')) :=
      Submodule.subset_span (AddSubgroup.mem_inf.mpr ⟨h1, h2⟩)
    have h4 := Submodule.smul_mem _ (((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ h3
    rwa [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn),
      one_smul] at h4

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IL

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IL

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions MeasureTheory Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB
open scoped Pointwise ENNReal Function

variable {D : Car} {N N' : ℕ}

theorem Hf_cont_left (T : Tor D) (w : VC D N N') : Continuous fun z : VC D N N' => Hf D T z w := by
  unfold Formalism.L2.Ker.Cd.TaylorLogMetric.Hf
  fun_prop

theorem Hf_cont_diag (T : Tor D) : Continuous fun z : VC D N N' => Hf D T z z := by
  unfold Formalism.L2.Ker.Cd.TaylorLogMetric.Hf
  refine Continuous.div_const ?_ _
  refine continuous_finset_sum _ fun τ _ => continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  have hc : Continuous fun z : VC D N N' => z τ i j :=
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))
  exact hc.mul (Complex.continuous_conj.comp hc)

theorem U_cont (T : Tor D) {G : VC D N N' → ℂ} (hG : Continuous G) (x : VC D N N') :
    Continuous (U D T x G) := by
  unfold Formalism.L2.Ker.Cd.TaylorLogMetric.U
  exact (hG.comp (continuous_id.add continuous_const)).mul
    (Complex.continuous_exp.comp ((continuous_const.mul (Hf_cont_left T x)).sub continuous_const))

theorem dens_cont (T : Tor D) {G : VC D N N' → ℂ} (hG : Continuous G) :
    Continuous (Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T G) := by
  unfold Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens
  exact ((continuous_norm.comp hG).pow 2).mul
    (Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp (Hf_cont_diag T))))

theorem crD_cont (T : Tor D) {A B : VC D N N' → ℂ} (hA : Continuous A) (hB : Continuous B) :
    Continuous (crD T A B) := by
  unfold crD
  exact (hA.mul (Complex.continuous_conj.comp hB)).mul (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp (Hf_cont_diag T)))))

theorem crD_self (T : Tor D) (A : VC D N N' → ℂ) (z : VC D N N') :
    crD T A A z = ((Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T A z : ℝ) : ℂ) := by
  unfold crD Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem normSq_eq (T : Tor D) (La' : AddSubgroup (VC D N N')) (G : VC D N N' → ℂ) :
    normSq D T La' G = ⨍ z in Classical.epsilon
      (fun Fd => IsAddFundamentalDomain La' Fd volume), Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T G z := rfl

theorem crD_Mper (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La₁) (hZ : ∀ x ∈ La₂, ∀ y ∈ La₂, ∃ b : ℤ, (Hf D T x y).im = b)
    {x x' : VC D N N'} (hx : x ∈ La₂) (hx' : x' ∈ La₂) :
    ∀ m ∈ La₁ ⊓ La₂, ∀ z, crD T (trm T G x) (trm T G x') (z + m) =
      crD T (trm T G x) (trm T G x') z := by
  intro m hm z
  have hm' := AddSubgroup.mem_inf.mp hm
  rw [crD_shift T hG hm'.1 x x' z, ep_mul_conj]
  obtain ⟨b, hb⟩ := hZ (x - x') (La₂.sub_mem hx hx') m hm'.2
  rw [(ep_eq_one_iff _).2 ⟨b, hb⟩, one_mul]

theorem trm_cont (T : Tor D) {G : VC D N N' → ℂ} (hG : Continuous G) (x : VC D N N') :
    Continuous (trm T G x) := by
  unfold trm
  exact continuous_const.mul (U_cont T hG x)

private theorem crD_const_mul_sum (T : Tor D) (c : ℂ) {ι : Type*} (s : Finset ι) (A : ι → VC D N N' → ℂ)
    (z : VC D N N') :
    crD T (fun w => c * ∑ i ∈ s, A i w) (fun w => c * ∑ i ∈ s, A i w) z =
      c * starRingEnd ℂ c * ∑ i ∈ s, ∑ j ∈ s, crD T (A i) (A j) z := by
  simp only [crD]
  rw [map_mul, map_sum]
  calc c * (∑ i ∈ s, A i z) * (starRingEnd ℂ c * ∑ j ∈ s, starRingEnd ℂ (A j z)) *
        ((Real.exp (-Real.pi * (Hf D T z z).re) : ℝ) : ℂ)
      = c * starRingEnd ℂ c * ((∑ i ∈ s, A i z) * (∑ j ∈ s, starRingEnd ℂ (A j z)) *
        ((Real.exp (-Real.pi * (Hf D T z z).re) : ℝ) : ℂ)) := by ring
    _ = _ := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]

theorem iso_core (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')}
    (h₁ : FullLat La₁) (h₂ : FullLat La₂)
    [Finite (La₂ ⧸ La₁.addSubgroupOf La₂)] [Finite (La₁ ⧸ La₂.addSubgroupOf La₁)]
    (hZ : ∀ x ∈ La₂, ∀ y ∈ La₂, ∃ b : ℤ, (Hf D T x y).im = b)
    (hS : SemiChar T La₂)
    (hSD : ∀ v ∈ La₂, (∀ y ∈ La₁, ∃ b : ℤ, (Hf D T v y).im = b) → v ∈ La₁)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) :
    normSq D T La₂ (Iop D T La₁ La₂ G) = normSq D T La₁ G := by
  have hGc : Continuous G := hG.1.continuous
  have hI := Iop_mem_ThSp T hS hG
  have hM : FullLat (La₁ ⊓ La₂) := full_inf h₁ h₂
  haveI : Countable (La₁ ⊓ La₂ : AddSubgroup (VC D N N')) := countable_of_full hM
  haveI : Countable La₁ := countable_of_full h₁
  haveI : Countable La₂ := countable_of_full h₂
  obtain ⟨t, ht⟩ := fd_of_full hM
  haveI : Finite (La₂ ⧸ (La₁ ⊓ La₂).addSubgroupOf La₂) := by
    rw [AddSubgroup.inf_addSubgroupOf_right]
    infer_instance
  haveI : Finite (La₁ ⧸ (La₁ ⊓ La₂).addSubgroupOf La₁) := by
    rw [AddSubgroup.inf_addSubgroupOf_left]
    infer_instance
  haveI := Fintype.ofFinite (La₂ ⧸ La₁.addSubgroupOf La₂)
  have hs₁ := Classical.epsilon_spec (fd_of_full h₁)
  have hs₂ := Classical.epsilon_spec (fd_of_full h₂)
  have hd0 : ∀ (F : VC D N N' → ℂ) z, 0 ≤ Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T F z := fun F z => by
    unfold Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens
    positivity

  have e1 : normSq D T La₂ (Iop D T La₁ La₂ G) = ⨍ z in t, Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (Iop D T La₁ La₂ G) z := by
    rw [normSq_eq]
    exact (avg_sub inf_le_right hs₂ ht _ (hd0 _) (dens_cont T hI.1.continuous)
      (fun g hg z => dens_periodic T La₂ _ hI g hg z)).symm
  have hdU : ∀ x w, Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (U D T x G) w = Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T G (w + x) := fun x w => by
    have h := crD_U T G G x w
    rw [crD_self, crD_self] at h
    exact_mod_cast h

  have hUx : ∀ x : VC D N N', ⨍ z in t, Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (U D T x G) z = normSq D T La₁ G := by
    intro x
    rw [← normSq_U_of_full T La₁ h₁ G hG x, normSq_eq]
    refine avg_sub inf_le_left hs₁ ht _ (hd0 _) (dens_cont T (U_cont T hGc x)) ?_
    intro g hg z
    rw [hdU, hdU, show z + g + x = z + x + g by abel, dens_periodic T La₁ G hG g hg]
  have hn0 : (((La₁.addSubgroupOf La₂).index : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr AddSubgroup.index_ne_zero_of_finite
  have hcard : Fintype.card (La₂ ⧸ La₁.addSubgroupOf La₂) = (La₁.addSubgroupOf La₂).index := by
    rw [AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hxq : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂, ((Quotient.out q : La₂) : VC D N N') ∈ La₂ := fun q => (Quotient.out q).2
  have hint : ∀ q q' : La₂ ⧸ La₁.addSubgroupOf La₂,
      MeasureTheory.IntegrableOn (crD T (trm T G ((Quotient.out q : La₂) : VC D N N')) (trm T G ((Quotient.out q' : La₂) : VC D N N'))) t volume :=
    fun q q' => intOn_of_full hM ht _ (crD_cont T (trm_cont T hGc _) (trm_cont T hGc _))
      (crD_Mper T hG hZ (hxq q) (hxq q'))

  have hoff : ∀ q q' : La₂ ⧸ La₁.addSubgroupOf La₂, q ≠ q' →
      ∫ z in t, crD T (trm T G ((Quotient.out q : La₂) : VC D N N')) (trm T G ((Quotient.out q' : La₂) : VC D N N')) z = 0 := by
    intro q q' hqq'
    have hnot : ((Quotient.out q : La₂) : VC D N N') - ((Quotient.out q' : La₂) : VC D N N') ∉ La₁ := by
      intro hmem
      apply hqq'
      have e1 : (QuotientAddGroup.mk (Quotient.out q) : La₂ ⧸ La₁.addSubgroupOf La₂) = q := Quotient.out_eq q
      have e2 : (QuotientAddGroup.mk (Quotient.out q') : La₂ ⧸ La₁.addSubgroupOf La₂) = q' :=
        Quotient.out_eq q'
      rw [← e1, ← e2, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
        AddSubgroup.coe_neg]
      have h3 : -((Quotient.out q : La₂) : VC D N N') + ((Quotient.out q' : La₂) : VC D N N') = -(((Quotient.out q : La₂) : VC D N N') - ((Quotient.out q' : La₂) : VC D N N')) := by abel
      rw [h3]
      exact La₁.neg_mem hmem
    have hex : ∃ y ∈ La₁, ¬ ∃ b : ℤ, (Hf D T (((Quotient.out q : La₂) : VC D N N') - ((Quotient.out q' : La₂) : VC D N N')) y).im = b := by
      by_contra hcon
      push_neg at hcon
      exact hnot (hSD _ (La₂.sub_mem (hxq q) (hxq q')) hcon)
    obtain ⟨y, hy, hyb⟩ := hex
    refine int_zero_of_char ht _ (crD_Mper T hG hZ (hxq q) (hxq q')) y
      (ep T ((Quotient.out q : La₂) : VC D N N') y * starRingEnd ℂ (ep T ((Quotient.out q' : La₂) : VC D N N') y)) ?_ (fun z => crD_shift T hG hy _ _ z)
    rw [ep_mul_conj]
    exact fun h1 => hyb ((ep_eq_one_iff _).1 h1)

  have hdiag : ∀ (q : La₂ ⧸ La₁.addSubgroupOf La₂) z, crD T (trm T G ((Quotient.out q : La₂) : VC D N N')) (trm T G ((Quotient.out q : La₂) : VC D N N')) z =
      ((Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (U D T ((Quotient.out q : La₂) : VC D N N') G) z : ℝ) : ℂ) := by
    intro q z
    show crD T (fun w => al D T ((Quotient.out q : La₂) : VC D N N') * U D T ((Quotient.out q : La₂) : VC D N N') G w)
      (fun w => al D T ((Quotient.out q : La₂) : VC D N N') * U D T ((Quotient.out q : La₂) : VC D N N') G w) z = _
    rw [crD_smul, al_mul_conj, one_mul, crD_self]

  have hexp : ∀ z, ((Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (Iop D T La₁ La₂ G) z : ℝ) : ℂ) =
      ((((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) * ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂, ∑ q' : La₂ ⧸ La₁.addSubgroupOf La₂,
        crD T (trm T G ((Quotient.out q : La₂) : VC D N N')) (trm T G ((Quotient.out q' : La₂) : VC D N N')) z := by
    intro z
    rw [← crD_self]
    have hI' : Iop D T La₁ La₂ G = fun w => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
        ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂, trm T G ((Quotient.out q : La₂) : VC D N N') w := by
      funext w
      unfold Formalism.L2.Ker.Cd.TaylorLogMetric.Iop
      rw [finsum_eq_sum_of_fintype]
      rfl
    have hcc : ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) * starRingEnd ℂ ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) =
        ((((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) := by
      rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (Nat.cast_nonneg _)]
    rw [hI', crD_const_mul_sum, hcc]
  have hint_sum : ∫ z in t, ((Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (Iop D T La₁ La₂ G) z : ℝ) : ℂ) =
      ((((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) * ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂,
        ((∫ z in t, Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (U D T ((Quotient.out q : La₂) : VC D N N') G) z : ℝ) : ℂ) := by
    simp_rw [hexp]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finset_sum _
      (fun q _ => MeasureTheory.integrable_finset_sum _ (fun q' _ => hint q q'))]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [MeasureTheory.integral_finset_sum _ (fun q' _ => hint q q'),
      Finset.sum_eq_single q (fun q' _ hq' => hoff q q' (Ne.symm hq'))
        (fun h => absurd (Finset.mem_univ q) h)]
    simp_rw [hdiag]
    exact integral_ofReal
  have hreal : ∫ z in t, Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (Iop D T La₁ La₂ G) z =
      (((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ * ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂, ∫ z in t, Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (U D T ((Quotient.out q : La₂) : VC D N N') G) z := by
    have h := hint_sum
    rw [integral_complex_ofReal] at h
    exact_mod_cast h
  have hU' : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      (volume t).toReal⁻¹ * ∫ z in t, Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (U D T ((Quotient.out q : La₂) : VC D N N') G) z = normSq D T La₁ G := by
    intro q
    rw [← hUx ((Quotient.out q : La₂) : VC D N N'), MeasureTheory.setAverage_eq, MeasureTheory.measureReal_def,
      smul_eq_mul]
  rw [e1, MeasureTheory.setAverage_eq, MeasureTheory.measureReal_def, smul_eq_mul, hreal, mul_left_comm, Finset.mul_sum]
  simp_rw [hU']
  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IL

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions MeasureTheory Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

def HfIntRec : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 →
    ∀ N N' (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
      HfInt (tor0 D cc δ) (La D (tor0 D cc δ) L L')

def SelfDualRec : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 →
    ∀ N N' (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
      ∀ v : VC D N N', (∀ y ∈ La D (tor0 D cc δ) L L', ∃ b : ℤ, (Hf D (tor0 D cc δ) v y).im = b) →
        v ∈ La D (tor0 D cc δ) L L'

theorem IopIso_of_parts (hA : HfIntRec) (hB : SelfDualRec) :
    ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      IopIso D (tor0 D cc δ) := by
  intro D cc hcc δ hδ N N' L₁ L₁' L₂ L₂' h₁ h₂ G hG
  by_cases h0 : δ = 0
  · subst h0
    have hLam : (tor0 D cc 0).abelian₂ = ⊥ := by
      show lamOf D cc 0 = ⊥
      unfold Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf
      rw [AddSubgroup.closure_eq_bot_iff]
      rintro w ⟨c, _, rfl⟩
      simp
    have hLa : ∀ (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
        (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), La D (tor0 D cc 0) L L' = ⊥ := by
      intro L L'
      unfold Formalism.L2.Ker.Cd.TaylorLogMetric.La
      rw [AddSubgroup.closure_eq_bot_iff]
      rintro z ⟨w, hw, A, _, rfl⟩
      rw [hLam, AddSubgroup.mem_bot] at hw
      simp [hw]
    rw [hLa L₂ L₂', ← hLa L₁ L₁']
    exact IopIso_diag D (tor0 D cc 0) L₁ L₁' G hG
  · have hF₁ := Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.fullLat D L₁ L₁' h₁ cc hcc δ h0
    have hF₂ := Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.fullLat D L₂ L₂' h₂ cc hcc δ h0
    haveI := La_index_finite cc hcc δ L₁ L₂ L₁' L₂' h₁ h₂
    haveI := La_index_finite cc hcc δ L₂ L₁ L₂' L₁' h₂ h₁
    have hI₂ := hA D cc hcc δ hδ h0 N N' L₂ L₂' h₂
    refine IL.iso_core (tor0 D cc δ) hF₁ hF₂ ?_ (semiChar_of_HfInt _ hI₂) ?_ hG
    · intro x hx y hy
      obtain ⟨a, b, _, hab⟩ := hI₂ x hx y hy
      exact ⟨b, by rw [hab]; simp⟩
    · intro v _ hv
      exact hB D cc hcc δ hδ h0 N N' L₁ L₁' h₁ v hv

theorem LinkThIndep_of_parts (hA : HfIntRec) (hB : SelfDualRec) : LinkThIndep := by
  exact Formalism.L2.Ker.Cd.IntegralLatticeDensity.LinkThIndep_of (IopIso_of_parts hA hB)
    Formalism.L2.Ker.Cd.IntegralLatticeDensity.character_unit_on_determinant

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
