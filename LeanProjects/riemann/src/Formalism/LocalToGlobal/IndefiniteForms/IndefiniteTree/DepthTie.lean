import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.VwEqZeroOfNotMem
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ONLeaves
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCondPf

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Indef.Tree.DepthTie

open NumberField IsDedekindDomain
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.DIV Formalism.BasicNotions Formalism.L2.Indef.Tree.DepthCond

section Places

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem vw_natCast_eq (v : HeightOneSpectrum (𝓞 K)) (N : ℕ) (hN : N ≠ 0) :
    vw v (N : K) = Formalism.L2.Pj.vLa v (N : K) := by
  have h := intValuation_eq_exp' v (N : 𝓞 K) (by exact_mod_cast hN)
  rw [Formalism.L2.Pj.Crude.crv_vLa_natCast_eq v N, h, WithZero.log_exp, neg_neg]
  simp

theorem ramw_eq_ramOverZ (v : HeightOneSpectrum (𝓞 K)) : ramw v = (Formalism.L2.Pj.ramOverZ v : ℤ) := by
  have hp := plc_prime v
  unfold ramw
  rw [vw_natCast_eq v _ hp.ne_zero]
  exact Formalism.L2.Pj.Crude.crv_vLa_char v

variable {F : Type} [Field F] [NumberField F] [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

theorem resChar_below (v : HeightOneSpectrum (𝓞 K)) :
    Formalism.L2.Pj.resCharOf (Formalism.L2.Pj.placeBelow (K := F) v) = plc v := by
  have hle : (Formalism.L2.Pj.placeBelow (K := F) v).asIdeal ≤ v.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) := le_rfl
  have hinj : Function.Injective (Ideal.quotientMap v.asIdeal (algebraMap (𝓞 F) (𝓞 K)) hle) :=
    Ideal.quotientMap_injective' le_rfl
  have : CharP (𝓞 K ⧸ v.asIdeal) (ringChar (𝓞 F ⧸ (Formalism.L2.Pj.placeBelow (K := F) v).asIdeal)) :=
    charP_of_injective_ringHom hinj _
  unfold plc Formalism.L2.Pj.resCharOf
  exact (ringChar.eq (𝓞 K ⧸ v.asIdeal) _).symm

theorem ramw_eq_below (v : HeightOneSpectrum (𝓞 K)) :
    ramw v = (Formalism.L2.Pj.ramOver (K := F) v : ℤ) *
      (Formalism.L2.Pj.ramOverZ (Formalism.L2.Pj.placeBelow (K := F) v) : ℤ) := by
  rw [ramw_eq_ramOverZ]
  have hl := resChar_below (F := F) v
  have hv : Formalism.L2.Pj.resCharOf v = plc v := rfl
  have hp := plc_prime v
  set la := Formalism.L2.Pj.placeBelow (K := F) v with hla
  have hg0 : Ideal.map (algebraMap (𝓞 F) (𝓞 K)) la.asIdeal ≠ ⊥ := by
    intro h
    have hx := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 K)) (Formalism.L2.Pj.Crude.crv_char_mem la)
    rw [h, Ideal.mem_bot, map_natCast] at hx
    exact (Formalism.L2.Pj.Crude.resCharOf_prime la).ne_zero (by exact_mod_cast hx)
  have hfg : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((plc v : ℕ) : ℤ)}) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hg : Ideal.map (algebraMap (𝓞 F) (𝓞 K)) la.asIdeal ≤ v.asIdeal := Ideal.map_le_iff_le_comap.2 le_rfl
  have ht := Ideal.ramificationIdx'_algebra_tower (R := ℤ) (S := 𝓞 F) (T := 𝓞 K)
    (p := Ideal.span {((plc v : ℕ) : ℤ)}) (P := la.asIdeal) (Q := v.asIdeal) hg0 hfg hg
  unfold Formalism.L2.Pj.ramOverZ Formalism.L2.Pj.ramOver
  rw [hv, hl, ht]
  push_cast
  ring

theorem one_le_ramOver_below (v : HeightOneSpectrum (𝓞 K)) :
    1 ≤ Formalism.L2.Pj.ramOver (K := F) v ∧ 1 ≤ Formalism.L2.Pj.ramOverZ (Formalism.L2.Pj.placeBelow (K := F) v) := by
  have h := one_le_ramw v
  rw [ramw_eq_below (F := F) v] at h
  constructor
  · refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0] at h
    simp at h
  · refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0] at h
    simp at h

end Places

section Ties

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
  {Dw : ℕ → Datum H} (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E)
variable {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  (O : OnObj S P oc) (ι : Bs.J → ℕ)

def e1 (v : HeightOneSpectrum (𝓞 K)) : ℕ := ramOver (K := c.F) v

def e2 (v : HeightOneSpectrum (𝓞 K)) : ℕ := ramOverZ (placeBelow (K := c.F) v)

def nuT (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : ℝ :=
  nuStarAt (Xo := Xo (ι j)) (c := c) Dd (placeBelow (K := c.F) v) (ι j)

def nuWT (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : ℝ :=
  (nuWAt (Xo := Xo (ι j)) (c := c) Dd (placeBelow (K := c.F) v) (ι j)).toReal / (e2 c v : ℝ)

def sWT (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : ℝ := nuT Xo c Dd ι v j - nuWT Xo c Dd ι v j

def s1T (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : ℝ :=
  (vw v (O.σ v j) : ℝ) / (ramw v : ℝ) - O.T * sWT Xo c Dd ι v j

theorem nuStar_nonneg (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : 0 ≤ nuT Xo c Dd ι v j := by
  have hp := plc_prime v
  have h2 : (2 : ℝ) ≤ (plc v : ℝ) := by exact_mod_cast hp.two_le
  unfold nuT nuStarAt DepPage.nuN
  rw [resChar_below (F := c.F) v]
  have hW : 0 ≤ (nuWAt (Xo := Xo (ι j)) (c := c) Dd (placeBelow (K := c.F) v) (ι j)).toReal :=
    EReal.toReal_nonneg (le_max_left _ _)
  split_ifs with h1 h2'
  · rw [← h1]; exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · rw [← h2']; exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · exact add_nonneg (div_nonneg hW (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem bad_iff (hpr : O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm)
    (v : HeightOneSpectrum (𝓞 K)) :
    Dd.Q.IsBad (resCharOf (placeBelow (K := c.F) v)) ↔ plc v ∈ O.Bad := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hpr
  rw [resChar_below (F := c.F) v]
  simp only [Formalism.L2.Pj.DepPage.IsBad, Formalism.L2.Pj.DepPage.IsRam, Formalism.L2.Indef.Tree.OnObj.Bad, Finset.mem_insert,
    h1, h2, h3, h4, h5]
  try tauto

theorem tieT (hT : O.T = ((Dd.Q.T : ℕ) : ℝ)) : TieT O (Dd.Q.T : ℕ) := hT

theorem tieE (hE : ∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j))
    (hT : O.T = ((Dd.Q.T : ℕ) : ℝ)) (hpr : O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) :
    TieE O (e1 c) (e2 c) (nuT Xo c Dd ι) := by
  have key : ∀ v : HeightOneSpectrum (𝓞 K), 1 ≤ e1 c v ∧ 1 ≤ e2 c v ∧ ramw v = (e1 c v : ℤ) * (e2 c v : ℤ) ∧
      ∀ j, (O.E v j : ℤ) ≤ (e1 c v : ℤ) *
        ⌈(e2 c v : ℝ) * O.T * (nuT Xo c Dd ι v j + if plc v ∈ O.Bad then 1 else 0)⌉ := by
    intro v
    classical
    obtain ⟨h1, h2⟩ := one_le_ramOver_below (F := c.F) v
    refine ⟨h1, h2, ramw_eq_below (F := c.F) v, fun j => ?_⟩
    have hb : (if Dd.Q.IsBad (resCharOf (placeBelow (K := c.F) v)) then (1 : ℝ) else 0) =
        (if plc v ∈ O.Bad then 1 else 0) := by
      by_cases h : plc v ∈ O.Bad
      · rw [if_pos h, if_pos ((bad_iff c Dd O hpr v).2 h)]
      · rw [if_neg h, if_neg (fun h' => h ((bad_iff c Dd O hpr v).1 h'))]
    have hnn := nuStar_nonneg Xo c Dd ι v j
    have hbn : (0 : ℝ) ≤ (if plc v ∈ O.Bad then 1 else 0) := by split_ifs <;> norm_num
    have hc : (0 : ℤ) ≤ ⌈(e2 c v : ℝ) * O.T * (nuT Xo c Dd ι v j + if plc v ∈ O.Bad then 1 else 0)⌉ := by
      apply Int.ceil_nonneg
      have hT0 : (0 : ℝ) ≤ O.T := by rw [hT]; positivity
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hT0) (add_nonneg hnn hbn)
    rw [hE v j]
    unfold EAt expE DepPage.eLam
    rw [hb]
    rw [Nat.cast_mul, Int.natCast_toNat_eq_self.2 (by rw [← hT]; exact hc)]
    rw [← hT]
    rfl
  intro w _
  exact ⟨key w, key (conjPl w)⟩

theorem nuLevel (hpr : O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) :
    NuLevel O (nuT Xo c Dd ι) (fun j => (DF (Dw (ι j)) (Dd.aL (ι j)) : ℝ)) := by
  obtain ⟨h1, h2, -, -, -⟩ := hpr
  have key : ∀ v : HeightOneSpectrum (𝓞 K), (plc v = O.g1 ∨ plc v = O.g2) → ∀ j,
      nuT Xo c Dd ι v j = (DF (Dw (ι j)) (Dd.aL (ι j)) : ℝ) / ((plc v : ℝ) - 1) := by
    intro v hv j
    simp only [nuT, nuStarAt]
    rw [resChar_below (F := c.F) v]
    rcases hv with hv | hv
    · rw [hv, h1]
      simp [Formalism.L2.Pj.DepPage.nuN]
    · rw [hv, h2]
      simp only [Formalism.L2.Pj.DepPage.nuN]
      split_ifs with hh <;> simp_all
  unfold NuLevel
  intro w _ hw j
  refine ⟨(key w hw j).le, le_of_eq ?_⟩
  rw [key _ ?_ j]
  · first
      | rw [Formalism.EigenvalueLevelCeiling.plc_conjPl]
      | rw [Formalism.L2.DIV.plc_conjPl]
  · first
      | (rw [Formalism.EigenvalueLevelCeiling.plc_conjPl]; exact hw)
      | (rw [Formalism.L2.DIV.plc_conjPl]; exact hw)

theorem tieScale : TieScale S (nuT Xo c Dd ι) (nuWT Xo c Dd ι) (sWT Xo c Dd ι) := by
  unfold TieScale AtPair
  intro w _
  exact ⟨fun j => by simp only [sWT]; ring, fun j => by simp only [sWT]; ring⟩

theorem tieSigma : TieSigma O (sWT Xo c Dd ι) (s1T Xo c Dd O ι) := by
  unfold TieSigma AtPair
  intro w _
  exact ⟨fun j => by simp only [s1T]; ring, fun j => by simp only [s1T]; ring⟩

end Ties

section Val

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
  {Dw : ℕ → Datum H} (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E)
variable {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  (O : OnObj S P oc) (ι : Bs.J → ℕ)

omit [StarRing (𝓞 E)] in
theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply NumberField.RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq]
  first
    | exact IsCMField.complexConj_apply_apply (a : E)
    | exact IsCMField.complexConj_apply_apply E (a : E)
    | simp

def Nsig (Q : DepPage) (DFL DFF : ℕ) : ℕ := Q.q ^ (Q.f * Q.r * Q.n') * Q.Z1 DFL DFF

omit [StarRing K] in
theorem vw_nonneg_of_isIntegral [StarRing K] (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : IsIntegral ℤ x) :
    0 ≤ vw v x := by
  by_cases h0 : x = 0
  · subst h0
    simp only [vw, FractionalIdeal.spanSingleton_zero]
    first
      | simp [FractionalIdeal.count_zero]
      | simp [FractionalIdeal.count]
  · let r : 𝓞 K := ⟨x, hx⟩
    have hr : algebraMap (𝓞 K) K r = x := rfl
    have hr0 : r ≠ 0 := by
      intro h
      apply h0
      rw [← hr, h, map_zero]
    unfold vw
    rw [← hr, ← FractionalIdeal.coeIdeal_span_singleton]
    apply FractionalIdeal.count_coe_nonneg
    try simpa using hr0

omit [StarRing K] [StarRing (𝓞 E)] in
theorem isIntegral_alg (a : 𝓞 E) : IsIntegral ℤ (algebraMap (𝓞 E) K a) := by
  first
    | exact IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral a)
    | exact IsIntegral.algebraMap (NumberField.RingOfIntegers.isIntegral a)

omit [StarRing K] [StarRing (𝓞 E)] in
theorem sigAt_eq (Dw' : Datum H) (j : ℕ) :
    sigAt (Dw := Dw') (H := H) (LL := K) Dd j =
      nnKAt (H := H) (LL := K) Dd j * ((Nsig Dd.Q (DF Dw' (Dd.aL j)) (DF Dw' (Dd.aF j)) : ℕ) : K) := by
  simp only [sigAt, nnKAt, sigOf, Nsig, Nat.cast_mul, Nat.cast_pow]

omit [StarRing K] [StarRing (𝓞 E)] in
theorem nnK_isIntegral (j : ℕ) : IsIntegral ℤ (nnKAt (H := H) (LL := K) Dd j) := by
  have h : nnKAt (H := H) (LL := K) Dd j =
      algebraMap (𝓞 E) K (∏ i : Fin 2, H.bar (Dd.pi i) ^ Dd.Dp j * Dd.pi i ^ Dd.Dm j) := by
    simp only [nnKAt, nnOf, map_prod, map_mul, map_pow]
  rw [h]
  exact isIntegral_alg _

omit [StarRing K] [StarRing (𝓞 E)] in
theorem alg_pi_ne_zero (hsp : PiSplit (H := H) Dd) (hprime : Dd.Q.g1.Prime ∧ Dd.Q.g2.Prime) :
    (algebraMap (𝓞 E) K (Dd.pi 0) * algebraMap (𝓞 E) K (H.bar (Dd.pi 0)) = (Dd.Q.g1 : K)) ∧
    (algebraMap (𝓞 E) K (Dd.pi 1) * algebraMap (𝓞 E) K (H.bar (Dd.pi 1)) = (Dd.Q.g2 : K)) ∧
    algebraMap (𝓞 E) K (Dd.pi 0) ≠ 0 ∧ algebraMap (𝓞 E) K (H.bar (Dd.pi 0)) ≠ 0 ∧
    algebraMap (𝓞 E) K (Dd.pi 1) ≠ 0 ∧ algebraMap (𝓞 E) K (H.bar (Dd.pi 1)) ≠ 0 := by
  obtain ⟨h0, h1⟩ := hsp
  have e0 : algebraMap (𝓞 E) K (Dd.pi 0) * algebraMap (𝓞 E) K (H.bar (Dd.pi 0)) = (Dd.Q.g1 : K) := by
    rw [← map_mul, h0, map_natCast]
  have e1 : algebraMap (𝓞 E) K (Dd.pi 1) * algebraMap (𝓞 E) K (H.bar (Dd.pi 1)) = (Dd.Q.g2 : K) := by
    rw [← map_mul, h1, map_natCast]
  have n0 : (Dd.Q.g1 : K) ≠ 0 := Nat.cast_ne_zero.mpr hprime.1.ne_zero
  have n1 : (Dd.Q.g2 : K) ≠ 0 := Nat.cast_ne_zero.mpr hprime.2.ne_zero
  rw [← e0] at n0
  rw [← e1] at n1
  exact ⟨e0, e1, left_ne_zero_of_mul n0, right_ne_zero_of_mul n0, left_ne_zero_of_mul n1,
    right_ne_zero_of_mul n1⟩

omit [StarRing K] [StarRing (𝓞 E)] in
theorem nnK_ne_zero (hsp : PiSplit (H := H) Dd) (hprime : Dd.Q.g1.Prime ∧ Dd.Q.g2.Prime) (j : ℕ) :
    nnKAt (H := H) (LL := K) Dd j ≠ 0 := by
  obtain ⟨-, -, a0, b0, a1, b1⟩ := alg_pi_ne_zero (H := H) (K := K) Dd hsp hprime
  simp only [nnKAt, nnOf, Fin.prod_univ_two]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ b0) (pow_ne_zero _ a0))
    (mul_ne_zero (pow_ne_zero _ b1) (pow_ne_zero _ a1))

theorem Nsig_ne_zero (Q : DepPage) (h : Q.g1.Prime ∧ Q.g2.Prime ∧ Q.q1.Prime ∧ Q.dd.Prime) (DFL DFF : ℕ) :
    Nsig Q DFL DFF ≠ 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold Nsig Formalism.L2.Pj.DepPage.Z1 Formalism.L2.Pj.DepPage.q
  apply mul_ne_zero
  · exact pow_ne_zero _ (mul_ne_zero h1.ne_zero h2.ne_zero)
  · refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ h3.ne_zero)) (pow_ne_zero _ h4.ne_zero)
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (Finset.mem_filter.mp hp).2.ne_zero)

omit [StarRing (𝓞 E)] in
theorem vw_N (v : HeightOneSpectrum (𝓞 K)) (N : ℕ) (hN : N ≠ 0) :
    vw v (N : K) = (padicValNat (plc v) N : ℤ) * ramw v := by
  rw [vw_natCast_eq v N hN, Formalism.L2.Pj.Crude.crv_vLa_natCast v hN, ramw_eq_ramOverZ]
  push_cast
  rfl

private theorem vw_mul_lemma (v : HeightOneSpectrum (𝓞 K)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    vw v (a * b) = vw v a + vw v b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  have h1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a ≠ 0 :=
    FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr ha
  have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) b ≠ 0 :=
    FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hb
  first
    | exact FractionalIdeal.count_mul K v h1 h2
    | exact FractionalIdeal.count_mul h1 h2

theorem vw_sig (hsp : PiSplit (H := H) Dd) (hprime : Dd.Q.g1.Prime ∧ Dd.Q.g2.Prime ∧ Dd.Q.q1.Prime ∧ Dd.Q.dd.Prime)
    (v : HeightOneSpectrum (𝓞 K)) (Dw' : Datum H) (j : ℕ) :
    (vw v (sigAt (Dw := Dw') (H := H) (LL := K) Dd j) : ℝ) = (vw v (nnKAt (H := H) (LL := K) Dd j) : ℝ) +
      (padicValNat (plc v) (Nsig Dd.Q (DF Dw' (Dd.aL j)) (DF Dw' (Dd.aF j))) : ℝ) * (ramw v : ℝ) := by
  have hn : nnKAt (H := H) (LL := K) Dd j ≠ 0 := nnK_ne_zero Dd hsp ⟨hprime.1, hprime.2.1⟩ j
  have hN : Nsig Dd.Q (DF Dw' (Dd.aL j)) (DF Dw' (Dd.aF j)) ≠ 0 := Nsig_ne_zero _ hprime _ _
  rw [sigAt_eq, vw_mul_lemma v _ _ hn (Nat.cast_ne_zero.mpr hN), vw_N v _ hN]
  rw [Int.cast_add, Int.cast_mul, Int.cast_natCast]

theorem sigmaLevel (hσ : ∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j))
    (hnn : ∀ j, O.nnK j = nnKAt (H := H) (LL := K) Dd (ι j)) (hsp : PiSplit (H := H) Dd)
    (hprime : Dd.Q.g1.Prime ∧ Dd.Q.g2.Prime ∧ Dd.Q.q1.Prime ∧ Dd.Q.dd.Prime) : SigmaLevel O := by
  unfold SigmaLevel
  intro w _ _ j
  have key : ∀ v : HeightOneSpectrum (𝓞 K), ∃ s : ℝ, 0 ≤ s ∧
      (vw v (O.σ v j) : ℝ) / (ramw v : ℝ) = O.nn v j + s := by
    intro v
    refine ⟨(padicValNat (plc v) (Nsig Dd.Q (DF (Dw (ι j)) (Dd.aL (ι j))) (DF (Dw (ι j)) (Dd.aF (ι j)))) : ℝ) *
      (ramw v : ℝ) / (ramw v : ℝ), ?_, ?_⟩
    · rw [mul_div_assoc]
      refine mul_nonneg (Nat.cast_nonneg _) ?_
      rcases eq_or_ne (ramw v : ℝ) 0 with h | h
      · rw [h, div_zero]
      · rw [div_self h]
        exact zero_le_one
    · rw [hσ v j, vw_sig Dd hsp hprime v (Dw (ι j)) (ι j), Formalism.L2.Indef.Tree.OnObj.nn, hnn j, add_div]
  exact ⟨key _, key _⟩

end Val

section Ram

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
  {Dw : ℕ → Datum H} (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E)
variable {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  (O : OnObj S P oc) (ι : Bs.J → ℕ)

theorem sprimeRam (hT : O.T = ((Dd.Q.T : ℕ) : ℝ))
    (hpr : O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm)
    (hσ : ∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) (hsp : PiSplit (H := H) Dd)
    (hprime : Dd.Q.g1.Prime ∧ Dd.Q.g2.Prime ∧ Dd.Q.q1.Prime ∧ Dd.Q.dd.Prime)
    (hqg : O.q1 ≠ O.g1 ∧ O.q1 ≠ O.g2 ∧ O.dd ≠ O.g1 ∧ O.dd ≠ O.g2) :
    SprimeRam O (s1T Xo c Dd O ι) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hpr
  have key : ∀ v j, (plc v = O.q1 ∨ plc v = O.dd) → 0 ≤ s1T Xo c Dd O ι v j := by
    intro v j hv
    have hn1 : plc v ≠ Dd.Q.g1 := by
      rw [← h1]; rcases hv with h | h <;> rw [h]; exacts [hqg.1, hqg.2.2.1]
    have hn2 : plc v ≠ Dd.Q.g2 := by
      rw [← h2]; rcases hv with h | h <;> rw [h]; exacts [hqg.2.1, hqg.2.2.2]
    have hs : sWT Xo c Dd ι v j = (Dd.Q.cP (DF (Dw (ι j)) (Dd.aL (ι j))) (plc v) : ℝ) := by
      unfold sWT nuT nuWT nuStarAt DepPage.nuN e2
      rw [resChar_below (F := c.F) v, if_neg hn1, if_neg hn2]
      ring
    set N := Nsig Dd.Q (DF (Dw (ι j)) (Dd.aL (ι j))) (DF (Dw (ι j)) (Dd.aF (ι j))) with hNdef
    have hN : N ≠ 0 := Nsig_ne_zero Dd.Q hprime _ _
    have : Fact (plc v).Prime := ⟨plc_prime v⟩
    have hdvd : (plc v) ^ ((Dd.Q.T : ℕ) * Dd.Q.cP (DF (Dw (ι j)) (Dd.aL (ι j))) (plc v)) ∣ N := by
      rw [hNdef]
      unfold Nsig DepPage.Z1
      refine Dvd.dvd.mul_left ?_ _
      rcases hv with h | h
      · rw [h, h3]
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ (Nat.le_add_right _ _)) _) _
      · rw [h, h4]
        exact Dvd.dvd.mul_left (pow_dvd_pow _ (Nat.le_add_right _ _)) _
    have hle : ((Dd.Q.T : ℕ) : ℝ) * (Dd.Q.cP (DF (Dw (ι j)) (Dd.aL (ι j))) (plc v) : ℝ) ≤ (padicValNat (plc v) N : ℝ) := by
      exact_mod_cast (padicValNat_dvd_iff_le hN).1 hdvd
    have hnn0 : (0 : ℝ) ≤ (vw v (nnKAt (H := H) (LL := K) Dd (ι j)) : ℝ) :=
      by exact_mod_cast vw_nonneg_of_isIntegral v _ (nnK_isIntegral Dd (ι j))
    have he := ramw_pos v
    unfold s1T
    rw [hs, hσ v j, vw_sig Dd hsp hprime v, add_div, mul_div_cancel_right₀ _ he.ne', hT]
    have : 0 ≤ (vw v (nnKAt (H := H) (LL := K) Dd (ι j)) : ℝ) / (ramw v : ℝ) := div_nonneg hnn0 he.le
    linarith
  intro w _ hw j
  refine ⟨key w j hw, key (conjPl w) j ?_⟩
  rw [plc_conjPl]; exact hw

theorem nnLevel (hnn : ∀ j, O.nnK j = nnKAt (H := H) (LL := K) Dd (ι j)) (hsp : PiSplit (H := H) Dd)
    (hprime : Dd.Q.g1.Prime ∧ Dd.Q.g2.Prime) (hg12 : Dd.Q.g1 ≠ Dd.Q.g2)
    (hpr : O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm)
    (hconj : ∀ a : 𝓞 E, star (algebraMap (𝓞 E) K a) = algebraMap (𝓞 E) K (H.bar a))
    (Nd : NumDatum) (hD : ∀ j, Nd.Dplus (ι j) = (Dd.Dp (ι j) : ℚ) ∧ Nd.Dminus (ι j) = (Dd.Dm (ι j) : ℚ)) :
    NnLevel O Nd ι := by
  intro w _ hg j
  obtain ⟨e0, e1, -⟩ := alg_pi_ne_zero (K := K) Dd hsp hprime
  have hnn0 := nnK_ne_zero (K := K) Dd hsp hprime (ι j)
  have hprod : nnKAt (H := H) (LL := K) Dd (ι j) * star (nnKAt (H := H) (LL := K) Dd (ι j)) =
      (((Dd.Q.g1 ^ (Dd.Dp (ι j) + Dd.Dm (ι j)) * Dd.Q.g2 ^ (Dd.Dp (ι j) + Dd.Dm (ι j)) : ℕ)) : K) := by
    unfold nnKAt nnOf
    simp only [Fin.prod_univ_two, star_mul', star_pow, hconj, bar_bar]
    push_cast
    rw [← e0, ← e1]
    ring
  have he := ramw_pos w
  have hlev := vw_level w hprime.1 hprime.2 hg12 (Dd.Dp (ι j) + Dd.Dm (ι j))
  have hw : plc w = Dd.Q.g1 ∨ plc w = Dd.Q.g2 := by
    rcases hg with h | h
    · left; rw [h, hpr.1]
    · right; rw [h, hpr.2.1]
  rw [if_pos hw] at hlev
  unfold OnObj.nn
  rw [ramw_conjPl w, ← ValuationRepresentative.vw_star w, hnn j, ← add_div, ← Int.cast_add,
    ← ValuationRepresentative.vw_mul w _ _ hnn0 (star_ne_zero.2 hnn0), hprod, hlev, mul_div_cancel_left₀ _ he.ne', (hD j).1, (hD j).2]
  push_cast
  ring

theorem crudeRam (_hstar : ∀ a : 𝓞 E, star a = H.bar a) (hEx : ∀ j, IntChartEx (Xo (ι j)) c)
    (hSat : ∀ j, ChartSaturated (Xo (ι j)) c) (hDom : ∀ j, DomW (Dw (ι j)) (Dd.aL (ι j)))
    (hcard : ∀ j, Fintype.card (Lt1 (Dw (ι j))) ≤ Dd.nW (ι j)) :
    CrudeRam O (nuWT Xo c Dd ι) (fun j => (DF (Dw (ι j)) (Dd.aL (ι j)) : ℝ)) := by
  have key : ∀ v j, nuWT Xo c Dd ι v j ≤ (DF (Dw (ι j)) (Dd.aL (ι j)) : ℝ) / ((plc v : ℝ) - 1) := by
    intro v j
    have hb := nuW_le_crude (hEx j) (hSat j) (placeBelow (K := c.F) v) l.M (Dd.aL (ι j)) (Dd.nW (ι j)) (hDom j) (hcard j)
    have hl := resChar_below (F := c.F) v
    have hp := plc_prime v
    have hp2 : (2 : ℝ) ≤ (plc v : ℝ) := by exact_mod_cast hp.two_le
    have he : (0 : ℝ) < (e2 c v : ℝ) := by exact_mod_cast (one_le_ramOver_below (F := c.F) v).2
    have hcb : (0 : ℝ) ≤ crudeBd (placeBelow (K := c.F) v) (DF (Dw (ι j)) (Dd.aL (ι j))) := by
      unfold crudeBd
      rw [hl]
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)
    have hcb' : (0 : EReal) ≤ (crudeBd (placeBelow (K := c.F) v) (DF (Dw (ι j)) (Dd.aL (ι j))) : EReal) := by
      exact_mod_cast hcb
    rw [max_eq_right hcb'] at hb
    have ht := EReal.toReal_le_toReal hb (ne_bot_of_le_ne_bot EReal.zero_ne_bot (le_max_left _ _)) (EReal.coe_ne_top _)
    rw [EReal.toReal_coe] at ht
    unfold crudeBd at ht
    rw [hl] at ht
    unfold nuWT nuWAt
    rw [div_le_iff₀ he]
    unfold e2
    calc _ ≤ _ := ht
      _ = _ := by ring
  intro w _ _ j
  refine ⟨key w j, ?_⟩
  have := key (conjPl w) j
  rwa [plc_conjPl] at this

end Ram

section Leaves

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
  {Dw : ℕ → Datum H} (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E)
variable {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  (O : OnObj S P oc) (ι : Bs.J → ℕ)

theorem page_facts (hPg : LeafPage O) (hpr : O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) :
    (Dd.Q.g1.Prime ∧ Dd.Q.g2.Prime ∧ Dd.Q.q1.Prime ∧ Dd.Q.dd.Prime) ∧ Dd.Q.g1 ≠ Dd.Q.g2 ∧
      (O.q1 ≠ O.g1 ∧ O.q1 ≠ O.g2 ∧ O.dd ≠ O.g1 ∧ O.dd ≠ O.g2) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hpr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, p1, p2, p3, p4, n12, -, nq1, nq2, nd1, nd2, -⟩ := hPg
  rw [← h1, ← h2, ← h3, ← h4]
  exact ⟨⟨p1, p2, p3, p4⟩, n12, nq1, nq2, nd1, nd2⟩

theorem leafDepthLevel_depth (N : IndefNum Bs) (Nd : NumDatum)
    (hE : ∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j))
    (hσ : ∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j))
    (hnn : ∀ j, O.nnK j = nnKAt (H := H) (LL := K) Dd (ι j)) (hT : O.T = ((Dd.Q.T : ℕ) : ℝ))
    (hpr : O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) (hsp : PiSplit (H := H) Dd)
    (hconj : ∀ a : 𝓞 E, star (algebraMap (𝓞 E) K a) = algebraMap (𝓞 E) K (H.bar a))
    (hD : ∀ j, Nd.Dplus (ι j) = (Dd.Dp (ι j) : ℚ) ∧ Nd.Dminus (ι j) = (Dd.Dm (ι j) : ℚ))
    (hPg : LeafPage O) (hTpos : TPos Dd) (tF : ContentEqualsDatumContent N Nd ι) (tP : TiePrimes O Nd) (Dk : Bs.J → ℝ)
    (iD : DegScale O (fun j => (DF (Dw (ι j)) (Dd.aL (ι j)) : ℝ)) Dk) (iP : DegLevelPage O Dk)
    (iR : RamLevel O (e2 c)) : LeafDepthLevel N O := by
  obtain ⟨⟨p1, p2, p3, p4⟩, h12, -⟩ := page_facts Dd O hPg hpr
  exact leafDepthLevel_of N O Nd ι (Dd.Q.T : ℕ) (e1 c) (e2 c) (nuT Xo c Dd ι)
    (fun j => (DF (Dw (ι j)) (Dd.aL (ι j)) : ℝ)) Dk rounding_condition_holds nu_level_condition_holds level_condition_holds
    content_prime_condition_holds hPg (tieT Dd O hT) hTpos (tieE Xo c Dd O ι hE hT hpr) tF tP (nuLevel Xo c Dd O ι hpr) iD iP iR
    (sigmaLevel Dd O ι hσ hnn hsp ⟨p1, p2, p3, p4⟩) (nnLevel Dd O ι hnn hsp ⟨p1, p2⟩ h12 hpr hconj Nd hD)

theorem leafDepthRam_depth (N : IndefNum Bs) (Nd : NumDatum)
    (hE : ∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j))
    (hσ : ∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j))
    (hT : O.T = ((Dd.Q.T : ℕ) : ℝ))
    (hpr : O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) (hsp : PiSplit (H := H) Dd)
    (hstar : ∀ a : 𝓞 E, star a = H.bar a) (hEx : ∀ j, IntChartEx (Xo (ι j)) c) (hSat : ∀ j, ChartSaturated (Xo (ι j)) c)
    (hDom : ∀ j, DomW (Dw (ι j)) (Dd.aL (ι j))) (hcard : ∀ j, Fintype.card (Lt1 (Dw (ι j))) ≤ Dd.nW (ι j))
    (hPg : LeafPage O) (hSz : LeafSizes O) (tF : ContentEqualsDatumContent N Nd ι) (tP : TiePrimes O Nd) (tK : TieFK O Nd)
    (Dk : Bs.J → ℝ) (C₀ : ℝ) (iD : DegScale O (fun j => (DF (Dw (ι j)) (Dd.aL (ι j)) : ℝ)) Dk)
    (iW : DegWeight O Dk C₀) (iP : PageRam O C₀) (iB : WtRam O Nd ι) : LeafDepthRam N O := by
  obtain ⟨⟨p1, p2, p3, p4⟩, -, hqg⟩ := page_facts Dd O hPg hpr
  exact leafDepthRam_of N O Nd ι (e1 c) (e2 c) (nuT Xo c Dd ι) (nuWT Xo c Dd ι) (sWT Xo c Dd ι)
    (s1T Xo c Dd O ι) (fun j => (DF (Dw (ι j)) (Dd.aL (ι j)) : ℝ)) Dk C₀ rounding_condition_holds ramification_condition_holds
    content_prime_condition_holds ramified_discriminant_condition_holds hPg hSz (tieE Xo c Dd O ι hE hT hpr) tF tP tK (tieScale Xo c Dd ι)
    (tieSigma Xo c Dd O ι) (crudeRam Xo c Dd O ι hstar hEx hSat hDom hcard)
    (sprimeRam Xo c Dd O ι hT hpr hσ hsp ⟨p1, p2, p3, p4⟩ hqg) iD iW iP iB

end Leaves

section Core

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} (T : Core D) [StarRing (𝓞 D.host.E)] (Dd : DepData D.host.E)
variable {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  (O : OnObj S P oc) (ι : Bs.J → ℕ)

omit [StarRing (𝓞 D.host.E)] in
theorem card_of_laws [StarRing (𝓞 D.host.E)] (hL : LawsPi T Dd) (hp : T.Q.Pins) (j : ℕ) (hj : InR D j) :
    Fintype.card (Lt1 (T.Q.Dw j)) ≤ Dd.nW j := by
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2
    simp only [Ranks.sigW, Ranks.r]; omega
  refine card_Lt1_le_finrank_mul.trans ?_
  rw [hfr, hr]; exact (hL.wts j hj).2

theorem leafDepthLevel_core (N : IndefNum Bs) (Nd : NumDatum) (hL : LawsPi T Dd)
    (hE : ∀ v j, O.E v j = EAt (Xo := T.Q.Xo (ι j)) (c := T.Q.c) (LL := K) Dd v (ι j))
    (hσ : ∀ v j, O.σ v j = sigAt (Dw := T.Q.Dw (ι j)) (H := T.Q.H) (LL := K) Dd (ι j))
    (hnn : ∀ j, O.nnK j = nnKAt (H := T.Q.H) (LL := K) Dd (ι j)) (hT : O.T = ((Dd.Q.T : ℕ) : ℝ))
    (hpr : O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm)
    (hconj : ∀ a : 𝓞 D.host.E, star (algebraMap (𝓞 D.host.E) K a) = algebraMap (𝓞 D.host.E) K (T.Q.H.bar a))
    (hD : ∀ j, Nd.Dplus (ι j) = (Dd.Dp (ι j) : ℚ) ∧ Nd.Dminus (ι j) = (Dd.Dm (ι j) : ℚ))
    (hPg : LeafPage O) (tF : ContentEqualsDatumContent N Nd ι) (tP : TiePrimes O Nd) (Dk : Bs.J → ℝ)
    (iD : DegScale O (fun j => (DF (T.Q.Dw (ι j)) (Dd.aL (ι j)) : ℝ)) Dk) (iP : DegLevelPage O Dk)
    (iR : RamLevel O (e2 T.Q.c)) : LeafDepthLevel N O := leafDepthLevel_depth T.Q.Xo T.Q.c Dd O ι N Nd hE hσ hnn hT hpr hL.piSplit hconj hD hPg
    hL.tPos tF tP Dk iD iP iR

theorem leafDepthRam_core (N : IndefNum Bs) (Nd : NumDatum) (hL : LawsPi T Dd) (hp : T.Q.Pins)
    (hι : ∀ j, InR D (ι j))
    (hE : ∀ v j, O.E v j = EAt (Xo := T.Q.Xo (ι j)) (c := T.Q.c) (LL := K) Dd v (ι j))
    (hσ : ∀ v j, O.σ v j = sigAt (Dw := T.Q.Dw (ι j)) (H := T.Q.H) (LL := K) Dd (ι j))
    (hT : O.T = ((Dd.Q.T : ℕ) : ℝ))
    (hpr : O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm)
    (hstar : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) (hEx : ∀ j, IntChartEx (T.Q.Xo (ι j)) T.Q.c)
    (hSat : ∀ j, ChartSaturated (T.Q.Xo (ι j)) T.Q.c) (hPg : LeafPage O) (hSz : LeafSizes O) (tF : ContentEqualsDatumContent N Nd ι) (tP : TiePrimes O Nd) (tK : TieFK O Nd)
    (Dk : Bs.J → ℝ) (C₀ : ℝ) (iD : DegScale O (fun j => (DF (T.Q.Dw (ι j)) (Dd.aL (ι j)) : ℝ)) Dk)
    (iW : DegWeight O Dk C₀) (iP : PageRam O C₀) (iB : WtRam O Nd ι) : LeafDepthRam N O := leafDepthRam_depth T.Q.Xo T.Q.c Dd O ι N Nd hE hσ hT hpr hL.piSplit hstar hEx hSat
    (fun j σ i k hik => (hL.wts _ (hι j)).1 σ hik) (fun j => card_of_laws T Dd hL hp (ι j) (hι j)) hPg hSz tF tP tK Dk C₀ iD iW iP iB

end Core

end Formalism.L2.Indef.Tree.DepthTie
