import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Taylor
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorWp
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorSigma

noncomputable section
open scoped BigOperators
open Filter Topology

namespace Formalism.L2.Th1.F

namespace EndoZ

open PowerSeries TaylorWp

theorem T.congr {f g : ℂ → ℂ} {F : PowerSeries ℂ} (hf : T f F) (h : f =ᶠ[𝓝 0] g) : T g F :=
  ⟨hf.1.congr h, (taylor_ring.2.2.2 f g h).symm.trans hf.2⟩

private theorem T_const (c : ℂ) : T (fun _ => c) (C c) :=
  ⟨analyticAt_const, taylor_ring.2.1 c⟩

theorem T.neg {f : ℂ → ℂ} {F : PowerSeries ℂ} (hf : T f F) : T (fun z => -f z) (-F) := by
  convert T.mul taylor_ring (T_const (-1)) hf using 1
  · funext z; simp
  · simp

theorem T.sub {f g : ℂ → ℂ} {F G : PowerSeries ℂ} (hf : T f F) (hg : T g G) :
    T (fun z => f z - g z) (F - G) := by
  convert T.add taylor_ring hf (T.neg hg) using 1
  · funext z; ring
  · ring

theorem T.sum {ι : Type} (s : Finset ι) (f : ι → ℂ → ℂ) (F : ι → PowerSeries ℂ)
    (h : ∀ i ∈ s, T (f i) (F i)) : T (fun z => ∑ i ∈ s, f i z) (∑ i ∈ s, F i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    convert T_const (0 : ℂ) using 1 <;> simp
  · intro a s ha ih h
    have h1 := T.add taylor_ring (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    convert h1 using 1
    · funext z; rw [Finset.sum_insert ha]
    · rw [Finset.sum_insert ha]

theorem T.prod {ι : Type} (s : Finset ι) (f : ι → ℂ → ℂ) (F : ι → PowerSeries ℂ)
    (h : ∀ i ∈ s, T (f i) (F i)) : T (fun z => ∏ i ∈ s, f i z) (∏ i ∈ s, F i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    convert T_const (1 : ℂ) using 1 <;> simp
  · intro a s ha ih h
    have h1 := T.mul taylor_ring (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    convert h1 using 1
    · funext z; rw [Finset.prod_insert ha]
    · rw [Finset.prod_insert ha]

theorem T.deriv {f : ℂ → ℂ} {F : PowerSeries ℂ} (hf : T f F) :
    T (deriv f) (derivative ℂ F) :=
  ⟨hf.1.deriv, by rw [taylor_deriv.1 f hf.1, hf.2]⟩

theorem T.rescale {f : ℂ → ℂ} {F : PowerSeries ℂ} (a : ℂ) (hf : T f F) :
    T (fun z => f (a * z)) (rescale a F) := by
  refine ⟨?_, by rw [taylor_deriv.2.1 f a hf.1, hf.2]⟩
  exact hf.1.comp_of_eq (analyticAt_const.mul analyticAt_id) (by simp)

theorem T.unique {f g : ℂ → ℂ} {F G : PowerSeries ℂ} (hf : T f F) (hg : T g G)
    (h : f =ᶠ[𝓝[≠] 0] g) : F = G := by
  have hfg : ∀ᶠ z in 𝓝 (0 : ℂ), f z = g z :=
    (hf.1.frequently_eq_iff_eventually_eq hg.1).1 h.frequently
  rw [← hf.2, ← hg.2]
  exact taylor_ring.2.2.2 f g hfg

theorem T_p (L : PeriodPair) : T (L.weierstrassPExcept 0) (pSeries L) :=
  ⟨TaylorSigmaUniqueness.analyticAt_pExcept L, rfl⟩

theorem wp_eq (L : PeriodPair) (z : ℂ) :
    L.weierstrassP z = 1 / z ^ 2 + L.weierstrassPExcept 0 z := by
  rw [IsogenyPAux.P_local L 0 L.lattice.zero_mem z, sub_zero, add_comm]

private theorem analyticAt_weierstrassP_of_not_mem (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) :
    AnalyticAt ℂ L.weierstrassP P := by
  have hda : DifferentiableOn ℂ L.weierstrassP (L.lattice : Set ℂ)ᶜ := fun w hw =>
    (PDeriv.hasDerivAt_P L hw).differentiableAt.differentiableWithinAt
  exact hda.analyticAt ((PeriodPair.isClosed_lattice L).isOpen_compl.mem_nhds hP)

theorem T_shift (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) :
    T (fun z => L.weierstrassP (z + P)) (taylor0 fun z => L.weierstrassP (z + P)) := by
  refine ⟨?_, rfl⟩
  exact (analyticAt_weierstrassP_of_not_mem L hP).comp_of_eq (analyticAt_id.add analyticAt_const) (by simp)

theorem ev_notMem (L : PeriodPair) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
  first
  | exact ThreeTermRelation.eventually_notMem L 0
  | exact Filter.inf_principal_eq_bot.1
      ((discreteTopology_subtype_iff.1 (inferInstanceAs (DiscreteTopology L.lattice))) 0
        L.lattice.zero_mem)

theorem tendsto_mul_nhdsNE {α : ℂ} (hα : α ≠ 0) :
    Tendsto (fun z : ℂ => α * z) (𝓝[≠] 0) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩
  · have h0 : Tendsto (fun z : ℂ => α * z) (𝓝 0) (𝓝 (α * 0)) := (continuous_mul_left α).tendsto 0
    rw [mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  · exact mul_ne_zero hα hz

theorem ev_shift_notMem (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z + P ∉ L.lattice := by
  have ho : IsOpen {z : ℂ | z + P ∉ L.lattice} :=
    (PeriodPair.isClosed_lattice L).isOpen_compl.preimage (continuous_id.add continuous_const)
  exact ho.mem_nhds (by simpa using hP)

theorem wp_congr (L : PeriodPair) {a b : ℂ} (h : a - b ∈ L.lattice) :
    L.weierstrassP a = L.weierstrassP b := by
  rw [IsogenyPAux.P_local L (a - b) h a, sub_sub_cancel,
    IsogenyPAux.P_local L 0 L.lattice.zero_mem b, sub_zero]

theorem clause3 (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (hα : α ≠ 0) (hm : MulStable L α)
    (hS : IsKerReps L α S) :
    C (α ^ 2) * rescale α (pSeries L) = pSeries L
      + ∑ P : S, (taylor0 (fun z => L.weierstrassP (z + (P : ℂ))) - C (L.weierstrassP (P : ℂ))) := by
  have hL := T.mul taylor_ring (T_const (α ^ 2)) (T.rescale α (T_p L))
  have hR := T.add taylor_ring (T_p L) (T.sum Finset.univ
    (fun (P : S) (z : ℂ) => L.weierstrassP (z + (P : ℂ)) - L.weierstrassP (P : ℂ))
    (fun (P : S) => taylor0 (fun z => L.weierstrassP (z + (P : ℂ))) - C (L.weierstrassP (P : ℂ)))
    (fun P _ => T.sub (T_shift L (hS.1 P P.2).2) (T_const _)))
  refine T.unique hL hR ?_
  filter_upwards [ev_notMem L, (tendsto_mul_nhdsNE hα).eventually (ev_notMem L),
    self_mem_nhdsWithin] with z hz hαz hz0
  have hz0' : z ≠ 0 := hz0
  have hip := isogenyP L α S hα hm hS z hαz
  rw [← Finset.sum_coe_sort S] at hip
  have e1 : L.weierstrassPExcept 0 (α * z) = L.weierstrassP (α * z) - 1 / (α * z) ^ 2 := by
    rw [wp_eq L (α * z)]; ring
  have e2 : L.weierstrassPExcept 0 z = L.weierstrassP z - 1 / z ^ 2 := by
    rw [wp_eq L z]; ring
  beta_reduce
  rw [e1, e2, mul_sub, hip]
  field_simp
  ring

private theorem hasDerivAt_sgStar' (L : PeriodPair) {u : ℂ} (hu : u ∉ L.lattice) :
    HasDerivAt (sgStar L) (sgStar L u * (wZeta L u - s2 L * u)) u := by
  have h1 := sigmaLogDeriv L u hu
  have h3 : HasDerivAt (fun w : ℂ => -(s2 L) * w ^ 2 / 2) (-(s2 L) * u) u :=
    (((hasDerivAt_pow 2 u).const_mul (-(s2 L))).div_const 2).congr_deriv (by norm_num <;> ring)
  have h5 := h1.mul h3.cexp
  unfold sgStar
  exact h5.congr_deriv (by ring)

theorem wp_logDeriv (L : PeriodPair) {P z : ℂ} (hP : P ∉ L.lattice) (hz : z ∉ L.lattice)
    (hp : z + P ∉ L.lattice) (hm : z - P ∉ L.lattice) :
    L.derivWeierstrassP z = (L.weierstrassP z - L.weierstrassP P)
      * (wZeta L (z + P) + wZeta L (z - P) - 2 * wZeta L z) := by
  have hz' : ∀ᶠ u in 𝓝 z, u ∉ L.lattice :=
    (PeriodPair.isClosed_lattice L).isOpen_compl.mem_nhds hz
  have hev : (fun u => sgStar L (u + P) * sgStar L (u - P)) =ᶠ[𝓝 z]
      fun u => -(sgStar L u ^ 2 * sgStar L P ^ 2 * (L.weierstrassP u - L.weierstrassP P)) := by
    filter_upwards [hz'] with u hu
    exact sgStarAdd L u P hu hP
  have hg := ((hasDerivAt_sgStar' L hp).comp z ((hasDerivAt_id' z).add_const P)).mul
    ((hasDerivAt_sgStar' L hm).comp z ((hasDerivAt_id' z).sub_const P))
  have hsq : HasDerivAt (fun u => sgStar L u ^ 2)
      (2 * sgStar L z * (sgStar L z * (wZeta L z - s2 L * z))) z := by
    exact ((hasDerivAt_sgStar' L hz).pow 2).congr_deriv (by norm_num <;> ring)
  have hh := ((hsq.mul_const (sgStar L P ^ 2)).mul
    ((PDeriv.hasDerivAt_P L hz).sub_const (L.weierstrassP P))).neg
  have heq := hg.unique (hh.congr_of_eventuallyEq hev)
  simp only [Function.comp_apply] at heq
  have hAB := sgStarAdd L z P hz hP
  have hs : sgStar L z ≠ 0 := mul_ne_zero (fun h => hz ((sigmaZero L z).1 h)) (Complex.exp_ne_zero _)
  have hc : sgStar L P ≠ 0 := mul_ne_zero (fun h => hP ((sigmaZero L P).1 h)) (Complex.exp_ne_zero _)
  have key : sgStar L z ^ 2 * sgStar L P ^ 2 * (L.derivWeierstrassP z - (L.weierstrassP z
      - L.weierstrassP P) * (wZeta L (z + P) + wZeta L (z - P) - 2 * wZeta L z)) = 0 := by
    linear_combination heq - (wZeta L (z + P) + wZeta L (z - P) - 2 * s2 L * z) * hAB
  have h0 := (mul_eq_zero.1 key).resolve_left (mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ hc))
  linear_combination h0

def U (L : PeriodPair) (P : ℂ) : Set ℂ :=
  {w | w ∉ L.lattice ∧ w + P ∉ L.lattice ∧ w - P ∉ L.lattice}

theorem isOpen_U (L : PeriodPair) (P : ℂ) : IsOpen (U L P) := by
  have hc := (PeriodPair.isClosed_lattice L).isOpen_compl
  exact (hc.preimage continuous_id).inter ((hc.preimage (continuous_id.add continuous_const)).inter
    (hc.preimage (continuous_id.sub continuous_const)))

theorem U_mem (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) : U L P ∈ 𝓝[≠] (0 : ℂ) := by
  have hP' : -P ∉ L.lattice := fun h => hP (by simpa using L.lattice.neg_mem h)
  have h1 := ev_notMem L
  have h2 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z + P ∉ L.lattice := nhdsWithin_le_nhds (ev_shift_notMem L hP)
  have h3 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z + -P ∉ L.lattice :=
    nhdsWithin_le_nhds (ev_shift_notMem L hP')
  filter_upwards [h1, h2, h3] with z a b c
  exact ⟨a, b, by simpa [sub_eq_add_neg] using c⟩

def fP (L : PeriodPair) (P : ℂ) (z : ℂ) : ℂ :=
  1 + z ^ 2 * (L.weierstrassPExcept 0 z - L.weierstrassP P)

def mP (L : PeriodPair) (P : ℂ) (z : ℂ) : ℂ :=
  2 * z⁻¹ + wZeta L (z + P) + wZeta L (z - P) - 2 * wZeta L z

theorem ne_zero_of_notMem (L : PeriodPair) {w : ℂ} (hw : w ∉ L.lattice) : w ≠ 0 := by
  rintro rfl
  exact hw L.lattice.zero_mem

theorem hasDerivAt_fP (L : PeriodPair) {P w : ℂ} (hP : P ∉ L.lattice) (hw : w ∈ U L P) :
    HasDerivAt (fP L P) (fP L P w * mP L P w) w := by
  obtain ⟨hw0, hwp, hwm⟩ := hw
  have hne : w ≠ 0 := ne_zero_of_notMem L hw0
  have hex : L.weierstrassPExcept 0 = fun u => L.weierstrassP u - (u ^ 2)⁻¹ := by
    funext u; rw [wp_eq L u]; ring
  have hinv : HasDerivAt (fun u : ℂ => (u ^ 2)⁻¹) (-(2 * w) / (w ^ 2) ^ 2) w :=
    ((hasDerivAt_pow 2 w).inv (pow_ne_zero 2 hne)).congr_deriv (by norm_num <;> ring)
  have hE : HasDerivAt (L.weierstrassPExcept 0)
      (L.derivWeierstrassP w - (-(2 * w) / (w ^ 2) ^ 2)) w := by
    rw [hex]; exact (PDeriv.hasDerivAt_P L hw0).sub hinv
  have hF : HasDerivAt (fP L P) (2 * w * (L.weierstrassPExcept 0 w - L.weierstrassP P)
      + w ^ 2 * (L.derivWeierstrassP w - (-(2 * w) / (w ^ 2) ^ 2))) w := by
    have h1 := ((hasDerivAt_pow 2 w).mul (hE.sub_const (L.weierstrassP P))).const_add 1
    exact h1.congr_deriv (by norm_num <;> ring)
  refine hF.congr_deriv ?_
  rw [wp_logDeriv L hP hw0 hwp hwm]
  simp only [fP, mP, hex]
  field_simp
  ring

theorem hasDerivAt_mP (L : PeriodPair) {P w : ℂ} (hw : w ∈ U L P) :
    HasDerivAt (mP L P) (2 * L.weierstrassPExcept 0 w - L.weierstrassP (w + P)
      - L.weierstrassP (w - P)) w := by
  obtain ⟨hw0, hwp, hwm⟩ := hw
  have hne := ne_zero_of_notMem L hw0
  have h1 := (hasDerivAt_inv hne).const_mul 2
  have h2 := (zetaHasDeriv L _ hwp).comp w ((hasDerivAt_id' w).add_const P)
  have h3 := (zetaHasDeriv L _ hwm).comp w ((hasDerivAt_id' w).sub_const P)
  have h4 := (zetaHasDeriv L _ hw0).const_mul 2
  have h := ((h1.add h2).add h3).sub h4
  refine h.congr_deriv ?_
  rw [wp_eq L w]
  field_simp
  ring

theorem d2log_fP (L : PeriodPair) {P w : ℂ} (hP : P ∉ L.lattice) (hw : w ∈ U L P) :
    deriv (deriv (fP L P)) w * fP L P w - deriv (fP L P) w ^ 2
      = (2 * L.weierstrassPExcept 0 w - L.weierstrassP (w + P) - L.weierstrassP (w - P))
        * fP L P w ^ 2 := by
  have hU : U L P ∈ 𝓝 w := (isOpen_U L P).mem_nhds hw
  have hev : deriv (fP L P) =ᶠ[𝓝 w] fun u => fP L P u * mP L P u :=
    Filter.eventually_of_mem hU fun u hu => (hasDerivAt_fP L hP hu).deriv
  have hd1 := (hasDerivAt_fP L hP hw).deriv
  have hprod := (hasDerivAt_fP L hP hw).mul (hasDerivAt_mP L hw)
  have hd2 : deriv (deriv (fP L P)) w = fP L P w * mP L P w * mP L P w
      + fP L P w * (2 * L.weierstrassPExcept 0 w - L.weierstrassP (w + P)
        - L.weierstrassP (w - P)) := by
    rw [hev.deriv_eq]; exact hprod.deriv
  rw [hd2, hd1]; ring

theorem T_fP (L : PeriodPair) (P : ℂ) :
    T (fP L P) (Formalism.L2.Th1.C.wpShift (pSeries L) (L.weierstrassP P)) := by
  have hX : T (fun z : ℂ => z) X := ⟨analyticAt_id, taylor_ring.2.2.1⟩
  have h := T.add taylor_ring (T_const 1) (T.mul taylor_ring
    (T.pow taylor_ring hX 2) (T.sub (T_p L) (T_const (L.weierstrassP P))))
  unfold fP Formalism.L2.Th1.C.wpShift
  convert h using 1
  simp

theorem clause2 (L : PeriodPair) {P Q : ℂ} (hP : P ∉ L.lattice) (hQ : Q + P ∈ L.lattice) :
    Formalism.L2.Th1.C.HasSecondLogDeriv (Formalism.L2.Th1.C.wpShift (pSeries L) (L.weierstrassP P))
      (2 * pSeries L - taylor0 (fun z => L.weierstrassP (z + P))
        - taylor0 (fun z => L.weierstrassP (z + Q))) := by
  have hF := T_fP L P
  have h1 := T.deriv hF
  have h2 := T.deriv h1
  have hL := T.sub (T.mul taylor_ring h2 hF) (T.pow taylor_ring h1 2)
  have hQn : Q ∉ L.lattice := by
    intro hq; apply hP
    have h3 := L.lattice.sub_mem hQ hq
    rwa [add_sub_cancel_left] at h3
  have hR := T.mul taylor_ring
    (T.sub (T.sub (T.mul taylor_ring (T_const 2) (T_p L)) (T_shift L hP)) (T_shift L hQn))
    (T.pow taylor_ring hF 2)
  have heq := T.unique hL hR (by
    filter_upwards [U_mem L hP] with w hw
    have hc : L.weierstrassP (w + Q) = L.weierstrassP (w - P) := wp_congr L (by
      have e : w + Q - (w - P) = Q + P := by ring
      rw [e]; exact hQ)
    beta_reduce
    rw [d2log_fP L hP hw, hc])
  unfold Formalism.L2.Th1.C.HasSecondLogDeriv
  rw [heq, show (C (2 : ℂ) : PowerSeries ℂ) = 2 from map_ofNat C 2]

theorem exists_neg (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (hS : IsKerReps L α S) (P : S) :
    ∃ Q : S, (Q : ℂ) + (P : ℂ) ∈ L.lattice := by
  obtain ⟨hPα, hPn⟩ := hS.1 P P.2
  have h1 : α * (-(P : ℂ)) ∈ L.lattice := by rw [mul_neg]; exact L.lattice.neg_mem hPα
  have h2 : -(P : ℂ) ∉ L.lattice := fun h => hPn (by simpa using L.lattice.neg_mem h)
  obtain ⟨Q, hQ, hQm⟩ := hS.2.2 _ h1 h2
  refine ⟨⟨Q, hQ⟩, ?_⟩
  have h3 := L.lattice.neg_mem hQm
  have e : -(-(P : ℂ) - Q) = Q + P := by ring
  rw [e] at h3
  exact h3

theorem taylorSgStar' : TaylorSgStar' :=
  taylorSgStar'_of (taylorSgStar_of (taylorSigma_of taylor_ring taylor_deriv)
    taylor_ring taylor_exp sigmaEntire)

theorem T_sgStar (L : PeriodPair) :
    T (sgStar L) (Formalism.L2.Th1.C.sgStar (pSeries L) (s2 L)) := by
  refine ⟨?_, taylorSgStar' L⟩
  have h1 : Differentiable ℂ fun z : ℂ => Complex.exp (-(s2 L) * z ^ 2 / 2) := by fun_prop
  have hd : Differentiable ℂ (sgStar L) := (sigmaEntire L).mul h1
  exact hd.analyticAt 0

theorem fP_eq (L : PeriodPair) (P : ℂ) {z : ℂ} (hz : z ≠ 0) :
    fP L P z = z ^ 2 * (L.weierstrassP z - L.weierstrassP P) := by
  unfold fP
  rw [wp_eq L z]
  field_simp
  ring

end EndoZ

theorem integer_endomorphism_instance : EndoZInstance := by
  intro L α S hα hm hS
  choose neg hneg using EndoZ.exists_neg L α S hS
  refine ⟨neg, hneg, ?_⟩
  unfold Formalism.L2.Th1.C.IsEndoZ
  refine ⟨?_, ?_, ?_⟩
  · intro P
    apply Subtype.ext
    apply hS.2.1 _ (neg (neg P)).2 _ P.2
    have e : ((neg (neg P) : ℂ) - P) = ((neg (neg P) : ℂ) + neg P) - (neg P + P) := by ring
    rw [e]
    exact L.lattice.sub_mem (hneg (neg P)) (hneg P)
  · intro P
    exact EndoZ.clause2 L (hS.1 P P.2).2 (hneg P)
  · exact EndoZ.clause3 L α S hα hm hS

open EndoZ TaylorWp in

theorem isogeny_formula_instance : IsogenyFormulaInstance := by
  intro L α S hα hm hS
  have hX : T (fun z : ℂ => z) PowerSeries.X := ⟨analyticAt_id, taylor_ring.2.2.1⟩
  have hsg := T_sgStar L
  have hL := T.mul taylor_ring (T.pow taylor_ring (T.rescale α hsg) 2)
    (T.pow taylor_ring hX (2 * Fintype.card S))
  have hR := T.mul taylor_ring
    (T.mul taylor_ring (T_const (α ^ 2))
      (T.pow taylor_ring hsg (2 * (Fintype.card S + 1))))
    (T.prod Finset.univ (fun (P : S) (z : ℂ) => fP L P z)
      (fun (P : S) => Formalism.L2.Th1.C.wpShift (pSeries L) (L.weierstrassP (P : ℂ)))
      (fun P _ => T_fP L P))
  have heq := T.unique hL hR (by
    filter_upwards [ev_notMem L, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    beta_reduce
    have hsig := isogenySigma L α S hα hm hS z hz
    have hp : ∏ P : S, fP L (P : ℂ) z
        = ∏ P : S, (z ^ 2 * (L.weierstrassP z - L.weierstrassP (P : ℂ))) :=
      Finset.prod_congr rfl fun P _ => fP_eq L P hz0'
    rw [hp, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Finset.prod_coe_sort S (fun P => L.weierstrassP z - L.weierstrassP P), hsig,
      Fintype.card_coe]
    ring)
  unfold Formalism.L2.Th1.C.IsogenyFormula
  exact heq

end Formalism.L2.Th1.F
