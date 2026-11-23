import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PCutoffs
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ContinuousTmaxShift
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTopNPoly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.JointExample
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceRateStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SignedConvergenceStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CompChartEventuallyEq
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFamilyC2PullbackOfSection
import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HsLinksOfMoriwaki
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.OfMoriwaki
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.OfMoriwakiFibreNormPullback

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ProvConj

open MeasureTheory _root_.Metric Filter Topology
open ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Regular hiding le_tmax tmax_le
open GroundTheory.Heights₂.Heights.LowerBoundFree ReciprocityTheory.ChartRestriction.G.Geo

theorem kθ_pos {x : ℝ} (hx : |x| < 1 / 2) : 0 < kθ x := by
  have : x ∈ Function.support kθ := by
    unfold kθ
    rw [ContDiffBump.support_normed_eq, mem_ball, Real.dist_eq, sub_zero]
    exact hx
  exact lt_of_le_of_ne (kθ_nonneg x) (Ne.symm this)

theorem regMax_lt {ι : Type} [Fintype ι] [Nonempty ι] {ε : ℝ} (hε : 0 < ε) (s t : ι → ℝ) (i : ι)
    (hst : ∀ j, s j ≤ t j) (hi : s i + ε ≤ t i) (hmax : ∀ j, t j ≤ t i) : regMax ε s < regMax ε t := by
  classical
  rw [regMax_eq_kK, regMax_eq_kK, ← sub_pos,
    ← integral_sub (integrable_mul_kK (continuous_tmax_shift ε t)) (integrable_mul_kK (continuous_tmax_shift ε s))]
  have hc : Continuous fun h : ι → ℝ => tmax (fun j => t j + ε * h j) * kK h - tmax (fun j => s j + ε * h j) * kK h :=
    ((continuous_tmax_shift ε t).mul kK_contDiff.continuous).sub
      ((continuous_tmax_shift ε s).mul kK_contDiff.continuous)
  have hs : HasCompactSupport
      fun h : ι → ℝ => tmax (fun j => t j + ε * h j) * kK h - tmax (fun j => s j + ε * h j) * kK h :=
    (kK_hasCompactSupport.mul_left).sub (kK_hasCompactSupport.mul_left)
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hs (fun h => ?_)
    (x := Pi.single i (1 / 4)) ?_
  · have : tmax (fun j => s j + ε * h j) ≤ tmax (fun j => t j + ε * h j) :=
      tmax_le fun j => le_trans (by linarith [hst j]) (le_tmax (fun j => t j + ε * h j) j)
    have := mul_le_mul_of_nonneg_right this (kK_nonneg h)
    simp only [Pi.zero_apply]
    linarith
  · have hk : 0 < kK (Pi.single i (1 / 4) : ι → ℝ) := by
      refine Finset.prod_pos fun j _ => kθ_pos ?_
      by_cases hj : j = i
      · subst hj; simp; norm_num [abs_of_pos]
      · simp [Pi.single_eq_of_ne hj]
    have h1 : tmax (fun j => s j + ε * (Pi.single i (1 / 4) : ι → ℝ) j) ≤ t i := by
      refine tmax_le fun j => ?_
      by_cases hj : j = i
      · subst hj; simp; linarith
      · simp [Pi.single_eq_of_ne hj]; linarith [hst j, hmax j]
    have h2 := le_tmax (fun j => t j + ε * (Pi.single i (1 / 4) : ι → ℝ) j) i
    simp only [Pi.single_eq_same] at h2
    rw [← sub_mul]
    exact (mul_pos (by linarith) hk).ne'

section Ext

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

def ext (B : BoundedPshData A) (j : Fin B.N) (V U : Set X) (hV : IsOpen V) (hU : IsOpen U) (hUV : closure U ⊆ V)
    (hVj : V ⊆ B.mid j) : BoundedPshData A where
  N := B.N + 1
  chart := Fin.cases (B.chart j) B.chart
  compat := Fin.cases (B.compat j) B.compat
  target_subset := Fin.cases (B.target_subset j) B.target_subset
  mid := Fin.cases V B.mid
  inner := Fin.cases U B.inner
  isOpen_mid := Fin.cases hV B.isOpen_mid
  isOpen_inner := Fin.cases hU B.isOpen_inner
  closure_inner := Fin.cases hUV B.closure_inner
  closure_mid := Fin.cases ((closure_mono hVj).trans (B.closure_mid j)) B.closure_mid
  cover x := ⟨(B.cover x).choose.succ, by simpa using (B.cover x).choose_spec⟩
  th := B.th
  th_pot := B.th_pot
  q := Fin.cases (B.q j) B.q
  q_smooth := Fin.cases (B.q_smooth j) B.q_smooth
  q_th := Fin.cases (B.q_th j) B.q_th
  ph := B.ph
  bdd := B.bdd
  u_psh := Fin.cases (B.u_psh j) B.u_psh

variable (B : BoundedPshData A) (j : Fin B.N) (V U : Set X) (hV : IsOpen V) (hU : IsOpen U) (hUV : closure U ⊆ V)
    (hVj : V ⊆ B.mid j)

theorem ext_cutoff {η : Fin (B.N + 1) → X → ℝ} {C : ℝ} (h : (ext B j V U hV hU hUV hVj).IsCutoffFamily η C) :
    (ext B j V ∅ hV isOpen_empty (by simp) hVj).IsCutoffFamily (Fin.cases (fun _ => -1) fun k => η k.succ)
      (max C 0) where
  smooth := Fin.cases (fun a => contDiffOn_const) fun k => h.smooth k.succ
  bounds := Fin.cases (fun x _ => ⟨le_rfl, by norm_num⟩) fun k => h.bounds k.succ
  eq_zero := Fin.cases (fun x hx => absurd hx (Set.notMem_empty x)) fun k => h.eq_zero k.succ
  eq_neg_one := Fin.cases ⟨∅, isClosed_empty, Set.empty_subset _, fun _ _ => rfl⟩ fun k => h.eq_neg_one k.succ
  levi_ge := by
    refine Fin.cases (fun k x hx w => ?_) fun i k x hx w => ?_
    · have : ReciprocityTheory.AnForm.levi (fun _ : Fin D → ℂ => (-1 : ℝ)) ((ext B j V ∅ hV isOpen_empty (by simp) hVj).chart k x) w = 0 := by
        simp [ReciprocityTheory.AnForm.levi]
      refine le_trans ?_ (le_of_eq this.symm)
      have := le_max_right C 0
      nlinarith [sq_nonneg ‖w‖]
    · refine le_trans ?_ (h.levi_ge i.succ k x hx w)
      have := le_max_left C 0
      nlinarith [sq_nonneg ‖w‖]

def back (k : Fin (B.N + 1)) : Fin B.N := Fin.cases j id k

theorem ext_phReg (ρ : Mollifier D) (t : ℝ) (k : Fin (B.N + 1)) (x : X) :
    (ext B j V U hV hU hUV hVj).phReg ρ t k x = B.phReg ρ t (back B j k) x := by
  refine Fin.cases rfl (fun _ => rfl) k

theorem ext_mid (k : Fin (B.N + 1)) : (ext B j V U hV hU hUV hVj).mid k ⊆ B.mid (back B j k) := by
  refine Fin.cases hVj (fun _ => subset_rfl) k

end Ext

section HidaSetting

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d}
  {Xo : Set ((Σ k, ι k) → ℂ)} {a : K → ℤ} {w : ((Σ k, ι k) → ℂ) → ℝ}

def extS (S : BoundedRegularisationSetting M Xo a w) (j : Fin S.B.N) (V U : Set M.Xc) (hV : IsOpen V) (hU : IsOpen U)
    (hUV : closure U ⊆ V) (hVj : V ⊆ S.B.mid j) (η : Fin (S.B.N + 1) → M.Xc → ℝ) (C : ℝ)
    (h : (ext S.B j V U hV hU hUV hVj).IsCutoffFamily η C) : BoundedRegularisationSetting M Xo a w where
  ref := S.ref
  ref_deg := S.ref_deg
  ref_smooth := S.ref_smooth
  B := ext S.B j V U hV hU hUV hVj
  th_ref := S.th_ref
  ph_eq := S.ph_eq
  ρ := S.ρ
  η := η
  Cη := C
  cutoff := h
  e1 := S.e1
  e1_ge := S.e1_ge

theorem extS_tied (S : BoundedRegularisationSetting M Xo a w) (hS : S.IsTied) (j : Fin S.B.N) (V U : Set M.Xc) (hV : IsOpen V)
    (hU : IsOpen U) (hUV : closure U ⊆ V) (hVj : V ⊆ S.B.mid j) (η : Fin (S.B.N + 1) → M.Xc → ℝ) (C : ℝ)
    (h : (ext S.B j V U hV hU hUV hVj).IsCutoffFamily η C) : (extS S j V U hV hU hUV hVj η C h).IsTied where
  e1_tendsto_zero := hS.e1_tendsto_zero
  compare := hS.compare.mono fun t ht k k' x hx => by
    have := ht (back S.B j k) (back S.B j k') x
      ⟨ext_mid S.B j V U hV hU hUV hVj k hx.1, ext_mid S.B j V U hV hU hUV hVj k' hx.2⟩
    rw [← ext_phReg S.B j V U hV hU hUV hVj S.ρ t k x, ← ext_phReg S.B j V U hV hU hUV hVj S.ρ t k' x] at this
    exact this

theorem exists_two (S : BoundedRegularisationSetting M Xo a w) (hS : S.IsTied) {x x' : M.Xc} (hxx : x ≠ x') (j : Fin S.B.N)
    (hj : x ∈ S.B.mid j) : ∃ S₁ S₂ : BoundedRegularisationSetting M Xo a w, S₁.IsTied ∧ S₂.IsTied ∧ S₁.ref = S.ref ∧ S₂.ref = S.ref ∧
      ∀ t, 0 < t → S₁.bregWeight t x' = S₂.bregWeight t x' ∧
        ((∀ k, x ∈ S.B.mid k → S.B.phReg S.ρ t k x ≤ S.B.phReg S.ρ t j x) → S₂.bregWeight t x < S₁.bregWeight t x) := by
  classical
  have hV : IsOpen (S.B.mid j ∩ {x'}ᶜ) := (S.B.isOpen_mid j).inter isOpen_compl_singleton
  have hxV : x ∈ S.B.mid j ∩ {x'}ᶜ := ⟨hj, hxx⟩
  obtain ⟨U, hU, hxU, hUV⟩ := normal_exists_closure_subset (isClosed_singleton (x := x)) hV
    (Set.singleton_subset_iff.2 hxV)
  have hxU : x ∈ U := hxU rfl
  have hVj : S.B.mid j ∩ {x'}ᶜ ⊆ S.B.mid j := Set.inter_subset_left
  obtain ⟨η, C, h⟩ := CutoffsExist.proof M.Xc d M.atlas (ext S.B j _ U hV hU hUV hVj).toPotentialCharts
  refine ⟨extS S j _ U hV hU hUV hVj η C h, extS S j _ ∅ hV isOpen_empty (by simp) hVj _ _
    (ext_cutoff S.B j _ U hV hU hUV hVj h), extS_tied S hS .., extS_tied S hS .., rfl, rfl, fun t ht => ⟨?_, fun hm => ?_⟩⟩
  · show regMax _ _ + _ = regMax _ _ + _
    congr 2
    funext k
    obtain ⟨k, hk⟩ := k
    revert hk
    refine Fin.cases (fun hk => absurd rfl hk.2) (fun k hk => rfl) k
  · have hε : 0 < S.e1 t := ht.trans_le (S.e1_ge t ht)
    show regMax _ _ + _ < regMax _ _ + _
    refine add_lt_add_left (regMax_lt hε _ _ ⟨(0 : Fin (S.B.N + 1)), hxV⟩ ?_ ?_ ?_) _
    · rintro ⟨k, hk⟩
      revert hk
      refine Fin.cases (fun hk => ?_) (fun k hk => le_rfl) k
      have h0 : η (0 : Fin (S.B.N + 1)) x = 0 := h.eq_zero (0 : Fin (S.B.N + 1)) x hxU
      show S.B.phReg S.ρ t j x + 4 * S.e1 t * (-1) ≤ S.B.phReg S.ρ t j x + 4 * S.e1 t * η (0 : Fin (S.B.N + 1)) x
      rw [h0]; linarith
    · have h0 : η (0 : Fin (S.B.N + 1)) x = 0 := h.eq_zero (0 : Fin (S.B.N + 1)) x hxU
      show S.B.phReg S.ρ t j x + 4 * S.e1 t * (-1) + S.e1 t ≤ S.B.phReg S.ρ t j x + 4 * S.e1 t * η (0 : Fin (S.B.N + 1)) x
      rw [h0]; linarith
    · rintro ⟨k, hk⟩
      have h0 : η (0 : Fin (S.B.N + 1)) x = 0 := h.eq_zero (0 : Fin (S.B.N + 1)) x hxU
      have h1 := (h.bounds k x hk).2
      have h2 := hm _ (ext_mid S.B j _ U hV hU hUV hVj k hk)
      rw [← ext_phReg S.B j _ U hV hU hUV hVj S.ρ t k x] at h2
      show (ext S.B j _ U hV hU hUV hVj).phReg S.ρ t k x + 4 * S.e1 t * η k x ≤
        S.B.phReg S.ρ t j x + 4 * S.e1 t * η (0 : Fin (S.B.N + 1)) x
      rw [h0]
      nlinarith

end HidaSetting

section Main

open MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem conj_mem {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : conjVec z ∈ mcPts P := by
  have he : ∀ f : MRing ι, eval (conjVec z) (map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp, conjVec]
  refine ⟨fun k => ?_, fun f hf => by rw [he, hz.2 f hf, map_zero]⟩
  obtain ⟨i, hi⟩ := hz.1 k
  exact ⟨i, by simpa [conjVec] using hi⟩

omit [DecidableEq Ψ] in
theorem MUc_h {H : HodgeData D} {M : XModel D} {w : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) (hv : ∀ p ∈ D.S, ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < D.vertFactor p z)
    (A : HermLine ι) (B : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ (S : BoundedRegularisationSetting M D.Xo H.aMu w) (t : ℝ), S.ref = A →
      (MUc H S B 1 1 t).h z = c * Real.exp (S.bregWeight t (M.proj z)) := by
  obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
  have hz0 := hz.1
  have hw0 := TopNPoly.orbitRep_blocks hz0
  have hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y) := by
    have h := mcPts_smul D.arith.2.1.2.1 (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz
    convert h using 1
    funext p
    have hp : z p = c p.1 * orbitRep z p := congrFun hzc p
    rw [hp, ← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have hpr : M.proj (orbitRep z) = M.proj z := (M.fibre _ hwP _ hz).2 ⟨c, hc, hzc⟩
  have hvf : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z) :=
    Finset.prod_pos fun p' hp' => hv p' (Finset.mem_filter.1 hp').1 _ hwP
  have hA := A.pos _ hw0
  have hA' := D.A'.pos _ hw0
  have hP := prod_norm_zpow_pos hc (((1 : ℕ) : ℤ) • muTwDeg H B + ((1 : ℕ) : ℤ) • D.a')
  refine ⟨(∏ k, ‖c k‖ ^ (((1 : ℕ) : ℤ) • muTwDeg H B + ((1 : ℕ) : ℤ) • D.a') k) * A.h (orbitRep z) *
    (∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z)) * D.A'.h (orbitRep z), by positivity, ?_⟩
  rintro S t rfl
  unfold MUc
  rw [smoothRepConj_h _ hz, TopNPoly.hermOfFun_h_smul hc hzc hz0 (by positivity), hpr]
  ring

theorem exists_not_conj (X : ComponentSetting D O Lt) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y))
    (hne : X.M.proj z ≠ X.M.proj (conjVec z))
    (hv : ∀ p ∈ D.S, ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < D.vertFactor p z) :
    ∃ (S' : BoundedRegularisationSetting X.M D.Xo X.H.aMu (cuspCorr X.H X.Cd)) (hS' : S'.IsTied),
      ¬ MUConjInvariant { X with S' := S', S'_tied := hS' } := by
  by_contra hall
  push Not at hall
  have hev : ∀ (S' : BoundedRegularisationSetting X.M D.Xo X.H.aMu (cuspCorr X.H X.Cd)), S'.IsTied →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), (MUc X.H S' (4 * D.f + 2) 1 1 t).h (conjVec z) = (MUc X.H S' (4 * D.f + 2) 1 1 t).h z := by
    intro S' hS'
    obtain ⟨t₀, ht₀, h⟩ := hall S' hS' (4 * D.f + 2) 1 1 le_rfl le_rfl le_rfl
    filter_upwards [Ioc_mem_nhdsGT ht₀] with t ht
    exact h t ht.1 ht.2 z
  have key := fun j : {j // X.M.proj z ∈ X.S'.B.mid j} => exists_two X.S' X.S'_tied hne j.1 j.2
  choose S₁ S₂ h₁ h₂ r₁ r₂ hw using key
  have e₁ := eventually_all.2 fun j => hev (S₁ j) (h₁ j)
  have e₂ := eventually_all.2 fun j => hev (S₂ j) (h₂ j)
  obtain ⟨t, ⟨a₁, a₂⟩, ht⟩ := ((e₁.and e₂).and self_mem_nhdsWithin).exists
  have ht : 0 < t := ht
  obtain ⟨j, hj⟩ := Finite.exists_max fun j : {j // X.M.proj z ∈ X.S'.B.mid j} =>
    X.S'.B.phReg X.S'.ρ t j (X.M.proj z)
  obtain ⟨c, hc, hcz⟩ := MUc_h (H := X.H) (M := X.M) (w := cuspCorr X.H X.Cd) hz hv X.S'.ref (4 * D.f + 2)
  obtain ⟨c', -, hcz'⟩ := MUc_h (H := X.H) (M := X.M) (w := cuspCorr X.H X.Cd) (conj_mem hz) hv X.S'.ref (4 * D.f + 2)
  have b₁ := a₁ j
  have b₂ := a₂ j
  rw [hcz _ _ (r₁ j), hcz' _ _ (r₁ j)] at b₁
  rw [hcz _ _ (r₂ j), hcz' _ _ (r₂ j), ← (hw j t ht).1, b₁] at b₂
  have := Real.exp_injective (mul_left_cancel₀ hc.ne' b₂)
  have hlt := (hw j t ht).2 fun k hk => hj ⟨k, hk⟩
  linarith

omit [DecidableEq Ψ] in

theorem exists_nonreal [Nonempty Ψ] (M : XModel D) (hne : (mcPts (mCoordIdeal D.y)).Nonempty) :
    ∃ z ∈ mcPts (mCoordIdeal D.y), M.proj z ≠ M.proj (conjVec z) := by
  classical
  by_contra hall
  push Not at hall
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨a, -⟩ := D.chart_cover z₀ hz₀
  set χ := D.chart a
  have hn : 0 < Fintype.card Ψ * D.j * (D.N - D.j) := by
    have := D.one_le_j
    have := D.j_le
    have := D.two_le_N
    exact Nat.mul_pos (Nat.mul_pos Fintype.card_pos (by omega)) (by omega)
  let v : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ := Pi.single ⟨0, hn⟩ 1
  have hv : ‖v‖ = 1 := by simp [v, Pi.norm_single]
  have h0 : (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) ∈ ball 0 1 := mem_ball_self one_pos
  choose c hc using (χ.mem 0 h0).1
  have hball : ∀ s ∈ ball (0 : ℂ) 1, s • v ∈ ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 := by
    intro s hs
    rw [mem_ball_zero_iff] at hs ⊢
    rwa [norm_smul, hv, mul_one]
  have han : ∀ p, AnalyticOnNhd ℂ (fun s : ℂ => χ.γ (s • v) p) (ball 0 1) := fun p s hs => by
    have h1 : AnalyticAt ℂ (fun s : ℂ => s • v) s := by fun_prop
    have h2 := (χ.analytic _ (hball s hs)).comp_of_eq h1 rfl
    exact analyticAt_pi_iff.1 h2 p
  have hnz : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ k, χ.γ (s • v) ⟨k, c k⟩ ≠ 0 := eventually_all.2 fun k =>
    (han ⟨k, c k⟩ 0 (mem_ball_self one_pos)).continuousAt.eventually_ne (by simpa using hc k)
  obtain ⟨r, hr, hrz⟩ := Metric.eventually_nhds_iff_ball.1 (hnz.and (ball_mem_nhds (0 : ℂ) one_pos))
  have hconst : ∀ p : Σ k, ι k, ∃ e, ∀ s ∈ ball (0 : ℂ) r, χ.γ (s • v) p / χ.γ (s • v) ⟨p.1, c p.1⟩ = e := by
    intro p
    refine AnalyticOnNhd.eq_const_of_im_eq_const (c₀ := 0) (fun s hs => ?_) (fun s hs => ?_) isOpen_ball
      (isConnected_ball hr)
    · exact (han p s (hrz s hs).2).div (han _ s (hrz s hs).2) ((hrz s hs).1 _)
    · have hm := χ.mem _ (hball s (hrz s hs).2)
      obtain ⟨d, hd, he⟩ := (M.fibre _ hm _ (conj_mem hm)).1 (hall _ hm)
      have e1 : starRingEnd ℂ (χ.γ (s • v) p) = d p.1 * χ.γ (s • v) p := congrFun he p
      have e2 : starRingEnd ℂ (χ.γ (s • v) ⟨p.1, c p.1⟩) = d p.1 * χ.γ (s • v) ⟨p.1, c p.1⟩ :=
        congrFun he ⟨p.1, c p.1⟩
      rw [← Complex.conj_eq_iff_im, map_div₀, e1, e2, mul_div_mul_left _ _ (hd _)]
  have hs : ((r / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hinj := χ.injective _ (hball _ (hrz _ hs).2) 0 h0
    (fun k => χ.γ (((r / 2 : ℝ) : ℂ) • v) ⟨k, c k⟩ / χ.γ 0 ⟨k, c k⟩)
    (fun k => div_ne_zero ((hrz _ hs).1 k) (hc k)) (by
      funext p
      obtain ⟨e, he⟩ := hconst p
      have e1 := he _ hs
      have e2 := he 0 (mem_ball_self hr)
      rw [zero_smul, ← e1, div_eq_div_iff (hc _) ((hrz _ hs).1 _)] at e2
      simp only [torusSmul]
      rw [div_mul_eq_mul_div, eq_div_iff (hc _)]
      linear_combination -e2)
  have := congrArg norm hinj
  rw [norm_smul, hv, mul_one, norm_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at this
  linarith

end Main

section Points

open MvPolynomial GroundTheory.Heights₂.Heights.Targets.LiftGraphPoints

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_scaled_eq_zero (y : (Σ k, ι k) → Ω) (T : K → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    aeval (fun p : Σ k, ι k => y p * T p.1) f = 0 := by
  have h0 : mConeMap y f = 0 := hf
  have h : ∀ f : MRing ι, aeval (fun p : Σ k, ι k => y p * T p.1) f = eval T (mConeMap y f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp]; simp [mConeMap]
  rw [h, h0, map_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem y_ne_of_X_notMem (y : (Σ k, ι k) → Ω) {p : Σ k, ι k} (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]

theorem exists_ringHom_complex (A : Type) [CommRing A] [Nontrivial A] [Algebra ℚ A] [Algebra.FiniteType ℚ A] :
    Nonempty (A →+* ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI := Ideal.Quotient.field m
  haveI : Module.Finite ℚ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ m)
  exact ⟨(IsAlgClosed.lift (R := ℚ) (S := A ⧸ m) (M := ℂ)).toRingHom.comp (Ideal.Quotient.mk m)⟩

theorem mcPts_nonempty [Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) (hy : IsRelevant (mCoordIdeal y)) :
    (mcPts (mCoordIdeal y)).Nonempty := by
  classical
  choose c hc using hy
  have hyc := fun k => y_ne_of_X_notMem y (hc k)
  let s : Set Ω := Set.range y ∪ Set.range fun k => (y ⟨k, c k⟩)⁻¹
  have hs : s.Finite := (Set.finite_range _).union (Set.finite_range _)
  let A := Algebra.adjoin ℚ s
  haveI : Algebra.FiniteType ℚ A := by
    refine ⟨(Subalgebra.fg_top A).2 ⟨hs.toFinset, by simp [A]⟩⟩
  obtain ⟨φ⟩ := exists_ringHom_complex A
  let y' : (Σ k, ι k) → A := fun p => ⟨y p, Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩)⟩
  refine ⟨fun p => φ (y' p), fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
  · have : y' ⟨k, c k⟩ * ⟨(y ⟨k, c k⟩)⁻¹, Algebra.subset_adjoin (Or.inr ⟨k, rfl⟩)⟩ = 1 :=
      Subtype.ext (mul_inv_cancel₀ (hyc k))
    have h2 := congrArg φ this
    rw [map_mul, map_one] at h2
    exact left_ne_zero_of_mul_eq_one h2
  · have h1 : aeval y f = 0 := by simpa using aeval_scaled_eq_zero y 1 hf
    have h2 : ∀ f : MRing ι, ((aeval y' f : A) : Ω) = aeval y f ∧ φ (aeval y' f) = aeval (fun p => φ (y' p)) f := by
      intro f
      induction f using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq => simp [hp.1, hq.1, hp.2, hq.2]
      | mul_X p i hp => simp [hp.1, hp.2, y']
    have h3 : aeval y' f = 0 := Subtype.ext ((h2 f).1.trans h1)
    rw [eval_map_int, ← (h2 f).2, h3, map_zero]

theorem exists_bound (F : MRing ι) : ∃ M : ℕ, ∀ M', M ≤ M' → ∀ m ∈ F.support, ∀ k, ∑ i, m ⟨k, i⟩ ≤ M' := by
  classical
  refine ⟨∑ m ∈ F.support, ∑ p, m p, fun M' hM' m hm k => le_trans ?_ hM'⟩
  calc ∑ i, m ⟨k, i⟩ ≤ ∑ k, ∑ i, m ⟨k, i⟩ :=
        Finset.single_le_sum (f := fun k => ∑ i, m ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    _ = ∑ p, m p := (Fintype.sum_sigma _).symm
    _ ≤ _ := Finset.single_le_sum (f := fun m : (Σ k, ι k) →₀ ℕ => ∑ p, m p) (fun _ _ => Nat.zero_le _) hm

theorem valAt_ne_zero {y : (Σ k, ι k) → Ω} {p : ℕ} (hp : p ≠ 0) {b : K → ℤ} {f g : MRing ι}
    (h : IsVerticalDivisorAt (mCoordIdeal y) p b f g) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (c : ∀ k, ι k) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hP : IsMultiHomogIdeal (mCoordIdeal y)) :
    valAt y (aeval y f / aeval y g * chartMono y c (-b)) z ≠ 0 := by
  classical
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => y_ne_of_X_notMem y fun hX => hc k (by simpa using hz.2 _ hX)
  set z' : (Σ k, ι k) → ℂ := fun q => (z ⟨q.1, c q.1⟩)⁻¹ * z q with hz'
  set y' : (Σ k, ι k) → Ω := fun q => y q * (y ⟨q.1, c q.1⟩)⁻¹ with hy'
  have hz'P : z' ∈ mcPts (mCoordIdeal y) :=
    mcPts_smul hP (fun k => (z ⟨k, c k⟩)⁻¹) (fun k => inv_ne_zero (hc k)) hz
  have hz1 : ∀ k, z' ⟨k, c k⟩ = 1 := fun k => inv_mul_cancel₀ (hc k)
  have hy1 : ∀ k, y' ⟨k, c k⟩ = 1 := fun k => mul_inv_cancel₀ (hyc k)
  obtain ⟨u, v, hu, hv, huv⟩ := h.unit_off_fibre (RingHom.ker (aeval z' : MRing ι →ₐ[ℤ] ℂ)) (RingHom.ker_isPrime _)
    (fun a ha => by rw [RingHom.mem_ker, ← eval_map_int]; exact hz'P.2 a ha)
    (fun k => ⟨c k, by simp [RingHom.mem_ker, hz1]⟩) (by simpa [RingHom.mem_ker] using hp)
  rw [RingHom.mem_ker] at hu hv
  obtain ⟨Mu, hMu⟩ := exists_bound u
  obtain ⟨Mv, hMv⟩ := exists_bound v
  have hU := homogAt_isMultiHomog c (Mu + Mv) u (hMu _ (by omega))
  have hV := homogAt_isMultiHomog c (Mu + Mv) v (hMv _ (by omega))
  have sy : ∀ q : Σ k, ι k, y q = y ⟨q.1, c q.1⟩ * y' q := fun q => by
    simp only [hy']; field_simp [hyc q.1]
  have sz : ∀ q : Σ k, ι k, z q = z ⟨q.1, c q.1⟩ * z' q := fun q => by
    simp only [hz']; field_simp [hc q.1]
  have eU := aeval_scale hU (fun k => z ⟨k, c k⟩) z' z sz
  have eV := aeval_scale hV (fun k => z ⟨k, c k⟩) z' z sz
  have eU' := aeval_scale hU (fun k => y ⟨k, c k⟩) y' y sy
  have eV' := aeval_scale hV (fun k => y ⟨k, c k⟩) y' y sy
  rw [aeval_homogAt c _ _ _ hz1] at eU eV
  rw [aeval_homogAt c _ _ _ hy1] at eU' eV'
  have hzp : (∏ k, z ⟨k, c k⟩ ^ (Mu + Mv)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have hUz : aeval z (homogAt c (Mu + Mv) u) ≠ 0 := by rw [eU]; exact mul_ne_zero hzp hu
  have hVz : aeval z (homogAt c (Mu + Mv) v) ≠ 0 := by rw [eV]; exact mul_ne_zero hzp hv
  have hUy : aeval y (homogAt c (Mu + Mv) u) ≠ 0 := fun h0 =>
    hUz (by rw [← eval_map_int]; exact hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hU h0))
  obtain ⟨bf, bg, hf, hg, hb⟩ := h.degrees
  have hgy : aeval y g ≠ 0 := fun h0 => h.den_not_mem (mem_mCoordIdeal_of_aeval_eq_zero y hg h0)
  have ef := aeval_scale hf (fun k => y ⟨k, c k⟩) y' y sy
  have eg := aeval_scale hg (fun k => y ⟨k, c k⟩) y' y sy
  have e0 : aeval y' (u * f - v * g) = 0 := aeval_scaled_eq_zero y (fun k => (y ⟨k, c k⟩)⁻¹) huv
  rw [map_sub, map_mul, map_mul] at e0
  have hm : chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k = ∏ k, y ⟨k, c k⟩ ^ bg k := by
    rw [chartMono, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), ← hb]
    congr 1
    simp
  have hval : IsValueAt y (aeval y f / aeval y g * chartMono y c (-b)) z
      (eval z (map (Int.castRingHom ℂ) (homogAt c (Mu + Mv) v)) /
        eval z (map (Int.castRingHom ℂ) (homogAt c (Mu + Mv) u))) := by
    refine ⟨_, _, _, hV, hU, hUy, ?_, by rwa [eval_map_int], rfl⟩
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hgy, eU', eV', ef, eg, ← hm]
    linear_combination (-(∏ k, y ⟨k, c k⟩ ^ (Mu + Mv)) * chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k) * e0
  rw [valAt_eq hz hval, eval_map_int, eval_map_int]
  exact div_ne_zero hVz hUz

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

theorem vertFactor_pos (D : ComponentData II Ψ K ι Ω E) :
    ∀ p ∈ D.S, ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < D.vertFactor p z := by
  intro p hp z hz
  unfold ComponentData.vertFactor
  split_ifs with hc
  · refine mul_pos (norm_pos_iff.2 (valAt_ne_zero (D.S_prime p hp).ne_zero (D.vertical p hp) hz _ hc.choose_spec
      D.arith.2.1.2.1)) (norm_pos_iff.2 (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc.choose_spec k)))
  · exact one_pos

theorem exists_not_conj' [Nonempty Ψ] {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) :
    ∃ (S' : BoundedRegularisationSetting X.M D.Xo X.H.aMu (cuspCorr X.H X.Cd)) (hS' : S'.IsTied),
      ¬ MUConjInvariant { X with S' := S', S'_tied := hS' } := by
  classical
  obtain ⟨z, hz, hne⟩ := exists_nonreal X.M (mcPts_nonempty D.y D.arith.2.1.2.2)
  exact exists_not_conj X hz hne (vertFactor_pos D)

end Points

section Final

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

theorem cmType_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : Nonempty (CMType H) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h0 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, h0]; simp
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre : (τ (H.rt : E)).re = 0 := by
    have a := congrArg Complex.re h1
    have b := congrArg Complex.im h1
    simp [sq] at a b
    by_contra hne
    have : (τ (H.rt : E)).im = 0 := by
      have : (τ (H.rt : E)).re * (τ (H.rt : E)).im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at a
    nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm) with h | h
  · exact ⟨⟨τ, h⟩⟩
  · refine ⟨⟨(starRingEnd ℂ).comp τ, ?_⟩⟩
    have : H.rt0 = -τ (H.rt : E) := by rw [h, neg_neg]
    rw [this]
    apply Complex.ext <;> simp [hre]

theorem line_not_conj : ∃ S' hS', ¬ MUConjInvariant
    { Line.projLineComponentSetting Line.zeroSystem Line.zero_hII with S' := S', S'_tied := hS' } :=
  exists_not_conj' _

end Final

end GlobalTheory.CompanionTheory.Ar.ProvConj

namespace GlobalTheory.CompanionTheory.Ar.ProvParts

section An

open MeasureTheory _root_.Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
open GlobalTheory.CompanionTheory.Ar.Giv

section PullTop

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isPsh_of_sameFns {A : FinHolAtlas e X} {P Q : LocPot X} (hQ : IsPotential A Q)
    (hφ : P.φ = Q.φ) (hP : IsPsh A P) : IsPsh A Q := by
  intro x j y hy w
  obtain ⟨W, hW, hzW, G, hG, hGe⟩ :=
    hQ.2 x ((A.chart j).symm y) ((A.chart j).symm y) ⟨hy.2, Q.mem_U _⟩
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy.1, hzW⟩
  have ho : IsOpen ((A.chart j).target ∩
      (A.chart j).symm ⁻¹' (W ∩ Q.U x ∩ Q.U ((A.chart j).symm y))) :=
    (A.chart j).isOpen_inter_preimage_symm ((hW.inter (Q.isOpen_U x)).inter (Q.isOpen_U _))
  have hev : (Q.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun v =>
      (Q.φ ((A.chart j).symm y) ∘ (A.chart j).symm) v + 1 * ((G ∘ (A.chart j).symm) v).re := by
    filter_upwards [ho.mem_nhds ⟨hy.1, ⟨hzW, hy.2⟩, Q.mem_U _⟩] with v hv
    have := hGe _ hv.2
    simp only [Function.comp_apply]
    linarith
  have ho2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U ((A.chart j).symm y)) :=
    (A.chart j).isOpen_inter_preimage_symm (Q.isOpen_U _)
  have h2 : ContDiffAt ℝ 2 (Q.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    ((hQ.1 _ j).contDiffAt (ho2.mem_nhds ⟨hy.1, Q.mem_U _⟩)).of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hRe : ContDiffAt ℝ 2 (fun v => ((G ∘ (A.chart j).symm) v).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 h2 hRe, levi_re_analytic hGa, mul_zero, add_zero, ← hφ]
  exact hP _ j y ⟨hy.1, P.mem_U _⟩ w

end PullTop

theorem pullback_holds : PullbackStatement := by
  intro e e' X X' _ _ _ _ _ _ A A' h hh Θ L Θ' s n n' m W m' W' hΘ hΘp hΘ' hΘ'p hL hs hsnc hs0
    hsnc' th ph phT C₅ C t₀ hSW hF hC2
  obtain ⟨hth, hSm, hPshOn, hbd⟩ := hSW
  have hΘpsh : IsPsh A Θ := TailBoundAlt.isPsh_of_isPosPot A Θ hΘp
  have hΘ'psh : IsPsh A' Θ' := TailBoundAlt.isPsh_of_isPosPot A' Θ' hΘ'p
  have hΘpb : IsPotential A' (Θ.pullback h hh.1) := isPotentialPullback A A' h hh Θ hΘ
  obtain ⟨K, hK0, -, hKpsh⟩ := TailBoundAlt.exists_psh_chern_bound A' Θ' (Θ.pullback h hh.1) hΘ' hΘ'p hΘpb
  have ht₀ : 0 < t₀ := hF.1
  have hU : IsOpen (bdry s)ᶜ := (LeviFormBoundaryTopology.isClosed_bdry hs).isOpen_compl
  set M : ℝ := max 1 K with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMK : K ≤ M := le_max_right _ _
  set C' : ℝ := |C| * M with hC'
  set t₁ : ℝ := min t₀ (Real.exp (-Real.exp 1)) with ht₁
  have ht₁0 : 0 < t₁ := lt_min ht₀ (Real.exp_pos _)
  have ht₁t₀ : t₁ ≤ t₀ := min_le_left _ _
  have ht₁e : t₁ ≤ Real.exp (-Real.exp 1) := min_le_right _ _
  have hCC' : |C| ≤ C' := le_mul_of_one_le_right (abs_nonneg C) hM1
  have F1 := isRegFamily_mono A Θ L s th ph phT C t₀ |C| t₁ hΘ hΘpsh hth hs0 hF le_rfl ht₁0 ht₁t₀ ht₁e
  have F2 := isRegFamily_mono A Θ L s th ph phT C t₀ C' t₁ hΘ hΘpsh hth hs0 hF hCC' ht₁0 ht₁t₀ ht₁e
  refine ⟨C', t₁, ⟨isPotentialPullback A A' h hh th hth, ?_, ?_, fun y hy => hbd (h y) hy⟩, ?_, ?_⟩
  · have := smoothOn_pull hh hU hSm
    rwa [Set.preimage_compl] at this
  · have := isPshOn_pull hh hU hth hSm hPshOn
    rwa [Set.preimage_compl] at this
  · obtain ⟨-, -, F1⟩ := F1
    obtain ⟨h1, h2, F2⟩ := F2
    refine ⟨h1, h2, fun t ht htt => ?_⟩
    obtain ⟨a1, a2, a3, a4, -, a6, a7, a8⟩ := F2 t ht htt
    obtain ⟨b1, -, -, -, b5, -⟩ := F1 t ht htt
    have hsm : A'.Smooth (phT t ∘ h) := by
      have := smoothOn_pull hh isOpen_univ a1
      rwa [Set.preimage_univ] at this
    refine ⟨hsm, fun y => a2 (h y), fun y hy => a3 (h y) hy, fun y => a4 (h y), ?_,
      fun y hy hyr => a6 (h y) hy hyr, fun y hy => a7 (h y) hy,
      fun t' h1 h2 y => a8 t' h1 h2 (h y)⟩

    set ε : ℝ := epsT |C| t with hε
    have hq := loglog_quot_nonneg ht (htt.trans ht₁e)
    have hε0 : 0 ≤ ε := by
      rw [hε, epsT_eq_mul]; exact mul_nonneg (abs_nonneg C) hq
    have hε' : epsT C' t = M * ε := by
      rw [hε, epsT, epsT, hC']; ring
    have hεK : 0 ≤ M * ε - K * ε := by nlinarith
    have hP0 : IsPotential A (th + LocPot.ofFun (phT t) + Θ.rsmul ε) :=
      isPotentialAdd A _ _ (isPotentialAdd A _ _ hth (isPotential_ofFun A _ b1))
        (isPotentialRsmul A ε Θ hΘ)
    have hD : IsPotential A' (Θ'.rsmul K + (Θ.pullback h hh.1).rsmul (-1)) :=
      isPotentialAdd A' _ _ (isPotentialRsmul A' K Θ' hΘ') (isPotentialRsmul A' (-1) _ hΘpb)
    have hS1 := isPotentialPullback A A' h hh _ hP0
    have hS1p := isPsh_pull hh hP0 b5
    have hS2 := isPotentialRsmul A' ε _ hD
    have hS2p := isPshRsmul A' ε _ hε0 hD hKpsh
    have hS3 := isPotentialRsmul A' (M * ε - K * ε) Θ' hΘ'
    have hS3p := isPshRsmul A' (M * ε - K * ε) Θ' hεK hΘ' hΘ'psh
    have hS := isPshAdd A' _ _ (isPotentialAdd A' _ _ hS1 hS2) hS3
      (isPshAdd A' _ _ hS1 hS2 hS1p hS2p) hS3p
    have hT : IsPotential A' (th.pullback h hh.1 + LocPot.ofFun (phT t ∘ h) + Θ'.rsmul (epsT C' t)) :=
      isPotentialAdd A' _ _ (isPotentialAdd A' _ _ (isPotentialPullback A A' h hh th hth)
        (isPotential_ofFun A' _ hsm)) (isPotentialRsmul A' _ Θ' hΘ')
    refine isPsh_of_sameFns hT ?_ hS
    funext x y
    show th.φ (h x) (h y) + phT t (h y) + ε * Θ.φ (h x) (h y) +
        ε * (K * Θ'.φ x y + -1 * Θ.φ (h x) (h y)) + (M * ε - K * ε) * Θ'.φ x y =
      th.φ (h x) (h y) + phT t (h y) + epsT C' t * Θ'.φ x y
    rw [hε']
    ring
  · have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), A.Smooth (phT t) :=
      Filter.mem_of_superset (Ioc_mem_nhdsGT ht₀) fun t ht => (hF.2.2 t ht.1 ht.2).1
    exact regular_family_C2_pullback_of_section A A' h hh L s ph phT hs hSm hev hC2

theorem an_iff : Prov.An ↔ UnifIntStatement ∧ RegGlobalStatement :=
  ⟨fun h => ⟨h.2.2.2.2.1, h.2.2.2.2.2.2⟩, fun h =>
    ⟨tailBound_holds, convergence_holds, SignedConv.convergenceSigned, convergenceRate_holds, h.1, pullback_holds, h.2⟩⟩

end An

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem nineFree_iff (hHS : MoriwakiHSStatement) (hBig : MoriwakiBigStatement) :
    Prov.ZhangDimensionPushDownGrassmannianHeightBounds ↔ PushDown.Statement ∧ GrassmannianHeightZTwo.Statement := by
  obtain ⟨-, -, -, -, hZ, hD⟩ := Giv.hsLinks_of_moriwaki hHS hBig
  exact ⟨fun h => h.2.2.2, fun h => ⟨hZ, hD, trivial, h⟩⟩

theorem hs_iff (hHS : MoriwakiHSStatement) (hBig : MoriwakiBigStatement) (hP : PackingStatement) :
    Prov.HS ↔ ArithmeticHilbertSamuelUpperBoundNumberField ∧ HilbertSamuel.G3.Statement ∧ HilbertSamuel.ArithmeticVolumeMultiplicative.Statement := by
  obtain ⟨g1, z1, z2, g6p, -, -⟩ := Giv.hsLinks_of_moriwaki hHS hBig
  exact ⟨fun h => h.2.2.2.2.2.2, fun h =>
    ⟨z1, z2, g1, g6p, ForSecondHalf.G6ppB.of_moriwaki hBig hHS, ForSecondHalf.NefBundleMoriwaki.of_moriwaki hHS hP, h⟩⟩

theorem all_iff (hHS : MoriwakiHSStatement) (hBig : MoriwakiBigStatement) (hP : PackingStatement) :
    Prov.All ↔ (ArithmeticHilbertSamuelUpperBoundNumberField ∧ HilbertSamuel.G3.Statement ∧ HilbertSamuel.ArithmeticVolumeMultiplicative.Statement) ∧
      (ReciprocityTheory.AnForm.P.UnifIntStatement ∧ ReciprocityTheory.AnForm.P.RegGlobalStatement) ∧
        (PushDown.Statement ∧ GrassmannianHeightZTwo.Statement) ∧ SlopeBoundSt := by
  rw [Prov.All, hs_iff hHS hBig hP, an_iff, nineFree_iff hHS hBig]

end GlobalTheory.CompanionTheory.Ar.ProvParts
