import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialBlockDecomposition
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SamePotBlock
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA.Flat

theorem levi_log_norm {e : ℕ} {G : (Fin e → ℂ) → ℂ} {u : Fin e → ℂ} (hG : AnalyticAt ℂ G u) (h0 : G u ≠ 0)
    (w : Fin e → ℂ) : levi (fun y => Real.log ‖G y‖) u w = 0 := by
  have h1 : AnalyticAt ℂ (fun y => Complex.log (G y / G u)) u :=
    (hG.div_const (c := G u)).clog (by simp [div_self h0])
  have h2 : (fun y => Real.log ‖G y‖) =ᶠ[𝓝 u]
      fun y => (Complex.log (G y / G u)).re + Real.log ‖G u‖ * (fun _ => (1 : ℝ)) y := by
    filter_upwards [hG.continuousAt.eventually_ne h0] with y hy
    rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hy) (norm_ne_zero_iff.2 h0)]
    ring
  have h3 : ContDiffAt ℝ 2 (fun y => (Complex.log (G y / G u)).re) u :=
    Complex.reCLM.contDiff.contDiffAt.comp u (h1.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr h2, levi_add_smul _ h3 contDiffAt_const, levi_re_analytic h1]
  simp [levi]

theorem blk_none_of_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j) {p : Ψ × Fin N} (h : (p.2 : ℕ) + 1 = N) :
    M.blk p = none := (M.blk_none p).2 fun hq => hq.2 h

theorem dy_eq_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j) {p : Ψ × Fin N} (h : (p.2 : ℕ) + 1 = N)
    {k : K} (hk : ¬ ∀ p', M.blk p' ≠ some k) : M.dy p k = 0 := by
  unfold FlagModel.dy
  rw [dif_neg hk, blk_none_of_top M h]
  simp

theorem gramLog_top {N : ℕ} (j : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) :
    gramLog (sigForm N j) N g = Real.log ‖g.det‖ := by
  have e : (gramHead (sigForm N j) N g).det = (gramOf (sigForm N j) g).det := by
    unfold gramHead
    exact Matrix.det_submatrix_equiv_self
      (Equiv.subtypeUnivEquiv (p := fun a : Fin N => (a : ℕ) < N) fun a => a.2) _
  have hd : ‖(Matrix.diagonal fun i => ((sigForm N j i : ℝ) : ℂ)).det‖ = 1 := by
    rw [Matrix.det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    unfold sigForm
    split_ifs <;> simp
  unfold gramLog
  rw [e, gramOf, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, hd, Matrix.det_conjTranspose, norm_star,
    mul_one, ← pow_two, Real.log_pow]
  push_cast
  ring

theorem stepPot_top {N : ℕ} {j : ℕ} (hj : j ≤ N) (i : Fin N) (h : (i : ℕ) + 1 = N)
    (g : Matrix (Fin N) (Fin N) ℂ) : stepPot N j i g = Real.log ‖g.det‖ := by
  unfold stepPot
  split_ifs with h1
  · have e1 : N - j + ((i : ℕ) + 1) = N := by omega
    have e2 : N - j = 0 := by omega
    rw [e1, gramLog_top, e2]
    have : gramLog (sigForm N j) 0 g = 0 := by
      unfold gramLog
      haveI : IsEmpty {a : Fin N // (a : ℕ) < 0} := ⟨fun a => by have := a.2; omega⟩
      simp
    rw [this, sub_zero]
  · have e1 : (i : ℕ) + 1 - j = N - j := by omega
    rw [e1, gramLog_top]
    ring

theorem minorIJ_one_self {N : ℕ} (S : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (S.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_one {N : ℕ} (j : ℕ) (i : Fin N) : detFac j i (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
  unfold detFac
  simp only [minorIJ_one_self]
  simp

theorem blockPot_top {N j : ℕ} (hj : j ≤ N) (i : Fin N) (h : (i : ℕ) + 1 = N) {Pi G : Matrix (Fin N) (Fin N) ℂ}
    (hP : IsPeriodGram j Pi G) (hG : IsBlockDiag j G) (hG' : G.PosDef) :
    blockPot j i G 1 = Real.log ‖Pi.det‖ := by
  have := (stepPot_mul_eq_blockPot N j i Pi G 1 hj hP hG hG' isBlockDiag_one (by simp)).2
  rw [mul_one, stepPot_top hj i h, detFac_one, norm_one, Real.log_one, add_zero] at this
  exact this.symm

theorem sameOrbit_symm {K : Type} {ι : K → Type} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun q => ?_⟩
  simp only [inv_mul_cancel_left₀ (hc q.1)]

theorem sameOrbit_trans {K : Type} {ι : K → Type} {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z')
    (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := h'
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), funext fun q => by simp only [mul_assoc]⟩

section Val

variable {Kb : Type} [Fintype Kb] {ιb : Kb → Type} [∀ k, Fintype (ιb k)] {Ω : Type} [Field Ω]

theorem eval_ne_zero_of_not_mem {z : (Σ k, ιb k) → ℂ} {h : MRing ιb} {d : Kb → ℕ} (hh : IsMultiHomog h d)
    (hq : h ∉ mCoordIdeal z) : eval z (map (Int.castRingHom ℂ) h) ≠ 0 := fun e => hq
  (mem_mCoordIdeal_of_aeval_eq_zero z hh (by
    have : aeval z h = eval z (map (Int.castRingHom ℂ) h) := by
      rw [eval_map, aeval_def]
      exact congrArg (fun f => eval₂ f z h) (Subsingleton.elim _ _)
    rw [this, e]))

theorem aeval_ne_zero_of_eval {x : (Σ k, ιb k) → Ω} {z : (Σ k, ιb k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x))
    {h : MRing ιb} {d : Kb → ℕ} (hh : IsMultiHomog h d) (hne : eval z (map (Int.castRingHom ℂ) h) ≠ 0) :
    aeval x h ≠ 0 := fun e => hne (eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero x hh e))

theorem isValueAt_of_orbit {x : (Σ k, ιb k) → Ω} {s : Ω} {d : Kb → ℕ} {g h : MRing ιb} (hg : IsMultiHomog g d)
    (hh : IsMultiHomog h d) (a : aeval x h ≠ 0) (he : aeval x g = s * aeval x h) {z z' : (Σ k, ιb k) → ℂ}
    (ho : SameOrbit z z') (hne : eval z' (map (Int.castRingHom ℂ) h) ≠ 0) :
    IsValueAt x s z (eval z' (map (Int.castRingHom ℂ) g) / eval z' (map (Int.castRingHom ℂ) h)) := by
  obtain ⟨c, hc, rfl⟩ := ho
  have hp : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, a, he, ?_, ?_⟩
  · rw [eval_smul_of_isMultiHomog hh]
    exact mul_ne_zero hp hne
  · rw [eval_smul_of_isMultiHomog hg, eval_smul_of_isMultiHomog hh, mul_div_mul_left _ _ hp]

theorem val_local {n : ℕ} {x : (Σ k, ιb k) → Ω} (Rb : AnLogRes (mCoordIdeal x) ⊤ n) (b₀ : Rb.X) {s : Ω}
    (hs0 : s ≠ 0) (hs : RegAt x (mCoordIdeal (Rb.lift b₀ b₀)) s)
    (hs' : RegAt x (mCoordIdeal (Rb.lift b₀ b₀)) s⁻¹) :
    ∃ (V : Set Rb.X) (f : Rb.X → ℂ), IsOpen V ∧ b₀ ∈ V ∧ Rb.A.HoloOn V f ∧ (∀ b ∈ V, f b ≠ 0) ∧
      ∀ b ∈ V, ∀ z, SameOrbit z (Rb.lift b b) → valAt x s z = f b := by
  obtain ⟨d, g, h, hg, hh, hQ, he⟩ := hs
  obtain ⟨d', g', h', hg', hh', hQ', he'⟩ := hs'
  have hz₀ : Rb.lift b₀ b₀ ∈ mcPts (mCoordIdeal x) := Rb.mem b₀ b₀ (Rb.mem_U b₀)
  have n1 := eval_ne_zero_of_not_mem hh hQ
  have n2 := eval_ne_zero_of_not_mem hh' hQ'
  have a1 := aeval_ne_zero_of_eval hz₀ hh n1
  have a2 := aeval_ne_zero_of_eval hz₀ hh' n2
  let E : MRing ιb → Rb.X → ℂ := fun f b => eval (Rb.lift b₀ b) (map (Int.castRingHom ℂ) f)
  have hE : ∀ f, Rb.A.HoloOn (Rb.U b₀) (E f) := holoOn_eval_lift Rb b₀
  have hC : ∀ f, ContinuousOn (E f) (Rb.U b₀) := fun f b hb =>
    (BlockPot.continuousAt_of_holoOn (hE f) hb).continuousWithinAt
  have hO : ∀ f, IsOpen (Rb.U b₀ ∩ E f ⁻¹' {0}ᶜ) := fun f =>
    (hC f).isOpen_inter_preimage (Rb.isOpen_U b₀) isOpen_compl_singleton
  refine ⟨(Rb.U b₀ ∩ E h ⁻¹' {0}ᶜ) ∩ (Rb.U b₀ ∩ E h' ⁻¹' {0}ᶜ), fun b => E g b / E h b, (hO h).inter (hO h'),
    ⟨⟨Rb.mem_U b₀, n1⟩, ⟨Rb.mem_U b₀, n2⟩⟩, ?_, ?_, ?_⟩
  · intro c u hu
    exact (hE g c u ⟨hu.1, hu.2.1.1⟩).div (hE h c u ⟨hu.1, hu.2.1.1⟩) hu.2.1.2
  · rintro b ⟨⟨hb, hb1⟩, -, hb2⟩ e
    have hm := Rb.mem b₀ b hb
    have v1 : IsValueAt x s (Rb.lift b₀ b) (E g b / E h b) :=
      isValueAt_of_orbit hg hh a1 he ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩ hb1
    have v2 : IsValueAt x s⁻¹ (Rb.lift b₀ b) (E g' b / E h' b) :=
      isValueAt_of_orbit hg' hh' a2 he' ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩ hb2
    have v3 := isValueAt_mul v1 v2
    rw [mul_inv_cancel₀ hs0] at v3
    have v4 : IsValueAt x 1 (Rb.lift b₀ b) 1 :=
      ⟨d, h, h, hh, hh, a1, by rw [one_mul], hb1, (div_self hb1).symm⟩
    have := isValueAt_unique hm v3 v4
    simp only at e
    rw [e, zero_mul] at this
    exact zero_ne_one this
  · rintro b ⟨⟨hb, hb1⟩, -⟩ z hz
    have ho : SameOrbit z (Rb.lift b₀ b) :=
      sameOrbit_trans hz (sameOrbit_symm (Rb.compat b₀ b b ⟨hb, Rb.mem_U b⟩))
    exact valAt_eq (mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal x) ho (Rb.mem b₀ b hb))
      (isValueAt_of_orbit hg hh a1 he ho hb1)

end Val

theorem exists_nhd_off_bdry {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    {s : X → X → ℂ} (hsec : IsSection A L s) {b₀ : X} (h : b₀ ∉ bdry s) :
    ∃ V : Set X, IsOpen V ∧ b₀ ∈ V ∧ V ⊆ (bdry s)ᶜ := by
  have hc : ContinuousOn (s b₀) (L.U b₀) := fun b hb =>
    (BlockPot.continuousAt_of_holoOn (hsec.1 b₀) hb).continuousWithinAt
  refine ⟨_, hc.isOpen_inter_preimage (L.isOpen_U b₀) isOpen_compl_singleton, ⟨L.mem_U b₀, h⟩, ?_⟩
  rintro b ⟨hb, hb'⟩ (e : s b b = 0)
  have h1 := hsec.2 b₀ b b ⟨hb, L.mem_U b⟩
  rw [e, norm_zero, zero_mul] at h1
  exact hb' (norm_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right (Real.exp_pos _).ne'))

theorem holoOn_det {e N : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {V : Set X}
    {P : X → Matrix (Fin N) (Fin N) ℂ} (h : ∀ a b, A.HoloOn V fun x => P x a b) :
    A.HoloOn V fun x => (P x).det := by
  intro c u hu
  have e1 : ((fun x => (P x).det) ∘ (A.chart c).symm) = fun t =>
      ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, P ((A.chart c).symm t) (σ i) i := by
    funext t
    simp only [Function.comp_apply, Matrix.det_apply', Int.cast_inj]
  rw [e1]
  refine Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul ?_
  exact Finset.analyticAt_fun_prod _ fun i _ => h (σ i) i c u hu

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

theorem base_flat {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) {p : Ψ × Fin N} (hN : (p.2 : ℕ) + 1 = N)
    {b₀ : BM.Rb.X} (hb₀ : b₀ ∉ bdry BM.s) :
    ∃ (l : Fin BM.q) (V : Set BM.Rb.X) (f : BM.Rb.X → ℂ), IsOpen V ∧ b₀ ∈ V ∧ V ⊆ BM.O l \ bdry BM.s ∧
      BM.Rb.A.HoloOn V f ∧ (∀ b ∈ V, f b ≠ 0) ∧ ∀ b ∈ V, ∀ z, SameOrbit z (BM.Rb.lift b b) →
        blockPot j p.2 (BM.G l p.1 b) 1 - Real.log ‖valAt M.x ((BM.F l).υ p) z‖ = Real.log ‖f b‖ := by
  obtain ⟨l, hl⟩ := BM.O_cover b₀
  have hbl : b₀ ∈ BM.O l \ bdry BM.s := ⟨hl, hb₀⟩
  have hnone := blk_none_of_top M hN
  obtain ⟨h0, h1, h2⟩ := (BM.good l b₀ hl).2.2 p hnone
  obtain ⟨V₁, f₁, o₁, m₁, H₁, n₁, e₁⟩ := val_local BM.Rb b₀ h0 h1 h2
  obtain ⟨V₂, Pi, m₂, o₂, H₂, P₂⟩ := BM.period l b₀ hbl
  obtain ⟨V₃, o₃, m₃, s₃⟩ := exists_nhd_off_bdry BM.sec hb₀
  have hsub : V₁ ∩ V₂ ∩ V₃ ∩ BM.O l ⊆ BM.O l \ bdry BM.s := fun b hb => ⟨hb.2, s₃ hb.1.2⟩
  have hdet := holoOn_det (H₂ p.1)
  refine ⟨l, V₁ ∩ V₂ ∩ V₃ ∩ BM.O l, fun b => (Pi p.1 b).det / f₁ b, ((o₁.inter o₂).inter o₃).inter (BM.O_open l),
    ⟨⟨⟨m₁, m₂⟩, m₃⟩, hl⟩, hsub, ?_, ?_, ?_⟩
  · intro c u hu
    have hu₁ : (BM.Rb.A.chart c).symm u ∈ V₁ := hu.2.1.1.1
    have hu₂ : (BM.Rb.A.chart c).symm u ∈ V₂ := hu.2.1.1.2
    exact (hdet c u ⟨hu.1, hu₂⟩).div (H₁ c u ⟨hu.1, hu₁⟩) (n₁ _ hu₁)
  · intro b hb
    exact div_ne_zero (P₂ p.1 b hb.1.1.2).1.1.ne_zero (n₁ b hb.1.1.1)
  · intro b hb z hz
    have hbG := BM.G_pos l p.1 b (hsub hb)
    rw [blockPot_top M.j_le p.2 hN (P₂ p.1 b hb.1.1.2) hbG.1 hbG.2, e₁ b hb.1.1.1 z hz, norm_div,
      Real.log_div (norm_ne_zero_iff.2 (P₂ p.1 b hb.1.1.2).1.1.ne_zero) (norm_ne_zero_iff.2 (n₁ b hb.1.1.1))]

def cz (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι k) → ℂ) (k : K) : ℂ :=
  if h : ∀ p', M.blk p' ≠ some k then z ⟨k, F.c ⟨k, h⟩⟩ else 1

theorem coord_ne {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) {l : Fin BM.q} {b : BM.Rb.X}
    (hb : b ∈ BM.O l) {z : (Σ k, ι k) → ℂ} (ho : SameOrbit (basePart M.blk z) (BM.Rb.lift b b))
    (k : NonPluckerBlocks M.blk) : z ⟨k.1, (BM.F l).c k⟩ ≠ 0 := by
  obtain ⟨t, ht, e⟩ := ho
  have h1 : BM.Rb.lift b b ⟨k, (BM.F l).c k⟩ ≠ 0 := fun h => (BM.good l b hb).1 k (by
    show mConeMap _ (X ⟨k, (BM.F l).c k⟩) = 0
    rw [mConeMap, aeval_X, h, map_zero, zero_mul])
  have h2 := congrFun e ⟨k, (BM.F l).c k⟩
  simp only [basePart] at h2
  rw [h2]
  exact mul_ne_zero (ht k) h1

theorem log_hom_eq {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) {p : Ψ × Fin N} (hN : (p.2 : ℕ) + 1 = N)
    {l : Fin BM.q} {b : BM.Rb.X} (hb : b ∈ BM.O l \ bdry BM.s) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) (ho : SameOrbit (basePart M.blk z) (BM.Rb.lift b b)) :
    ∃ zb, SameOrbit zb (BM.Rb.lift b b) ∧ Real.log ((BM.hom p).h z) =
      ∑ k, (M.dy p k : ℝ) * Real.log ‖cz M (BM.F l) z k‖ + blockPot j p.2 (BM.G l p.1 b) 1 -
        Real.log ‖valAt M.x ((BM.F l).υ p) zb‖ := by
  have hc : ∀ k, cz M (BM.F l) z k ≠ 0 := by
    intro k
    unfold cz
    split_ifs with h
    · exact coord_ne BM hb.1 ho ⟨k, h⟩
    · exact one_ne_zero
  set t : K → ℂ := fun k => (cz M (BM.F l) z k)⁻¹ with ht
  have ht0 : ∀ k, t k ≠ 0 := fun k => inv_ne_zero (hc k)
  set z' : (Σ k, ι k) → ℂ := fun q => t q.1 * z q with hz'
  have hm : z' ∈ mcPts (mCoordIdeal y) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) ⟨t, ht0, rfl⟩ hz
  have ho' : SameOrbit (basePart M.blk z') (BM.Rb.lift b b) := by
    refine sameOrbit_trans ⟨fun k => t k.1, fun k => ht0 _, rfl⟩ ho
  have hone : ∀ k, basePart M.blk z' ⟨k, (BM.F l).c k⟩ = 1 := by
    intro k
    have e : cz M (BM.F l) z k.1 = z ⟨k.1, (BM.F l).c k⟩ := dif_pos k.2
    show t k.1 * z ⟨k.1, (BM.F l).c k⟩ = 1
    rw [ht]
    simp only
    rw [e]
    exact inv_mul_cancel₀ (coord_ne BM hb.1 ho k)
  have h1 := (BM.induced l b hb p z' hm ho' hone 1 isBlockDiag_one (by simp)).2 (blk_none_of_top M hN)
  have h2 := (BM.hom p).smul t z ht0
  have hpos := (BM.hom p).pos z hz.1
  refine ⟨_, ho', ?_⟩
  rw [← sub_eq_zero]
  have h3 : Real.log ((BM.hom p).h z') = ∑ k, (M.dy p k : ℝ) * Real.log ‖t k‖ + Real.log ((BM.hom p).h z) := by
    show Real.log ((BM.hom p).h fun q => t q.1 * z q) = _
    rw [h2, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (ht0 k))) hpos.ne',
      Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (ht0 k))]
    simp only [Real.log_zpow, BM.hom_deg]
  have h4 : ∑ k, (M.dy p k : ℝ) * Real.log ‖t k‖ = - ∑ k, (M.dy p k : ℝ) * Real.log ‖cz M (BM.F l) z k‖ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ht, norm_inv, Real.log_inv]
    ring
  rw [h3, h4] at h1
  linarith

theorem torus_move {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) {p : Ψ × Fin N} (hN : (p.2 : ℕ) + 1 = N)
    {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)] {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)}
    (hb : IsBlockMap κ v) (hr : ∀ k, (∀ p', M.blk p' ≠ some k) → k ∈ Set.range κ) {e : ℕ}
    (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (ph : R.X → ℝ)
    (H1 : ∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x)))
    (H2 : ∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x →
      Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x)
    {x₀ t : R.X} (ht : t ∈ R.U x₀) (hbd : pr t ∉ bdry BM.s) :
    ∃ z₁ ∈ mcPts (mCoordIdeal y), z₁ ∘ v = R.lift x₀ t ∧ SameOrbit (basePart M.blk z₁) (BM.Rb.lift (pr t) (pr t)) ∧
      Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ t)) + ph t = Real.log ((BM.hom p).h z₁) := by
  obtain ⟨z, hz, hzv, ho⟩ := H1 t
  obtain ⟨c, hc, ec⟩ := R.compat x₀ t t ⟨ht, R.mem_U t⟩
  set ct : K → ℂ := Function.extend κ c 1 with hct
  have hκ : ∀ k, ct (κ k) = c k := fun k => hb.1.extend_apply _ _ _
  have hct0 : ∀ k, ct k ≠ 0 := by
    intro k
    by_cases hk : ∃ k', κ k' = k
    · obtain ⟨k', rfl⟩ := hk
      rw [hκ]
      exact hc k'
    · rw [hct, Function.extend_apply' _ _ _ hk]
      exact one_ne_zero
  have hm : (fun q => ct q.1 * z q) ∈ mcPts (mCoordIdeal y) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) ⟨ct, hct0, rfl⟩ hz
  have hv : (fun q => ct q.1 * z q) ∘ v = R.lift x₀ t := by
    funext q
    have e1 := congrFun ec q
    have e2 := congrFun hzv q
    simp only [Function.comp_apply] at e2 ⊢
    rw [e1, hb.2.2.1 q, hκ, e2]
  have ha : ∀ k, k ∉ Set.range κ → M.dy p k = 0 := fun k hk => dy_eq_zero M hN fun h => hk (hr k h)
  refine ⟨fun q => ct q.1 * z q, hm, hv, sameOrbit_trans ⟨fun k => ct k.1, fun k => hct0 _, rfl⟩ ho, ?_⟩
  have e1 : refNorm (fun k => M.dy p (κ k)) (R.lift x₀ t) = refNorm (M.dy p) fun q => ct q.1 * z q := by
    rw [← hv]
    exact (BlockPot.refNorm_block hb ha _).symm
  have e2 : refNorm (M.dy p) (fun q => ct q.1 * z q) = (∏ k, ‖ct k‖ ^ M.dy p k) * refNorm (M.dy p) z :=
    refNorm_smul _ ct z
  have e3 := (BM.hom p).smul ct z hct0
  rw [BM.hom_deg] at e3
  have hP : (∏ k, ‖ct k‖ ^ M.dy p k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hct0 k))
  rw [e1, e2, e3, Real.log_mul hP (refNorm_pos _ hz.1).ne', Real.log_mul hP ((BM.hom p).pos z hz.1).ne',
    H2 t hbd z hz hzv, fsHerm_h]
  ring

end Flag

section Main

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

theorem local_log_norm {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) {p : Ψ × Fin N}
    (hN : (p.2 : ℕ) + 1 = N) {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)] {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) (hr : ∀ k, (∀ p', M.blk p' ≠ some k) → k ∈ Set.range κ)
    {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr)
    (ph : R.X → ℝ)
    (H1 : ∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x)))
    (H2 : ∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x →
      Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x)
    {x₀ t₀ : R.X} (ht₀ : t₀ ∈ R.U x₀) (hbd : pr t₀ ∉ bdry BM.s) :
    ∃ (W : Set R.X) (H : R.X → ℂ), IsOpen W ∧ t₀ ∈ W ∧ R.A.HoloOn W H ∧ (∀ t ∈ W, H t ≠ 0) ∧
      ∀ t ∈ W, Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ t)) + ph t = Real.log ‖H t‖ := by
  obtain ⟨l, V, f, oV, mV, sV, HV, nV, eV⟩ := base_flat BM hN hbd

  have hw : ∀ k : NonPluckerBlocks M.blk, ∃ q, v q = ⟨k.1, (BM.F l).c k⟩ := fun k => hb.2.2.2 _ (hr k.1 k.2)
  choose w hw using hw
  have hE : ∀ k, R.A.HoloOn (R.U x₀) fun t => R.lift x₀ t (w k) := fun k => R.holo x₀ (w k)
  have hO : ∀ k, IsOpen (R.U x₀ ∩ (fun t => R.lift x₀ t (w k)) ⁻¹' {0}ᶜ) := fun k =>
    ContinuousOn.isOpen_inter_preimage (fun t ht => (BlockPot.continuousAt_of_holoOn (hE k) ht).continuousWithinAt)
      (R.isOpen_U x₀) isOpen_compl_singleton
  set W₀ : Set R.X := R.U x₀ ∩ pr ⁻¹' V with hW₀
  set W : Set R.X := W₀ ∩ ⋂ k, (R.U x₀ ∩ (fun t => R.lift x₀ t (w k)) ⁻¹' {0}ᶜ) with hW
  have oW : IsOpen W := ((R.isOpen_U x₀).inter (oV.preimage hp.1)).inter (isOpen_iInter_of_finite hO)
  have hbase : ∀ t ∈ W, ∃ z₁ ∈ mcPts (mCoordIdeal y), z₁ ∘ v = R.lift x₀ t ∧
      SameOrbit (basePart M.blk z₁) (BM.Rb.lift (pr t) (pr t)) ∧
      Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ t)) + ph t = Real.log ((BM.hom p).h z₁) :=
    fun t ht => torus_move BM hN hb hr R pr ph H1 H2 ht.1.1 (sV ht.1.2).2
  let ℓ : K → R.X → ℂ := fun k t => if h : ∀ p', M.blk p' ≠ some k then R.lift x₀ t (w ⟨k, h⟩) else 1
  have hℓ0 : ∀ t ∈ W, ∀ k, ℓ k t ≠ 0 := by
    intro t ht k
    simp only [ℓ]
    split_ifs with h
    · exact (Set.mem_iInter.1 ht.2 ⟨k, h⟩).2
    · exact one_ne_zero
  have hℓH : ∀ k, R.A.HoloOn W (ℓ k) := by
    intro k c u hu
    by_cases h : ∀ p', M.blk p' ≠ some k
    · have e : ℓ k ∘ (R.A.chart c).symm = (fun t => R.lift x₀ t (w ⟨k, h⟩)) ∘ (R.A.chart c).symm := by
        funext t
        simp only [ℓ, Function.comp_apply, dif_pos h]
      rw [e]
      exact hE ⟨k, h⟩ c u ⟨hu.1, hu.2.1.1⟩
    · have e : ℓ k ∘ (R.A.chart c).symm = fun _ => 1 := by
        funext t
        simp only [ℓ, Function.comp_apply, dif_neg h]
      rw [e]
      exact analyticAt_const
  have hfH : R.A.HoloOn W fun t => f (pr t) :=
    fun c u hu => BlockPot.holoOn_comp hp HV c u ⟨hu.1, hu.2.1.2⟩
  have hcz : ∀ z₁, ∀ t, z₁ ∘ v = R.lift x₀ t → ∀ k, cz M (BM.F l) z₁ k = ℓ k t := by
    intro z₁ t hz k
    simp only [cz, ℓ]
    split_ifs with h
    · rw [← hz, Function.comp_apply, hw]
    · rfl
  have mW : t₀ ∈ W := by
    refine ⟨⟨ht₀, mV⟩, Set.mem_iInter.2 fun k => ⟨ht₀, ?_⟩⟩
    obtain ⟨z₁, -, hz, ho, -⟩ := torus_move BM hN hb hr R pr ph H1 H2 ht₀ hbd
    have := coord_ne BM (sV mV).1 ho k
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [← hz, Function.comp_apply, hw]
    exact this
  refine ⟨W, fun t => (∏ k, ℓ k t ^ M.dy p k) * f (pr t), oW, mW, ?_, ?_, ?_⟩
  · intro c u hu
    refine AnalyticAt.mul (Finset.analyticAt_fun_prod _ fun k _ => ?_) (hfH c u hu)
    exact (hℓH k c u hu).zpow (hℓ0 _ hu.2 k)
  · intro t ht
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hℓ0 t ht k)) (nV _ ht.1.2)
  · intro t ht
    obtain ⟨z₁, hz₁, hv, ho, he⟩ := hbase t ht
    obtain ⟨zb, hzb, hf⟩ := log_hom_eq BM hN (sV ht.1.2) hz₁ ho
    have hb' := eV _ ht.1.2 zb hzb
    rw [he, hf, norm_mul, norm_prod,
      Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => norm_ne_zero_iff.2 (zpow_ne_zero _ (hℓ0 t ht k)))
        (norm_ne_zero_iff.2 (nV _ ht.1.2)),
      Real.log_prod fun k _ => norm_ne_zero_iff.2 (zpow_ne_zero _ (hℓ0 t ht k)), ← hb']
    simp only [norm_zpow, Real.log_zpow, hcz z₁ t hv]
    ring

end Main

theorem flat_off_boundary : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (BM : BaseMetric M n) (p : Ψ × Fin N), (p.2 : ℕ) + 1 = N → ∀ (Kk : Type) [Fintype Kk] (ιk : Kk → Type)
    [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v →
    (∀ k, (∀ p', M.blk p' ≠ some k) → k ∈ Set.range κ) →
    ∀ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr)
      (ph : R.X → ℝ),
    (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))) →
    (∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x →
      Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x) →
    IsPshOn R.A (bdry fun x y => BM.s (pr x) (pr y))ᶜ
        (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph) ∧
      IsPshOn R.A (bdry fun x y => BM.s (pr x) (pr y))ᶜ
        ((potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph).rsmul (-1)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p hN Kk _ ιk _ κ v hb hr e R pr hp ph H1 H2
  have key : ∀ (x₀ : R.X) (c : Fin R.A.n) (u : Fin e → ℂ), u ∈ (R.A.chart c).target →
      (R.A.chart c).symm u ∈ R.U x₀ → (R.A.chart c).symm u ∉ bdry (fun x y => BM.s (pr x) (pr y)) →
      ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G u ∧ G u ≠ 0 ∧
        (fun t => Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ ((R.A.chart c).symm t))) +
          ph ((R.A.chart c).symm t)) =ᶠ[𝓝 u] fun t => Real.log ‖G t‖ := by
    intro x₀ c u hu h1 h2
    obtain ⟨W, H, oW, mW, HW, nW, eW⟩ := local_log_norm BM hN hb hr R pr hp ph H1 H2 h1 h2
    refine ⟨H ∘ (R.A.chart c).symm, HW c u ⟨hu, mW⟩, nW _ mW, ?_⟩
    filter_upwards [((R.A.chart c).isOpen_inter_preimage_symm oW).mem_nhds ⟨hu, mW⟩] with t ht
    exact eW _ ht.2
  constructor
  · intro x₀ c u hu w
    obtain ⟨G, hG, hG0, hE⟩ := key x₀ c u hu.1 hu.2.1.1 hu.2.2
    refine (levi_congr (φ := (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph).φ x₀ ∘
      (R.A.chart c).symm) hE w).trans_ge ?_
    rw [levi_log_norm hG hG0]
  · intro x₀ c u hu w
    obtain ⟨G, hG, hG0, hE⟩ := key x₀ c u hu.1 hu.2.1.1 hu.2.2
    have hE' : ((potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph).rsmul (-1)).φ x₀ ∘
        (R.A.chart c).symm =ᶠ[𝓝 u] fun t => Real.log ‖(G t)⁻¹‖ := by
      filter_upwards [hE] with t ht
      have ht' : ((potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun ph).rsmul (-1)).φ x₀
          ((R.A.chart c).symm t) = -1 * (Real.log (refNorm (fun k => M.dy p (κ k)) (R.lift x₀ ((R.A.chart c).symm t))) +
            ph ((R.A.chart c).symm t)) := rfl
      rw [Function.comp_apply, ht', ht, norm_inv, Real.log_inv]
      ring
    rw [levi_congr hE' w, levi_log_norm (G := fun t => (G t)⁻¹) (hG.inv hG0) (inv_ne_zero hG0)]

end GlobalTheory.CompanionTheory.Ar.PB.FA.Flat
