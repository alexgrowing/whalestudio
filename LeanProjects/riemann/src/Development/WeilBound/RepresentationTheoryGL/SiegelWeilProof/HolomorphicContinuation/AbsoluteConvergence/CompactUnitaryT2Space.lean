import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RootsBound

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.Vac

private theorem vacOut_of'_lemma (n : ℕ) : CompactSpace (KR n) := by
  have hb : ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ, Matrix.conjTranspose g * g = 1 → ∀ i j, ‖g i j‖ ≤ 1 := by
    intro g hg i j
    exact entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.mpr hg) i j
  have hS : IsCompact {g : M2 n | InG g ∧ Matrix.conjTranspose g * g = 1} := by
    have hbox : IsCompact (Set.pi univ fun _ : Fin n ⊕ Fin n => Set.pi univ fun _ : Fin n ⊕ Fin n => Metric.closedBall (0 : ℂ) 1) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
    refine hbox.of_isClosed_subset ?_ ?_
    · refine IsClosed.inter ?_ ?_
      · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const
      · exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
    · intro g hg i _ j _
      simpa using hb g hg.2 i j
  have hcl : IsClosed (range fun k : KR n => mR (k : GR n)) := by
    convert hS.isClosed using 1
    ext g
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k.1.2, k.2.2⟩
    · rintro ⟨hG, hg⟩
      let u : GL (Fin n ⊕ Fin n) ℂ := ⟨g, Matrix.conjTranspose g, mul_eq_one_comm.mp hg, hg⟩
      exact ⟨⟨⟨u, hG⟩, ⟨hG, hg⟩⟩, rfl⟩
  constructor
  rw [(kr_inducing n).isCompact_iff, Set.image_univ]
  refine hS.of_isClosed_subset hcl ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨k.1.2, k.2.2⟩

theorem vacOut_of' (hD : CayleyBlocksInvertible) (hLO : LocOp) (hHP : HolParam) (hTS : ThSph) : VacOut := by
  intro m n ε c t p q e sL ρ hL hGS G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I Λ hG
  haveI := vacOut_of'_lemma n
  letI : MeasurableSpace (KR n) := borel _
  haveI : BorelSpace (KR n) := ⟨rfl⟩
  let μ : Measure (KR n) := Measure.haarMeasure ⊤
  haveI : μ.IsHaarMeasure := by infer_instance
  haveI : IsProbabilityMeasure μ := ⟨by simpa using Measure.haarMeasure_self (G := KR n) (K₀ := ⊤)⟩
  obtain ⟨ψ, a, b, nb, cz, hψ, hnb, hnbc, hcz, hcz0, hid⟩ := hLO n p q e hGS μ
  obtain ⟨U, d, E, σ, hU, hR, hs, hd, hEd, hEc, hEi, hEs⟩ := hG.eis
  have hψc := hψ.1
  have hψs := hψ.2.1
  obtain ⟨d1, hdd, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd d hd s₀
  have hd1 : Polynomial.eval s₀ d1 ≠ 0 := fun h => hnd (Polynomial.dvd_iff_isRoot.mpr h)
  set k₀ := d.rootMultiplicity s₀
  have hdeval : ∀ z, Polynomial.eval z d = (z - s₀) ^ k₀ * Polynomial.eval z d1 := by
    intro z
    conv_lhs => rw [hdd]
    simp [Polynomial.eval_mul, Polynomial.eval_pow]
  have hTE : ∀ z ∈ U, ∀ g, Vac.Top μ ι p q e a b nb ψ (E z) g = cz (z - s₀) * E z g :=
    top_E μ hL hG hD hHP hnbc hψc hψs hcz hid hU hR hd hEd hEc hEs
  have hTI : ∀ g, Vac.Top μ ι p q e a b nb ψ (I 1) g = cz 0 * I 1 g :=
    top_theta μ hD hG.ιcont hnbc hψc hψs hid (I 1) hG.Icont
      (fun g y => hTS m n ε c t p q e sL ρ hL G Pp Γ ι s₀ Ht sec I Λ hG μ g y)
  have hloc := lam_local banachHol factorL hG hU hR hs hd hEd hEc hEi (fun z hz g => (hEs z hz).2 g)
  have hloc' : ∀ l ∈ Λ, ∃ H : ℂ → ℂ, ContinuousAt H s₀ ∧ H s₀ = l (I 1) ∧
      ∀ᶠ z in 𝓝[≠] s₀, l (E z) = (z - s₀) ^ k₀ * Polynomial.eval z d1 * H z := by
    intro l hl
    obtain ⟨H, hHa, hH0, hHe⟩ := hloc l hl
    refine ⟨H, hHa.continuousAt, hH0, ?_⟩
    filter_upwards [hHe] with z hz
    rw [hz, hdeval]
  obtain ⟨Ek, hEkc, hEkd, hEk, hEk0⟩ := core Γ Λ (Vac.Top μ ι p q e a b nb ψ) (I 1) s₀ U hU hs E cz k₀
    (fun z => Polynomial.eval z d1) dslopeFam hcz.continuous hcz0 (Polynomial.continuous d1).continuousAt
    hG.Λadd (fun l hl F hFc hFd hFi => lam_cont banachHol factorL hG l hl hU hs F hFc hFd hFi) hloc'
    (fun F hF hFi hΛ g => top_sing μ hG hψ hnb F hF hFi hΛ g)
    (fun a' F F' hF hF' g => top_linear μ hD hG.ιcont hnbc hψc hψs F F' hF hF' a' g)
    hG.Icont hG.Ileft hTI
    (fun F hFc hFd g => (top_hol μ hD hHP hG.ιcont hnbc hψc hψs hU F hFc hFd g).continuousOn)
    hEc hEd hEi hTE
  have hnear : ∀ᶠ z in 𝓝 s₀, z ∈ U ∧ Polynomial.eval z d1 ≠ 0 :=
    (show ∀ᶠ z in 𝓝 s₀, z ∈ U from hU.mem_nhds hs).and
      ((Polynomial.continuous d1).continuousAt.eventually_ne hd1)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hsub : Metric.ball s₀ r ⊆ U := fun z hz => (hball hz).1
  have hFd : ∀ g, DifferentiableOn ℂ (fun z => Ek z g / Polynomial.eval z d1) (Metric.ball s₀ r) :=
    fun g => ((hEkd g).mono hsub).div (Polynomial.differentiable d1).differentiableOn
      (fun z hz => (hball hz).2)
  obtain ⟨σ2, hσ2⟩ := roots_bound d hd
  have hmain : ∀ g, ∀ z ∈ Metric.ball s₀ r, GlobalTheory.Cont.HolValueAt
      (fun w => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (w - s₀) * sec 1 x) g) z
      (Ek z g / Polynomial.eval z d1) := by
    intro g z hz
    have hext : GlobalTheory.Cont.IsExtAt
        (fun w => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (w - s₀) * sec 1 x) g) z
        (fun w => E w g / Polynomial.eval w d) := by
      refine ⟨U, hsub hz, hR, ?_, ?_⟩
      · intro w hw
        exact (((hEd g).analyticAt (hU.mem_nhds hw)).meromorphicAt).div
          ((Polynomial.differentiable d).analyticAt w).meromorphicAt
      · refine ⟨max σ σ2, fun w hw => ?_⟩
        have hw1 : σ < w.re := lt_of_le_of_lt (le_max_left _ _) hw
        have hw2 : σ2 < w.re := lt_of_le_of_lt (le_max_right _ _) hw
        show E w g / Polynomial.eval w d = _
        rw [(hEs w hw1).2 g, mul_div_cancel_left₀ _ (hσ2 w hw2)]
    rw [hext.holValueAt_iff]
    have hFc : ContinuousAt (fun w => Ek w g / Polynomial.eval w d1) z :=
      (hFd g).continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hz)
    refine (hFc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    have hev : ∀ᶠ w in 𝓝[≠] z, w ∈ Metric.ball s₀ r ∧ w ≠ s₀ := by
      by_cases hzs : z = s₀
      · subst hzs
        exact eventually_mem_ne z _ Metric.isOpen_ball hz
      · exact nhdsWithin_le_nhds ((Metric.isOpen_ball.inter isOpen_ne).mem_nhds ⟨hz, hzs⟩)
    filter_upwards [hev] with w hw
    have hpow : (w - s₀) ^ k₀ ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hw.2)
    show Ek w g / Polynomial.eval w d1 = E w g / Polynomial.eval w d
    rw [hEk w (hsub hw.1) g, hdeval w, mul_div_mul_left _ _ hpow]
  have hval : ∀ g, Ek s₀ g / Polynomial.eval s₀ d1 = I 1 g := fun g => by
    rw [hEk0 g, mul_div_cancel_left₀ _ hd1]
  refine ⟨r, 0, fun z g => Ek z g / Polynomial.eval z d1, hr, subset_union_right, ?_, hFd, hval, ?_, hmain⟩
  · exact (hEkc.mono (prod_mono hsub subset_rfl)).div
      ((Polynomial.continuous d1).comp continuous_fst).continuousOn (fun y hy => (hball hy.1).2)
  · intro g
    have h0 := hmain g s₀ (Metric.mem_ball_self hr)
    rwa [hval g] at h0

end PositivityTheory.Rg.Sw.AbsSt
