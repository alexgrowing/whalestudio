import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightC
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ImportsAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMap

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw GlobalTheory.Cont

section
variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {G : Type} [Group G] [TopologicalSpace G] {Pp Γ : Subgroup G} {ι : GR n →* G}
  {s₀ : ℂ} {Ht : G → ℝ≥0} {sec I : PX m n →ₗ[ℂ] (G → ℂ)}

theorem I_eq_of_sL' (hS : SecZero) (hLC : LC) (hL : LocData ε c t p q e sL ρ) (hD : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I)
    {Q Q' : PX m n} (h : ∀ y, sL Q y = sL Q' y) (g : G) : I Q g = I Q' g := by
  have hN : NullSec ε c (Q - Q') :=
    (hS m n ε c t p q e sL ρ hL (Q - Q')).2 (fun y => by simp [map_sub, h y])
  have h0 := hLC m n ε c hL.cpos ((LinearMap.proj g).comp I)
    (fun a b P => by simpa using hD.Iinv g a b P) (Q - Q') hN
  simp [map_sub, sub_eq_zero] at h0
  exact h0

theorem hz_comb' (hD : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) {N : ℕ} {P : PX m n} {QQ : Fin N → PX m n} {cc : Fin N → ℂ}
    (hP : ∀ y, sL P y = ∑ j, cc j * sL (QQ j) y) (z : ℂ) (x : G) :
    hz Ht sec s₀ z P x = ∑ j, cc j * hz Ht sec s₀ z (QQ j) x := by
  obtain ⟨x', y, S, r, -, hx, hsec⟩ := hD.split x
  have key : ∀ P' : PX m n, sec P' x = S * sL P' y := by
    intro P'
    have := (hsec y).2 P'
    rw [← hx] at this
    exact this
  simp only [hz, key, hP, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

end

theorem mulVec_sum' {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) (j : Fin N) :
    ∑ i, A j i * ∑ l, B i l * v l = ∑ l, (A * B) j l * v l := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

private theorem ev_ne_lemma {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a : ℂ} (ha : f a ≠ 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
  rcases (hf.analyticAt z).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hA : AnalyticOnNhd ℂ f Set.univ := fun w _ => hf.analyticAt w
    exact ha (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z) h (Set.mem_univ a))
  · exact h

private theorem merExt_lemma_2 {h F : ℂ → ℂ} {U : Set ℂ} {σ : ℝ} (hU : IsRightDomain U)
    (hF : MeromorphicOn F U) (hev : ∀ z, ∀ᶠ w in 𝓝[≠] z, σ < w.re → h w = F w) :
    IsMerExt h U (fun z => if σ < z.re then h z else F z) := by
  refine ⟨hU, fun z hz => (hF z hz).congr ?_, σ, fun z hz => ?_⟩
  · filter_upwards [hev z] with w hw
    split_ifs with h1
    · exact (hw h1).symm
    · rfl
  · have : σ < z.re := hz
    simp [this]

private theorem diffDet_lemma_3 {N : ℕ} {A : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ i j, Differentiable ℂ fun w => A w i j) :
    Differentiable ℂ fun w => (A w).det := by
  have e : (fun w => (A w).det) = fun w => ∑ σ : Equiv.Perm (Fin N),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A w (σ i) i := funext fun w => Matrix.det_apply' _
  rw [e]
  fun_prop

private theorem diffAdj_lemma_4 {N : ℕ} {A : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ i j, Differentiable ℂ fun w => A w i j) (i j : Fin N) :
    Differentiable ℂ fun w => (A w).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  apply diffDet_lemma_3
  intro k l
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiable_const _
  · exact h k l

theorem genCore_of (hP : ProjOp) (hT : TSGenC) (hB : Basis) (hFar : FarRightC) (hS : SecZero) (hLC : LC)
    (hH : HolParam) (hG : Glue) : GenCore := by
  intro m n ε c t p q e sL ρ hL G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I hD hV P g
  show HolValueAt (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z P) g) s₀ (I P g)
  letI : MeasurableSpace (KR n) := borel (KR n)
  haveI : BorelSpace (KR n) := ⟨rfl⟩
  obtain ⟨W, hWfin, hPW, hWst, -⟩ := hL.kfin P
  obtain ⟨ν, κ, hν, hκ, hrep, hproj⟩ := hP m n ε c t p q e sL ρ hL W hWfin hWst
  haveI := hν
  obtain ⟨N, yy, QQ, cc, M, hQW, hPsum, hM0, hMd, hF0, hMrel⟩ :=
    hB m n ε c t p q e sL ρ hL W hWfin hWst ν κ hν hκ hrep hproj P hPW
  obtain ⟨σF, -, hFsum, hFrel⟩ := hFar m n ε c t p q e sL ρ hL G Pp Γ ι s₀ Ht sec I hD
  obtain ⟨U, d, E, σE, hUo, hUr, hs₀U, hd0, hEd, hEc, -, hEfar⟩ := hD.eis
  obtain ⟨r, Fv, hr, hFvc, hFvd, hFv0, hFvh⟩ := hV
  have hdd : Differentiable ℂ fun z => d.eval z := Polynomial.differentiable d
  obtain ⟨a, ha⟩ : ∃ a, d.eval a ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hd0 (Polynomial.funext fun x => by simpa using hc x)
  have hMdiff : ∀ i j, Differentiable ℂ fun z => M (z - s₀) i j :=
    fun i j => (hMd i j).comp (differentiable_id.sub_const s₀)
  have hDt : Differentiable ℂ fun z => (M (z - s₀)).det := diffDet_lemma_3 hMdiff
  have hadj : ∀ j i, Differentiable ℂ fun z => (M (z - s₀)).adjugate j i := diffAdj_lemma_4 hMdiff
  have hιc : ∀ i, Continuous fun y : KR n × ℂ => g * ι (↑y.1 * yy i) := fun i =>
    continuous_const.mul (hD.ιcont.comp ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Fin N → ℂ → ℂ, ∀ i z, Ψ i z = ∫ k, κ k * E z (g * ι (↑k * yy i)) ∂ν :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : Fin N → ℂ → ℂ, ∀ i z, Λ i z = ∫ k, κ k * Fv z (g * ι (↑k * yy i)) ∂ν :=
    ⟨_, fun _ _ => rfl⟩
  have hΨU : ∀ i, DifferentiableOn ℂ (Ψ i) U := by
    intro i
    have hc : ContinuousOn (fun y : KR n × ℂ => κ y.1 * E y.2 (g * ι (↑y.1 * yy i))) (Set.univ ×ˢ U) := by
      refine (hκ.comp continuous_fst).continuousOn.mul ?_
      exact hEc.comp (continuous_snd.prodMk (hιc i)).continuousOn (fun y hy => ⟨hy.2, Set.mem_univ _⟩)
    have := (hH (KR n) ν Set.univ isCompact_univ (by simp) U
      (fun k z => κ k * E z (g * ι (↑k * yy i))) hUo hc (fun k _ => (hEd _).const_mul (κ k))).1
    convert this using 1
    funext z
    exact hΨ i z
  have hΛB : ∀ i, DifferentiableOn ℂ (Λ i) (Metric.ball s₀ r) := by
    intro i
    have hc : ContinuousOn (fun y : KR n × ℂ => κ y.1 * Fv y.2 (g * ι (↑y.1 * yy i)))
        (Set.univ ×ˢ Metric.ball s₀ r) := by
      refine (hκ.comp continuous_fst).continuousOn.mul ?_
      exact hFvc.comp (continuous_snd.prodMk (hιc i)).continuousOn (fun y hy => ⟨hy.2, Set.mem_univ _⟩)
    have := (hH (KR n) ν Set.univ isCompact_univ (by simp) (Metric.ball s₀ r)
      (fun k z => κ k * Fv z (g * ι (↑k * yy i))) Metric.isOpen_ball hc
      (fun k _ => (hFvd _).const_mul (κ k))).1
    convert this using 1
    funext z
    exact hΛ i z
  have key : ∀ w ∈ Metric.ball s₀ r, w ∈ U → d.eval w ≠ 0 → ∀ x, Fv w x = E w x / d.eval w := by
    intro w hwB hwU hdw x
    have hev : ∀ z, ∀ᶠ v in 𝓝[≠] z, σE < v.re →
        GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ v 1) x = E v x / d.eval v := fun z =>
      (ev_ne_lemma hdd ha z).mono fun v hv hre => by
        rw [(hEfar v hre).2 x, mul_div_cancel_left₀ _ hv]
        rfl
    have hmer : MeromorphicOn (fun z => E z x / d.eval z) U := fun z hz =>
      ((hEd x).analyticAt (hUo.mem_nhds hz)).meromorphicAt.div (hdd.analyticAt z).meromorphicAt
    have hext := (merExt_lemma_2 hUr hmer hev).isExtAt hwU
    have h1 := hext.holValueAt_iff.1 (hFvh x w hwB)
    have h2 : Tendsto (fun z => E z x / d.eval z) (𝓝[≠] w) (𝓝 (E w x / d.eval w)) :=
      (((hEd x).continuousOn.continuousAt (hUo.mem_nhds hwU)).div
        hdd.continuous.continuousAt hdw).tendsto.mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique h1 (h2.congr' ?_)
    filter_upwards [hev w] with v hv
    split_ifs with hh
    · exact (hv hh).symm
    · rfl
  have hΛ0 : ∀ j, Λ j s₀ = I (QQ j) g := by
    intro j
    rw [hΛ]
    simp only [hFv0]
    exact hT m n ε c t p q e sL ρ hL G Pp Γ ι s₀ Ht sec I hD W hWfin hWst ν κ hν hκ hrep hproj g
      (yy j) (QQ j) (hQW j) (hF0 j)
  have hIP : ∑ j, cc j * I (QQ j) g = I P g := by
    have hs : ∀ y, sL P y = sL (∑ j, cc j • QQ j) y := fun y => by
      rw [hPsum y]
      simp [map_sum, Finset.sum_apply]
    rw [I_eq_of_sL' hS hLC hL hD hs g]
    simp [map_sum, Finset.sum_apply]
  obtain ⟨NumL, hNumL⟩ : ∃ F : ℂ → ℂ, ∀ z,
      F z = ∑ j, cc j * ∑ i, (M (z - s₀)).adjugate j i * Λ i z := ⟨_, fun _ => rfl⟩
  obtain ⟨Num, hNum⟩ : ∃ F : ℂ → ℂ, ∀ z,
      F z = ∑ j, cc j * ∑ i, (M (z - s₀)).adjugate j i * Ψ i z := ⟨_, fun _ => rfl⟩
  have hNumU : DifferentiableOn ℂ Num U := by
    rw [show Num = fun z => ∑ j, cc j * ∑ i, (M (z - s₀)).adjugate j i * Ψ i z from funext hNum]
    exact DifferentiableOn.fun_sum fun j _ => (DifferentiableOn.fun_sum fun i _ =>
      (hadj j i).differentiableOn.mul (hΨU i)).const_mul (cc j)
  have hNumLB : DifferentiableOn ℂ NumL (Metric.ball s₀ r) := by
    rw [show NumL = fun z => ∑ j, cc j * ∑ i, (M (z - s₀)).adjugate j i * Λ i z from funext hNumL]
    exact DifferentiableOn.fun_sum fun j _ => (DifferentiableOn.fun_sum fun i _ =>
      (hadj j i).differentiableOn.mul (hΛB i)).const_mul (cc j)
  have hval : NumL s₀ / (M (s₀ - s₀)).det = I P g := by
    rw [hNumL, ← hIP]
    simp [hM0, Matrix.adjugate_one, Matrix.one_apply, hΛ0]
  have hΩc : ContinuousAt (fun z => NumL z / (M (z - s₀)).det) s₀ :=
    (hNumLB.continuousOn.continuousAt (Metric.ball_mem_nhds s₀ hr)).div
      hDt.continuous.continuousAt (by simp [hM0])
  have hformΩ : ∀ᶠ w in 𝓝[≠] s₀,
      Num w / (d.eval w * (M (w - s₀)).det) = NumL w / (M (w - s₀)).det := by
    filter_upwards [ev_ne_lemma hdd ha s₀, nhdsWithin_le_nhds
      (Filter.inter_mem (Metric.ball_mem_nhds s₀ hr) (hUo.mem_nhds hs₀U))] with w hdw hw
    have hΨw : ∀ i, Ψ i w = d.eval w * Λ i w := by
      intro i
      rw [hΨ, hΛ, ← integral_const_mul]
      congr 1
      funext k
      rw [key w hw.1 hw.2 hdw]
      field_simp
    have : Num w = d.eval w * NumL w := by
      rw [hNum, hNumL]
      simp only [hΨw, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [this, mul_div_mul_left _ _ hdw]
  have hfar : ∀ w, max σF σE < w.re → d.eval w ≠ 0 → (M (w - s₀)).det ≠ 0 →
      GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w P) g = Num w / (d.eval w * (M (w - s₀)).det) := by
    intro w hw hdw hDw
    have hwF : σF < w.re := lt_of_le_of_lt (le_max_left _ _) hw
    have hwE : σE < w.re := lt_of_le_of_lt (le_max_right _ _) hw
    have hsplit : GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w P) g =
        ∑ j, cc j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w (QQ j)) g := by
      calc GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w P) g
          = ∑' q, ∑ j, cc j * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ w (QQ j)) g q :=
            tsum_congr fun q => hz_comb' hD hPsum w _
        _ = ∑ j, ∑' q, cc j * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ w (QQ j)) g q :=
            Summable.tsum_finsetSum fun j _ => (hFsum (QQ j) g w hwF).mul_left (cc j)
        _ = _ := Finset.sum_congr rfl fun j _ => tsum_mul_left
    have hΦ : ∀ i, ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w 1) (g * ι (↑k * yy i)) ∂ν =
        ∑ l, M (w - s₀) i l * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w (QQ l)) g :=
      fun i => hFrel ν κ N yy QQ M hν hκ hMrel w hwF g i
    have hΨd : ∀ i, Ψ i w = d.eval w *
        ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w 1) (g * ι (↑k * yy i)) ∂ν := by
      intro i
      rw [hΨ, ← integral_const_mul]
      congr 1
      funext k
      rw [(hEfar w hwE).2]
      exact mul_left_comm _ _ _
    have hinner : ∀ j, ∑ i, (M (w - s₀)).adjugate j i * Ψ i w =
        d.eval w * ((M (w - s₀)).det * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w (QQ j)) g) := by
      intro j
      simp only [hΨd, hΦ]
      have : ∑ i, (M (w - s₀)).adjugate j i * (d.eval w *
            ∑ l, M (w - s₀) i l * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w (QQ l)) g) =
          d.eval w * ∑ i, (M (w - s₀)).adjugate j i *
            ∑ l, M (w - s₀) i l * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w (QQ l)) g := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, mulVec_sum', Matrix.adjugate_mul]
      simp [Matrix.smul_apply, Matrix.one_apply]
    rw [hsplit, hNum]
    have hsum : ∑ j, cc j * ∑ i, (M (w - s₀)).adjugate j i * Ψ i w =
        (d.eval w * (M (w - s₀)).det) * ∑ j, cc j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w (QQ j)) g := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hinner]; ring
    rw [hsum, mul_div_cancel_left₀ _ (mul_ne_zero hdw hDw)]
  have hmerF : MeromorphicOn (fun z => Num z / (d.eval z * (M (z - s₀)).det)) U := fun z hz =>
    (hNumU.analyticAt (hUo.mem_nhds hz)).meromorphicAt.div ((hdd.mul hDt).analyticAt z).meromorphicAt
  have hevm : ∀ z, ∀ᶠ w in 𝓝[≠] z, max σF σE < w.re →
      GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w P) g = Num w / (d.eval w * (M (w - s₀)).det) := by
    intro z
    filter_upwards [ev_ne_lemma hdd ha z, ev_ne_lemma hDt (a := s₀) (by simp [hM0]) z] with w h1 h2 h3
    exact hfar w h3 h1 h2
  have hext := (merExt_lemma_2 hUr hmerF hevm).isExtAt hs₀U
  refine hext.holValueAt_iff.2 ?_
  have hΩt : Tendsto (fun z => NumL z / (M (z - s₀)).det) (𝓝[≠] s₀) (𝓝 (I P g)) := by
    rw [← hval]
    exact hΩc.tendsto.mono_left nhdsWithin_le_nhds
  refine hΩt.congr' ?_
  filter_upwards [hformΩ, hevm s₀] with w h1 h2
  split_ifs with hh
  · rw [h2 hh, h1]
  · rw [h1]

end PositivityTheory.Rg.Sw.AbsSt
