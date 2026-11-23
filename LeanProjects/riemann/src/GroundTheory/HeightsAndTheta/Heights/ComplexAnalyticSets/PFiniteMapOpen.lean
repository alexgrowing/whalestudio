import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteMapOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

namespace FiniteMapOpen

abbrev evalYT {d : ℕ} (F : Polynomial (MvPolynomial (Fin d) ℂ)) (y : Fin d → ℂ) (t : ℂ) : ℂ :=
  (F.map (MvPolynomial.eval y)).eval t

theorem continuous_evalYT {d : ℕ} (F : Polynomial (MvPolynomial (Fin d) ℂ)) (t : ℂ) :
    Continuous fun y => evalYT F y t := by
  have : (fun y => evalYT F y t) =
      fun y => ∑ k ∈ Finset.range (F.natDegree + 1), MvPolynomial.eval y (F.coeff k) * t ^ k := by
    funext y
    rw [evalYT, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  rw [this]
  exact continuous_finsetSum _ fun k _ => (MvPolynomial.continuous_eval _).mul continuous_const

theorem eventually_exists_root {d : ℕ} {F : Polynomial (MvPolynomial (Fin d) ℂ)} (hF : F.Monic)
    {y₀ : Fin d → ℂ} {t₀ : ℂ} (h₀ : evalYT F y₀ t₀ = 0) {V : Set ℂ} (hV : V ∈ 𝓝 t₀) :
    ∀ᶠ y in 𝓝 y₀, ∃ t ∈ V, evalYT F y t = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  have hcont := (continuous_evalYT F t₀).tendsto y₀
  rw [h₀] at hcont
  have hsmall : ∀ᶠ y in 𝓝 y₀, ‖evalYT F y t₀‖ < ε ^ F.natDegree :=
    (tendsto_norm_zero.comp hcont) (Iio_mem_nhds (pow_pos hε _))
  filter_upwards [hsmall] with y hy
  set G := F.map (MvPolynomial.eval y) with hG
  have hGm : G.Monic := hF.map _
  have hGdeg : G.natDegree = F.natDegree := hF.natDegree_map _
  have hsplit : G.Splits := IsAlgClosed.splits G
  by_contra! hfar
  have hle : ∀ r ∈ G.roots, ε ≤ ‖t₀ - r‖ := by
    intro r hr
    have hr0 : G.eval r = 0 := (Polynomial.mem_roots hGm.ne_zero).1 hr
    by_contra! hlt
    refine hfar r (hball ?_) hr0
    rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    exact hlt
  have hprod : ‖G.eval t₀‖ = (G.roots.map fun r => ‖t₀ - r‖).prod := by
    rw [hsplit.eval_eq_prod_roots_of_monic hGm]
    exact (G.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun r : ℂ => t₀ - r)).symm
  have hge : ε ^ F.natDegree ≤ ‖G.eval t₀‖ := by
    have := Multiset.prod_map_le_prod_map₀ (fun _ => ε) (fun r => ‖t₀ - r‖)
      (fun _ _ => hε.le) hle
    rw [Multiset.map_const', Multiset.prod_replicate] at this
    rw [hprod, ← hGdeg, hsplit.natDegree_eq_card_roots]
    exact this
  exact absurd hy (not_lt.2 hge)

theorem norm_le_of_monic_root {G : Polynomial ℂ} (hG : G.Monic) {t : ℂ} (ht : G.eval t = 0) :
    ‖t‖ ≤ ∑ k ∈ Finset.range G.natDegree, ‖G.coeff k‖ + 1 := by
  have h1 := Polynomial.IsRoot.norm_lt_cauchyBound hG.ne_zero ht
  have h2 : Polynomial.cauchyBound G ≤ ∑ k ∈ Finset.range G.natDegree, ‖G.coeff k‖₊ + 1 := by
    rw [Polynomial.cauchyBound, hG.leadingCoeff, nnnorm_one, div_one]
    gcongr
    exact Finset.sup_le fun k hk =>
      Finset.single_le_sum (f := fun k => ‖G.coeff k‖₊) (fun _ _ => zero_le) hk
  have h3 : ‖t‖₊ ≤ ∑ k ∈ Finset.range G.natDegree, ‖G.coeff k‖₊ + 1 := (h1.trans_le h2).le
  have h4 := NNReal.coe_le_coe.2 h3
  simpa using h4

variable {n d : ℕ}

def evalAt (J : Ideal (MvPolynomial (Fin n) ℂ)) {z : Fin n → ℂ} (hz : z ∈ zeroLocus J) :
    (MvPolynomial (Fin n) ℂ ⧸ J) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ J (aeval z) fun q hq => by rw [aeval_eq_eval]; exact hz q hq

theorem evalAt_mk (J : Ideal (MvPolynomial (Fin n) ℂ)) {z : Fin n → ℂ} (hz : z ∈ zeroLocus J)
    (q : MvPolynomial (Fin n) ℂ) : evalAt J hz (Ideal.Quotient.mk J q) = eval z q := by
  simp [evalAt]

theorem evalAt_comp_toRingHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    {z : Fin n → ℂ} (hz : z ∈ zeroLocus J) :
    (evalAt J hz : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ).comp
      ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom = MvPolynomial.eval fun i => eval z (p i) := by
  ext a <;> simp [evalAt]

theorem evalYT_eq_zero (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    {F : Polynomial (MvPolynomial (Fin d) ℂ)} {s : MvPolynomial (Fin n) ℂ ⧸ J}
    (hs : Polynomial.eval₂ ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom s F = 0)
    {z : Fin n → ℂ} (hz : z ∈ zeroLocus J) :
    evalYT F (fun i => eval z (p i)) (evalAt J hz s) = 0 := by
  have h := congrArg (evalAt J hz : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ) hs
  rw [map_zero, Polynomial.hom_eval₂, evalAt_comp_toRingHom] at h
  rw [evalYT, Polynomial.eval_map]
  exact h

theorem exists_point_of_evalYT_eq_zero (J : Ideal (MvPolynomial (Fin n) ℂ))
    (p : Fin d → MvPolynomial (Fin n) ℂ) (hfin : ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).Finite)
    (L : MvPolynomial (Fin n) ℂ) (μ : Polynomial (MvPolynomial (Fin d) ℂ))
    (hdvd : ∀ F, Polynomial.eval₂ ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom
      (Ideal.Quotient.mk J L) F = 0 → μ ∣ F)
    {y : Fin d → ℂ} {t : ℂ} (hyt : evalYT μ y t = 0) :
    ∃ z ∈ zeroLocus J, (fun i => eval z (p i)) = y ∧ eval z L = t := by
  classical
  set f := ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom with hf
  let g : Polynomial (MvPolynomial (Fin d) ℂ) →+* MvPolynomial (Fin n) ℂ ⧸ J :=
    Polynomial.eval₂RingHom f (Ideal.Quotient.mk J L)
  let e : Polynomial (MvPolynomial (Fin d) ℂ) →+* ℂ := Polynomial.eval₂RingHom (MvPolynomial.eval y) t
  have he : Function.Surjective e := fun c => ⟨Polynomial.C (MvPolynomial.C c), by simp [e]⟩
  have hPmax : (RingHom.ker e).IsMaximal := RingHom.ker_isMaximal_of_surjective e he
  have hgC : g.comp Polynomial.C = f := RingHom.ext fun a => by simp [g]
  have hfint : f.IsIntegral := RingHom.IsIntegral.of_finite hfin
  have hgint : g.IsIntegral := RingHom.IsIntegral.tower_top Polynomial.C g (hgC ▸ hfint)
  let _ : Algebra (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) := g.toAlgebra
  have : Algebra.IsIntegral (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ⟨hgint⟩
  have hker : RingHom.ker (algebraMap (Polynomial (MvPolynomial (Fin d) ℂ))
      (MvPolynomial (Fin n) ℂ ⧸ J)) ≤ RingHom.ker e := by
    intro F hF
    rw [RingHom.mem_ker] at hF ⊢
    obtain ⟨H, rfl⟩ := hdvd F hF
    have hμ : e μ = 0 := by simpa [e, evalYT, Polynomial.eval_map] using hyt
    rw [map_mul, hμ, zero_mul]
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (RingHom.ker e) hker
  have hQ' : (Q.comap (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨z, hz⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hQ'
  have key : ∀ q, Ideal.Quotient.mk J q ∈ Q → eval z q = 0 := by
    intro q hq
    have hq' : q ∈ Q.comap (Ideal.Quotient.mk J) := hq
    rw [hz, MvPolynomial.mem_vanishingIdeal_singleton_iff, aeval_eq_eval] at hq'
    exact hq'
  have key2 : ∀ F, e F = 0 → g F ∈ Q := by
    intro F hF
    have hF' : F ∈ Q.comap (algebraMap _ _) := by rw [hQP]; exact hF
    exact hF'
  refine ⟨z, fun q hq => key q ?_, ?_, ?_⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem.2 hq]
    exact Q.zero_mem
  · funext i
    have h1 := key2 (Polynomial.C (X i - C (y i))) (by simp [e])
    have h2 : g (Polynomial.C (X i - C (y i))) = Ideal.Quotient.mk J (p i - C (y i)) := by
      simp [g, f]
      rfl
    rw [h2] at h1
    have h3 := key _ h1
    simpa [sub_eq_zero] using h3
  · have h1 := key2 (Polynomial.X - Polynomial.C (C t)) (by simp [e])
    have h2 : g (Polynomial.X - Polynomial.C (C t)) = Ideal.Quotient.mk J (L - C t) := by
      simp [g, f]
      rfl
    rw [h2] at h1
    have h3 := key _ h1
    simpa [sub_eq_zero] using h3

end FiniteMapOpen

set_option synthInstance.maxHeartbeats 400000 in
open FiniteMapOpen in

theorem FiniteMapOpen.proof : FiniteMapOpen.Statement := by
  classical
  intro n d J p hJ hinj hfin x hx U hU
  set f := (Ideal.Quotient.mkₐ ℂ J).comp (aeval p) with hf
  set φ : (Fin n → ℂ) → (Fin d → ℂ) := fun z i => eval z (p i) with hφ
  set y₀ := φ x with hy₀
  have := hJ
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := f.toRingHom.toAlgebra
  have hint : ∀ s : MvPolynomial (Fin n) ℂ ⧸ J, IsIntegral (MvPolynomial (Fin d) ℂ) s :=
    fun s => RingHom.IsIntegral.of_finite hfin s

  choose g hgm hg0 using fun j : Fin n => hint (Ideal.Quotient.mk J (X j))
  have hcoord : ∀ z (hz : z ∈ zeroLocus J) j, evalYT (g j) (φ z) (z j) = 0 := by
    intro z hz j
    have := evalYT_eq_zero J p (hg0 j) hz
    simpa [evalAt_mk] using this

  have hfib : {w | w ∈ zeroLocus J ∧ φ w = y₀}.Finite := by
    refine (Set.Finite.pi (t := fun j => {t : ℂ | evalYT (g j) y₀ t = 0}) fun j => ?_).subset ?_
    · exact Polynomial.finite_setOfPred_isRoot ((hgm j).map _).ne_zero
    · rintro w ⟨hw, hwy⟩ j -
      rw [← hwy]
      exact hcoord w hw j

  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ w, w ∈ zeroLocus J ∧ φ w = y₀ → w ≠ x →
      ∑ j : Fin n, c ^ (j : ℕ) * w j ≠ ∑ j : Fin n, c ^ (j : ℕ) * x j := by
    let P : (Fin n → ℂ) → Polynomial ℂ := fun w => ∑ j : Fin n, Polynomial.monomial (j : ℕ) (w j - x j)
    have hP : ∀ w c, (P w).eval c = ∑ j : Fin n, c ^ (j : ℕ) * w j - ∑ j : Fin n, c ^ (j : ℕ) * x j := by
      intro w c
      simp [P, Polynomial.eval_finsetSum, Finset.sum_sub_distrib, mul_comm]
    have hP0 : ∀ w, w ≠ x → P w ≠ 0 := by
      intro w hw h0
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
      have h1 := congrArg (fun q => Polynomial.coeff q j) h0
      simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at h1
      rw [Finset.sum_eq_single j (fun k _ hk => if_neg (fun h => hk (Fin.ext h))) (by simp)] at h1
      simp only [if_true] at h1
      exact hj (sub_eq_zero.1 h1)
    have hbad : (⋃ w ∈ {w | (w ∈ zeroLocus J ∧ φ w = y₀) ∧ w ≠ x},
        {c : ℂ | (P w).eval c = 0}).Finite :=
      (hfib.subset fun w hw => hw.1).biUnion fun w hw =>
        Polynomial.finite_setOfPred_isRoot (hP0 w hw.2)
    obtain ⟨c, hc⟩ := hbad.infinite_compl.nonempty
    refine ⟨c, fun w hw hwx h => hc ?_⟩
    exact Set.mem_biUnion (x := w) ⟨hw, hwx⟩ (by simp [hP, h])
  set L : MvPolynomial (Fin n) ℂ := ∑ j : Fin n, C (c ^ (j : ℕ)) * X j with hL
  have hLz : ∀ z, eval z L = ∑ j : Fin n, c ^ (j : ℕ) * z j := by
    intro z
    simp [hL]

  set ℓ := Ideal.Quotient.mk J L with hℓ
  set μ := minpoly (MvPolynomial (Fin d) ℂ) ℓ with hμ
  have hμm : μ.Monic := minpoly.monic (hint ℓ)
  have : Module.IsTorsionFree (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  have hdvd : ∀ F, Polynomial.eval₂ f.toRingHom ℓ F = 0 → μ ∣ F := fun F hF =>
    minpoly.isIntegrallyClosed_dvd (hint ℓ) (by rw [Polynomial.aeval_def]; exact hF)
  have hμx : evalYT μ y₀ (eval x L) = 0 := by
    have h0 := minpoly.aeval (MvPolynomial (Fin d) ℂ) ℓ
    rw [Polynomial.aeval_def] at h0
    have := evalYT_eq_zero J p (F := μ) (s := ℓ) h0 hx
    rw [hℓ, evalAt_mk] at this
    exact this

  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hφc : Continuous φ := continuous_pi fun i => MvPolynomial.continuous_eval _
  have hZc : IsClosed (zeroLocus J) := by
    have hZ : zeroLocus J = ⋂ q ∈ J, {z : Fin n → ℂ | eval z q = 0} := by
      ext z
      simp [zeroLocus]
    rw [hZ]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  set K := zeroLocus J ∩ (φ ⁻¹' Metric.closedBall y₀ 1 ∩ (Metric.ball x r)ᶜ) with hK
  have hKc : IsClosed K :=
    hZc.inter ((Metric.isClosed_closedBall.preimage hφc).inter Metric.isOpen_ball.isClosed_compl)
  let B : (Fin d → ℂ) → ℝ := fun y =>
    ∑ j, ∑ k ∈ Finset.range (g j).natDegree, ‖MvPolynomial.eval y ((g j).coeff k)‖
  have hBc : Continuous B := continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun k _ => (MvPolynomial.continuous_eval _).norm
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall y₀ 1).exists_bound_of_continuousOn hBc.continuousOn
  have hKb : Bornology.IsBounded K := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C0 + 1, fun z hz => ?_⟩
    have hB := hC0 _ hz.2.1
    have hB0 : 0 ≤ B (φ z) := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hB0] at hB
    refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun j => ?_
    have h1 := norm_le_of_monic_root ((hgm j).map (MvPolynomial.eval (φ z))) (hcoord z hz.1 j)
    rw [(hgm j).natDegree_map] at h1
    simp only [Polynomial.coeff_map] at h1
    have h2 : ∑ k ∈ Finset.range (g j).natDegree, ‖eval (φ z) ((g j).coeff k)‖ ≤ B (φ z) :=
      Finset.single_le_sum
        (f := fun j => ∑ k ∈ Finset.range (g j).natDegree, ‖eval (φ z) ((g j).coeff k)‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    linarith
  have hKcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
  set Ψ : (Fin n → ℂ) → (Fin d → ℂ) × ℂ := fun z => (φ z, eval z L) with hΨ
  have hΨc : Continuous Ψ := hφc.prodMk (MvPolynomial.continuous_eval L)
  have hCcl : IsClosed (Ψ '' K) := (hKcpt.image hΨc).isClosed
  have hnot : (y₀, eval x L) ∉ Ψ '' K := by
    rintro ⟨z, hzK, hz⟩
    simp only [Ψ, Prod.mk.injEq] at hz
    have hzx : z ≠ x := fun h => hzK.2.2 (h ▸ Metric.mem_ball_self hr)
    exact hc z ⟨hzK.1, hz.1⟩ hzx (by rw [← hLz, ← hLz, hz.2])
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 (hCcl.isOpen_compl.mem_nhds hnot)
  filter_upwards [eventually_exists_root hμm hμx hv, hu, Metric.closedBall_mem_nhds y₀ one_pos]
    with y hyt hyu hyB
  obtain ⟨t, htv, ht⟩ := hyt
  obtain ⟨z, hz, hzy, hzt⟩ := exists_point_of_evalYT_eq_zero J p hfin L μ hdvd ht
  by_cases hzr : z ∈ Metric.ball x r
  · exact ⟨z, ⟨hz, hrU hzr⟩, hzy⟩
  · exfalso
    refine huv (Set.mk_mem_prod hyu htv) ⟨z, ⟨hz, ?_, hzr⟩, ?_⟩
    · change φ z ∈ Metric.closedBall y₀ 1
      rw [← hzy] at hyB
      exact hyB
    · simp only [Ψ, Prod.mk.injEq]
      exact ⟨hzy, hzt⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
