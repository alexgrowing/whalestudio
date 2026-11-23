import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

theorem contDiff_of_differentiable_fd {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {F : W → ℂ} (hF : Differentiable ℂ F) (k : ℕ) : ContDiff ℂ k F := by
  classical
  set e := Module.finrank ℂ W
  let L : W ≃L[ℂ] (Fin e → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp [e])
  have hg : Differentiable ℂ (F ∘ L.symm) := hF.comp L.symm.differentiable
  have ha := ReciprocityTheory.AnForm.Osgood.osgood e Set.univ (F ∘ L.symm) isOpen_univ hg.differentiableOn
  have hc : ContDiff ℂ k (F ∘ L.symm) :=
    contDiff_iff_contDiffAt.2 fun x => (ha x (Set.mem_univ x)).contDiffAt
  have hF' : F = (F ∘ L.symm) ∘ L := by
    funext w
    simp
  rw [hF']
  exact hc.comp L.contDiff

theorem polyDeriv_sum {σ W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) (s : Finset ι) (c : ι → ℂ) (F : ι → W → ℂ)
    (hF : ∀ i ∈ s, ∀ k : ℕ, ContDiff ℂ k (F i)) (x : W) :
    polyDeriv P u (fun w => ∑ i ∈ s, c i * F i w) x = ∑ i ∈ s, c i * polyDeriv P u (F i) x := by
  unfold polyDeriv
  have hD : ∀ N : ℕ, iteratedFDeriv ℂ N (fun w => ∑ i ∈ s, c i * F i w) x =
      ∑ i ∈ s, c i • iteratedFDeriv ℂ N (F i) x := by
    intro N
    show iteratedFDeriv ℂ N (fun w => ∑ i ∈ s, c i • F i w) x = _
    rw [iteratedFDeriv_sum (fun i hi => (hF i hi N).const_smul (c i)), Finset.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    exact iteratedFDeriv_const_smul_apply (a := c i) (hF i hi N).contDiffAt
  simp only [hD, ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
  ring

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace PT

variable (X : PT E)

theorem fd_eq (n : ℕ) : X.fd n = Set.univ.pi (fun _ : Fin n => ZSpan.fundamentalDomain X.b) := by
  ext v
  simp [PT.fd, Set.mem_pi]

theorem isBounded_fd (n : ℕ) : Bornology.IsBounded (X.fd n) := by
  rw [fd_eq]
  exact Bornology.IsBounded.pi fun _ => ZSpan.fundamentalDomain_isBounded X.b

theorem integrableOn_fd {n : ℕ} {g : (Fin n → Vsp X.dim) → ℂ} (hg : Continuous g) :
    IntegrableOn g (X.fd n) := by
  exact (hg.continuousOn.integrableOn_compact (X.isBounded_fd n).isCompact_closure).mono_set
    subset_closure

theorem continuous_weight (q n : ℕ) :
    Continuous fun v : Fin n → Vsp X.dim => (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ) := by
  have hc : ∀ (k : Fin n) (i : Idx X.dim), Continuous fun v : Fin n → Vsp X.dim => v k i :=
    fun k i => (EuclideanSpace.proj i).continuous.comp (continuous_apply k)
  have hHC : Continuous fun v : Fin n → Vsp X.dim => HC v v := by
    unfold HC Hf
    exact continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun i _ =>
      (hc k i).mul (Complex.continuous_conj.comp (hc k i))
  exact Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp hHC)))

theorem l2_sum_eq_sum_norm_sq_of_orthogonal {n : ℕ} (q : ℕ) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (e : ι → (Fin n → Vsp X.dim) → ℂ) (he : ∀ i ∈ s, Continuous (e i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → X.l2ip q (e i) (e j) = 0) :
    X.l2 q (fun v => ∑ i ∈ s, c i * e i v) = ∑ i ∈ s, ‖c i‖ ^ 2 * X.l2 q (e i) := by
  classical
  have hwc := X.continuous_weight q n
  have hpt : ∀ (G : (Fin n → Vsp X.dim) → ℂ) (v : Fin n → Vsp X.dim), X.ptN2 q G v =
      (G v * (starRingEnd ℂ) (G v) * (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ)).re := by
    intro G v
    simp only [PT.ptN2]
    rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hint : ∀ G H : (Fin n → Vsp X.dim) → ℂ, Continuous G → Continuous H →
      MeasureTheory.IntegrableOn (fun v => G v * (starRingEnd ℂ) (H v) *
        (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ)) (X.fd n) :=
    fun G H hG hH => X.integrableOn_fd ((hG.mul (Complex.continuous_conj.comp hH)).mul hwc)
  have hA : ∀ G : (Fin n → Vsp X.dim) → ℂ, Continuous G → X.l2 q G = (X.l2ip q G G).re := by
    intro G hG
    simp only [PT.l2, PT.l2ip, MeasureTheory.setAverage_eq]
    simp_rw [hpt G]
    rw [Complex.smul_re]
    congr 1
    first
      | exact integral_re (hint G G hG hG)
      | simpa using integral_re (hint G G hG hG)
  have hsum_int : ∀ v : Fin n → Vsp X.dim,
      (∑ i ∈ s, c i * e i v) * (starRingEnd ℂ) (∑ i ∈ s, c i * e i v) *
        (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) *
        (e i v * (starRingEnd ℂ) (e j v) * (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ)) := by
    intro v
    rw [map_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  have hterm : ∀ i ∈ s, ∀ j ∈ s, MeasureTheory.IntegrableOn (fun v => (c i * (starRingEnd ℂ) (c j)) *
      (e i v * (starRingEnd ℂ) (e j v) * (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ))) (X.fd n) :=
    fun i hi j hj => (hint (e i) (e j) (he i hi) (he j hj)).const_mul _
  have hB : ∫ v in X.fd n, (∑ i ∈ s, c i * e i v) * (starRingEnd ℂ) (∑ i ∈ s, c i * e i v) *
        (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) *
        ∫ v in X.fd n, e i v * (starRingEnd ℂ) (e j v) * (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ) := by
    simp_rw [hsum_int]
    rw [MeasureTheory.integral_finset_sum _ fun i hi =>
      MeasureTheory.integrable_finset_sum _ fun j hj => hterm i hi j hj]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [MeasureTheory.integral_finset_sum _ fun j hj => hterm i hi j hj]
    refine Finset.sum_congr rfl fun j _ => ?_
    first
      | exact MeasureTheory.integral_const_mul _ _
      | exact MeasureTheory.integral_mul_left _ _
  have hF : Continuous (fun v => ∑ i ∈ s, c i * e i v) :=
    continuous_finset_sum _ fun i hi => continuous_const.mul (he i hi)
  have hip : X.l2ip q (fun v => ∑ i ∈ s, c i * e i v) (fun v => ∑ i ∈ s, c i * e i v) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) * X.l2ip q (e i) (e j) := by
    simp only [PT.l2ip, MeasureTheory.setAverage_eq]
    rw [hB, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    first
      | (simp only [Complex.real_smul]; ring)
      | rw [mul_smul_comm]
  have hdiag : ∀ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) * X.l2ip q (e i) (e j) =
      (c i * (starRingEnd ℂ) (c i)) * X.l2ip q (e i) (e i) := by
    intro i hi
    refine Finset.sum_eq_single i (fun j hj hji => ?_) (fun h => absurd hi h)
    rw [horth i hi j hj (Ne.symm hji), mul_zero]
  rw [hA _ hF, hip, Finset.sum_congr rfl hdiag, Complex.re_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hA _ (he i hi), Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]

end PT

theorem iOf (hJ : JStatement) (hN : NStatement) : IStatement := by
  unfold IStatement
  intro E _ _ _ X n nb bs hbs P π hπ s hs hs0 K hK
  obtain ⟨hmem, horth, hl2, hspan⟩ := hN E X P.q n π P.hq hπ s hs hs0 K hK
  obtain ⟨F, hF, hF1, hJF⟩ := hJ E X n nb bs hbs P
  have hUd : ∀ b ∈ K, Differentiable ℂ (X.U P.q b (s0 X π s)) := fun b hb => (hmem b hb).1
  have hUc : ∀ b ∈ K, Continuous (X.U P.q b (s0 X π s)) := fun b hb => (hUd b hb).continuous
  have hFspan := hspan hF
  rw [Finsupp.mem_span_image_iff_linearCombination] at hFspan
  obtain ⟨l, hl, hlF⟩ := hFspan
  have hsub : l.support ⊆ K := by
    have h := (Finsupp.mem_supported ℂ l).1 hl
    exact Finset.coe_subset.1 h
  have hFsum : F = fun v => ∑ b ∈ K, l b * X.U P.q b (s0 X π s) v := by
    rw [← hlF, Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset l hsub (fun b a => a • X.U P.q b (s0 X π s))
        (fun b _ => zero_smul ℂ _)]
    funext v
    simp [Finset.sum_apply, smul_eq_mul]
  have hl2F : X.l2 P.q F = ∑ b ∈ K, ‖l b‖ ^ 2 * X.l2 1 s ^ n := by
    rw [hFsum, X.l2_sum_eq_sum_norm_sq_of_orthogonal P.q K l (fun b => X.U P.q b (s0 X π s)) hUc
      (fun b hb b' hb' hne => horth b hb b' hb' hne)]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hl2 b hb]
  have hpd : polyDeriv (P1 bs) dir F 0 =
      ∑ b ∈ K, l b * polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0 := by
    rw [hFsum]
    exact polyDeriv_sum _ _ K l (fun b => X.U P.q b (s0 X π s))
      (fun b hb k => contDiff_of_differentiable_fd (hUd b hb) k) 0
  have hS : X.l2 1 s ^ n * ∑ b ∈ K, ‖l b‖ ^ 2 = 1 := by
    rw [← hF1, hl2F, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hSnn : 0 ≤ ∑ b ∈ K, ‖l b‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hLpos : 0 < X.l2 1 s ^ n := by
    rcases le_or_gt (X.l2 1 s ^ n) 0 with h | h
    · nlinarith
    · exact h
  have hnorm : ‖polyDeriv (P1 bs) dir F 0‖ ≤
      ∑ b ∈ K, ‖l b‖ * ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖ := by
    rw [hpd]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq K (fun b => ‖l b‖)
    (fun b => ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖)
  have h1 : ‖polyDeriv (P1 bs) dir F 0‖ ^ 2 ≤ (∑ b ∈ K, ‖l b‖ ^ 2) *
      ∑ b ∈ K, ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖ ^ 2 := by
    refine le_trans ?_ hcs
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc P.Jbound n * X.l2 1 s ^ n ≤ ‖polyDeriv (P1 bs) dir F 0‖ ^ 2 * X.l2 1 s ^ n :=
        mul_le_mul_of_nonneg_right hJF hLpos.le
    _ ≤ ((∑ b ∈ K, ‖l b‖ ^ 2) *
          ∑ b ∈ K, ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖ ^ 2) * X.l2 1 s ^ n :=
        mul_le_mul_of_nonneg_right h1 hLpos.le
    _ = ∑ b ∈ K, ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖ ^ 2 := by
        rw [mul_comm (∑ b ∈ K, ‖l b‖ ^ 2), mul_assoc, mul_comm (∑ b ∈ K, ‖l b‖ ^ 2), hS, mul_one]

end

end ReciprocityTheory.ChartRestriction.G.I2
