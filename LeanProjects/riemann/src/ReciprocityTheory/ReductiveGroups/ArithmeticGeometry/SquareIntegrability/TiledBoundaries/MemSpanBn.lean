import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.PointwiseNormSqPullbackTensorEqProd

namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries

open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex Module

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def Bn (X : PT E) (n : ℕ) :
    Basis (Σ _ : Fin n, Fin (2 * Fintype.card (Idx X.dim))) ℝ (Fin n → Vsp X.dim) :=
  Pi.basis fun _ => X.b

theorem Bn_repr (X : PT E) (n : ℕ) (v : Fin n → Vsp X.dim) (k : Fin n)
    (i : Fin (2 * Fintype.card (Idx X.dim))) : (Bn X n).repr v ⟨k, i⟩ = X.b.repr (v k) i := by
  first
    | exact Pi.basis_repr _ _ _
    | simp [Bn, Pi.basis_repr]

instance volHaar (X : PT E) (n : ℕ) : (volume : Measure (Fin n → Vsp X.dim)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ => volume)

instance cntL (X : PT E) (n : ℕ) : Countable (Submodule.span ℤ (Set.range (Bn X n))).toAddSubgroup :=
  inferInstanceAs (Countable (Submodule.span ℤ (Set.range (Bn X n))))

theorem fd_eq (X : PT E) (n : ℕ) : X.fd n = ZSpan.fundamentalDomain (Bn X n) := by
  ext v
  simp only [PT.fd, Set.mem_setOf_eq, ZSpan.mem_fundamentalDomain, Sigma.forall, Bn_repr]

theorem mem_spanBn (X : PT E) (n : ℕ) (v : Fin n → Vsp X.dim) :
    v ∈ Submodule.span ℤ (Set.range (Bn X n)) ↔ ∀ k, v k ∈ X.L := by
  simp only [PT.L, lat, Basis.mem_span_iff_repr_mem, Sigma.forall, Bn_repr]

theorem fd_fund (X : PT E) (n : ℕ) :
    IsAddFundamentalDomain (Submodule.span ℤ (Set.range (Bn X n))).toAddSubgroup (X.fd n) volume := by
  rw [fd_eq]
  exact ZSpan.isAddFundamentalDomain (Bn X n) volume

theorem fd_bdd (X : PT E) (n : ℕ) : Bornology.IsBounded (X.fd n) := by
  rw [fd_eq]
  exact ZSpan.fundamentalDomain_isBounded (Bn X n)

theorem fd_ne_zero (X : PT E) (n : ℕ) : volume (X.fd n) ≠ 0 := by
  first
    | exact (fd_fund X n).measure_ne_zero (NeZero.ne volume)
    | (rw [fd_eq]; exact ZSpan.measure_fundamentalDomain_ne_zero (Bn X n))

theorem fd_ne_top (X : PT E) (n : ℕ) : volume (X.fd n) ≠ ⊤ := (fd_bdd X n).measure_lt_top.ne

theorem fd_trans (X : PT E) (n : ℕ) (a : Fin n → Vsp X.dim) :
    IsAddFundamentalDomain (Submodule.span ℤ (Set.range (Bn X n))).toAddSubgroup
      ((fun u => u + a) ⁻¹' X.fd n) volume := by
  refine (fd_fund X n).preimage_of_equiv (measurePreserving_add_right volume a).quasiMeasurePreserving
    (e := id) Function.bijective_id (fun g x => ?_)
  show ((g : Fin n → Vsp X.dim) + x) + a = (g : Fin n → Vsp X.dim) + (x + a)
  exact add_assoc _ _ _

theorem per_span (X : PT E) (n : ℕ) {F : Type} (g : (Fin n → Vsp X.dim) → F)
    (hper : ∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → ∀ v, g (v + γ) = g v) :
    ∀ (γ : (Submodule.span ℤ (Set.range (Bn X n))).toAddSubgroup) (x), g (γ +ᵥ x) = g x := by
  intro γ x
  have h1 : γ +ᵥ x = x + (γ : Fin n → Vsp X.dim) := add_comm _ _
  rw [h1]
  exact hper _ ((mem_spanBn X n _).mp γ.2) x

theorem stepI : StepI := by
  intro E _ _ X n g hg
  exact (hg.continuousOn.integrableOn_compact (fd_bdd X n).isCompact_closure).mono_set subset_closure

theorem stepT : StepT := by
  intro E _ _ X n F _ _ _ g hg hper a
  rw [setAverage_eq, setAverage_eq]
  congr 1
  have h1 := (measurePreserving_add_right (volume : Measure (Fin n → Vsp X.dim)) a).setIntegral_preimage_emb
    (measurableEmbedding_addRight a) (fun v => g (v - a)) (X.fd n)
  simp only [add_sub_cancel_right] at h1
  rw [← h1]
  exact (fd_trans X n a).setIntegral_eq (fd_fund X n) (per_span X n g hper)

theorem stepPos : StepPos := by
  intro E _ _ X q n F hF hF0
  have hc : Continuous (X.ptN2 q F) := continuous_pointNormSq_quotient X q hF.1.continuous
  have hnn : ∀ v, 0 ≤ X.ptN2 q F v := by
    intro v
    unfold PT.ptN2
    positivity
  have hper : ∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → ∀ v, X.ptN2 q F (v + γ) = X.ptN2 q F v :=
    fun γ hγ v => pointwiseNormSq_add_period X hF hγ v
  set U : Set (Fin n → Vsp X.dim) := {v | 0 < X.ptN2 q F v} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const hc
  have hUne : U.Nonempty := by
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hF0
    refine ⟨v, ?_⟩
    show 0 < X.ptN2 q F v
    unfold PT.ptN2
    exact mul_pos (pow_pos (norm_pos_iff.mpr hv) 2) (Real.exp_pos _)
  have hUpos : 0 < volume U := hUopen.measure_pos volume hUne
  have hUfd : 0 < volume (U ∩ X.fd n) := by
    open Pointwise in (
      have hinv : ∀ g : (Submodule.span ℤ (Set.range (Bn X n))).toAddSubgroup, g +ᵥ U = U := by
        intro g
        ext v
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        show 0 < X.ptN2 q F (-g +ᵥ v) ↔ 0 < X.ptN2 q F v
        rw [per_span X n (X.ptN2 q F) hper (-g) v]
      have hfd := (fd_fund X n).measure_eq_tsum U
      simp only [hinv, tsum_const] at hfd
      rw [pos_iff_ne_zero]
      intro h0
      rw [h0] at hfd
      simp at hfd
      exact hUpos.ne' hfd)
  have hint : IntegrableOn (X.ptN2 q F) (X.fd n) volume :=
    (hc.continuousOn.integrableOn_compact (fd_bdd X n).isCompact_closure).mono_set subset_closure
  have hpos : 0 < ∫ v in X.fd n, X.ptN2 q F v := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hnn) hint]
    refine lt_of_lt_of_le hUfd (measure_mono (Set.inter_subset_inter_left _ ?_))
    intro v hv
    exact ne_of_gt hv
  rw [PT.l2, setAverage_eq, smul_eq_mul]
  refine mul_pos (inv_pos.mpr ?_) hpos
  first
    | (rw [measureReal_def]; exact ENNReal.toReal_pos (fd_ne_zero X n) (fd_ne_top X n))
    | exact ENNReal.toReal_pos (fd_ne_zero X n) (fd_ne_top X n)

theorem stepF : StepF := by
  intro E _ _ X n f hf
  have hset : X.fd n = Set.univ.pi (fun _ : Fin n => ZSpan.fundamentalDomain X.b) := by
    ext v
    simp [PT.fd]
  rw [setAverage_eq, setAverage_eq, hset, volume_pi]
  first
    | simp only [measureReal_def, Measure.pi_pi, Measure.restrict_pi_pi]
    | simp only [Measure.real_def, Measure.pi_pi, Measure.restrict_pi_pi]
  rw [integral_fintype_prod_eq_prod (f := fun _ => f)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow, smul_eq_mul]
  rw [mul_pow, inv_pow]

theorem stepDual : StepDual := by
  intro E _ _ X x hx
  classical
  choose! m hm using hx
  have hHadd : ∀ z y y' : Vsp X.dim, Hf z (y + y') = Hf z y + Hf z y' := by
    intro z y y'
    simp only [Hf, PiLp.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  have hHsub : ∀ z z' y : Vsp X.dim, Hf (z - z') y = Hf z y - Hf z' y := by
    intro z z' y
    simp only [Hf, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hHsmul : ∀ (z : Vsp X.dim) (c : ℝ) (y : Vsp X.dim), (Hf z (c • y)).im = c * (Hf z y).im := by
    intro z c y
    simp only [Hf, PiLp.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, Complex.im_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hadd : ∀ y ∈ X.L, ∀ y' ∈ X.L, m (y + y') = m y + m y' := by
    intro y hy y' hy'
    have h1 := hm (y + y') (X.L.add_mem hy hy')
    have h2 := hm y hy
    have h3 := hm y' hy'
    rw [hHadd, Complex.add_im, h2, h3] at h1
    exact_mod_cast h1.symm
  obtain ⟨x', hx'L, hx'⟩ := X.perfect (AddMonoidHom.mk' (fun y : X.L => m y)
    (fun y y' => hadd y y.2 y' y'.2))
  set z := x - x' with hzdef
  have hz : ∀ y ∈ X.L, (Hf z y).im = 0 := by
    intro y hy
    have h1 := hx' ⟨y, hy⟩
    simp only [AddMonoidHom.mk'_apply] at h1
    rw [hzdef, hHsub, Complex.sub_im, hm y hy, h1, sub_self]
  let A : Vsp X.dim →+ ℝ := AddMonoidHom.mk' (fun y => (Hf z y).im)
    (fun y y' => by simp only [hHadd, Complex.add_im])
  have hA : ∀ y, (Hf z y).im = 0 := by
    intro y
    have h1 : (Hf z y).im = A y := rfl
    rw [h1, ← X.b.sum_repr y, map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    show (Hf z (X.b.repr y i • X.b i)).im = 0
    rw [hHsmul, hz (X.b i) (Submodule.subset_span ⟨i, rfl⟩), mul_zero]
  have hI : (Hf z (Complex.I • z)).im = -∑ i, Complex.normSq (z i) := by
    simp only [Hf, PiLp.smul_apply, smul_eq_mul, Complex.im_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [map_mul, Complex.conj_I, Complex.mul_im, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.I_re, Complex.I_im, Complex.normSq_apply, Complex.neg_re, Complex.neg_im]
    ring
  have hsum : ∑ i, Complex.normSq (z i) = 0 := by
    have h1 := hA (Complex.I • z)
    rw [hI] at h1
    linarith
  have hz0 : z = 0 := by
    ext i
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (z j))).mp hsum i
      (Finset.mem_univ i)
    simpa using Complex.normSq_eq_zero.mp h1
  have hxx : x = x' := sub_eq_zero.mp hz0
  rw [hxx]
  exact hx'L

end

end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
