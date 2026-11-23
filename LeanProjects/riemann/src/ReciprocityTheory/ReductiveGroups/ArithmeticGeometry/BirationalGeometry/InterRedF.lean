import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedE

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem maDens_congr_fderiv {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ i, fderiv ℝ (φ i) =ᶠ[𝓝 z] fderiv ℝ (ψ i)) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have h2 : ∀ i, fderiv ℝ (fderiv ℝ (φ i)) z = fderiv ℝ (fderiv ℝ (ψ i)) z :=
    fun i => (h i).fderiv_eq
  unfold ReciprocityTheory.AnForm.maDens ReciprocityTheory.AnForm.hessC
  simp only [h2]

theorem isSmoothHerm_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) := by
  unfold IsSmoothHerm at *
  exact hA.mul hB

theorem isSectionOn_one {P : Ideal (MRing ι)} (hP : P.IsPrime) {B : HermLine ι} (hB : B.a = 0) :
    IsSectionOn P B 1 := by
  refine ⟨0, fun k => by simp [hB], ?_, ?_⟩
  · intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  · exact fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)

def oneLine : HermLine ι := HermLine.ofWeight (fun _ => 1) (fun _ _ _ => rfl)

theorem logNorm_oneLine (z : (Σ k, ι k) → ℂ) : logNorm (oneLine (ι := ι)) 1 z = 1 := by
  simp [logNorm, oneLine, HermLine.ofWeight, Real.exp_neg]

theorem isSmoothHerm_oneLine : IsSmoothHerm (oneLine (ι := ι)) := by
  simp only [IsSmoothHerm, oneLine, HermLine.ofWeight]
  exact contDiffOn_const

def HermLine.sqMetric (b : K → ℕ) : HermLine ι where
  a k := b k
  h z := ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ b k
  pos z hz := Finset.prod_pos fun k _ => by
    obtain ⟨i, hi⟩ := hz k
    refine pow_pos (Real.sqrt_pos.mpr ?_) _
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ i))
  smul c z hc := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have : ∑ i, ‖c k * z ⟨k, i⟩‖ ^ 2 = ‖c k‖ ^ 2 * ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
      simp [mul_pow, Finset.mul_sum]
    simp only
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _), mul_pow, zpow_natCast]

theorem isSmoothHerm_sqMetric (b : K → ℕ) : IsSmoothHerm (HermLine.sqMetric (ι := ι) b) := by
  unfold IsSmoothHerm
  have hs : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Σ k, ι k) → ℂ => ∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
    intro k
    apply ContDiff.sum
    intro i _
    exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))
  show ContDiffOn ℝ _ (fun z : (Σ k, ι k) → ℂ => ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ b k) _
  apply contDiffOn_prod
  intro k _
  apply ContDiffOn.pow
  apply ContDiffOn.sqrt (hs k).contDiffOn
  intro z hz
  obtain ⟨i, hi⟩ := hz k
  have hpos : 0 < ‖z ⟨k, i⟩‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
  exact (lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2)
    (fun i _ => by positivity) (Finset.mem_univ i))).ne'

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem germ_of_eqOn (R : AnLogRes P J e) {Q Q' : LocPot R.X}
    (h : ∀ x, ∀ y ∈ R.U x, Q.φ x y = Q'.φ x y) (j : Fin R.A.n) (y : Fin e → ℂ)
    (hy : y ∈ (R.A.chart j).target) :
    (fun y' => Q.φ ((R.A.chart j).symm y) ((R.A.chart j).symm y')) =ᶠ[𝓝 y]
      fun y' => Q'.φ ((R.A.chart j).symm y) ((R.A.chart j).symm y') := by
  have hc : ContinuousAt (R.A.chart j).symm y := (R.A.chart j).continuousAt_symm hy
  have hU : R.U ((R.A.chart j).symm y) ∈ 𝓝 ((R.A.chart j).symm y) :=
    (R.isOpen_U _).mem_nhds (R.mem_U _)
  filter_upwards [hc hU] with y' hy'
  exact h _ _ hy'

theorem locDens_congr_of_eqOn (R : AnLogRes P J e) {Φ Φ' : Fin e → LocPot R.X}
    (h : ∀ i x, ∀ y ∈ R.U x, (Φ i).φ x y = (Φ' i).φ x y) :
    ∀ j, ∀ y ∈ (R.A.chart j).target, locDens R.A Φ j y = locDens R.A Φ' j y := by
  intro j y hy
  unfold locDens
  apply maDens_congr_fderiv
  intro i
  exact (germ_of_eqOn R (h i) j y hy).fderiv

theorem potOf_cons {n : ℕ} (R : AnLogRes P J e) (C : HermLine ι) (L : Fin n → HermLine ι) :
    (fun j => potOf R ((Fin.cons C L : Fin (n + 1) → HermLine ι) j)) =
      Fin.cons (potOf R C) (fun j => potOf R (L j)) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero]
  · simp only [Fin.cons_succ]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}

theorem ptsIntegral_one_eq_mInt (hE : ResExistsStatement) (hB : ResBridgeStatement) {e : ℕ}
    (R : AnLogRes P J e) {L : Fin e → HermLine ι} (hP : IsArithVar P (e + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) :
    ptsIntegral P (pot L) (fun _ => 1) = mInt R.A (fun j => potOf R (L j)) (fun _ => 1) := by
  have h1 : (fun _ : (Σ k, ι k) → ℂ => (1 : ℝ)) = logNorm oneLine 1 :=
    funext fun z => (logNorm_oneLine z).symm
  rw [h1, ptsIntegral_eq_mInt' hE hB R hP hL isSmoothHerm_oneLine (isSectionOn_one hP.2.1.1 rfl)]
  exact mInt_congr _ (fun _ _ _ => rfl) fun x => logNorm_oneLine _

end ReciprocityTheory.ChartRestriction.G.Geo
