import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches
import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsAlg
import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsPoint
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar

theorem trdeg_of_arithVar {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)} {n : ℕ}
    (h : IsArithVar P (n + 1)) : Algebra.trdeg ℤ (MRing J ⧸ P) = ((n + Fintype.card K : ℕ) : Cardinal) := by
  obtain ⟨_, ⟨hP, _, _⟩, hhor, hdim⟩ := h
  haveI := hP
  have hinj : Function.Injective (algebraMap ℤ (MRing J ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : (MvPolynomial.C a : MRing J) ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have hc : algebraMap ℤ (MRing J ⧸ P) a = Ideal.Quotient.mk P (MvPolynomial.C a) := by simp
      rw [← hc]
      exact ha
    have hc : a ∈ Ideal.comap (MvPolynomial.C : ℤ →+* MRing J) P := hmem
    rw [hhor] at hc
    exact (Submodule.mem_bot _).1 hc
  have hd := GroundTheory.Heights₂.Heights.IntDomainDim.proof (MRing J ⧸ P) hinj
  rw [hd] at hdim
  have h4 : (Cardinal.toENat (Algebra.trdeg ℤ (MRing J ⧸ P)) + 1 : ℕ∞)
      = ((n + Fintype.card K : ℕ) : ℕ∞) + 1 := by
    rw [show n + 1 + Fintype.card K = n + Fintype.card K + 1 by ring] at hdim
    exact_mod_cast hdim
  have h3 : Cardinal.toENat (Algebra.trdeg ℤ (MRing J ⧸ P)) = ((n + Fintype.card K : ℕ) : ℕ∞) :=
    WithTop.add_right_cancel ENat.one_ne_top h4
  exact Cardinal.toENat_eq_nat.1 h3

theorem chartMeets : ChartMeets := by
  intro X Ω _ _ ξ K _ J _ y n Bd χ U htie hspec harith hU
  haveI : (mCoordIdeal y).IsPrime := harith.2.1.1
  have hhom : IsMultiHomogIdeal (mCoordIdeal y) := harith.2.1.2.1
  have hconv : ∀ (w : (k : K) × J k → ℂ) (f : MvPolynomial ((k : K) × J k) ℤ),
      aeval w f = MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) f) := by
    intro w f
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]
  have hscale : ∀ (c : K → ℂ) (w : (k : K) × J k → ℂ) (s : MvPolynomial ((k : K) × J k) ℤ)
      (a : K → ℕ), IsMultiHomog s a → aeval (torusSmul c w) s = (∏ k, c k ^ a k) * aeval w s := by
    intro c w s a hs
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hprod : ∏ i, (torusSmul c w i) ^ d i = (∏ k, c k ^ a k) * ∏ i, w i ^ d i := by
      simp only [torusSmul, mul_pow, Finset.prod_mul_distrib]
      congr 1
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show ∏ j : J k, c k ^ d ⟨k, j⟩ = c k ^ a k
      rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
    rw [hprod]
    ring
  have htor : ∀ (c : K → ℂ) (w : (k : K) × J k → ℂ), w ∈ mcPts (mCoordIdeal y) →
      ∀ f ∈ mCoordIdeal y, aeval (torusSmul c w) f = 0 := by
    intro c w hw f hf
    obtain ⟨S, hS, hPS⟩ := hhom
    have hf' : f ∈ Ideal.span S := by
      rw [← hPS]
      exact hf
    clear hf
    induction hf' using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨a, ha⟩ := hS s hs
      have hsP : s ∈ mCoordIdeal y := by
        rw [hPS]
        exact Ideal.subset_span hs
      rw [hscale c w s a ha, hconv, hw.2 s hsP, mul_zero]
    | zero => simp
    | add f₁ f₂ _ _ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
    | smul r f₁ _ h₁ => rw [smul_eq_mul, map_mul, h₁, mul_zero]
  obtain ⟨g, hg, hgU⟩ := SheetDecomposition.ChartForm.exists_form htie U hU
  have h0b : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  let D := fderiv ℂ χ.γ 0
  let Γ : (Fin n → ℂ) × (K → ℂ) → (k : K) × J k → ℂ :=
    fun w => torusSmul (fun k => 1 + w.2 k) (χ.γ w.1)
  let L : ((Fin n → ℂ) × (K → ℂ)) →L[ℂ] ((k : K) × J k → ℂ) :=
    ContinuousLinearMap.pi fun p : (k : K) × J k =>
      (ContinuousLinearMap.proj p).comp (D.comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (K → ℂ)))
      + χ.γ 0 p • (ContinuousLinearMap.proj p.1).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))
  have hγ : HasStrictFDerivAt χ.γ D 0 := (χ.analytic 0 h0b).hasStrictFDerivAt
  have hstrict : HasStrictFDerivAt Γ L 0 := by
    rw [hasStrictFDerivAt_pi']
    intro p
    have h1 : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => (1 : ℂ) + w.2 p.1)
        ((ContinuousLinearMap.proj p.1).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))) 0 :=
      by
        have hs : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => w.2 p.1)
            ((ContinuousLinearMap.proj p.1).comp
              (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))) 0 :=
          ((ContinuousLinearMap.proj p.1).comp
            (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))).hasStrictFDerivAt
        exact hs.const_add (1 : ℂ)
    have h2 : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => χ.γ w.1 p)
        ((ContinuousLinearMap.proj p).comp (D.comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (K → ℂ)))) 0 :=
      by
        have hγp : HasStrictFDerivAt (fun t : Fin n → ℂ => χ.γ t p)
            ((ContinuousLinearMap.proj p).comp D) (0 : Fin n → ℂ) := hasStrictFDerivAt_pi'.1 hγ p
        have hfst : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => w.1)
            (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (K → ℂ)) 0 := hasStrictFDerivAt_fst
        exact hγp.comp (0 : (Fin n → ℂ) × (K → ℂ)) hfst
    refine (h1.mul h2).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp [L] <;> ring
  have hinjL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨v, d⟩ h0
    have hcomp : ∀ p : (k : K) × J k, D v p + χ.γ 0 p * d p.1 = 0 := by
      intro p
      have := congrFun h0 p
      simpa [L] using this
    have hv : v = 0 := by
      refine χ.immersion 0 h0b v ⟨fun k => -d k, ?_⟩
      funext p
      simp only [torusSmul]
      linear_combination hcomp p
    subst hv
    have hd : d = 0 := by
      funext k
      obtain ⟨i, hi⟩ := (χ.mem 0 h0b).1 k
      have := hcomp ⟨k, i⟩
      simp only [map_zero, Pi.zero_apply, zero_add] at this
      exact (mul_eq_zero.1 this).resolve_left hi
    rw [hd]
    rfl
  have hfin : Module.finrank ℂ ((Fin n → ℂ) × (K → ℂ)) = n + Fintype.card K := by simp
  have htr : Algebra.trdeg ℤ (MvPolynomial ((k : K) × J k) ℤ ⧸ mCoordIdeal y)
      ≤ ↑(Module.finrank ℂ ((Fin n → ℂ) × (K → ℂ))) :=
    (trdeg_of_arithVar harith).trans_le (le_of_eq (by rw [hfin]))
  have hN : ∀ᶠ w : (Fin n → ℂ) × (K → ℂ) in 𝓝 0,
      w.1 ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ k, 1 + w.2 k ≠ 0 := by
    refine Filter.Eventually.and ?_ (Filter.eventually_all.2 fun k => ?_)
    · exact (Metric.isOpen_ball.preimage continuous_fst).mem_nhds (by simpa using h0b)
    · exact (isOpen_ne_fun (continuous_const.add ((continuous_apply k).comp continuous_snd))
        continuous_const).mem_nhds (by simp)
  have hev : ∀ f ∈ mCoordIdeal y, ∀ᶠ w : (Fin n → ℂ) × (K → ℂ) in 𝓝 0, aeval (Γ w) f = 0 := by
    intro f hf
    filter_upwards [hN] with w hw
    exact htor _ _ (χ.mem _ hw.1) f hf
  have hne := SheetDecomposition.ChartAlg.not_eventually_zero (mCoordIdeal y) htr Γ 0 L hstrict hinjL hev g hg
  obtain ⟨w, hwN, hwg⟩ : ∃ w : (Fin n → ℂ) × (K → ℂ),
      (w.1 ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ k, 1 + w.2 k ≠ 0) ∧ aeval (Γ w) g ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (hN.mono fun w hw => hcon w hw)
  have hmem := χ.mem _ hwN.1
  obtain ⟨z, hsp, hco⟩ := SheetDecomposition.ChartForm.exists_point htie (Γ w)
    (fun k => by
      obtain ⟨i, hi⟩ := hmem.1 k
      exact ⟨i, (mul_ne_zero (hwN.2 k) hi).isUnit⟩)
    (fun f hf => htor _ _ hmem f hf)
  have hcU := hgU z (Γ w) hsp hco hwg
  have hcoord : CoordsAt ξ y z (χ.γ w.1) := by
    obtain ⟨_, hrel⟩ := hco
    refine ⟨fun k => ?_, fun k c' hu => ?_⟩
    · obtain ⟨i, hi⟩ := hmem.1 k
      exact ⟨i, hi.isUnit⟩
    · have hu' : IsUnit (Γ w ⟨k, c'⟩) := (hwN.2 k).isUnit.mul hu
      obtain ⟨hy, hr⟩ := hrel k c' hu'
      refine ⟨hy, fun i => ?_⟩
      obtain ⟨r, hval, hreq⟩ := hr i
      refine ⟨r, hval, ?_⟩
      have hreq' : (1 + w.2 k) * χ.γ w.1 ⟨k, i⟩ = r * ((1 + w.2 k) * χ.γ w.1 ⟨k, c'⟩) := hreq
      apply mul_left_cancel₀ (hwN.2 k)
      linear_combination hreq'
  refine ⟨w.1, hwN.1, z, hcoord, ?_⟩
  intro x _
  have hx : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
  rw [hx]
  exact hcU

end SheetDecomposition
