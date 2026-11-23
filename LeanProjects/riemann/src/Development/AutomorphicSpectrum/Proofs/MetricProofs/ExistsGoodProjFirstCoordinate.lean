import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreCoordGoodProj
import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem card_le_ringKrullDim {σ : Type} [Finite σ] (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime] {n : ℕ}
    (x : Fin n → MvPolynomial σ ℂ ⧸ Q) (hx : AlgebraicIndependent ℂ x) :
    ((n : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℂ ⧸ Q) := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℂ (MvPolynomial σ ℂ ⧸ Q)
  have hns : n ≤ s := by
    set S := Algebra.adjoin ℂ (Set.range (g ∘ X))
    have hmem : ∀ y, g y ∈ S := by
      intro y
      show g y ∈ Algebra.adjoin ℂ (Set.range (g ∘ X))
      rw [Algebra.adjoin_range_eq_range_aeval]
      refine ⟨y, ?_⟩
      show aeval (g ∘ X) y = g y
      rw [← MvPolynomial.aeval_unique g]
    let g' : MvPolynomial (Fin s) ℂ →+* S := g.toRingHom.codRestrict S.toSubsemiring hmem
    have hg' : (algebraMap S (MvPolynomial σ ℂ ⧸ Q)).comp g' = g.toRingHom := by
      ext y <;> rfl
    have halg : Algebra.IsAlgebraic S (MvPolynomial σ ℂ ⧸ Q) := by
      refine ⟨fun b => ?_⟩
      obtain ⟨p, hpm, hp⟩ := hint b
      refine IsIntegral.isAlgebraic ⟨p.map g', hpm.map g', ?_⟩
      rw [Polynomial.eval₂_map, hg']
      exact hp
    have h1 := hx.cardinalMk_le_trdeg
    have h2 := Algebra.IsAlgebraic.trdeg_le_cardinalMk ℂ (Set.range (g ∘ X))
    have h3 := Cardinal.mk_range_le (f := g ∘ X)
    have := h1.trans (h2.trans h3)
    simpa using this
  have hdim : (s : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℂ ⧸ Q) := by
    refine le_ringKrullDim_of_isIntegral g.toRingHom hint hinj s ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  exact le_trans (by exact_mod_cast hns) hdim

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isWeightedHomogeneous_of_isMultiHomog (f : MRingOver ℂ ι) (a : K → ℕ) (hf : IsMultiHomog f a) :
    IsWeightedHomogeneous (blkWt (ι := ι)) f (Finsupp.equivFunOnFinite.symm a) := by
  intro m hm
  have hms : m ∈ f.support := mem_support_iff.mpr hm
  ext k
  rw [weight_blkWt_apply, hf m hms k]
  simp

theorem ideal_isHomogeneous (Q : Ideal (MRingOver ℂ ι)) (hQ : IsMultiHomogIdeal Q) :
    Q.IsHomogeneous (weightedHomogeneousSubmodule ℂ (blkWt (ι := ι))) := by
  obtain ⟨S, hS, rfl⟩ := hQ
  apply Ideal.homogeneous_span
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨_, (mem_weightedHomogeneousSubmodule ℂ _ _ _).mpr (isWeightedHomogeneous_of_isMultiHomog f a ha)⟩

def segMonC (i : (k : K) → ι k) : MRingOver ℂ ι := ∏ k, X ⟨k, i k⟩

theorem segMonC_isWeightedHomogeneous (i : (k : K) → ι k) :
    IsWeightedHomogeneous (blkWt (ι := ι)) (segMonC i) oneK := by
  unfold segMonC
  have := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, i k⟩ : MRingOver ℂ ι))
    (fun k => Finsupp.single k 1) (w := blkWt (ι := ι))
    (fun k _ => isWeightedHomogeneous_X ℂ _ _)
  convert this using 1
  ext k
  rw [Finsupp.finsetSum_apply]
  simp [oneK, Finsupp.single_apply]

theorem component_aeval_cx {E : Type*} (w' : E → (K →₀ ℕ))
    (yt : E → MRingOver ℂ ι)
    (hy : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (w' e)) (H : MvPolynomial E ℂ)
    (δ : K →₀ ℕ) :
    weightedHomogeneousComponent (blkWt (ι := ι)) δ (aeval yt H) =
      aeval yt (weightedHomogeneousComponent w' δ H) := by
  classical
  rw [H.as_sum, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hmon : IsWeightedHomogeneous (blkWt (ι := ι)) (aeval yt (monomial m (coeff m H)))
      (Finsupp.weight w' m) := by
    rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
    refine IsWeightedHomogeneous.C_mul ?_ _
    have := IsWeightedHomogeneous.prod m.support (fun e => yt e ^ m e) (fun e => m e • w' e)
      (fun e _ => (hy e).pow (m e))
    rwa [Finsupp.weight_apply]
  by_cases h : Finsupp.weight w' m = δ
  · subst h
    rw [hmon.weightedHomogeneousComponent_same,
      (isWeightedHomogeneous_monomial w' m (coeff m H) rfl).weightedHomogeneousComponent_same]
  · rw [hmon.weightedHomogeneousComponent_ne δ (Ne.symm h),
      (isWeightedHomogeneous_monomial w' m (coeff m H) rfl).weightedHomogeneousComponent_ne δ
        (Ne.symm h), map_zero]

theorem aeval_sumElim_factor_cx (k0 : K) {S : Type*} [CommRing S] [Algebra ℂ S] {r : ℕ}
    {H : MvPolynomial (Fin r ⊕ {k // k ≠ k0}) ℂ} {δ : K →₀ ℕ}
    (hH : IsWeightedHomogeneous (sWt k0 r) H δ) {n0 : (Fin r ⊕ {k // k ≠ k0}) →₀ ℕ}
    (hn0 : n0 ∈ H.support) (a : Fin r → S) (b : {k // k ≠ k0} → S) :
    aeval (Sum.elim a b) H = (∏ k', b k' ^ n0 (Sum.inr k')) * aeval (Sum.elim a 1) H := by
  conv_lhs => rw [H.as_sum]
  conv_rhs => rw [H.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hw : Finsupp.weight (sWt k0 r) n = Finsupp.weight (sWt k0 r) n0 :=
    (hH (mem_support_iff.mp hn)).trans (hH (mem_support_iff.mp hn0)).symm
  simp only [aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.one_apply, one_pow, Finset.prod_const_one, mul_one,
    inr_eq_of_weight_eq k0 hw]
  ring

def segC (Q : Ideal (MRingOver ℂ ι)) (i : (k : K) → ι k) : MRingOver ℂ ι ⧸ Q :=
  Ideal.Quotient.mk _ (segMonC i)

theorem algebraicIndependent_sumElim_cx (Q : Ideal (MRingOver ℂ ι)) [Q.IsPrime]
    (hhom : IsMultiHomogIdeal Q) (k0 : K) (i0 : (k : K) → ι k)
    (hi0 : ∀ k, (X ⟨k, i0 k⟩ : MRingOver ℂ ι) ∉ Q) {r : ℕ} (L : Fin r → ((k : K) → ι k) → ℂ)
    (hind : AlgebraicIndependent ℂ (forms (segC Q) L)) :
    AlgebraicIndependent ℂ (Sum.elim (forms (segC Q) L)
      (fun k' : {k // k ≠ k0} => Ideal.Quotient.mk Q (X ⟨k'.1, i0 k'.1⟩))) := by
  set xs : {k // k ≠ k0} → MRingOver ℂ ι ⧸ Q :=
    fun k' => Ideal.Quotient.mk Q (X ⟨k'.1, i0 k'.1⟩) with hxs
  let π := Ideal.Quotient.mkₐ ℂ Q
  let yt : Fin r ⊕ {k // k ≠ k0} → MRingOver ℂ ι :=
    Sum.elim (fun j => ∑ i, L j i • segMonC i) (fun k' => X ⟨k'.1, i0 k'.1⟩)
  have hyt : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (sWt k0 r e) := by
    rintro (j | k')
    · refine IsWeightedHomogeneous.sum _ _ _ fun i _ => ?_
      rw [smul_eq_C_mul]
      exact (segMonC_isWeightedHomogeneous i).C_mul _
    · exact isWeightedHomogeneous_X ℂ _ _
  have hπy : (fun e => π (yt e)) = Sum.elim (forms (segC Q) L) xs := by
    funext e
    rcases e with j | k'
    · simp [yt, π, forms, segC, map_sum]
    · rfl
  have hcomp : ∀ G : MvPolynomial (Fin r ⊕ {k // k ≠ k0}) ℂ,
      Ideal.Quotient.mk Q (aeval yt G) = aeval (Sum.elim (forms (segC Q) L) xs) G := by
    intro G
    rw [← hπy, ← MvPolynomial.comp_aeval]
    rfl
  have hx0 : ∀ k', xs k' ≠ 0 := by
    intro k' h
    rw [hxs, Ideal.Quotient.eq_zero_iff_mem] at h
    exact hi0 k'.1 h
  rw [algebraicIndependent_iff]
  intro H hH0
  by_contra hne
  obtain ⟨n0, hn0⟩ := support_nonempty.mpr hne
  set δ := Finsupp.weight (sWt k0 r) n0
  set H' := weightedHomogeneousComponent (sWt k0 r) δ H
  have hH'hom : IsWeightedHomogeneous (sWt k0 r) H' δ :=
    weightedHomogeneousComponent_isWeightedHomogeneous δ H
  have hn0' : n0 ∈ H'.support := by
    rw [mem_support_iff, coeff_weightedHomogeneousComponent, if_pos rfl]
    exact mem_support_iff.mp hn0
  have hmem : aeval yt H ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hcomp]
    exact hH0
  have hmem' : aeval yt H' ∈ Q := by
    rw [← component_aeval_cx (sWt k0 r) yt hyt H δ]
    exact weightedHomogeneousComponent_mem_of_mem ℂ blkWt (ideal_isHomogeneous Q hhom) hmem δ
  have hzero : aeval (Sum.elim (forms (segC Q) L) xs) H' = 0 := by
    rw [← hcomp]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem'
  rw [aeval_sumElim_factor_cx k0 hH'hom hn0'] at hzero
  have hprod : (∏ k', xs k' ^ n0 (Sum.inr k')) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k' _ => pow_ne_zero _ (hx0 k')
  have h1 : aeval (Sum.elim (forms (segC Q) L) 1) H' = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hprod
  let G : MvPolynomial (Fin r) ℂ := aeval (Sum.elim X 1) H'
  have hG : ∀ {S : Type} [CommRing S] [Algebra ℂ S] (a : Fin r → S),
      aeval a G = aeval (Sum.elim a 1) H' := by
    intro S _ _ a
    simp only [G]
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    exact congrArg (fun f => aeval f H') (funext fun e => by rcases e with j | k' <;> simp)
  have hG0 : G = 0 := (algebraicIndependent_iff.mp hind) G (by rw [hG]; exact h1)
  have hH'0 : H' * ∏ k', X (Sum.inr k') = 0 := by
    apply MvPolynomial.funext
    intro z
    rw [map_mul, map_zero, map_prod]
    by_cases hz : ∀ k', z (Sum.inr k') ≠ 0
    · have := aeval_sumElim_factor_cx k0 hH'hom hn0' (S := ℂ) (z ∘ Sum.inl) (z ∘ Sum.inr)
      have hzz : Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) = z := by
        funext e; rcases e with j | k' <;> rfl
      rw [hzz, ← hG, hG0, map_zero, mul_zero] at this
      rw [← coe_aeval_eq_eval]
      simp only [AlgHom.coe_toRingHom] at this ⊢
      rw [this, zero_mul]
    · push Not at hz
      obtain ⟨k', hk'⟩ := hz
      rw [Finset.prod_eq_zero (Finset.mem_univ k') (by simp [hk']), mul_zero]
  have hH'z : H' = 0 := by
    rcases mul_eq_zero.mp hH'0 with h | h
    · exact h
    · exact absurd h (Finset.prod_ne_zero_iff.mpr fun k' _ => X_ne_zero _)
  rw [hH'z] at hn0'
  simp at hn0'

theorem forms_not_algebraicIndependent_cx (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (hQ : IsCxVar Q e)
    {r : ℕ} (hr : e + 1 < r) (L : Fin r → ((k : K) → ι k) → ℂ) :
    ¬ AlgebraicIndependent ℂ (forms (segC Q) L) := by
  intro hind
  obtain ⟨⟨k0⟩, ⟨hprime, hhom, hrel⟩, hdim⟩ := hQ
  haveI := hprime
  choose i0 hi0 using hrel
  have hs := algebraicIndependent_sumElim_cx Q hhom k0 i0 hi0 L hind
  let eqv : Fin (r + Fintype.card {k // k ≠ k0}) ≃ Fin r ⊕ {k // k ≠ k0} :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin _).symm)
  have h := card_le_ringKrullDim Q _ (hs.comp eqv eqv.injective)
  rw [hdim] at h
  have hc : Fintype.card {k // k ≠ k0} + 1 = Fintype.card K := by
    have h1 := Fintype.card_subtype_compl (fun k => k = k0)
    rw [Fintype.card_subtype_eq] at h1
    have := Fintype.card_pos_iff.mpr ⟨k0⟩
    simp only [ne_eq]
    omega
  have h' : r + Fintype.card {k // k ≠ k0} ≤ e + Fintype.card K := by exact_mod_cast h
  omega

def evC (Q : Ideal (MRingOver ℂ ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts Q) :
    (MRingOver ℂ ι ⧸ Q) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ Q (aeval z) fun a ha => by
    have h := hz.2 a ha
    rw [← coe_aeval_eq_eval] at h
    exact h

theorem evC_mk (Q : Ideal (MRingOver ℂ ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts Q)
    (q : MRingOver ℂ ι) : evC Q z hz (Ideal.Quotient.mk _ q) = aeval z q := rfl

theorem evC_segC (Q : Ideal (MRingOver ℂ ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts Q)
    (t : (k : K) → ι k) : evC Q z hz (segC Q t) = segre z t := by
  rw [segC, evC_mk, segMonC, map_prod]
  simp [segre]

theorem evC_forms (Q : Ideal (MRingOver ℂ ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts Q) {r : ℕ}
    (L : Fin r → ((k : K) → ι k) → ℂ) (j : Fin r) :
    evC Q z hz (forms (segC Q) L j) = ∑ t, L j t * segre z t := by
  simp only [forms, map_sum, map_smul, evC_segC, smul_eq_mul]

theorem mem_conePts (Q : Ideal (MRingOver ℂ ι)) (hQ : IsMultiHomogIdeal Q) (k0 : K) {c : ℂ}
    (hc : c ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) : scaleBlock k0 c z ∈ conePts Q := by
  refine ⟨fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, mul_ne_zero ?_ hi⟩
    split_ifs <;> simp [hc]
  · exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hQ (fun k => if k = k0 then c else 1) z hz.2

theorem false_of_forms_vanish_cx (Q : Ideal (MRingOver ℂ ι)) (hhom : IsMultiHomogIdeal Q) (k0 : K)
    {r : ℕ} (L : Fin r → ((k : K) → ι k) → ℂ) (hL : ∀ t, IntOver ℂ (forms (segC Q) L) (segC Q t))
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) (hV : ∀ j, ∑ t, L j t * segre z t = 0) : False := by
  choose i1 hi1 using hz.1
  have hs : segre z i1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hi1 k
  obtain ⟨p, hpm, hp⟩ := hL i1
  let g0 : MvPolynomial (Fin r) ℂ →+* ℂ := eval₂Hom (RingHom.id ℂ) 0
  have key : ∀ c : ℂ, c ≠ 0 → Polynomial.eval (c * segre z i1) (p.map g0) = 0 := by
    intro c hc
    have hzc := mem_conePts Q hhom k0 hc hz
    have hcomp : ((evC Q _ hzc : (MRingOver ℂ ι ⧸ Q) →+* ℂ)).comp
        ((aeval (forms (segC Q) L) : MvPolynomial (Fin r) ℂ →ₐ[ℂ] _) : MvPolynomial (Fin r) ℂ →+* _) =
        g0 := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [g0]
      · intro j
        have h1 : ∑ t, L j t * (c * segre z t) = c * ∑ t, L j t * segre z t := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring
        simp [g0, evC_forms, GroundTheory.Heights₂.Heights.SegreCoordGoodProj.segre_scaleBlock, h1, hV j]
    have := congrArg (evC Q _ hzc : (MRingOver ℂ ι ⧸ Q) →+* ℂ) hp
    rw [Polynomial.hom_eval₂, hcomp] at this
    simp only [RingHom.coe_coe, evC_segC, GroundTheory.Heights₂.Heights.SegreCoordGoodProj.segre_scaleBlock,
      map_zero] at this
    rw [Polynomial.eval_map]
    exact this
  have hinf : {x : ℂ | (p.map g0).IsRoot x}.Infinite := by
    refine Set.Infinite.mono ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro x hx
    have hx0 : x ≠ 0 := hx
    have := key (x / segre z i1) (div_ne_zero hx0 hs)
    rw [div_mul_cancel₀ x hs] at this
    exact this
  exact (hpm.map g0).ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ hinf)

theorem evC_aeval (Q : Ideal (MRingOver ℂ ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts Q) {r : ℕ}
    (ℓ : Fin r → MRingOver ℂ ι ⧸ Q) (F : MvPolynomial (Fin r) ℂ) :
    evC Q z hz (aeval ℓ F) = aeval (fun j => evC Q z hz (ℓ j)) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp]

theorem exists_goodProj_coord (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (i : (k : K) → ι k) :
    IsCxVar Q e → (∃ z ∈ conePts Q, segre z i ≠ 0) →
    ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ),
      IsSetGoodProj (conePts Q) Ψ ∧ ∀ w, Ψ w 0 = w i := by
  intro hQ ⟨z0, hz0, hz0i⟩
  classical
  obtain ⟨r, hr, L, hL⟩ := exists_linear_normalization (k := ℂ) (segC Q) (e + 1)
    (fun r L hr => forms_not_algebraicIndependent_cx Q e hQ hr L)
  obtain ⟨⟨k0⟩, ⟨hprime, hhom, -⟩, -⟩ := hQ
  haveI := hprime
  cases r with
  | zero => exact (false_of_forms_vanish_cx Q hhom k0 L hL hz0 fun j => j.elim0).elim
  | succ r' =>
  have hw : segC Q i ≠ 0 := fun h =>
    hz0i (by rw [← evC_segC Q z0 hz0, h, map_zero])
  obtain ⟨p, hpm, hp, hc0⟩ :=
    GroundTheory.Heights₂.Heights.SegreCoordGoodProj.exists_monic_coeff_zero_ne _ hw (hL i)
  set c0 := p.coeff 0 with hc0def
  have hsupp : ∀ m ∈ (homogeneousComponent c0.totalDegree c0).support,
      Finsupp.degree m = c0.totalDegree := by
    intro m hm
    rw [mem_support_iff, coeff_homogeneousComponent] at hm
    by_contra hne
    exact hm (if_neg hne)
  obtain ⟨lam, hlam⟩ := exists_eval_cons_one_ne_zero _ _ hsupp
    (homogeneousComponent_totalDegree_ne_zero hc0)
  let Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
    { toFun := fun w j => Fin.cases (w i) (fun j' : Fin e => if h : (j' : ℕ) < r' then
          ∑ t, (L (Fin.succ ⟨j', h⟩) t - lam ⟨j', h⟩ * L 0 t) * w t else 0) j
      map_add' := by
        intro w w'
        funext j
        refine Fin.cases ?_ (fun j' => ?_) j
        · simp
        · simp only [Fin.cases_succ, Pi.add_apply]
          split_ifs <;> simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c w
        funext j
        refine Fin.cases ?_ (fun j' => ?_) j
        · simp
        · simp only [Fin.cases_succ, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          split_ifs <;> simp [Finset.mul_sum, mul_left_comm] }
  refine ⟨Ψ, fun z hz hΨ => ?_, fun w => rfl⟩
  set V : Fin (r' + 1) → ℂ := fun j => ∑ t, L j t * segre z t with hVdef
  have hzi : segre z i = 0 := congrFun hΨ 0
  have hVs : ∀ j : Fin r', V j.succ = lam j * V 0 := by
    intro j
    have h := congrFun hΨ (Fin.succ ⟨j, by omega⟩)
    simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, Fin.cases_succ, dif_pos j.2, Fin.eta,
      Pi.zero_apply] at h
    simp only [hVdef]
    rw [← sub_eq_zero, Finset.mul_sum, ← Finset.sum_sub_distrib, ← h]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  by_cases hs : V 0 = 0
  · refine false_of_forms_vanish_cx Q hhom k0 L hL hz fun j => ?_
    refine Fin.cases hs (fun j => ?_) j
    exact (hVs j).trans (by rw [hs, mul_zero])
  let g : Polynomial ℂ := (ReciprocityTheory.ChartRestriction.G.Geo.subst lam c0).map
    ((aeval (0 : Fin r' → ℂ) : MvPolynomial (Fin r') ℂ →ₐ[ℂ] ℂ) : MvPolynomial (Fin r') ℂ →+* ℂ)
  have hgD : g.coeff c0.totalDegree ≠ 0 := by
    simp only [g, Polynomial.coeff_map, subst_coeff_totalDegree]
    simpa using hlam
  have hroot : ∀ x : ℂ, x ≠ 0 → g.eval x = 0 := by
    intro x hx
    have hc : x / V 0 ≠ 0 := div_ne_zero hx hs
    have hzc := mem_conePts Q hhom k0 hc hz
    set u : Fin (r' + 1) → ℂ := fun j => x / V 0 * V j with hudef
    have hu0 : u 0 = x := div_mul_cancel₀ x hs
    have hu' : (fun j : Fin r' => u j.succ - lam j • u 0) = 0 := by
      funext j
      simp only [hudef, hVs j, smul_eq_mul, Pi.zero_apply]
      ring
    have h1 : aeval u c0 = 0 := by
      have := congrArg (evC Q _ hzc : (MRingOver ℂ ι ⧸ Q) →+* ℂ) hp
      rw [Polynomial.hom_eval₂] at this
      simp only [RingHom.coe_coe, evC_segC, GroundTheory.Heights₂.Heights.SegreCoordGoodProj.segre_scaleBlock,
        hzi, mul_zero, Polynomial.eval₂_at_zero, map_zero, RingHom.comp_apply] at this
      rw [← this]
      simp only [AlgHom.coe_toRingHom, RingHom.coe_coe, evC_aeval]
      refine congrArg (fun v => aeval v c0) (funext fun j => ?_)
      rw [evC_forms]
      simp only [GroundTheory.Heights₂.Heights.SegreCoordGoodProj.segre_scaleBlock, hudef, hVdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    have h2 := eval₂_subst lam u c0
    rw [hu', hu0, h1] at h2
    rw [Polynomial.eval_map]
    exact h2
  have hg0 : g = 0 := Polynomial.eq_zero_of_infinite_isRoot g
    (Set.Infinite.mono (fun x hx => hroot x hx) (Set.finite_singleton (0 : ℂ)).infinite_compl)
  exact hgD (by rw [hg0, Polynomial.coeff_zero])

end GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj
