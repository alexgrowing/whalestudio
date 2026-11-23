import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.FunFieldEquivMemChartRingIff
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.AddBlockEquivSymmChartRingMap
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsChartFormsIffIsFormSystem
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PChartLatSection
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PSectionSmall
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.MemMCoordIdealIffOfIsWeightedHomogeneous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ chartLat)
open _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.AddBlockData

noncomputable section

namespace SmallSectionsEquivalence

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem eval₂_mul_const {σ Ω : Type*} [CommRing Ω] {F : MvPolynomial σ ℤ} {τ : ℕ}
    (hF : F.IsHomogeneous τ) (x : σ → Ω) (r : Ω) :
    eval₂ (Int.castRingHom Ω) (fun j ↦ x j * r) F = eval₂ (Int.castRingHom Ω) x F * r ^ τ := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [eval₂_sum, eval₂_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hdeg : ∑ j ∈ m.support, m j = τ := by
    have h := hF (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  rw [eval₂_monomial, eval₂_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem map_aeval_int {σ A B : Type*} [CommRing A] [CommRing B] {instA : Algebra ℤ A} [Algebra ℤ B]
    {Fφ : Type*} [FunLike Fφ A B] [RingHomClass Fφ A B] (φ : Fφ) (x : σ → A) (F : MvPolynomial σ ℤ) :
    φ (aeval x F) = aeval (fun j ↦ φ (x j)) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp only [eq_intCast, map_intCast]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, hp, aeval_X]

theorem aeval_eq_eval₂_cast {σ A : Type*} [CommRing A] {_ : Algebra ℤ A} (x : σ → A)
    (F : MvPolynomial σ ℤ) : aeval x F = eval₂ (Int.castRingHom A) x F := by
  rw [aeval_def, RingHom.ext_int (algebraMap ℤ A) (Int.castRingHom A)]

theorem aeval_mul_const {σ Ω : Type*} [CommRing Ω] {_ : Algebra ℤ Ω} {F : MvPolynomial σ ℤ} {τ : ℕ}
    (hF : F.IsHomogeneous τ) (x : σ → Ω) (r : Ω) :
    aeval (fun j ↦ x j * r) F = aeval x F * r ^ τ := by
  rw [aeval_eq_eval₂_cast, aeval_eq_eval₂_cast, eval₂_mul_const hF]

theorem isWeightedHomogeneous_aeval {σ : Type*} {F : MvPolynomial σ ℤ} {τ : ℕ}
    (hF : F.IsHomogeneous τ) {g : σ → MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hg : ∀ j, IsWeightedHomogeneous (coordDeg n) (g j) δ) :
    IsWeightedHomogeneous (coordDeg n) (aeval g F) (τ • δ) := by
  rw [F.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm ↦ ?_
  have hdeg : ∑ j ∈ m.support, m j = τ := by
    have h := hF (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  rw [aeval_monomial, Finsupp.prod, algebraMap_eq]
  have h := (isWeightedHomogeneous_C (coordDeg n) (coeff m F)).mul
    (IsWeightedHomogeneous.prod m.support (fun j ↦ g j ^ m j) (fun j ↦ m j • δ)
      fun j _ ↦ (hg j).pow (m j))
  rwa [zero_add, ← Finset.sum_smul, hdeg] at h

theorem aeval_mem_chartLat {σ : Type*} {Ω : Type} [Field Ω] (y : Coord n → Ω) (a : ι → ℤ)
    (x : σ → Ω)
    (hx : ∀ c : (k : ι) → Fin (n k + 1), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ j,
      x j * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ chartRingZ y c)
    {F : MvPolynomial σ ℤ} {τ : ℕ} (hF : F.IsHomogeneous τ) :
    eval₂ (Int.castRingHom Ω) x F ∈ chartLat y a τ := by
  intro c hc
  have hpow : ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) = (∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ τ := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [hpow, ← eval₂_mul_const hF]
  have key : ∀ G : MvPolynomial σ ℤ,
      eval₂ (Int.castRingHom Ω) (fun j ↦ x j * ∏ k, y ⟨k, c k⟩ ^ (-a k)) G ∈ chartRingZ y c :=
    fun G ↦ by
    induction G using MvPolynomial.induction_on with
    | C r =>
      rw [eval₂_C, eq_intCast]
      exact intCast_mem _ r
    | add p q hp hq =>
      rw [eval₂_add]
      exact add_mem hp hq
    | mul_X p j hp =>
      rw [eval₂_mul, eval₂_X]
      exact mul_mem hp (hx c hc j)
  exact key F

theorem val_eq_zero_iff (P : ArithVariety n) (f : MvPolynomial (Coord n) ℤ) :
    val P f = 0 ↔ f ∈ P.ideal := by
  rw [← funFieldEquiv_mkF, map_eq_zero_iff _ (funFieldEquiv P).injective, P.mkF_eq_zero_iff]

theorem monomial_mem_chartLat {P : ArithVariety n} (D : AddBlockData P) (τ : ℕ)
    (μ : Fin (D.m + 1) → ℕ) (hμ : ∑ j, μ j = τ) :
    ∏ j, D.x j ^ μ j ∈ chartLat (genPt P) D.deg τ := by
  have hF : (∏ j, (X j : MvPolynomial (Fin (D.m + 1)) ℤ) ^ μ j).IsHomogeneous τ := by
    rw [← hμ]
    exact IsHomogeneous.prod _ _ _ fun j _ ↦ isHomogeneous_X_pow j (μ j)
  have h := aeval_mem_chartLat (genPt P) D.deg D.x ?_ hF
  · simpa [eval₂_prod, eval₂_pow, eval₂_X] using h
  intro c hc j
  have hlive : IsLive P c := fun k hk ↦ hc k ((val_eq_zero_iff P _).mpr hk)
  have h1 := D.chart c hlive j
  simpa [chartPow, chartRing] using h1

theorem mem_chartRingZ_of_mem_chartRing (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1))
    {u : P.FunField} (hu : u ∈ P.chartRing c) : u ∈ chartRingZ P.genericPt c := by
  induction hu using Subring.closure_induction with
  | mem u hu =>
    obtain ⟨v, rfl⟩ := hu
    exact (@Algebra.subset_adjoin ℤ P.FunField _ _ (Ring.toIntAlgebra _) _) ⟨v, rfl⟩
  | zero => exact zero_mem _
  | one => exact one_mem _
  | add u w _ _ hu hw => exact add_mem hu hw
  | neg u _ hu => exact neg_mem hu
  | mul u w _ _ hu hw => exact mul_mem hu hw

theorem aeval_genericPt (P : ArithVariety n) {_ : Algebra ℤ P.FunField} (f : MvPolynomial (Coord n) ℤ) :
    aeval P.genericPt f = P.mkF f := by
  rw [aeval_eq_eval₂_cast, P.eval₂_genericPt]

theorem exists_section (P : ArithVariety n) (D : Heights.AddBlockData P) (τ : ℕ)
    (F : MvPolynomial (Fin (D.size + 1)) ℤ) (hF : F.IsHomogeneous τ) :
    ∃ s : IntegralSection P (τ • D.deg), s.toFun = aeval D.elt F := by
  have hmem : aeval D.elt F ∈ chartLat (ι := blockIdx n) P.genericPt D.deg τ := by
    rw [aeval_eq_eval₂_cast]
    refine aeval_mem_chartLat P.genericPt D.deg D.elt ?_ hF
    intro c hc j
    have hlive : P.IsLive c := fun k hk ↦ hc k ((P.mkF_eq_zero_iff _).mpr hk)
    have h2 : D.elt j * ∏ k, P.genericPt ⟨k, c k⟩ ^ (-D.deg k) = D.elt j / P.chartPow c D.deg := by
      rw [div_eq_mul_inv, ArithVariety.chartPow, ← Finset.prod_inv_distrib]
      simp only [zpow_neg]
      rfl
    rw [h2]
    exact mem_chartRingZ_of_mem_chartRing P c (D.chart_mem c hlive j)
  obtain ⟨t, ht⟩ := (ChartLatSection.proof ι n P.FunField P.genericPt P D.deg τ _
    P.mCoordIdeal_genericPt.symm).mp hmem
  refine ⟨t, ?_⟩
  have hden := SectionSmall.mkF_den_ne_zero t
  have h := (ht t.num t.den t.numDeg t.denDeg t.num_isHomogeneous t.den_isHomogeneous
    (fun k ↦ by linarith [t.deg_eq k])).mpr
    (by rw [IntegralSection.toFun, div_mul_cancel₀ _ hden])
  rw [aeval_genericPt, aeval_genericPt] at h
  rw [IntegralSection.toFun, h, mul_div_cancel_right₀ _ hden]

theorem mkF_aeval_forms {P : ArithVariety n} {D : Heights.AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (h : D.IsFormSystem d g) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {F : MvPolynomial (Fin (D.size + 1)) ℤ} {τ : ℕ} (hF : F.IsHomogeneous τ) :
    P.mkF (aeval (g c) F) = aeval D.elt F * P.mkF (chartMonomial c d ^ τ) := by
  rw [map_aeval_int, map_pow]
  simp_rw [h.value c hc]
  rw [show (fun j ↦ P.mkF (chartMonomial c d) * D.elt j) =
      fun j ↦ D.elt j * P.mkF (chartMonomial c d) from funext fun j ↦ mul_comm _ _,
    aeval_mul_const hF]

theorem chart_mem {P : ArithVariety n} {D : Heights.AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (h : D.IsFormSystem d g) {F : MvPolynomial (Fin (D.size + 1)) ℤ} {τ : ℕ}
    (hF : F.IsHomogeneous τ) {p q : MvPolynomial (Coord n) ℤ}
    (hpq : P.mkF p = aeval D.elt F * P.mkF q) (c : (k : ι) → Fin (n k + 1)) (hc : P.IsLive c) :
    chartMonomial c d ^ τ * p - aeval (g c) F * q ∈ P.ideal := by
  rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, mkF_aeval_forms h hc hF, hpq]
  ring

theorem bound_of_chart {P : ArithVariety n} {D : Heights.AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (h : D.IsFormSystem d g) {F : MvPolynomial (Fin (D.size + 1)) ℤ} {τ : ℕ}
    (hF : F.IsHomogeneous τ) (N : HermLine n)
    (hb : ∀ c, P.IsLive c → ∀ z ∈ P.points ℂ,
      ‖evalCone z (aeval (g c) F)‖ ≤ ‖evalCone z (chartMonomial c d ^ τ)‖ * N.metric z ^ τ)
    {p q : MvPolynomial (Coord n) ℤ} (hpq : P.mkF p = aeval D.elt F * P.mkF q) :
    ∀ z ∈ P.points ℂ, ‖evalCone z p‖ ≤ ‖evalCone z q‖ * N.metric z ^ τ := by
  intro z hz
  obtain ⟨c, hcz⟩ := SectionSmall.exists_chart hz
  have hc : P.IsLive c := SectionSmall.live_of_ne hz hcz
  have hm : evalCone z (chartMonomial c d ^ τ) ≠ 0 := by
    rw [← chartMonomial_nsmul]
    exact SectionSmall.evalCone_chartMonomial_ne_zero hcz _
  have h0 := hz.2 _ (chart_mem h hF hpq c hc)
  have he : evalCone z (chartMonomial c d ^ τ) * evalCone z p =
      evalCone z (aeval (g c) F) * evalCone z q := by
    simp only [evalCone, eval₂_sub, eval₂_mul] at h0 ⊢
    exact sub_eq_zero.mp h0
  have hle : ‖evalCone z (chartMonomial c d ^ τ)‖ * ‖evalCone z p‖ ≤
      ‖evalCone z (chartMonomial c d ^ τ)‖ * (‖evalCone z q‖ * N.metric z ^ τ) := by
    rw [← norm_mul, he, norm_mul]
    calc ‖evalCone z (aeval (g c) F)‖ * ‖evalCone z q‖
        ≤ ‖evalCone z (chartMonomial c d ^ τ)‖ * N.metric z ^ τ * ‖evalCone z q‖ :=
          mul_le_mul_of_nonneg_right (hb c hc z hz) (norm_nonneg _)
      _ = ‖evalCone z (chartMonomial c d ^ τ)‖ * (‖evalCone z q‖ * N.metric z ^ τ) := by ring
  exact le_of_mul_le_mul_left hle (norm_pos_iff.mpr hm)

end SmallSectionsEquivalence

open SmallSectionsEquivalence

theorem SmallSections.smallSections_of_alt (hB : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.SmallSections.Statement) :
    GroundTheory.Heights₂.Heights.SmallSections.Statement := by
  intro ι _ _ n P D
  refine ⟨fun τ F hF ↦ exists_section P D τ F hF, ?_⟩
  intro N hN d g h r Gs δ hGs τ F hF p q hpq
  refine ⟨chart_mem h hF hpq, fun hsmall ↦ bound_of_chart h hF N ?_ hpq⟩
  intro c hc z hz
  have hgj : ∀ j, IsWeightedHomogeneous (coordDeg n) (g c j)
      (fun k ↦ ((d k : ℤ) + D.deg k).toNat) := fun j ↦ by
    obtain ⟨δ', hδ', hd'⟩ := h.homog c j
    convert hδ' using 1
    funext k
    have := hd' k
    omega
  have hsmall' : ∀ w ∈ conePoints (ofObjects D).ext ℂ,
      ‖eval₂ (Int.castRingHom ℂ) (newPart w) F‖ ≤
        hPlus (ChartForms.ofFormSystem h) (GenSystem.ofIsHomogGenerators hGs) N w ^ τ := by
    intro w hw
    exact hsmall w (by rw [AddBlockEq.extPoints_eq]; exact hw)
  have hval : val P (aeval (g c) F) = aeval (ofObjects D).x F * val P (chartMonomial c d ^ τ) := by
    have e := congrArg (funFieldEquiv P) (mkF_aeval_forms h hc hF)
    rw [funFieldEquiv_mkF, map_mul, funFieldEquiv_mkF, map_aeval_int] at e
    exact e
  have hdeg : ∀ k, (((τ • fun k ↦ ((d k : ℤ) + D.deg k).toNat) k : ℕ) : ℤ) =
      ((τ • d) k : ℕ) + τ * (ofObjects D).deg k := fun k ↦ by
    have := h.nonneg k
    simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
    rw [Int.toNat_of_nonneg this]
    change (τ : ℤ) * (d k + D.deg k) = τ * d k + τ * D.deg k
    ring
  have hB' := (hB ι n P (ofObjects D) (ChartForms.ofFormSystem h)
    (GenSystem.ofIsHomogGenerators hGs) N hN τ).2 F hF hsmall' (aeval (g c) F)
    (chartMonomial c d ^ τ) _ _ (isWeightedHomogeneous_aeval hF hgj)
    ((isWeightedHomogeneous_chartMonomial c d).pow τ) hdeg hval
  exact hB'.2 z hz

theorem SmallSections.mpr_of_first (hA : GroundTheory.Heights₂.Heights.SmallSections.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.SmallSections.Statement := by
  intro ι _ _ n P D G Γ N hN τ
  refine ⟨fun μ hμ ↦ monomial_mem_chartLat D τ μ hμ, ?_⟩
  intro F hF hsmall g h dg dh hg hh hd hval
  have hx : (fun j ↦ funFieldEquiv P ((toObjects D).elt j)) = D.x :=
    funext fun j ↦ RingEquiv.apply_symm_apply _ _
  have hmk : P.mkF g = aeval (toObjects D).elt F * P.mkF h := by
    apply (funFieldEquiv P).injective
    have e1 := map_aeval_int (instA := inferInstance) (funFieldEquiv P) (toObjects D).elt F
    rw [map_mul, funFieldEquiv_mkF, funFieldEquiv_mkF, e1, hx]
    exact hval
  obtain ⟨h1, h2⟩ := (hA ι n P (toObjects D)).2 N hN G.d G.g G.isFormSystem Γ.r Γ.f Γ.δ
    Γ.isHomogGenerators τ F hF g h hmk
  refine ⟨fun c hc ↦ h1 c hc, h2 fun w hw ↦ hsmall w ?_⟩
  rw [← AddBlockEq.addBlockEquiv_symm_conePoints]
  exact hw

theorem SmallSections.equiv :
    GroundTheory.Heights₂.Heights.SmallSections.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.SmallSections.Statement :=
  ⟨SmallSections.mpr_of_first, SmallSections.smallSections_of_alt⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
