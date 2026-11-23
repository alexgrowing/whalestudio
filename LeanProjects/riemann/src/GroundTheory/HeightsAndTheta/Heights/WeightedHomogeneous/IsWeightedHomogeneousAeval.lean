import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SmallSections

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem aeval_mul_of_isHomogeneous {σ A : Type*} [CommRing A] [Algebra ℤ A] {F : MvPolynomial σ ℤ} {τ : ℕ}
    (hF : F.IsHomogeneous τ) (t : A) (x : σ → A) :
    aeval (fun j ↦ t * x j) F = t ^ τ * aeval x F := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, aeval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ ↦ ?_
  have hw : (μ.sum fun _ e ↦ e) = τ := by
    have h := hF (mem_support_iff.mp hμ)
    rw [Finsupp.weight_apply] at h
    simpa using h
  rw [← hw]
  simp only [Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

omit [Fintype ι] in

theorem isWeightedHomogeneous_aeval {σ : Type*} {F : MvPolynomial σ ℤ} {τ : ℕ} (hF : F.IsHomogeneous τ)
    {g : σ → MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hg : ∀ j, IsWeightedHomogeneous (coordDeg n) (g j) δ) :
    IsWeightedHomogeneous (coordDeg n) (aeval g F) (τ • δ) := by
  rw [F.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun μ hμ ↦ ?_
  have hw : (μ.sum fun _ e ↦ e) = τ := by
    have h := hF (mem_support_iff.mp hμ)
    rw [Finsupp.weight_apply] at h
    simpa using h
  have h := IsWeightedHomogeneous.prod μ.support (fun i ↦ g i ^ μ i) (fun i ↦ μ i • δ)
    (fun i _ ↦ (hg i).pow (μ i))
  rw [← hw, Finsupp.sum, Finset.sum_smul, aeval_monomial, algebraMap_eq]
  exact h.C_mul _

omit [Fintype ι] in

theorem mkF_aeval (P : ArithVariety n) {σ : Type*} (g : σ → MvPolynomial (Coord n) ℤ)
    (F : MvPolynomial σ ℤ) : P.mkF (aeval g F) = aeval (fun j ↦ P.mkF (g j)) F := by
  rw [aeval_def, aeval_def, eval₂_comp_left]
  congr 1

omit [Fintype ι] [DecidableEq ι] in

theorem evalCone_aeval {σ : Type*} (z : Cone n ℂ) (g : σ → MvPolynomial (Coord n) ℤ)
    (F : MvPolynomial σ ℤ) :
    evalCone z (aeval g F) = eval₂ (Int.castRingHom ℂ) (fun j ↦ evalCone z (g j)) F := by
  change (eval₂Hom (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2)) (aeval g F) = _
  rw [aeval_def, eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

omit [Fintype ι] in

theorem mkF_X_ne_zero {P : ArithVariety n} {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (k : ι) :
    P.mkF (X ⟨k, c k⟩) ≠ 0 := fun h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)

theorem mkF_chartMonomial_ne_zero {P : ArithVariety n} {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    (d : ι → ℕ) : P.mkF (chartMonomial c d) ≠ 0 := by
  rw [chartMonomial, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ by rw [map_pow]; exact pow_ne_zero _ (mkF_X_ne_zero hc k)

theorem mkF_aeval_forms {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) {τ : ℕ} {F : MvPolynomial (Fin (D.size + 1)) ℤ}
    (hF : F.IsHomogeneous τ) :
    P.mkF (aeval (g c) F) = P.mkF (chartMonomial c d) ^ τ * aeval D.elt F := by
  rw [mkF_aeval, show (fun j ↦ P.mkF (g c j)) = fun j ↦ P.mkF (chartMonomial c d) * D.elt j from
    funext (hg.value c hc), aeval_mul_of_isHomogeneous hF]

omit [Fintype ι] in

theorem isLive_of_mem_points {P : ArithVariety n} {z : Cone n ℂ} (hz : z ∈ P.points ℂ)
    {c : (k : ι) → Fin (n k + 1)} (hzc : ∀ k, z k (c k) ≠ 0) : P.IsLive c :=
  fun k hk ↦ hzc k (by simpa [evalCone] using hz.2 _ hk)

theorem exists_mul_pow_eq_mkF {P : ArithVariety n} {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {u : P.FunField} (hu : u ∈ P.chartRing c) :
    ∃ (N : ℕ) (E : MvPolynomial (Coord n) ℤ), u * P.mkF (chartMonomial c 1) ^ N = P.mkF E := by
  unfold ArithVariety.chartRing at hu
  induction hu using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    refine ⟨1, X v * ∏ k ∈ Finset.univ.erase v.1, X ⟨k, c k⟩, ?_⟩
    have h1 : P.mkF (chartMonomial c 1) =
        P.mkF (X ⟨v.1, c v.1⟩) * ∏ k ∈ Finset.univ.erase v.1, P.mkF (X ⟨k, c k⟩) := by
      rw [chartMonomial, map_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v.1)]
      simp
    have hne := mkF_X_ne_zero hc v.1
    rw [pow_one, h1, map_mul, map_prod, ArithVariety.chartCoord]
    field_simp
  | zero => exact ⟨0, 0, by simp⟩
  | one => exact ⟨0, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, E, hE⟩ := hx
    obtain ⟨N', E', hE'⟩ := hy
    refine ⟨N + N', E * chartMonomial c 1 ^ N' + E' * chartMonomial c 1 ^ N, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hE, ← hE', pow_add]
    ring
  | neg x _ hx =>
    obtain ⟨N, E, hE⟩ := hx
    exact ⟨N, -E, by rw [map_neg, ← hE]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨N, E, hE⟩ := hx
    obtain ⟨N', E', hE'⟩ := hy
    exact ⟨N + N', E * E', by rw [map_mul, ← hE, ← hE', pow_add]; ring⟩

theorem exists_evalCone_ne_zero {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} (hzc : ∀ k, z k (c k) ≠ 0) :
    ∃ j, evalCone z (g c j) ≠ 0 := by
  have hc : P.IsLive c := isLive_of_mem_points hz hzc
  by_contra hall
  simp only [not_exists, not_not] at hall
  obtain ⟨u, hu, hsum⟩ := D.generating c hc
  have hex : ∀ j, ∃ (N : ℕ) (E : MvPolynomial (Coord n) ℤ),
      u j * P.mkF (chartMonomial c 1) ^ N = P.mkF E := fun j ↦ exists_mul_pow_eq_mkF hc (hu j)
  choose N E hE using hex
  obtain ⟨S, hSdef⟩ : ∃ S, S = ∑ j, N j := ⟨_, rfl⟩
  have hcp : P.chartPow c D.deg ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (mkF_X_ne_zero hc k)
  have hxu : ∑ j, u j * D.elt j = P.chartPow c D.deg := by
    have h := congrArg (· * P.chartPow c D.deg) hsum
    simp only [Finset.sum_mul, one_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_assoc, div_mul_cancel₀ _ hcp]
  let R : MvPolynomial (Coord n) ℤ := ∏ k, X ⟨k, c k⟩ ^ ((d k : ℤ) + D.deg k).toNat
  have hR : P.mkF R = P.mkF (chartMonomial c d) * P.chartPow c D.deg := by
    simp only [R, chartMonomial, ArithVariety.chartPow, map_prod, map_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [← zpow_natCast, Int.toNat_of_nonneg (hg.nonneg k), zpow_add₀ (mkF_X_ne_zero hc k), zpow_natCast]
  have hterm : ∀ j, P.mkF (E j * chartMonomial c 1 ^ (S - N j) * g c j) =
      P.mkF (chartMonomial c 1) ^ S * P.mkF (chartMonomial c d) * (u j * D.elt j) := by
    intro j
    have hS : N j ≤ S := hSdef ▸ Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    rw [map_mul, map_mul, map_pow, ← hE j, hg.value c hc j]
    conv_rhs => rw [← Nat.add_sub_cancel' hS, pow_add]
    ring
  have hmem : chartMonomial c 1 ^ S * R - ∑ j, E j * chartMonomial c 1 ^ (S - N j) * g c j ∈ P.ideal := by
    rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_pow, hR, map_sum]
    simp only [hterm]
    rw [← Finset.mul_sum, hxu]
    ring
  have h0 := hz.2 _ hmem
  have hall' : ∀ j, eval₂ (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2) (g c j) = 0 := hall
  simp only [evalCone, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_sum, hall', mul_zero,
    Finset.sum_const_zero, sub_zero] at h0
  have hM : evalCone z (chartMonomial c 1) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hzc k)
  have hRz : evalCone z R ≠ 0 := by
    simp only [R, evalCone, eval₂_prod, eval₂_pow, eval₂_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hzc k)
  exact mul_ne_zero (pow_ne_zero S hM) hRz h0

def formSubst {P : ArithVariety n} (D : AddBlockData P)
    (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ)
    (c : (k : ι) → Fin (n k + 1)) : Coord D.extSizes → MvPolynomial (Coord n) ℤ
  | ⟨none, j⟩ => g c j
  | ⟨some k, i⟩ => X ⟨k, i⟩

theorem aeval_formSubst_mem {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) {f : MvPolynomial (Coord D.extSizes) ℤ}
    (hf : f ∈ D.extIdeal) : aeval (formSubst D g c) f ∈ P.ideal := by
  let ψ : MvPolynomial (Option ι) P.FunField →+* P.FunField :=
    eval fun o ↦ o.elim (P.mkF (chartMonomial c d)) fun _ ↦ 1
  have hid : P.mkF.comp (aeval (formSubst D g c)).toRingHom = ψ.comp D.extMap := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun v ↦ ?_)
    · simp [AddBlockData.extMap]
    · obtain ⟨o, i⟩ := v
      cases o with
      | none =>
        simp [AddBlockData.extMap, AddBlockData.extVal, formSubst, ψ, hg.value c hc i, mul_comm]
      | some k =>
        simp [AddBlockData.extMap, AddBlockData.extVal, formSubst, ψ]
  rw [← P.mkF_eq_zero_iff]
  have h := congrArg (fun φ ↦ φ f) hid
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h
  rw [h, (RingHom.mem_ker).mp hf, map_zero]

theorem joinPt_mem_extPoints {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} (hzc : ∀ k, z k (c k) ≠ 0) :
    D.joinPt z (fun j ↦ evalCone z (g c j)) ∈ D.extPoints := by
  have hc : P.IsLive c := isLive_of_mem_points hz hzc
  refine ⟨fun o ↦ ?_, fun f hf ↦ ?_⟩
  · cases o with
    | none =>
      obtain ⟨j, hj⟩ := exists_evalCone_ne_zero hg hz hzc
      exact fun h ↦ hj (congrFun h j)
    | some k => exact hz.1 k
  · have h := hz.2 _ (aeval_formSubst_mem hg hc hf)
    rw [evalCone_aeval] at h
    rw [← h, evalCone]
    congr 1
    funext v
    obtain ⟨o, i⟩ := v
    cases o with
    | none => rfl
    | some k => simp [formSubst, evalCone, AddBlockData.joinPt]

theorem evalCone_cross {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} (hzc : ∀ k, z k (c k) ≠ 0)
    (c' : (k : ι) → Fin (n k + 1)) (j : Fin (D.size + 1)) :
    evalCone z (g c' j) =
      evalCone z (chartMonomial c' d) * evalCone z (g c j) / evalCone z (chartMonomial c d) := by
  have hc : P.IsLive c := isLive_of_mem_points hz hzc
  have hm : evalCone z (chartMonomial c d) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hzc k)
  by_cases hc' : P.IsLive c'
  · have hmem : chartMonomial c' d * g c j - chartMonomial c d * g c' j ∈ P.ideal := by
      rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc j, hg.value c' hc' j]
      ring
    have h0 := hz.2 _ hmem
    rw [eq_div_iff hm]
    simp only [evalCone, eval₂_sub, eval₂_mul, sub_eq_zero] at h0 ⊢
    rw [h0]
    ring
  · obtain ⟨k, hk⟩ : ∃ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∈ P.ideal := by
      by_contra h
      exact hc' fun k hk ↦ h ⟨k, hk⟩
    have hzk : z k (c' k) = 0 := by simpa [evalCone] using hz.2 _ hk
    have hm' : evalCone z (chartMonomial c' d) = 0 := by
      rw [evalCone_chartMonomial]
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      rw [hzk]
      exact zero_pow (by have := hg.pos k; omega)
    rw [hg.dead c' hc' j, hm']
    simp [evalCone]

theorem plusMetric_joinPt {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    (N : HermLine n) {r : ℕ} {G : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ}
    (hG : P.IsHomogGenerators G δ)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} (hzc : ∀ k, z k (c k) ≠ 0) :
    D.plusMetric N d g G δ (D.joinPt z (fun j ↦ evalCone z (g c j))) =
      ‖evalCone z (chartMonomial c d)‖ * N.metric z := by
  have hm : evalCone z (chartMonomial c d) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hzc k)
  have hm2 : 0 < ‖evalCone z (chartMonomial c d)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hm) 2
  have hGz : ∀ i, evalCone z (G i) = 0 := fun i ↦
    hz.2 _ (hG.span_eq ▸ Ideal.subset_span ⟨i, rfl⟩)
  have hL : 0 < ∑ j, ‖evalCone z (g c j)‖ ^ 2 := by
    obtain ⟨j, hj⟩ := exists_evalCone_ne_zero hg hz hzc
    exact Finset.sum_pos' (fun _ _ ↦ by positivity) ⟨j, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hj) 2⟩
  have hS : 0 < ∑ c', ‖evalCone z (chartMonomial c' d)‖ ^ 2 :=
    Finset.sum_pos' (fun _ _ ↦ by positivity) ⟨c, Finset.mem_univ _, hm2⟩
  have hden : D.den d g G δ z = (∑ c', ‖evalCone z (chartMonomial c' d)‖ ^ 2) *
      (∑ j, ‖evalCone z (g c j)‖ ^ 2) / ‖evalCone z (chartMonomial c d)‖ ^ 2 := by
    have hG0 : ∑ i, ‖evalCone z (G i)‖ ^ 2 *
        ∏ k, l2Norm (z k) ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) = 0 :=
      Finset.sum_eq_zero fun i _ ↦ by rw [hGz i, norm_zero]; ring
    rw [AddBlockData.den, hG0, add_zero, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun c' _ ↦ ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [evalCone_cross hg hz hzc c' j, norm_div, norm_mul, div_pow, mul_pow]
  have hq : (∑ c', ‖evalCone z (chartMonomial c' d)‖ ^ 2) / D.den d g G δ z =
      ‖evalCone z (chartMonomial c d)‖ ^ 2 / ∑ j, ‖evalCone z (g c j)‖ ^ 2 := by
    rw [hden]
    field_simp
  change N.metric z * l2Norm (fun j ↦ evalCone z (g c j)) *
    Real.sqrt ((∑ c', ‖evalCone z (chartMonomial c' d)‖ ^ 2) / D.den d g G δ z) = _
  rw [hq, l2Norm, mul_assoc, ← Real.sqrt_mul hL.le, mul_div_cancel₀ _ hL.ne',
    Real.sqrt_sq (norm_nonneg _), mul_comm]

end SmallSections

theorem SmallSections.proof (hForms : ChartFormsAlt.Statement) : SmallSections.Statement := by
  intro ι _ _ n P D
  refine ⟨fun τ F hF ↦ ?_, fun N _ d g hg r G δ hG τ F hF p q hpq ↦ ?_⟩
  · obtain ⟨d₀, hd₀⟩ := hForms ι n P D
    obtain ⟨g, hg⟩ := hd₀ d₀ le_rfl
    obtain ⟨c₀, hc₀⟩ := P.exists_chart
    have hc₀' : P.IsLive c₀ := hc₀
    let e : ι → ℕ := fun k ↦ ((d₀ k : ℤ) + D.deg k).toNat
    have he : ∀ k, (e k : ℤ) = d₀ k + D.deg k := fun k ↦ Int.toNat_of_nonneg (hg.nonneg k)
    have hge : ∀ c j, IsWeightedHomogeneous (coordDeg n) (g c j) e := by
      intro c j
      obtain ⟨δ', h, hδ'⟩ := hg.homog c j
      have : δ' = e := funext fun k ↦ by have := hδ' k; have := he k; omega
      exact this ▸ h
    have hne : P.mkF (chartMonomial c₀ d₀) ^ τ ≠ 0 := pow_ne_zero _ (SmallSections.mkF_chartMonomial_ne_zero hc₀' d₀)
    refine ⟨{ num := aeval (g c₀) F
              den := chartMonomial c₀ d₀ ^ τ
              numDeg := τ • e
              denDeg := τ • d₀
              num_isHomogeneous := SmallSections.isWeightedHomogeneous_aeval hF (hge c₀)
              den_isHomogeneous := (isWeightedHomogeneous_chartMonomial c₀ d₀).pow τ
              deg_eq := fun k ↦ ?_
              den_not_mem := fun h ↦ hne (by rw [← map_pow]; exact (P.mkF_eq_zero_iff _).mpr h)
              regular := fun c hc ↦ ?_ }, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, he k]
      ring
    · refine ⟨τ • d₀, aeval (g c) F, ⟨τ • e, SmallSections.isWeightedHomogeneous_aeval hF (hge c), fun k ↦ ?_⟩, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, he k]
        ring
      · rw [chartMonomial_nsmul, ← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, map_pow, map_pow,
          SmallSections.mkF_aeval_forms hg hc₀' hF, SmallSections.mkF_aeval_forms hg hc hF]
        ring
    · change P.mkF (aeval (g c₀) F) / P.mkF (chartMonomial c₀ d₀ ^ τ) = _
      rw [SmallSections.mkF_aeval_forms hg hc₀' hF, map_pow, mul_div_cancel_left₀ _ hne]
  · have hfirst : ∀ c : (k : ι) → Fin (n k + 1), P.IsLive c →
        chartMonomial c d ^ τ * p - aeval (g c) F * q ∈ P.ideal := by
      intro c hc
      rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, map_pow, SmallSections.mkF_aeval_forms hg hc hF, hpq]
      ring
    refine ⟨hfirst, fun hsmall z hz ↦ ?_⟩
    obtain ⟨c, hzc⟩ : ∃ c : (k : ι) → Fin (n k + 1), ∀ k, z k (c k) ≠ 0 := by
      have h : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ by
        by_contra h'
        exact hz.1 k (funext fun i ↦ by by_contra hi; exact h' ⟨i, hi⟩)
      choose c hc using h
      exact ⟨c, hc⟩
    have hc : P.IsLive c := SmallSections.isLive_of_mem_points hz hzc
    have hm : evalCone z (chartMonomial c d) ≠ 0 := by
      rw [evalCone_chartMonomial]
      exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hzc k)
    have hs := hsmall _ (SmallSections.joinPt_mem_extPoints hg hz hzc)
    rw [SmallSections.plusMetric_joinPt hg N hG hz hzc] at hs
    have heq : evalCone z (chartMonomial c d) ^ τ * evalCone z p =
        eval₂ (Int.castRingHom ℂ) (fun j ↦ evalCone z (g c j)) F * evalCone z q := by
      have h0 := hz.2 _ (hfirst c hc)
      rw [← SmallSections.evalCone_aeval]
      simp only [evalCone, eval₂_sub, eval₂_mul, eval₂_pow, sub_eq_zero] at h0 ⊢
      exact h0
    have hA : ‖evalCone z (chartMonomial c d)‖ ^ τ * ‖evalCone z p‖ =
        ‖eval₂ (Int.castRingHom ℂ) (fun j ↦ evalCone z (g c j)) F‖ * ‖evalCone z q‖ := by
      rw [← norm_pow, ← norm_mul, heq, norm_mul]
    have hle := mul_le_mul_of_nonneg_right hs (norm_nonneg (evalCone z q))
    refine le_of_mul_le_mul_left ?_ (pow_pos (norm_pos_iff.mpr hm) τ)
    calc ‖evalCone z (chartMonomial c d)‖ ^ τ * ‖evalCone z p‖
        = ‖eval₂ (Int.castRingHom ℂ) (D.newPart (D.joinPt z fun j ↦ evalCone z (g c j))) F‖ *
            ‖evalCone z q‖ := hA
      _ ≤ (‖evalCone z (chartMonomial c d)‖ * N.metric z) ^ τ * ‖evalCone z q‖ := hle
      _ = ‖evalCone z (chartMonomial c d)‖ ^ τ * (‖evalCone z q‖ * N.metric z ^ τ) := by ring

end

end GroundTheory.Heights₂.Heights
