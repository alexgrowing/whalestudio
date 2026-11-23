import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfA
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMahlerCompactness

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace ComplexOrder

theorem isOpen_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    IsOpen (ballDom q) := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  refine Filter.eventually_all.2 fun τ => ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.posDef_eventually
    (fun t : Fin n → ℂ => 1 - (ballMat q t τ)ᴴ * ballMat q t τ) (fun a b => ?_) (fun t => ?_) x0 (hx0 τ)
  · simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, ballMat, Matrix.of_apply]
    exact continuous_const.sub (continuous_finsetSum _ fun c _ =>
      (continuous_star.comp (continuous_apply _)).mul (continuous_apply _))
  · have : (1 - (ballMat q t τ)ᴴ * ballMat q t τ)ᴴ = 1 - (ballMat q t τ)ᴴ * ballMat q t τ := by
      simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
    exact this

theorem exists_transversal {α ι : Type*} [MeasurableSpace α] [Countable ι] (X : Set α)
    (hX : MeasurableSet X) (A : ι → α → α) (hA : ∀ i, Measurable (A i)) (ψ : α → ℝ)
    (hψ : Measurable ψ) (hinj : Set.InjOn ψ X) (Rel : α → α → Prop)
    (hmaps : ∀ i, Set.MapsTo (A i) X X)
    (hrel : ∀ t ∈ X, ∀ t' ∈ X, Rel t t' ↔ ∃ i, t' = A i t)
    (hrefl : ∀ t ∈ X, Rel t t) (hsymm : ∀ t t', Rel t t' → Rel t' t)
    (htrans : ∀ t t' t'', Rel t t' → Rel t' t'' → Rel t t'')
    (hfin : ∀ t ∈ X, ∀ c : ℝ, {i | ψ (A i t) ≤ c}.Finite) :
    ∃ FF : Set α, MeasurableSet FF ∧ FF ⊆ X ∧ (∀ t ∈ X, ∃ t' ∈ FF, Rel t t') ∧
      ∀ t ∈ FF, ∀ t' ∈ FF, Rel t t' → t = t' := by
  refine ⟨X ∩ ⋂ i, {t | ψ t ≤ ψ (A i t)}, ?_, Set.inter_subset_left, ?_, ?_⟩
  · exact hX.inter (MeasurableSet.iInter fun i => measurableSet_le hψ (hψ.comp (hA i)))
  · intro t ht
    obtain ⟨i₀, hi₀⟩ := (hrel t ht t ht).1 (hrefl t ht)
    have hne : {i | ψ (A i t) ≤ ψ t}.Nonempty := ⟨i₀, by simp [← hi₀]⟩
    obtain ⟨i, hi, hmin⟩ := Set.exists_min_image _ (fun i => ψ (A i t)) (hfin t ht (ψ t)) hne
    have hmin' : ∀ k, ψ (A i t) ≤ ψ (A k t) := fun k => by
      by_cases hk : ψ (A k t) ≤ ψ t
      · exact hmin k hk
      · exact le_trans hi (le_of_not_ge hk)
    have hit : A i t ∈ X := hmaps i ht
    have hR : Rel t (A i t) := (hrel t ht _ hit).2 ⟨i, rfl⟩
    refine ⟨A i t, ⟨hit, Set.mem_iInter.2 fun k => ?_⟩, hR⟩
    have h1 : Rel (A i t) (A k (A i t)) := (hrel _ hit _ (hmaps k hit)).2 ⟨k, rfl⟩
    obtain ⟨l, hl⟩ := (hrel t ht _ (hmaps k hit)).1 (htrans _ _ _ hR h1)
    show ψ (A i t) ≤ ψ (A k (A i t))
    rw [hl]
    exact hmin' l
  · rintro t ⟨ht, htm⟩ t' ⟨ht', htm'⟩ hR
    obtain ⟨i, hi⟩ := (hrel t ht t' ht').1 hR
    obtain ⟨k, hk⟩ := (hrel t' ht' t ht).1 (hsymm _ _ hR)
    have h1 : ψ t ≤ ψ t' := by
      have : ψ t ≤ ψ (A i t) := Set.mem_iInter.1 htm i
      rwa [← hi] at this
    have h2 : ψ t' ≤ ψ t := by
      have : ψ t' ≤ ψ (A k t') := Set.mem_iInter.1 htm' k
      rwa [← hk] at this
    exact hinj ht ht' (le_antisymm h1 h2)

section Lat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem RiemLat.quad_nonneg (R : RiemLat E g Λ) (z : Fin g → ℂ) : 0 ≤ (z ⬝ᵥ R.Hm *ᵥ star z).re := by
  by_cases hz : z = 0
  · simp [hz]
  · exact (R.pos z hz).le

theorem RiemLat.normSq_nonneg (R : RiemLat E g Λ) (x : Λ) : 0 ≤ R.normSq x := R.quad_nonneg _

theorem RiemLat.form_antisymm (R : RiemLat E g Λ) (x y : Λ) : R.form y x = - R.form x y := by
  have h := R.alt (x + y)
  simp only [map_add, LinearMap.add_apply, R.alt] at h
  linarith

theorem RiemLat.form_sq_le (R : RiemLat E g Λ) (x y : Λ) :
    ((R.form x y : ℤ) : ℝ) ^ 2 ≤ R.normSq x * R.normSq y := by
  set z := R.P x
  set w := R.P y
  have key : ∀ s : ℝ, 0 ≤ R.normSq y * (s * s) + (2 * (R.form x y : ℤ) : ℝ) * s + R.normSq x := by
    intro s
    have h := R.quad_nonneg (z + ((s : ℂ) * Complex.I) • w)
    have e1 : (z ⬝ᵥ R.Hm *ᵥ star z).re = R.normSq x := rfl
    have e2 : (w ⬝ᵥ R.Hm *ᵥ star w).re = R.normSq y := rfl
    have e3 : (z ⬝ᵥ R.Hm *ᵥ star w).im = (R.form x y : ℤ) := R.im x y
    have e4 : (w ⬝ᵥ R.Hm *ᵥ star z).im = (R.form y x : ℤ) := R.im y x
    rw [R.form_antisymm x y] at e4
    have hexp : (z + ((s : ℂ) * Complex.I) • w) ⬝ᵥ R.Hm *ᵥ star (z + ((s : ℂ) * Complex.I) • w) =
        (z ⬝ᵥ R.Hm *ᵥ star z) + (-(s : ℂ) * Complex.I) * (z ⬝ᵥ R.Hm *ᵥ star w) +
          ((s : ℂ) * Complex.I) * (w ⬝ᵥ R.Hm *ᵥ star z) + (s : ℂ) ^ 2 * (w ⬝ᵥ R.Hm *ᵥ star w) := by
      simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal,
        Complex.conj_I]
      have hI := Complex.I_mul_I
      ring_nf
      simp only [Complex.I_sq]
      ring
    rw [hexp] at h
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im, e1, e2, e3, e4, sq] at h
    push_cast at h
    nlinarith [h]
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

theorem RiemLat.finite_normSq_le (R : RiemLat E g Λ) (c : ℝ) : {x | R.normSq x ≤ c}.Finite := by
  haveI := R.free
  haveI := R.fin
  let b := Module.Free.chooseBasis ℤ Λ
  let ι := Module.Free.ChooseBasisIndex ℤ Λ
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i : ι, c * R.normSq (b i) ≤ (N : ℝ) ^ 2 := by
    obtain ⟨N, hN⟩ := exists_nat_ge (∑ i : ι, |c * R.normSq (b i)| + 1)
    refine ⟨N, fun i => ?_⟩
    have h1 : |c * R.normSq (b i)| ≤ ∑ i : ι, |c * R.normSq (b i)| :=
      Finset.single_le_sum (f := fun i : ι => |c * R.normSq (b i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := le_abs_self (c * R.normSq (b i))
    have h3 : (0 : ℝ) ≤ ∑ i : ι, |c * R.normSq (b i)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    nlinarith
  have hfin : (Set.pi Set.univ fun _ : ι => Set.Icc (-(N : ℤ)) N).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine Set.Finite.of_finite_image (f := fun x (i : ι) => R.form x (b i)) (hfin.subset ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩ i -
    have h1 := R.form_sq_le x (b i)
    have h2 : R.normSq x * R.normSq (b i) ≤ c * R.normSq (b i) :=
      mul_le_mul_of_nonneg_right hx (R.normSq_nonneg _)
    have h3 : ((R.form x (b i) : ℤ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := h1.trans (h2.trans (hN i))
    have h4 := abs_le.1 (abs_le_of_sq_le_sq h3 (by positivity))
    constructor
    · have := h4.1
      exact_mod_cast this
    · have := h4.2
      exact_mod_cast this
  · intro x _ y _ hxy
    refine R.unimod.1 (b.ext fun i => ?_)
    exact congrFun hxy i

theorem RiemLat.left_inv_gram (R : RiemLat E g Λ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ Λ) :
    ∃ Y : Matrix ι ι ℂ, Y * (Matrix.of fun i j => ((R.form (b i) (b j) : ℤ) : ℂ)) = 1 := by
  choose y hy using fun i => R.unimod.2 (b.coord i)
  refine ⟨Matrix.of fun i k => ((b.repr (y i) k : ℤ) : ℂ), ?_⟩
  ext i j
  have h1 : R.form (y i) (b j) = ∑ k, b.repr (y i) k * R.form (b k) (b j) := by
    have e : R.form (∑ k, b.repr (y i) k • b k) (b j) = ∑ k, b.repr (y i) k * R.form (b k) (b j) := by
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rwa [b.sum_repr] at e
  have h2 : R.form (y i) (b j) = if i = j then 1 else 0 := by
    rw [hy i]
    simp [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]
  have h3 := congrArg (fun z : ℤ => (z : ℂ)) (h1.symm.trans h2)
  simp only [Int.cast_sum, Int.cast_mul] at h3
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [h3]
  split_ifs <;> simp

def RiemLat.perMat (R : RiemLat E g Λ) {ι : Type} (b : ι → Λ) : Matrix (Fin g) ι ℂ :=
  Matrix.of fun a i => R.P (b i) a

theorem RiemLat.riemann_rel (R : RiemLat E g Λ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : ι → Λ) (hc : Fintype.card ι = Fintype.card (Fin g ⊕ Fin g)) (Y : Matrix ι ι ℂ)
    (hY : Y * (Matrix.of fun i j => ((R.form (b i) (b j) : ℤ) : ℂ)) = 1) :
    (R.perMat b * Y * (R.perMat b)ᴴ) * R.Hmᵀ = (-2 * Complex.I) • (1 : Matrix (Fin g) (Fin g) ℂ) := by
  set Q := R.perMat b with hQ
  set Qb : Matrix (Fin g) ι ℂ := Q.map (starRingEnd ℂ) with hQb
  set S : Matrix ι ι ℂ := Qᵀ * R.Hm * Qb with hS
  have hSe : ∀ i j, S i j = R.P (b i) ⬝ᵥ R.Hm *ᵥ star (R.P (b j)) := by
    intro i j
    simp only [hS, hQb, hQ, Matrix.mul_apply, dotProduct, mulVec, RiemLat.perMat, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    simp [mul_assoc]
  have hSc : Qᴴ * R.Hmᵀ * Q = S.map (starRingEnd ℂ) := by
    have hH : R.Hm.map (starRingEnd ℂ) = R.Hmᵀ := by
      have := R.herm
      ext a c
      have h := this.apply c a
      simpa using h
    have : S.map (starRingEnd ℂ) = (Qᵀ).map (starRingEnd ℂ) * R.Hm.map (starRingEnd ℂ) * Qb.map (starRingEnd ℂ) := by
      rw [hS, Matrix.map_mul, Matrix.map_mul]
    rw [this, hH]
    congr 2
    ext a c; simp [hQb]
  have hdiff : S - S.map (starRingEnd ℂ) =
      (2 * Complex.I) • (Matrix.of fun i j => ((R.form (b i) (b j) : ℤ) : ℂ)) := by
    ext i j
    have h := R.im (b i) (b j)
    rw [← hSe] at h
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    have key : ∀ w : ℂ, w - (starRingEnd ℂ) w = 2 * Complex.I * ((w.im : ℝ) : ℂ) := by
      intro w
      apply Complex.ext <;> simp <;> ring
    have h5 := key (S i j)
    rw [h] at h5
    simpa using h5
  set c : ℂ := 2 * Complex.I with hcdef
  have hc0 : c ≠ 0 := by simp [hcdef]
  have h1 : Matrix.fromCols (c⁻¹ • (Y * Qᵀ * R.Hm)) (-(c⁻¹ • (Y * Qᴴ * R.Hmᵀ))) * Matrix.fromRows Qb Q = 1 := by
    rw [Matrix.fromCols_mul_fromRows]
    have : Y * (S - S.map (starRingEnd ℂ)) = c • 1 := by rw [hdiff, Matrix.mul_smul, hY]
    rw [← hSc, hS, Matrix.mul_sub] at this
    simp only [Matrix.smul_mul, Matrix.neg_mul]
    rw [← sub_eq_add_neg, ← smul_sub]
    have e : Y * Qᵀ * R.Hm * Qb - Y * Qᴴ * R.Hmᵀ * Q = c • 1 := by
      rw [← this]; simp only [Matrix.mul_assoc]
    rw [e, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have h2 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hc)).1 h1
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one] at h2
  have h3 := (Matrix.fromBlocks_inj.1 h2).2.2.2
  have h4 : Q * (Y * Qᴴ * R.Hmᵀ) = (-c) • 1 := by
    have := congrArg (fun M => (-c) • M) h3
    simp only [Matrix.mul_neg, Matrix.mul_smul, smul_neg, neg_smul, smul_smul] at this
    simpa [mul_inv_cancel₀ hc0] using this
  rw [show (-2 * Complex.I) = -c by simp [hcdef]]
  rw [← h4]
  simp only [Matrix.mul_assoc]

theorem continuousOn_normSq_of_holomorphic_family {n : ℕ} {U : Set (Fin n → ℂ)} {R : (Fin n → ℂ) → RiemLat E g Λ}
    (hR : IsHolFam U R) (x : Λ) {t₀ : Fin n → ℂ} (ht₀ : t₀ ∈ U) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ Λ) : ContinuousOn (fun t => (R t).normSq x) U := by
  haveI := (R t₀).fin
  obtain ⟨Y, hY⟩ := (R t₀).left_inv_gram b
  have hc : Fintype.card ι = Fintype.card (Fin g ⊕ Fin g) := by
    have := (R t₀).rank
    rw [Module.finrank_eq_card_basis b] at this
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hPc : ∀ y, Continuous fun t : U => (R t).P y := fun y =>
    continuousOn_iff_continuous_restrict.1 (hR.2 y).continuousOn
  have hrel : ∀ t : U, ((R t).perMat b * Y * ((R t).perMat b)ᴴ) * (R t).Hmᵀ =
      (-2 * Complex.I) • (1 : Matrix (Fin g) (Fin g) ℂ) := by
    intro t
    refine (R t).riemann_rel b hc Y ?_
    rw [hR.1 t t.2 t₀ ht₀]
    exact hY
  let N : U → Matrix (Fin g) (Fin g) ℂ := fun t => (R t).perMat b * Y * ((R t).perMat b)ᴴ
  have hQc : Continuous fun t : U => (R t).perMat b :=
    continuous_matrix fun a i => (continuous_apply a).comp (hPc (b i))
  have hNc : Continuous N := (hQc.matrix_mul continuous_const).matrix_mul hQc.matrix_conjTranspose
  set c : ℂ := -2 * Complex.I with hcdef
  have hc0 : c ≠ 0 := by simp [hcdef]
  have hinv : ∀ t : U, (R t).Hm = (c • (N t)⁻¹)ᵀ := by
    intro t
    have h1 : N t * (c⁻¹ • (R t).Hmᵀ) = 1 := by
      rw [Matrix.mul_smul, hrel t, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [Matrix.inv_eq_right_inv h1, smul_smul, mul_inv_cancel₀ hc0, one_smul, Matrix.transpose_transpose]
  have hdet : ∀ t : U, (N t).det ≠ 0 := by
    intro t h0
    have h1 := congrArg Matrix.det (hrel t)
    rw [Matrix.det_mul] at h1
    change (N t).det * _ = _ at h1
    rw [h0, zero_mul, Matrix.det_smul, Matrix.det_one] at h1
    exact (mul_ne_zero (pow_ne_zero _ hc0) one_ne_zero) h1.symm
  have hNi : Continuous fun t : U => (N t)⁻¹ := by
    have : (fun t : U => (N t)⁻¹) = fun t => ((N t).det)⁻¹ • (N t).adjugate := by
      funext t
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [this]
    exact (hNc.matrix_det.inv₀ hdet).smul hNc.matrix_adjugate
  have hHc : Continuous fun t : U => (R t).Hm := by
    have : (fun t : U => (R t).Hm) = fun t => (c • (N t)⁻¹)ᵀ := funext hinv
    rw [this]
    exact (hNi.const_smul c).matrix_transpose
  rw [continuousOn_iff_continuous_restrict]
  change Continuous fun t : U => ((R t).P x ⬝ᵥ (R t).Hm *ᵥ star ((R t).P x)).re
  exact Complex.continuous_re.comp ((hPc x).dotProduct (hHc.matrix_mulVec (hPc x).star))

theorem continuousOn_normSq {n : ℕ} {U : Set (Fin n → ℂ)} {R : (Fin n → ℂ) → RiemLat E g Λ}
    (hR : IsHolFam U R) (x : Λ) : ContinuousOn (fun t => (R t).normSq x) U := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · simp
  haveI := (R t₀).free
  haveI := (R t₀).fin
  classical
  exact continuousOn_normSq_of_holomorphic_family hR x ht₀ (Module.Free.chooseBasis ℤ Λ)

end Lat

section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem RiemLat.eqvBy_refl (R : RiemLat E g Λ) : R.EqvBy R 1 := ⟨LinearEquiv.refl _ _, fun _ => rfl⟩

theorem RiemLat.EqvBy.symm {R R' : RiemLat E g Λ} {γ : Λ ≃ₗ[𝓞 E] Λ} (h : R.EqvBy R' γ) : R'.EqvBy R γ⁻¹ := by
  obtain ⟨h₀, hx⟩ := h
  refine ⟨h₀.symm, fun x => ?_⟩
  have h1 := hx (γ⁻¹ x)
  have h2 : γ (γ⁻¹ x) = x := γ.apply_symm_apply x
  rw [h2] at h1
  rw [h1, LinearEquiv.symm_apply_apply]

theorem RiemLat.EqvBy.trans {R R' R'' : RiemLat E g Λ} {γ γ' : Λ ≃ₗ[𝓞 E] Λ} (h : R.EqvBy R' γ)
    (h' : R'.EqvBy R'' γ') : R.EqvBy R'' (γ' * γ) := by
  obtain ⟨h₀, hx⟩ := h
  obtain ⟨h₁, hy⟩ := h'
  exact ⟨h₀.trans h₁, fun x => (hy (γ x)).trans (congrArg h₁ (hx x))⟩

end Main

theorem exists_isFundSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (Δ : GroupDict F) (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)), F.IsArith Γ → ∃ FF, F.IsFundSet Γ FF := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F Δ Γ hΓ
  classical
  have hXo : IsOpen (ballDom F.q) := isOpen_ballDom F.q
  have hXm : MeasurableSet (ballDom F.q) := hXo.measurableSet
  haveI := (F.R (Δ.π 1)).free
  haveI := (F.R (Δ.π 1)).fin
  let b := Module.Free.chooseBasis ℤ Λ
  let u : (Fin n → ℂ) → ℝ := fun t => ∑ i, (F.R t).normSq (b i)
  have huc : ContinuousOn u (ballDom F.q) :=
    continuousOn_finset_sum _ fun i _ => continuousOn_normSq F.hol (b i)
  haveI : Countable Λ := b.repr.toEquiv.injective.countable
  have hext : ∀ γ γ' : Λ ≃ₗ[𝓞 E] Λ, (∀ i, γ (b i) = γ' (b i)) → γ = γ' := by
    intro γ γ' h
    have h1 := b.ext (f₁ := (γ : Λ →ₗ[𝓞 E] Λ).toAddMonoidHom.toIntLinearMap)
      (f₂ := (γ' : Λ →ₗ[𝓞 E] Λ).toAddMonoidHom.toIntLinearMap) h
    exact LinearEquiv.ext fun x => LinearMap.congr_fun h1 x
  haveI : Countable (Λ ≃ₗ[𝓞 E] Λ) :=
    Function.Injective.countable (f := fun (γ : Λ ≃ₗ[𝓞 E] Λ) i => γ (b i))
      fun γ γ' h => hext γ γ' fun i => congrFun h i
  let δ : Γ → latticeStab Δ.h Δ.e.range := fun γ => Δ.α.symm ⟨γ.1, hΓ.1 γ.2⟩
  have hαδ : ∀ γ : Γ, (Δ.α (δ γ)).1 = γ.1 := fun γ => by simp [δ]
  let a₀ : Γ → archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))) := fun γ =>
    archEmbed Δ.h (Pi.basisFun E (Fin (j + j'))) (δ γ)
  choose A G hAd hGd hAπ hpot using Δ.act
  let B : Γ → (Fin n → ℂ) → Fin n → ℂ := fun γ => A (a₀ γ)
  have hBπ : ∀ γ a, Δ.π (a₀ γ * a) = B γ (Δ.π a) := fun γ a => hAπ _ a
  have hmemπ : ∀ a, Δ.π a ∈ ballDom F.q := fun a => Δ.π_range ▸ Set.mem_range_self a
  have hsurj : ∀ t ∈ ballDom F.q, ∃ a, Δ.π a = t := fun t ht => by
    rw [← Δ.π_range] at ht
    exact ht
  have hBX : ∀ γ, Set.MapsTo (B γ) (ballDom F.q) (ballDom F.q) := by
    intro γ t ht
    obtain ⟨a, rfl⟩ := hsurj t ht
    rw [← hBπ]
    exact hmemπ _
  have hBc : ∀ γ, ContinuousOn (B γ) (ballDom F.q) := fun γ => (hAd _).continuousOn
  have hact : ∀ (γ : Γ) t, t ∈ ballDom F.q → (F.R t).EqvBy (F.R (B γ t)) γ.1 := by
    intro γ t ht
    obtain ⟨a, rfl⟩ := hsurj t ht
    have h := Δ.α_act (δ γ) a
    rw [hαδ] at h
    rw [← hBπ]
    exact h
  have hiso : ∀ (γ : Γ) t, t ∈ ballDom F.q → ∀ x, (F.R (B γ t)).normSq (γ.1 x) = (F.R t).normSq x := by
    intro γ t ht x
    obtain ⟨a, rfl⟩ := hsurj t ht
    rw [← hBπ, Δ.len, Δ.len]
    have h1 := Δ.α_eq (δ γ) x
    rw [hαδ] at h1
    rw [h1]
    have h2 := invApply_archEmbed_mul Δ.h (Pi.basisFun E (Fin (j + j'))) (δ γ : Δ.h.unitaryGroup) a (Δ.e x)
    exact congrArg (fun y => Δ.κ * Δ.M.len y ^ 2) h2
  have hrel : ∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, F.Eqv Γ t t' ↔ ∃ γ : Γ, t' = B γ t := by
    intro t ht t' ht'
    constructor
    · rintro ⟨γ, hγ, h⟩
      refine ⟨⟨γ, hγ⟩, ?_⟩
      have h1 := hact ⟨γ, hγ⟩ t ht
      have h2 : (F.R (B ⟨γ, hγ⟩ t)).EqvBy (F.R t') 1 := by
        have h3 := h1.symm.trans h
        simpa using h3
      exact (F.univ (F.R t') (F.form_eq t') (F.sig t' ht')).unique ⟨ht', (F.R t').eqvBy_refl⟩
        ⟨hBX _ ht, h2⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨γ.1, γ.2, hact γ t ht⟩
  have hfinu : ∀ t ∈ ballDom F.q, ∀ c : ℝ, {γ : Γ | u (B γ t) ≤ c}.Finite := by
    intro t ht c
    have hS := (F.R t).finite_normSq_le c
    have hfinp : (Set.pi Set.univ fun _ : Module.Free.ChooseBasisIndex ℤ Λ =>
        {x | (F.R t).normSq x ≤ c}).Finite := Set.Finite.pi fun _ => hS
    refine Set.Finite.of_finite_image (f := fun (γ : Γ) i => (γ⁻¹ : Γ).1 (b i)) (hfinp.subset ?_) ?_
    · rintro _ ⟨γ, hγ, rfl⟩ i -
      have h1 := hiso γ t ht ((γ⁻¹ : Γ).1 (b i))
      have h2 : γ.1 ((γ⁻¹ : Γ).1 (b i)) = b i := γ.1.apply_symm_apply _
      rw [h2] at h1
      show (F.R t).normSq ((γ⁻¹ : Γ).1 (b i)) ≤ c
      rw [← h1]
      exact (Finset.single_le_sum (f := fun i => (F.R (B γ t)).normSq (b i))
        (fun _ _ => RiemLat.normSq_nonneg _ _) (Finset.mem_univ i)).trans hγ
    · intro γ _ γ' _ h
      have h1 : (γ⁻¹ : Γ).1 = (γ'⁻¹ : Γ).1 := hext _ _ fun i => congrFun h i
      exact inv_injective (Subtype.ext h1)
  obtain ⟨φ, hφ⟩ := exists_measurableEmbedding_real (Fin n → ℂ)
  let ũ : (Fin n → ℂ) → ℝ := (ballDom F.q).piecewise u 0
  have hũ : Measurable ũ := huc.measurable_piecewise continuousOn_const hXm
  let ψ : (Fin n → ℂ) → ℝ := fun t => 4 * (⌈ũ t⌉₊ : ℝ) + Real.arctan (φ t)
  have hψ : Measurable ψ :=
    (measurable_const.mul (measurable_from_nat.comp (Nat.measurable_ceil.comp hũ))).add
      (Real.measurable_arctan.comp hφ.measurable)
  have hψinj : Function.Injective ψ := by
    intro t t' h
    have hb := Real.arctan_lt_pi_div_two (φ t)
    have hb' := Real.arctan_lt_pi_div_two (φ t')
    have hc := Real.neg_pi_div_two_lt_arctan (φ t)
    have hc' := Real.neg_pi_div_two_lt_arctan (φ t')
    have hpi := Real.pi_lt_four
    simp only [ψ] at h
    have hn : ⌈ũ t⌉₊ = ⌈ũ t'⌉₊ := by
      rcases lt_trichotomy ⌈ũ t⌉₊ ⌈ũ t'⌉₊ with h1 | h1 | h1
      · have : (⌈ũ t⌉₊ : ℝ) + 1 ≤ ⌈ũ t'⌉₊ := by exact_mod_cast h1
        linarith
      · exact h1
      · have : (⌈ũ t'⌉₊ : ℝ) + 1 ≤ ⌈ũ t⌉₊ := by exact_mod_cast h1
        linarith
    rw [hn] at h
    exact hφ.injective (Real.arctan_injective (by linarith))
  let B' : Γ → (Fin n → ℂ) → Fin n → ℂ := fun γ => (ballDom F.q).piecewise (B γ) id
  have hB' : ∀ γ t, t ∈ ballDom F.q → B' γ t = B γ t := fun γ t ht => Set.piecewise_eq_of_mem _ _ _ ht
  obtain ⟨FF, h1, h2, h3, h4⟩ := exists_transversal (ι := Γ) (ballDom F.q) hXm B'
    (fun γ => (hBc γ).measurable_piecewise continuousOn_id hXm) ψ hψ hψinj.injOn (F.Eqv Γ)
    (fun γ t ht => by rw [hB' γ t ht]; exact hBX γ ht)
    (fun t ht t' ht' => by
      rw [hrel t ht t' ht']
      exact exists_congr fun γ => by rw [hB' γ t ht])
    (fun t _ => ⟨1, Γ.one_mem, (F.R t).eqvBy_refl⟩)
    (fun t t' ⟨γ, hγ, h⟩ => ⟨γ⁻¹, Γ.inv_mem hγ, h.symm⟩)
    (fun t t' t'' ⟨γ, hγ, h⟩ ⟨γ', hγ', h'⟩ => ⟨γ' * γ, Γ.mul_mem hγ' hγ, h.trans h'⟩)
    (fun t ht c => by
      refine (hfinu t ht (c + 2)).subset fun γ hγ => ?_
      have hγ' : ψ (B' γ t) ≤ c := hγ
      rw [hB' γ t ht] at hγ'
      have hs := hBX γ ht
      have hu : ũ (B γ t) = u (B γ t) := Set.piecewise_eq_of_mem _ _ _ hs
      have hc := Real.neg_pi_div_two_lt_arctan (φ (B γ t))
      have hpi := Real.pi_lt_four
      have hle := Nat.le_ceil (ũ (B γ t))
      have hnn : (0 : ℝ) ≤ ⌈ũ (B γ t)⌉₊ := Nat.cast_nonneg _
      simp only [ψ] at hγ'
      show u (B γ t) ≤ c + 2
      rw [← hu]
      linarith)
  exact ⟨FF, h1, h2, h3, h4⟩

end GlobalTheory.CompanionTheory.Ar.Cusp
