import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitConjSum
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace OrbitConjSum

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem map_aeval_int {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {κ : Type*}
    (w : κ → A) (f : MvPolynomial κ ℤ) : φ (aeval w f) = aeval (fun p ↦ φ (w p)) f := by
  rw [aeval_def, aeval_def, hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

theorem eval_map_int {κ : Type*} (z : κ → ℂ) (f : MvPolynomial κ ℤ) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def, algebraMap_int_eq]

omit [Fintype ι] [DecidableEq ι] in

theorem aeval_eq_zero_of_mem (x : Cone n (AlgebraicClosure ℚ)) {f : MvPolynomial (Coord n) ℤ}
    (hmem : f ∈ orbitIdeal x) : aeval (flatCone x) f = 0 := by
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker] at hmem
  have h : ∀ f : MvPolynomial (Coord n) ℤ, aeval (flatCone x) f =
      eval (fun _ : ι ↦ (1 : AlgebraicClosure ℚ))
        (Geo.mConeMap (ι := blockIdx n) (flatCone x) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [Geo.mConeMap]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f p hf => simp only [map_mul, hf, aeval_X, eval_X, Geo.mConeMap, eval_C, mul_one]
  rw [h, hmem, map_zero]

theorem mem_orbitIdeal_of_homog (x : Cone n (AlgebraicClosure ℚ)) {f : MvPolynomial (Coord n) ℤ}
    {d : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f d) (h0 : aeval (flatCone x) f = 0) :
    f ∈ orbitIdeal x := by
  have hf' := (geoMultiHomog_iff f d).mpr hf
  have key : Geo.mConeMap (ι := blockIdx n) (flatCone x) f =
      C (aeval (flatCone x) f) * ∏ k, (X k : MvPolynomial ι (AlgebraicClosure ℚ)) ^ d k := by
    conv_lhs => rw [f.as_sum]
    conv_rhs => rw [f.as_sum]
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hX : ∏ p : Coord n, (X p.1 : MvPolynomial ι (AlgebraicClosure ℚ)) ^ m p =
        ∏ k, (X k : MvPolynomial ι (AlgebraicClosure ℚ)) ^ d k := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show ∏ i, (X k : MvPolynomial ι (AlgebraicClosure ℚ)) ^ m ⟨k, i⟩ = _
      rw [Finset.prod_pow_eq_pow_sum, hf' m hm k]
    simp only [Geo.mConeMap, aeval_monomial]
    rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
    simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
      MvPolynomial.algebraMap_apply]
    ac_rfl
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, key, h0, map_zero, zero_mul]

omit [Fintype ι] [DecidableEq ι] in

theorem conj_mem (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x)
    (σ : coordField x →+* ℂ) :
    (fun p : Coord n ↦ σ (coordVec x p.1 p.2)) ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x) := by
  refine ⟨fun k ↦ ?_, fun f hf ↦ ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp (hx k)
    exact ⟨i, (map_ne_zero σ).mpr fun h ↦ hi (congrArg Subtype.val h)⟩
  · have h0 : aeval (fun p : Coord n ↦ coordVec x p.1 p.2) f = 0 := by
      apply Subtype.val_injective
      have := map_aeval_int (coordField x).val.toRingHom (fun p : Coord n ↦ coordVec x p.1 p.2) f
      exact this.trans (aeval_eq_zero_of_mem x hf)
    rw [eval_map_int, ← map_aeval_int σ]
    exact (congrArg σ h0).trans (map_zero σ)

theorem chart_ne_zero (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) {z : Coord n → ℂ}
    (hz : z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x)) (k : ι) : z ⟨k, c k⟩ ≠ 0 := by
  intro h0
  obtain ⟨i, hi⟩ := hz.1 k
  obtain ⟨g, hg0, hg⟩ := exists_int_relation (flatCone x ⟨k, i⟩ / flatCone x ⟨k, c k⟩)
  have := hz.2 _ (homogForm_mem_orbitIdeal x g ⟨k, i⟩ ⟨k, c k⟩ rfl (hc k) hg)
  rw [eval_homogForm, h0, homog_sum_zero] at this
  exact mul_ne_zero (Int.cast_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hg0))
    (pow_ne_zero _ hi) this

theorem exists_int_mul {κ : Type*} (F : MvPolynomial κ ℚ) :
    ∃ (N : ℤ) (P : MvPolynomial κ ℤ), N ≠ 0 ∧ map (Int.castRingHom ℚ) P = C (N : ℚ) * F := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a.den, C a.num, by exact_mod_cast a.den_nz, ?_⟩
    rw [map_C, ← C_mul]
    congr 1
    rw [eq_intCast, Int.cast_natCast]
    exact (Rat.den_mul_eq_num a).symm
  | add f g hf hg =>
    obtain ⟨N₁, P₁, h₁, e₁⟩ := hf
    obtain ⟨N₂, P₂, h₂, e₂⟩ := hg
    refine ⟨N₁ * N₂, C N₂ * P₁ + C N₁ * P₂, mul_ne_zero h₁ h₂, ?_⟩
    rw [map_add, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, e₁, e₂, Int.cast_mul,
      C_mul]
    simp only [eq_intCast]
    ring
  | mul_X f p hf =>
    obtain ⟨N, P, h, e⟩ := hf
    exact ⟨N, P * X p, h, by rw [map_mul, e, map_X, mul_assoc]⟩

def chartHomog (c : (k : ι) → Fin (n k + 1)) (P : MvPolynomial (Coord n) ℤ) :
    MvPolynomial (Coord n) ℤ :=
  ∑ m ∈ P.support, monomial m (P.coeff m) * chartMonomial c (fun k ↦ P.totalDegree - ∑ i, m ⟨k, i⟩)

omit [DecidableEq ι] in
theorem blockDeg_le (P : MvPolynomial (Coord n) ℤ) {m : Coord n →₀ ℕ} (hm : m ∈ P.support)
    (k : ι) : ∑ i, m ⟨k, i⟩ ≤ P.totalDegree := by
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl), Fintype.sum_sigma]
  exact Finset.single_le_sum (f := fun k ↦ ∑ i, m ⟨k, i⟩) (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ k)

theorem isWeightedHomogeneous_chartHomog (c : (k : ι) → Fin (n k + 1))
    (P : MvPolynomial (Coord n) ℤ) :
    IsWeightedHomogeneous (coordDeg n) (chartHomog c P) (fun _ ↦ P.totalDegree) := by
  apply (mem_weightedHomogeneousSubmodule _ _ _ _).mp
  refine Submodule.sum_mem _ fun m hm ↦ (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_
  have h := (isWeightedHomogeneous_monomial (coordDeg n) m (P.coeff m) rfl).mul
    (isWeightedHomogeneous_chartMonomial c (fun k ↦ P.totalDegree - ∑ i, m ⟨k, i⟩))
  convert h using 1
  funext k
  rw [Pi.add_apply, weight_coordDeg_apply, Nat.add_sub_cancel' (blockDeg_le P hm k)]

omit [DecidableEq ι] in

theorem aeval_chartHomog {F : Type*} [Field F] (c : (k : ι) → Fin (n k + 1))
    (P : MvPolynomial (Coord n) ℤ) (w : Coord n → F) (hw : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    aeval w (chartHomog c P) =
      (∏ k, w ⟨k, c k⟩ ^ P.totalDegree) * aeval (fun p ↦ w p / w ⟨p.1, c p.1⟩) P := by
  have hP : aeval (fun p ↦ w p / w ⟨p.1, c p.1⟩) P =
      ∑ m ∈ P.support, aeval (fun p ↦ w p / w ⟨p.1, c p.1⟩) (monomial m (P.coeff m)) := by
    conv_lhs => rw [P.as_sum]
    exact map_sum _ _ _
  rw [hP, chartHomog, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hden : ∏ p : Coord n, w ⟨p.1, c p.1⟩ ^ m p = ∏ k, w ⟨k, c k⟩ ^ ∑ i, m ⟨k, i⟩ := by
    rw [Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun k _ ↦ by
      show ∏ i, w ⟨k, c k⟩ ^ m ⟨k, i⟩ = _
      exact Finset.prod_pow_eq_pow_sum _ _ _
  have hE : ∏ k, w ⟨k, c k⟩ ^ P.totalDegree = (∏ k, w ⟨k, c k⟩ ^ ∑ i, m ⟨k, i⟩) *
      ∏ k, w ⟨k, c k⟩ ^ (P.totalDegree - ∑ i, m ⟨k, i⟩) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ ↦ by
      rw [← pow_add, Nat.add_sub_cancel' (blockDeg_le P hm k)]
  have h0 : ∏ k, w ⟨k, c k⟩ ^ ∑ i, m ⟨k, i⟩ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hw k)
  simp only [map_mul, aeval_monomial, chartMonomial, map_prod, map_pow, aeval_X]
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp only [div_pow, Finset.prod_div_distrib, hden]
  field_simp
  rw [hE]
  ring

def ratio (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) (p : Coord n) :
    coordField x :=
  coordVec x p.1 p.2 / coordVec x p.1 (c p.1)

def ratioField (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    IntermediateField ℚ (coordField x) :=
  IntermediateField.adjoin ℚ (Set.range (ratio x c))

instance (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    NumberField (ratioField x c) := {}

instance (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    FiniteDimensional (ratioField x c) (coordField x) :=
  FiniteDimensional.right ℚ (ratioField x c) (coordField x)

omit [Fintype ι] [DecidableEq ι] in
theorem conj_chart_ne_zero (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) (σ : coordField x →+* ℂ) (k : ι) :
    σ (coordVec x k (c k)) ≠ 0 :=
  (map_ne_zero σ).mpr fun h ↦ hc k (congrArg Subtype.val h)

omit [Fintype ι] [DecidableEq ι] in

theorem restrict_eq_iff (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (σ σ' : coordField x →+* ℂ) :
    σ.comp (algebraMap (ratioField x c) (coordField x)) =
        σ'.comp (algebraMap (ratioField x c) (coordField x)) ↔
      ∀ p, σ (ratio x c p) = σ' (ratio x c p) := by
  constructor
  · intro h p
    exact DFunLike.congr_fun h ⟨ratio x c p, IntermediateField.subset_adjoin ℚ _ ⟨p, rfl⟩⟩
  · intro h
    have e : (σ.comp (algebraMap (ratioField x c) (coordField x))).toRatAlgHom =
        (σ'.comp (algebraMap (ratioField x c) (coordField x))).toRatAlgHom :=
      IntermediateField.adjoin_algHom_ext ℚ fun y ⟨p, hp⟩ ↦ by
        subst hp
        exact h p
    ext a
    exact DFunLike.congr_fun e a

def conjPt (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x) (σ : coordField x →+* ℂ) :
    projPts (ι := blockIdx n) (orbitIdeal x) :=
  Quot.mk _ ⟨_, conj_mem x hx σ⟩

omit [DecidableEq ι] in

theorem conjPt_eq_iff (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x)
    (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, x k (c k) ≠ 0) (σ σ' : coordField x →+* ℂ) :
    conjPt x hx σ = conjPt x hx σ' ↔ ∀ p, σ (ratio x c p) = σ' (ratio x c p) := by
  have hne := conj_chart_ne_zero x c hc
  constructor
  · intro h p
    let R : projPts (ι := blockIdx n) (orbitIdeal x) → Coord n → ℂ :=
      Quot.lift (fun z ↦ fun p ↦ (z : Coord n → ℂ) p / (z : Coord n → ℂ) ⟨p.1, c p.1⟩)
        (by
          rintro z z' ⟨a, ha, e⟩
          funext p
          simp only [e]
          exact (mul_div_mul_left _ _ (ha p.1)).symm)
    have := congrFun (congrArg R h) p
    rw [ratio, map_div₀, map_div₀]
    exact this
  · intro h
    refine Quot.sound ⟨fun k ↦ σ' (coordVec x k (c k)) / σ (coordVec x k (c k)),
      fun k ↦ div_ne_zero (hne σ' k) (hne σ k), funext fun p ↦ ?_⟩
    have e := h p
    rw [ratio, map_div₀, map_div₀, div_eq_div_iff (hne σ p.1) (hne σ' p.1)] at e
    show σ' (coordVec x p.1 p.2) =
      σ' (coordVec x p.1 (c p.1)) / σ (coordVec x p.1 (c p.1)) * σ (coordVec x p.1 p.2)
    rw [div_mul_eq_mul_div, eq_div_iff (hne σ p.1)]
    linear_combination -e

theorem exists_conjPt_eq (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x)
    (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, x k (c k) ≠ 0)
    (q : projPts (ι := blockIdx n) (orbitIdeal x)) : ∃ σ, conjPt x hx σ = q := by
  classical
  induction q using Quot.ind with
  | mk z =>
  obtain ⟨z, hz⟩ := z
  have hz0 := chart_ne_zero x c hc hz
  have hne := conj_chart_ne_zero x c hc
  let L := ratioField x c
  let gen : Coord n → L := fun p ↦ ⟨ratio x c p, IntermediateField.subset_adjoin ℚ _ ⟨p, rfl⟩⟩
  let φ : MvPolynomial (Coord n) ℚ →ₐ[ℚ] L := aeval gen
  have hφ : ∀ F, ((φ F : L) : coordField x) = aeval (ratio x c) F := fun F ↦
    DFunLike.congr_fun (comp_aeval (R := ℚ) (f := gen) L.val) F
  have hsurj : Function.Surjective φ := by
    rintro ⟨a, ha⟩
    have ha' : a ∈ Algebra.adjoin ℚ (Set.range (ratio x c)) := by
      rw [← IntermediateField.adjoin_toSubalgebra]
      exact ha
    rw [← aeval_range] at ha'
    obtain ⟨F, hF⟩ := ha'
    exact ⟨F, Subtype.ext ((hφ F).trans hF)⟩
  let r : Coord n → ℂ := fun p ↦ z p / z ⟨p.1, c p.1⟩
  have hint : ∀ P : MvPolynomial (Coord n) ℤ, aeval (ratio x c) P = 0 → aeval r P = 0 := by
    intro P hP
    have hx0 : aeval (flatCone x) (chartHomog c P) = 0 := by
      rw [show aeval (flatCone x) (chartHomog c P) = _ from aeval_chartHomog c P (flatCone x) hc]
      have h1 : aeval (fun p ↦ (coordField x).val.toRingHom (ratio x c p)) P = 0 :=
        (map_aeval_int (coordField x).val.toRingHom (ratio x c) P).symm.trans
          (by exact (congrArg _ hP).trans (map_zero _))
      have h2 : (fun p : Coord n ↦ flatCone x p / flatCone x ⟨p.1, c p.1⟩) =
          fun p ↦ (coordField x).val.toRingHom (ratio x c p) := by
        funext p
        simp [ratio, flatCone, coordVec]
      have h5 : aeval (fun p : Coord n ↦ flatCone x p / flatCone x ⟨p.1, c p.1⟩) P = 0 := by
        rw [h2]
        exact h1
      exact mul_eq_zero_of_right _ h5
    have h3 := hz.2 _ (mem_orbitIdeal_of_homog x (isWeightedHomogeneous_chartHomog c P) hx0)
    rw [eval_map_int, aeval_chartHomog c P z hz0] at h3
    exact (mul_eq_zero.mp h3).resolve_left
      (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hz0 k))
  let ψ : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ℂ := aeval r
  let φR : MvPolynomial (Coord n) ℚ →+* L := φ.toRingHom
  have hsurjR : Function.Surjective φR := hsurj
  have hker : RingHom.ker φR ≤ RingHom.ker ψ.toRingHom := by
    intro F hF
    rw [RingHom.mem_ker] at hF ⊢
    obtain ⟨N, P, hN, hP⟩ := exists_int_mul F
    have hF' : aeval (ratio x c) F = 0 := by
      rw [← hφ]
      exact congrArg Subtype.val hF
    have hyP : aeval (ratio x c) P = 0 := by
      have := congrArg (aeval (ratio x c)) hP
      rw [← algebraMap_int_eq, aeval_map_algebraMap, map_mul, aeval_C, hF', mul_zero] at this
      exact this
    have := congrArg (aeval r) hP
    rw [← algebraMap_int_eq, aeval_map_algebraMap, map_mul, aeval_C, hint P hyP] at this
    have hN' : algebraMap ℚ ℂ (N : ℚ) ≠ 0 := by simpa using hN
    exact (mul_eq_zero.mp this.symm).resolve_left hN'
  let τ : L →+* ℂ := φR.liftOfSurjective hsurjR ⟨ψ.toRingHom, hker⟩
  have hτ : ∀ p, τ (gen p) = r p := fun p ↦ by
    have := φR.liftOfSurjective_comp_apply hsurjR ⟨ψ.toRingHom, hker⟩ (X p)
    have e1 : φR (X p) = gen p := aeval_X gen p
    have e2 : ψ.toRingHom (X p) = r p := aeval_X r p
    rw [e1, e2] at this
    exact this
  obtain ⟨σ, hσ⟩ : ∃ σ : coordField x →+* ℂ, σ.comp (algebraMap L (coordField x)) = τ := by
    have h := card_embeddings_restrict (K := L) (L := coordField x) τ
    have hpos : 0 < (Finset.univ.filter fun σ : coordField x →+* ℂ ↦
        σ.comp (algebraMap L (coordField x)) = τ).card := by
      rw [h]
      exact Module.finrank_pos
    obtain ⟨σ, hσ⟩ := Finset.card_pos.mp hpos
    exact ⟨σ, (Finset.mem_filter.mp hσ).2⟩
  have hσr : ∀ p, σ (ratio x c p) = r p := fun p ↦ by
    rw [← hτ p, ← hσ]
    rfl
  refine ⟨σ, (Quot.sound ⟨fun k ↦ σ (coordVec x k (c k)) / z ⟨k, c k⟩,
    fun k ↦ div_ne_zero (hne σ k) (hz0 k), funext fun p ↦ ?_⟩).symm⟩
  have e := hσr p
  rw [ratio, map_div₀, div_eq_div_iff (hne σ p.1) (hz0 p.1)] at e
  show σ (coordVec x p.1 p.2) = σ (coordVec x p.1 (c p.1)) / z ⟨p.1, c p.1⟩ * z p
  rw [div_mul_eq_mul_div, eq_div_iff (hz0 p.1)]
  linear_combination e

end OrbitConjSum

end

end GroundTheory.Heights₂.Heights
