import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqSumMultihomogeneousComponents
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.FibreDimB

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

def graphForm (g : (Σ k, ι₂ k) → MRing ι) : (Σ k, Sum.elim ι ι₂ k) → MRing ι
  | ⟨.inl k, i⟩ => X ⟨k, i⟩
  | ⟨.inr k, j⟩ => g ⟨k, j⟩

def graphExp : (Σ k, Sum.elim ι ι₂ k) → (K₂ →₀ ℕ)
  | ⟨.inl _, _⟩ => 0
  | ⟨.inr k, _⟩ => Finsupp.single k 1

def graphLift (g : (Σ k, ι₂ k) → MRing ι) :
    MRing (Sum.elim ι ι₂) →+* MvPolynomial K₂ (MRing ι) :=
  eval₂Hom (Int.castRingHom _) fun p => monomial (graphExp p) (graphForm g p)

theorem graphMap_eq (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (F : MRing (Sum.elim ι ι₂)) :
    graphMap P g F = map (Ideal.Quotient.mk P) (graphLift g F) := by
  have : graphMap P g = (map (Ideal.Quotient.mk P)).comp (graphLift g) := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp [graphMap, graphLift]
    · rintro ⟨k | k, i⟩
      · simp [graphMap, graphLift, graphExp, graphForm]
      · simp [graphMap, graphLift, graphExp, graphForm, C_mul_X_eq_monomial]
  exact congrArg (fun f => f F) this

theorem mem_graphIdeal_iff (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (F : MRing (Sum.elim ι ι₂)) :
    F ∈ graphIdeal P g ↔ ∀ b, coeff b (graphLift g F) ∈ P := by
  rw [graphIdeal, RingHom.mem_ker, graphMap_eq]
  constructor
  · intro h b
    have := congrArg (coeff b) h
    rwa [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem] at this
  · intro h
    ext b
    rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact h b

def baseDeg (δ : K₂ → K → ℕ) (c : K ⊕ K₂ → ℕ) : K → ℕ :=
  fun k => c (.inl k) + ∑ k₂, c (.inr k₂) * δ k₂ k

def expDeg (c : K ⊕ K₂ → ℕ) : K₂ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun k₂ => c (.inr k₂)

theorem baseDeg_add (δ : K₂ → K → ℕ) (c c' : K ⊕ K₂ → ℕ) :
    baseDeg δ (c + c') = baseDeg δ c + baseDeg δ c' := by
  funext k
  simp only [baseDeg, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem expDeg_add (c c' : K ⊕ K₂ → ℕ) : expDeg (c + c') = expDeg c + expDeg c' := by
  ext k
  simp [expDeg]

theorem deg_injective {δ : K₂ → K → ℕ} {c c' : K ⊕ K₂ → ℕ} (h₁ : expDeg c = expDeg c')
    (h₂ : baseDeg δ c = baseDeg δ c') : c = c' := by
  have hr : ∀ k₂, c (.inr k₂) = c' (.inr k₂) := fun k₂ => by
    simpa [expDeg] using DFunLike.congr_fun h₁ k₂
  funext x
  rcases x with k | k₂
  · have := congrFun h₂ k
    simp only [baseDeg, hr] at this
    omega
  · exact hr k₂

theorem i2bdeg_single {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] [DecidableEq K]
    (p : Σ k, ι k) (k : K) : i2bdeg (Finsupp.single p 1) k = if p.1 = k then 1 else 0 := by
  classical
  obtain ⟨k₀, i₀⟩ := p
  by_cases h : k₀ = k
  · subst h
    simp only [i2bdeg, if_true]
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg]
      intro e
      exact hb (by simpa using e.symm)
    · simp
  · simp only [i2bdeg, if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro e
    exact h (congrArg Sigma.fst e)

theorem isMultiHomog_X_single {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (i2bdeg (Finsupp.single p 1)) := by
  classical
  rw [isMultiHomog_iff_coeff]
  intro m hm
  rw [X, coeff_monomial] at hm
  by_cases e : Finsupp.single p 1 = m
  · rw [e]
  · simp [e] at hm

theorem isMultiHomog_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsMultiHomog (1 : MRing ι) 0 := by
  classical
  rw [isMultiHomog_iff_coeff]
  intro m hm
  rw [coeff_one] at hm
  by_cases e : 0 = m
  · subst e
    funext k
    simp [i2bdeg]
  · simp [e] at hm

theorem exists_graphLift_monomial {g : (Σ k, ι₂ k) → MRing ι} {δ : K₂ → K → ℕ}
    (hg : ∀ q, IsMultiHomog (g q) (δ q.1)) (m : (Σ k, Sum.elim ι ι₂ k) →₀ ℕ) :
    ∃ h : MRing ι, IsMultiHomog h (baseDeg δ (i2bdeg m)) ∧
      graphLift g (monomial m 1) = monomial (expDeg (i2bdeg m)) h := by
  classical
  have h0 : ∃ h : MRing ι, IsMultiHomog h (baseDeg δ (i2bdeg (0 : (Σ k, Sum.elim ι ι₂ k) →₀ ℕ))) ∧
      graphLift g (monomial 0 1) = monomial (expDeg (i2bdeg (0 : (Σ k, Sum.elim ι ι₂ k) →₀ ℕ))) h := by
    have e : i2bdeg (0 : (Σ k, Sum.elim ι ι₂ k) →₀ ℕ) = 0 := by
      funext k
      simp [i2bdeg]
    refine ⟨1, ?_, ?_⟩
    · rw [e]
      have : baseDeg δ (0 : K ⊕ K₂ → ℕ) = 0 := by
        funext k
        simp [baseDeg]
      rw [this]
      exact isMultiHomog_one
    · rw [e]
      have : expDeg (0 : K ⊕ K₂ → ℕ) = 0 := by
        ext k
        simp [expDeg]
      rw [this]
      have e1 : (monomial 0 1 : MRing (Sum.elim ι ι₂)) = 1 := rfl
      rw [e1, map_one]
      rfl
  have hadd : ∀ m₁ m₂ : (Σ k, Sum.elim ι ι₂ k) →₀ ℕ,
      (∃ h : MRing ι, IsMultiHomog h (baseDeg δ (i2bdeg m₁)) ∧
        graphLift g (monomial m₁ 1) = monomial (expDeg (i2bdeg m₁)) h) →
      (∃ h : MRing ι, IsMultiHomog h (baseDeg δ (i2bdeg m₂)) ∧
        graphLift g (monomial m₂ 1) = monomial (expDeg (i2bdeg m₂)) h) →
      ∃ h : MRing ι, IsMultiHomog h (baseDeg δ (i2bdeg (m₁ + m₂))) ∧
        graphLift g (monomial (m₁ + m₂) 1) = monomial (expDeg (i2bdeg (m₁ + m₂))) h := by
    rintro m₁ m₂ ⟨h₁, hh₁, e₁⟩ ⟨h₂, hh₂, e₂⟩
    refine ⟨h₁ * h₂, ?_, ?_⟩
    · rw [i2bdeg_add, baseDeg_add]
      exact isMultiHomog_mul' hh₁ hh₂
    · have : (monomial (m₁ + m₂) 1 : MRing (Sum.elim ι ι₂)) = monomial m₁ 1 * monomial m₂ 1 := by
        rw [monomial_mul, one_mul]
      rw [this, map_mul, e₁, e₂, monomial_mul, i2bdeg_add, expDeg_add]
  have hone : ∀ p : Σ k, Sum.elim ι ι₂ k,
      ∃ h : MRing ι, IsMultiHomog h (baseDeg δ (i2bdeg (Finsupp.single p 1))) ∧
        graphLift g (monomial (Finsupp.single p 1) 1) =
          monomial (expDeg (i2bdeg (Finsupp.single p 1))) h := by
    intro p
    refine ⟨graphForm g p, ?_, ?_⟩
    · rcases p with ⟨k₀ | k₀, i⟩
      · have : baseDeg δ (i2bdeg (Finsupp.single (⟨.inl k₀, i⟩ : Σ k, Sum.elim ι ι₂ k) 1)) =
            i2bdeg (Finsupp.single (⟨k₀, i⟩ : Σ k, ι k) 1) := by
          funext k
          simp [baseDeg, i2bdeg_single]
        rw [this]
        exact isMultiHomog_X_single _
      · have : baseDeg δ (i2bdeg (Finsupp.single (⟨.inr k₀, i⟩ : Σ k, Sum.elim ι ι₂ k) 1)) = δ k₀ := by
          funext k
          simp [baseDeg, i2bdeg_single]
        rw [this]
        exact hg ⟨k₀, i⟩
    · have e : expDeg (i2bdeg (Finsupp.single p 1)) = graphExp p := by
        ext k
        rcases p with ⟨k₀ | k₀, i⟩
        · simp [expDeg, i2bdeg_single, graphExp]
        · simp [expDeg, i2bdeg_single, graphExp, Finsupp.single_apply]
      rw [e]
      have e1 : (monomial (Finsupp.single p 1) 1 : MRing (Sum.elim ι ι₂)) = X p := rfl
      rw [e1]
      simp [graphLift]
  induction m using Finsupp.induction_linear with
  | zero => exact h0
  | add m₁ m₂ i₁ i₂ => exact hadd _ _ i₁ i₂
  | single p e =>
    induction e with
    | zero => simpa using h0
    | succ e ih =>
      rw [Finsupp.single_add]
      exact hadd _ _ ih (hone p)

theorem coeff_graphLift_i2comp {g : (Σ k, ι₂ k) → MRing ι} {δ : K₂ → K → ℕ}
    (hg : ∀ q, IsMultiHomog (g q) (δ q.1)) (c : K ⊕ K₂ → ℕ) (F : MRing (Sum.elim ι ι₂))
    (b : K₂ →₀ ℕ) :
    coeff b (graphLift g (i2comp c F)) =
      if b = expDeg c then i2comp (baseDeg δ c) (coeff b (graphLift g F)) else 0 := by
  classical
  induction F using MvPolynomial.induction_on' with
  | add F F' hF hF' =>
    rw [i2comp_add, map_add, coeff_add, hF, hF', map_add, coeff_add]
    split_ifs
    · rw [i2comp_add]
    · simp
  | monomial m n =>
    obtain ⟨h, hh, e⟩ := exists_graphLift_monomial hg m
    have hm : IsMultiHomog (monomial m n : MRing (Sum.elim ι ι₂)) (i2bdeg m) := by
      rw [isMultiHomog_iff_coeff]
      intro m' hm'
      rw [coeff_monomial] at hm'
      by_cases e' : m = m'
      · rw [e']
      · simp [e'] at hm'
    have em : graphLift g (monomial m n) = monomial (expDeg (i2bdeg m)) (n • h) := by
      have : (monomial m n : MRing (Sum.elim ι ι₂)) = n • monomial m 1 := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this, map_zsmul, e, smul_monomial]
    have hnh : IsMultiHomog (n • h) (baseDeg δ (i2bdeg m)) := by
      rw [isMultiHomog_iff_coeff] at hh ⊢
      intro m' hm'
      rw [coeff_smul] at hm'
      exact hh m' fun h0 => hm' (by rw [h0, smul_zero])
    rw [i2comp_of_homog hm, em, coeff_monomial]
    by_cases hd : i2bdeg m = c
    · subst hd
      rw [if_pos rfl, em, coeff_monomial]
      by_cases hb : b = expDeg (i2bdeg m)
      · subst hb
        simp only [↓reduceIte, i2comp_self hnh]
      · simp [hb, Ne.symm hb]
    · rw [if_neg hd, map_zero, coeff_zero]
      by_cases hb : b = expDeg c
      · subst hb
        rw [if_pos rfl]
        by_cases he : expDeg (i2bdeg m) = expDeg c
        · rw [if_pos he, i2comp_of_homog hnh, if_neg]
          exact fun h' => hd (deg_injective he h')
        · rw [if_neg he, i2comp_zero]
      · rw [if_neg hb]

theorem i2comp_mem_graphIdeal {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P)
    {g : (Σ k, ι₂ k) → MRing ι} {δ : K₂ → K → ℕ} (hg : ∀ q, IsMultiHomog (g q) (δ q.1))
    (c : K ⊕ K₂ → ℕ) {F : MRing (Sum.elim ι ι₂)} (hF : F ∈ graphIdeal P g) :
    i2comp c F ∈ graphIdeal P g := by
  classical
  rw [mem_graphIdeal_iff] at hF ⊢
  intro b
  rw [coeff_graphLift_i2comp hg]
  split_ifs
  · exact i2comp_mem hP _ (hF b)
  · exact zero_mem _

theorem isMultiHomogIdeal_graphIdeal {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P)
    {g : (Σ k, ι₂ k) → MRing ι} {δ : K₂ → K → ℕ} (hg : ∀ q, IsMultiHomog (g q) (δ q.1)) :
    IsMultiHomogIdeal (graphIdeal P g) := by
  classical
  refine ⟨{f | f ∈ graphIdeal P g ∧ ∃ a, IsMultiHomog f a}, fun f hf => hf.2,
    le_antisymm (fun F hF => ?_) (Ideal.span_le.mpr fun f hf => hf.1)⟩
  rw [eq_sum_multihomogeneous_components F]
  exact Ideal.sum_mem _ fun b _ =>
    Ideal.subset_span ⟨i2comp_mem_graphIdeal hP hg b hF, b, isMultiHomog_i2comp b F⟩

theorem graphMap_rename_inlV (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (f : MRing ι) :
    graphMap P g (rename inlV f) = C (Ideal.Quotient.mk P f) := by
  have : (graphMap P g).comp (rename inlV : MRing ι →ₐ[ℤ] MRing (Sum.elim ι ι₂)).toRingHom =
      C.comp (Ideal.Quotient.mk P) := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp [graphMap]
    · rintro ⟨k, i⟩
      simp [graphMap, inlV]
  exact congrArg (fun φ => φ f) this

theorem imageZ_graphIdeal (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) :
    imageZ inlV (graphIdeal P g) = P := by
  ext f
  rw [imageZ, Ideal.mem_comap, graphIdeal, RingHom.mem_ker]
  change graphMap P g (rename inlV f) = 0 ↔ _
  rw [graphMap_rename_inlV, map_eq_zero_iff C (C_injective _ _), Ideal.Quotient.eq_zero_iff_mem]

theorem graphMap_X_inr (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (k : K₂) (j : ι₂ k) :
    graphMap P g (X ⟨.inr k, j⟩) = C (Ideal.Quotient.mk P (g ⟨k, j⟩)) * X k := by
  simp [graphMap]

theorem graphMap_intCast (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (n : ℤ) :
    graphMap P g (C n) = C (Ideal.Quotient.mk P (C n)) := by
  have := graphMap_rename_inlV P g (C n)
  rwa [rename_C] at this

theorem isRelevant_graphIdeal {P : Ideal (MRing ι)} (hP : IsRelevant P) [P.IsPrime]
    {g : (Σ k, ι₂ k) → MRing ι} (hne : ∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P) :
    IsRelevant (graphIdeal P g) := by
  rintro (k | k)
  · obtain ⟨i, hi⟩ := hP k
    refine ⟨i, fun h => hi ?_⟩
    have h' : (X ⟨k, i⟩ : MRing ι) ∈ imageZ inlV (graphIdeal P g) := by
      rw [imageZ, Ideal.mem_comap]
      change rename inlV (X ⟨k, i⟩) ∈ graphIdeal P g
      rw [rename_X]
      exact h
    rwa [imageZ_graphIdeal] at h'
  · obtain ⟨j, hj⟩ := hne k
    refine ⟨j, fun h => hj ?_⟩
    rw [graphIdeal, RingHom.mem_ker, graphMap_X_inr, mul_eq_zero, map_eq_zero_iff C (C_injective _ _),
      Ideal.Quotient.eq_zero_iff_mem] at h
    exact h.resolve_right (X_ne_zero k)

theorem isHorizontal_graphIdeal {P : Ideal (MRing ι)} (hP : IsHorizontal P)
    (g : (Σ k, ι₂ k) → MRing ι) : IsHorizontal (graphIdeal P g) := by
  rw [IsHorizontal, eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, graphIdeal, RingHom.mem_ker, graphMap_intCast, map_eq_zero_iff C (C_injective _ _),
    Ideal.Quotient.eq_zero_iff_mem] at hn
  have : n ∈ P.comap (C : ℤ →+* MRing ι) := hn
  rwa [show P.comap (C : ℤ →+* MRing ι) = ⊥ from hP] at this

section Dim

variable (P : Ideal (MRing ι)) [P.IsPrime] (g : (Σ k, ι₂ k) → MRing ι)
  (L : Type) [Field L] [Algebra (MvPolynomial K₂ (MRing ι ⧸ P)) L]
  [IsFractionRing (MvPolynomial K₂ (MRing ι ⧸ P)) L]

def graphPt : (Σ k, Sum.elim ι ι₂ k) → L :=
  fun p => algebraMap (MvPolynomial K₂ (MRing ι ⧸ P)) L (graphMap P g (X p))

theorem aeval_graphPt (F : MRing (Sum.elim ι ι₂)) :
    aeval (graphPt P g L) F = algebraMap (MvPolynomial K₂ (MRing ι ⧸ P)) L (graphMap P g F) := by
  have : (aeval (graphPt P g L) : MRing (Sum.elim ι ι₂) →ₐ[ℤ] L).toRingHom =
      (algebraMap (MvPolynomial K₂ (MRing ι ⧸ P)) L).comp (graphMap P g) := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp
    · intro p
      simp [graphPt]
  exact congrArg (fun φ => φ F) this

theorem ker_aeval_graphPt :
    RingHom.ker (aeval (graphPt P g L) : MRing (Sum.elim ι ι₂) →ₐ[ℤ] L) = graphIdeal P g := by
  ext F
  rw [RingHom.mem_ker, aeval_graphPt, graphIdeal, RingHom.mem_ker,
    map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial K₂ (MRing ι ⧸ P)) L)]

theorem graphPt_closure (hne : ∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P) (z : L) :
    z ∈ Subfield.closure (Set.range (graphPt P g L)) := by
  have hval : ∀ F : MRing (Sum.elim ι ι₂),
      algebraMap (MvPolynomial K₂ (MRing ι ⧸ P)) L (graphMap P g F) ∈
        Subfield.closure (Set.range (graphPt P g L)) := fun F => by
    rw [← aeval_graphPt]
    exact GroundTheory.Heights₂.Heights.ForSecondHalf.FibreDimB.aeval_mem_closure _ F
  have hC : ∀ a : MRing ι ⧸ P, algebraMap (MvPolynomial K₂ (MRing ι ⧸ P)) L (C a) ∈
      Subfield.closure (Set.range (graphPt P g L)) := fun a => by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← graphMap_rename_inlV P g f]
    exact hval _
  have hT : ∀ k, algebraMap (MvPolynomial K₂ (MRing ι ⧸ P)) L (X k) ∈
      Subfield.closure (Set.range (graphPt P g L)) := fun k => by
    obtain ⟨j, hj⟩ := hne k
    have h0 : algebraMap (MvPolynomial K₂ (MRing ι ⧸ P)) L
        (C (Ideal.Quotient.mk P (g ⟨k, j⟩))) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial K₂ (MRing ι ⧸ P)) L),
        map_eq_zero_iff C (C_injective _ _), Ideal.Quotient.eq_zero_iff_mem]
      exact hj
    have e : algebraMap (MvPolynomial K₂ (MRing ι ⧸ P)) L (X k) =
        algebraMap (MvPolynomial K₂ (MRing ι ⧸ P)) L (graphMap P g (X ⟨.inr k, j⟩)) /
          algebraMap (MvPolynomial K₂ (MRing ι ⧸ P)) L (C (Ideal.Quotient.mk P (g ⟨k, j⟩))) := by
      rw [graphMap_X_inr, map_mul, mul_div_cancel_left₀ _ h0]
    rw [e]
    exact div_mem (hval _) (hC _)
  have hB : ∀ b : MvPolynomial K₂ (MRing ι ⧸ P),
      algebraMap (MvPolynomial K₂ (MRing ι ⧸ P)) L b ∈
        Subfield.closure (Set.range (graphPt P g L)) := fun b => by
    induction b using MvPolynomial.induction_on with
    | C a => exact hC a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p k hp => rw [map_mul]; exact mul_mem hp (hT k)
  obtain ⟨x, y, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial K₂ (MRing ι ⧸ P)) z
  exact div_mem (hB x) (hB y)

theorem graphPt_gen (hne : ∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P) (z : L) :
    ∃ f f' : MRing (Sum.elim ι ι₂), z = aeval (graphPt P g L) f / aeval (graphPt P g L) f' := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Subfield.mem_closure_iff.1 (graphPt_closure P g L hne z)
  have hle : Subring.closure (Set.range (graphPt P g L)) ≤
      (aeval (graphPt P g L) : MRing (Sum.elim ι ι₂) →ₐ[ℤ] L).toRingHom.range :=
    Subring.closure_le.2 (by
      rintro _ ⟨p, rfl⟩
      exact ⟨X p, by simp⟩)
  obtain ⟨f, rfl⟩ := hle hu
  obtain ⟨f', rfl⟩ := hle hv
  exact ⟨f, f', rfl⟩

end Dim

theorem trdeg_graph_eq (P : Ideal (MRing ι)) [P.IsPrime] (g : (Σ k, ι₂ k) → MRing ι)
    (L : Type) [Field L] [Algebra (MvPolynomial K₂ (MRing ι ⧸ P)) L]
    [IsFractionRing (MvPolynomial K₂ (MRing ι ⧸ P)) L] (hne : ∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P)
    (hB : Function.Injective (algebraMap ℤ (MvPolynomial K₂ (MRing ι ⧸ P)))) :
    Algebra.trdeg ℤ (MRing (Sum.elim ι ι₂) ⧸ graphIdeal P g) =
      @Algebra.trdeg ℤ (MvPolynomial K₂ (MRing ι ⧸ P)) _ _ (Ring.toIntAlgebra _) := by
  have hZ : Function.Injective (algebraMap ℤ L) := fun a b h =>
    hB (IsFractionRing.injective (MvPolynomial K₂ (MRing ι ⧸ P)) L
      (by simpa only [eq_intCast, map_intCast] using h))
  rw [← GroundTheory.Heights₂.Heights.ForSecondHalf.FibreDimB.trdeg_eq_of_gen (graphPt P g L) (graphIdeal P g)
    (ker_aeval_graphPt P g L) hZ (graphPt_gen P g L hne)]
  exact GroundTheory.Heights₂.Heights.ForSecondHalf.FibreDimB.trdeg_eq_of_isFractionRing _ L hB

theorem trdeg_mvPolynomial_int (A : Type) [CommRing A] [IsDomain A] (σ : Type) [Finite σ]
    (hA : Function.Injective (algebraMap ℤ A)) :
    Algebra.trdeg ℤ (MvPolynomial σ A) = Algebra.trdeg ℤ A + Nat.card σ := by
  have : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).2 hA
  have : FaithfulSMul A (MvPolynomial σ A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (C_injective _ _)
  rw [← trdeg_add_eq ℤ A (A := MvPolynomial σ A), MvPolynomial.trdeg_of_isDomain, Nat.cast_card]
  simp

theorem ringKrullDim_graphIdeal {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d)
    {g : (Σ k, ι₂ k) → MRing ι} (hne : ∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P) :
    ringKrullDim (MRing (Sum.elim ι ι₂) ⧸ graphIdeal P g) =
      ((d + Fintype.card (K ⊕ K₂) : ℕ) : WithBot ℕ∞) := by
  obtain ⟨t, ht, htd⟩ := GroundTheory.Heights₂.Heights.ForSecondHalf.FibreDimB.trdeg_of_isArithVar hP
  obtain ⟨-, ⟨hprime, -, -⟩, hhor, -⟩ := hP
  have := hprime
  have hA := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.algebraMap_injective P hhor
  have hBinj : Function.Injective (algebraMap ℤ (MvPolynomial K₂ (MRing ι ⧸ P))) := fun a b h =>
    hA (C_injective K₂ _ (by simpa only [eq_intCast, map_intCast] using h))
  have h1 := trdeg_graph_eq P g (FractionRing (MvPolynomial K₂ (MRing ι ⧸ P))) hne hBinj
  have h3 := trdeg_mvPolynomial_int (MRing ι ⧸ P) K₂ hA
  have hhor' := isHorizontal_graphIdeal hhor g
  haveI : (graphIdeal P g).IsPrime := RingHom.ker_isPrime _
  have hdim := GroundTheory.Heights₂.Heights.IntDomainDim.proof (MRing (Sum.elim ι ι₂) ⧸ graphIdeal P g)
    (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.algebraMap_injective _ hhor')
  have h4 : Algebra.trdeg ℤ (MRing (Sum.elim ι ι₂) ⧸ graphIdeal P g) =
      ((t + Fintype.card K₂ : ℕ) : Cardinal) := by
    rw [h1]
    refine (congrArg (fun a : Algebra ℤ (MvPolynomial K₂ (MRing ι ⧸ P)) =>
      @Algebra.trdeg ℤ (MvPolynomial K₂ (MRing ι ⧸ P)) _ _ a) (Subsingleton.elim _ _)).trans
      (h3.trans ?_)
    have ht' : @Algebra.trdeg ℤ (MRing ι ⧸ P) _ _ (Ring.toIntAlgebra _) = t :=
      (congrArg (fun a : Algebra ℤ (MRing ι ⧸ P) => @Algebra.trdeg ℤ (MRing ι ⧸ P) _ _ a)
        (Subsingleton.elim _ _)).trans ht
    rw [ht', Nat.card_eq_fintype_card]
    push_cast
    rfl
  rw [hdim, h4, Cardinal.toENat_nat, Fintype.card_sum]
  have : t + Fintype.card K₂ + 1 = d + (Fintype.card K + Fintype.card K₂) := by omega
  exact_mod_cast this

theorem graphIdeal_isArithVar : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₂ : Type) [Fintype K₂]
    (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (P : Ideal (MRing ι)) (d : ℕ) (g : (Σ k, ι₂ k) → MRing ι)
    (δ : K₂ → K → ℕ), IsArithVar P d → (∀ q, IsMultiHomog (g q) (δ q.1)) → (∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P) →
    IsArithVar (graphIdeal P g) d ∧ imageZ inlV (graphIdeal P g) = P := by
  intro K _ ι _ K₂ _ ι₂ _ P d g δ hP hg hne
  obtain ⟨hK, ⟨hprime, hmh, hrel⟩, hhor, -⟩ := id hP
  have := hprime
  refine ⟨⟨?_, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal_graphIdeal hmh hg, isRelevant_graphIdeal hrel hne⟩,
    isHorizontal_graphIdeal hhor g, ringKrullDim_graphIdeal hP hne⟩, imageZ_graphIdeal P g⟩
  exact hK.elim fun k => ⟨.inl k⟩

end GlobalTheory.CompanionTheory.Ar.Giv
