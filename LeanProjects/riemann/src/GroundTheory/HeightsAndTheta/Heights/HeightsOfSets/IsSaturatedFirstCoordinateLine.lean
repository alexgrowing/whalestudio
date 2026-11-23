import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.ArithDegree
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section HeightObjects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def height (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (A : HermLine ι)
    (W : Ideal (MRing ι)) : ℝ :=
  I W 1 ![A] / degC W

variable {Ω : Type*} [Field Ω]

def IsSectionBounded (P : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (A : HermLine ι) (s : Ω) (c : ℝ) :
    Prop :=
  ∀ (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ),
    IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + A.a k) →
    aeval y g = s * aeval y h → z ∈ mcPts P →
    ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ c * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z

def NoCommonZero {n : ℕ} (P : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Fin n → Ω) :
    Prop :=
  ∀ z ∈ mcPts P, ∃ (j : Fin n) (dg dh : K → ℕ) (g h : MRing ι),
    IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + a k) ∧
      aeval y g = s j * aeval y h ∧
      eval z (map (Int.castRingHom ℂ) g) ≠ 0 ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0

end HeightObjects

def HeightLowerBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (A : HermLine ι) (n : ℕ) (s : Fin n → Ω) (C : ℝ),
    IsIntersectionFamily I → IsSmoothHerm A →
    (∀ j, s j ∈ chartLat y A.a 1) → (∀ j, IsSectionBounded (mCoordIdeal y) y A (s j) (Real.exp C)) →
    NoCommonZero (mCoordIdeal y) y A.a s →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal y ≤ W → -C ≤ height I A W

def HeightMetricChange.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    (A A' : HermLine ι) (c : ℝ),
    IsIntersectionFamily I → IsSmoothHerm A → IsSmoothHerm A' → A.a = A'.a →
    (∀ z ∈ mcPts P, |Real.log (A.h z / A'.h z)| ≤ c) →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → P ≤ W → |height I A W - height I A' W| ≤ c

def HeightPullback.Statement : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k', ι' k') → Ω) (A : HermLine ι) (A' : HermLine ι'),
      IsBlockMap κ v → IsArithVar (mCoordIdeal y) 1 → IsArithVar (imageZ v (mCoordIdeal y)) 1 →
      IsSmoothHerm A → IsPullHerm κ v A A' →
      IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) = 1 →
      height (II K' ι') A' (mCoordIdeal y) = height (II K ι) A (imageZ v (mCoordIdeal y))

def HeightComparison.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (A H : HermLine ι),
    IsIntersectionFamily I → IsSmoothHerm A → IsSmoothHerm H → H.a = 1 →
    ∃ (k : ℕ) (C : ℝ), ∀ W : Ideal (MRing ι), IsArithVar W 1 →
      |height I A W| ≤ (k : ℝ) * height I H W + C

def DenseBoundedHeight.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (D : ℕ)
    (H : HermLine ι),
    IsIntersectionFamily I → IsArithVar P (D + 1) → IsSmoothHerm H → H.a = 1 →
    ∃ (C : ℝ) (F : Set (Ideal (MRing ι))), IsZariskiDense P F ∧
      ∀ W ∈ F, IsArithVar W 1 ∧ P ≤ W ∧ height I H W ≤ C

section Lattices

open NumberField Matrix

variable {K : Type*} [Field K] [NumberField K] (E : HermitianBundle K)

def IsSaturated (F : Submodule (𝓞 K) E.carrier) : Prop :=
  ∀ (a : 𝓞 K) (x : E.carrier), a ≠ 0 → a • x ∈ F → x ∈ F

def subDegree (F : Submodule (𝓞 K) E.carrier) : ℝ :=
  Real.log (Nat.card (F ⧸ Submodule.span (𝓞 K)
      (Set.range (exists_linearIndependent_fin (K := K) (E := F)).choose))) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (gramDet E.metric σ
      (fun i ↦ ((exists_linearIndependent_fin (K := K) (E := F)).choose i : E.carrier)))

def subSlope (F : Submodule (𝓞 K) E.carrier) : ℝ :=
  subDegree E F / ((Module.finrank (𝓞 K) F : ℝ) * Module.finrank ℚ K)

def slopeMax : EReal :=
  ⨆ (F : Submodule (𝓞 K) E.carrier) (_ : F ≠ ⊥), ((subSlope E F : ℝ) : EReal)

def slopeMaxSub (F' : Submodule (𝓞 K) E.carrier) : EReal :=
  ⨆ (F : Submodule (𝓞 K) E.carrier) (_ : F ≠ ⊥) (_ : F ≤ F'), ((subSlope E F : ℝ) : EReal)

def quotFibreVec (F' : Submodule (𝓞 K) E.carrier) (σ : K →+* ℂ) (x : E.carrier ⧸ F') :
    FibreSpace E.metric σ :=
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i ↦ fibreVec E.metric σ
      ((exists_linearIndependent_fin (K := K) (E := F')).choose i : E.carrier))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  fibreVec E.metric σ (Submodule.mkQ_surjective F' x).choose -
    (Submodule.span ℂ (Set.range fun i ↦ fibreVec E.metric σ
      ((exists_linearIndependent_fin (K := K) (E := F')).choose i : E.carrier))).starProjection
      (fibreVec E.metric σ (Submodule.mkQ_surjective F' x).choose)

def quotGramDet (F' : Submodule (𝓞 K) E.carrier) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (t : ι → E.carrier ⧸ F') : ℝ :=
  (det (gram ℂ fun i ↦ quotFibreVec E F' σ (t i))).re

def quotDegree (F' : Submodule (𝓞 K) E.carrier) (G : Submodule (𝓞 K) (E.carrier ⧸ F')) : ℝ :=
  Real.log (Nat.card (G ⧸ Submodule.span (𝓞 K)
      (Set.range (exists_linearIndependent_fin (K := K) (E := G)).choose))) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (quotGramDet E F' σ
      (fun i ↦ ((exists_linearIndependent_fin (K := K) (E := G)).choose i : E.carrier ⧸ F')))

def slopeMaxQuot (F' : Submodule (𝓞 K) E.carrier) : EReal :=
  ⨆ (G : Submodule (𝓞 K) (E.carrier ⧸ F')) (_ : G ≠ ⊥),
    ((quotDegree E F' G / ((Module.finrank (𝓞 K) G : ℝ) * Module.finrank ℚ K) : ℝ) : EReal)

end Lattices

def SlopeMaxExtension.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    (F' : Submodule (NumberField.RingOfIntegers K) E.carrier),
    IsSaturated E F' → slopeMax E ≤ max (slopeMaxSub E F') (slopeMaxQuot E F')

def FlagDegreeBound.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (m : ℕ)
    (f : Fin (m + 1) → Submodule (NumberField.RingOfIntegers K) E.carrier),
    Monotone f → (∀ i, IsSaturated E (f i)) →
    (∀ i : Fin (m + 1), Module.finrank (NumberField.RingOfIntegers K) (f i) = (i : ℕ)) →
    ∀ i : Fin (m + 1), ((-((i : ℕ) : ℝ) : ℝ) : EReal) * slopeMax E ≤
      ((-(subDegree E (f i) / Module.finrank ℚ K) : ℝ) : EReal)

section Inhabitants

open NumberField

theorem subsingleton_pt : Subsingleton (Σ _ : Unit, PBlk 1 ()) :=
  ⟨fun ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ ↦ by rw [Subsingleton.elim a b]⟩

theorem isArithVar_pointZ : IsArithVar (⊥ : Ideal (MRing (PBlk 1))) 1 := by
  refine ⟨inferInstance, ⟨Ideal.isPrime_bot,
    ⟨∅, fun f hf ↦ absurd hf (Set.notMem_empty f), Ideal.span_empty.symm⟩,
    fun _ ↦ ⟨0, by rw [Submodule.mem_bot]; exact X_ne_zero _⟩⟩, ?_, ?_⟩
  · ext a
    simp [Ideal.mem_comap]
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    have hc : Nat.card ((_ : Unit) × PBlk 1 ()) = 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp
    rw [hc, Fintype.card_unit]
    rfl

def yPt : (Σ _ : Unit, PBlk 1 ()) → ℚ := fun _ ↦ 1

theorem mCoordIdeal_yPt : mCoordIdeal (ι := PBlk 1) yPt = ⊥ := by
  have hf : ∀ f : MRing (PBlk 1), mConeMap yPt f =
      map (Int.castRingHom ℚ) (rename (fun p : Σ _ : Unit, PBlk 1 () ↦ p.1) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => rw [map_add, hp, hq, map_add, map_add]
    | mul_X p n hp => simp [mConeMap, yPt] at hp ⊢; rw [hp]
  have hinj : Function.Injective (mConeMap (ι := PBlk 1) yPt) := by
    intro f g hfg
    rw [hf, hf] at hfg
    have := subsingleton_pt
    exact rename_injective _ (fun a b _ ↦ Subsingleton.elim a b)
      (map_injective _ Int.cast_injective hfg)
  rw [mCoordIdeal]
  exact (RingHom.injective_iff_ker_eq_bot _).mp hinj

theorem eval₂_homog_pt {R : Type*} [CommRing R] (f : ℤ →+* R) (z : (Σ _ : Unit, PBlk 1 ()) → R)
    (g : MRing (PBlk 1)) (d : Unit → ℕ) (hg : IsMultiHomog g d) :
    eval₂ f z g = f (∑ m ∈ g.support, g.coeff m) * z ⟨(), 0⟩ ^ d () := by
  have := subsingleton_pt
  rw [eval₂_eq', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [Fintype.prod_subsingleton _ ⟨(), 0⟩]
  have := hg m hm ()
  simp only [Fin.sum_univ_one] at this
  rw [this]

theorem fsLine_one_h (z : (Σ _ : Unit, PBlk 1 ()) → ℂ) : (fsLine 1).h z = ‖z ⟨(), 0⟩‖ := by
  simp only [fsLine, HermLine.ofMetrics, fsMetric, Pi.one_apply, zpow_one, EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq (norm_nonneg _)]

theorem isSectionBounded_one :
    IsSectionBounded (mCoordIdeal (ι := PBlk 1) yPt) yPt (fsLine 1) 1 (Real.exp 0) := by
  intro dg dh g h z hg hh hd hgh _
  have hd' : dg () = dh () + 1 := by
    have := hd ()
    simp only [fsLine, HermLine.ofMetrics, Pi.one_apply] at this
    omega
  rw [aeval_def, aeval_def, eval₂_homog_pt _ _ g dg hg, eval₂_homog_pt _ _ h dh hh] at hgh
  simp only [yPt, one_pow, mul_one, one_mul, algebraMap_int_eq, eq_intCast, Int.cast_inj] at hgh
  rw [eval_map, eval_map, eval₂_homog_pt _ _ g dg hg, eval₂_homog_pt _ _ h dh hh, hgh, hd',
    fsLine_one_h, Real.exp_zero, one_mul, pow_succ, ← mul_assoc, norm_mul (_ * _)]

theorem noCommonZero_one :
    NoCommonZero (mCoordIdeal (ι := PBlk 1) yPt) yPt (fsLine 1).a ![(1 : ℚ)] := by
  intro z hz
  refine ⟨0, fun _ ↦ 1, fun _ ↦ 0, X ⟨(), 0⟩, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm k
    rw [support_X, Finset.mem_singleton] at hm
    subst hm
    simp
  · intro m hm k
    rw [support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  · intro k
    simp [fsLine, HermLine.ofMetrics]
  · simp [yPt]
  · obtain ⟨i, hi⟩ := hz.1 ()
    simpa [Subsingleton.elim i 0] using hi
  · simp

theorem one_mem_chartLat : (1 : ℚ) ∈ chartLat yPt (fsLine 1).a 1 := by
  intro c _
  simp only [yPt, one_zpow, Finset.prod_const_one, mul_one]
  exact one_mem _

theorem HeightLowerBound.hyps_inhabited :
    IsSmoothHerm (fsLine 1) ∧ (∀ j, ![(1 : ℚ)] j ∈ chartLat yPt (fsLine 1).a 1) ∧
      (∀ j, IsSectionBounded (mCoordIdeal (ι := PBlk 1) yPt) yPt (fsLine 1) (![(1 : ℚ)] j)
        (Real.exp 0)) ∧
      NoCommonZero (mCoordIdeal (ι := PBlk 1) yPt) yPt (fsLine 1).a ![(1 : ℚ)] ∧
      IsArithVar (mCoordIdeal (ι := PBlk 1) yPt) 1 ∧
      mCoordIdeal (ι := PBlk 1) yPt ≤ mCoordIdeal (ι := PBlk 1) yPt :=
  ⟨Inter.isSmoothHerm_fsLine 1, fun j ↦ by fin_cases j; exact one_mem_chartLat,
    fun j ↦ by fin_cases j; exact isSectionBounded_one, noCommonZero_one,
    mCoordIdeal_yPt ▸ isArithVar_pointZ, le_rfl⟩

def fsLineScaled : HermLine (PBlk 1) :=
  (fsLine 1).tensor (HermLine.ofWeight (fun _ ↦ 1) fun _ _ _ ↦ rfl)

theorem HeightMetricChange.hyps_inhabited :
    IsSmoothHerm (fsLine 1) ∧ IsSmoothHerm fsLineScaled ∧ (fsLine 1).a = fsLineScaled.a ∧
      (∀ z ∈ mcPts (⊥ : Ideal (MRing (PBlk 1))),
        |Real.log ((fsLine 1).h z / fsLineScaled.h z)| ≤ 1) ∧
      IsArithVar (⊥ : Ideal (MRing (PBlk 1))) 1 ∧ (⊥ : Ideal (MRing (PBlk 1))) ≤ ⊥ := by
  refine ⟨Inter.isSmoothHerm_fsLine 1, ?_, ?_, ?_, isArithVar_pointZ, le_rfl⟩
  · exact (Inter.isSmoothHerm_fsLine 1).mul contDiffOn_const
  · simp [fsLineScaled, HermLine.tensor, HermLine.ofWeight]
  · intro z hz
    have hpos := (fsLine 1).pos z hz.1
    simp only [fsLineScaled, HermLine.tensor, HermLine.ofWeight]
    rw [div_mul_cancel_left₀ hpos.ne', ← Real.exp_neg, neg_neg, Real.log_exp, abs_one]

theorem HeightPullback.hyps_inhabited :
    IsBlockMap (ι := PBlk 1) (ι' := PBlk 1) id id ∧ IsArithVar (mCoordIdeal (ι := PBlk 1) yPt) 1 ∧
      IsArithVar (imageZ (ι := PBlk 1) (ι' := PBlk 1) id (mCoordIdeal yPt)) 1 ∧
      IsSmoothHerm (fsLine 1) ∧ IsPullHerm (ι := PBlk 1) (ι' := PBlk 1) id id (fsLine 1) (fsLine 1) ∧
      IntermediateField.relfinrank (blockFnField (yPt ∘ id)) (blockFnField yPt) = 1 := by
  have h1 : IsArithVar (mCoordIdeal (ι := PBlk 1) yPt) 1 := mCoordIdeal_yPt ▸ isArithVar_pointZ
  refine ⟨isBlockMap_id, h1, ?_, Inter.isSmoothHerm_fsLine 1, ⟨?_, fun _ ↦ rfl⟩,
    IntermediateField.relfinrank_self _⟩
  · have : imageZ (ι := PBlk 1) (ι' := PBlk 1) id (mCoordIdeal yPt) = mCoordIdeal yPt := by
      simp [imageZ, rename_id]
    rw [this]
    exact h1
  · funext k
    unfold pullDeg
    exact (Function.injective_id.extend_apply _ _ k).symm

theorem HeightComparison.hyps_inhabited :
    IsSmoothHerm (fsLine 1) ∧ (fsLine 1).a = 1 :=
  ⟨Inter.isSmoothHerm_fsLine 1, rfl⟩

theorem DenseBoundedHeight.hyps_inhabited :
    IsArithVar (⊥ : Ideal (MRing (PBlk 1))) (0 + 1) ∧ IsSmoothHerm (fsLine 1) ∧ (fsLine 1).a = 1 :=
  ⟨isArithVar_pointZ, Inter.isSmoothHerm_fsLine 1, rfl⟩

def firstCoordinateLine : Submodule (𝓞 ℚ) (Fin 2 → 𝓞 ℚ) :=
  LinearMap.ker (LinearMap.proj (R := 𝓞 ℚ) (φ := fun _ : Fin 2 ↦ 𝓞 ℚ) 1)

theorem isSaturated_firstCoordinateLine : IsSaturated (HermitianBundle.standard ℚ 2) firstCoordinateLine := by
  intro a x ha hx
  simp only [firstCoordinateLine] at hx ⊢
  change a * x 1 = 0 at hx
  change x 1 = 0
  exact (mul_eq_zero.mp hx).resolve_left ha

theorem isSaturated_bot : IsSaturated (HermitianBundle.standard ℚ 2) ⊥ := by
  intro a x ha hx
  rw [Submodule.mem_bot] at hx ⊢
  exact (smul_eq_zero.mp hx).resolve_left ha

theorem isSaturated_top : IsSaturated (HermitianBundle.standard ℚ 2) ⊤ :=
  fun _ _ _ _ ↦ Submodule.mem_top

def firstCoordinateLineEquiv : firstCoordinateLine ≃ₗ[𝓞 ℚ] 𝓞 ℚ where
  toFun x := x.1 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun a := ⟨Pi.single 0 a, by
    rw [firstCoordinateLine, LinearMap.mem_ker, LinearMap.proj_apply]; simp⟩
  left_inv x := by
    have hx : x.1 1 = 0 := x.2
    apply Subtype.ext
    funext i
    fin_cases i
    · simp
    · simp [hx]
  right_inv a := by simp

theorem finrank_firstCoordinateLine : Module.finrank (𝓞 ℚ) firstCoordinateLine = 1 := by
  rw [firstCoordinateLineEquiv.finrank_eq, Module.finrank_self]

theorem SlopeMaxExtension.hyps_inhabited : IsSaturated (HermitianBundle.standard ℚ 2) firstCoordinateLine :=
  isSaturated_firstCoordinateLine

def flagE : Fin 3 → Submodule (𝓞 ℚ) (Fin 2 → 𝓞 ℚ) := ![⊥, firstCoordinateLine, ⊤]

theorem FlagDegreeBound.hyps_inhabited :
    Monotone flagE ∧ (∀ i, IsSaturated (HermitianBundle.standard ℚ 2) (flagE i)) ∧
      ∀ i : Fin (2 + 1), Module.finrank (𝓞 ℚ) (flagE i) = (i : ℕ) := by
  refine ⟨Fin.monotone_iff_le_succ.mpr fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩
  · fin_cases i
    · exact bot_le
    · exact le_top
  · fin_cases i
    · exact isSaturated_bot
    · exact isSaturated_firstCoordinateLine
    · exact isSaturated_top
  · fin_cases i
    · change Module.finrank (𝓞 ℚ) (⊥ : Submodule (𝓞 ℚ) (Fin 2 → 𝓞 ℚ)) = 0
      exact finrank_bot _ _
    · exact finrank_firstCoordinateLine
    · change Module.finrank (𝓞 ℚ) (⊤ : Submodule (𝓞 ℚ) (Fin 2 → 𝓞 ℚ)) = 2
      rw [finrank_top, Module.finrank_fin_fun]

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
