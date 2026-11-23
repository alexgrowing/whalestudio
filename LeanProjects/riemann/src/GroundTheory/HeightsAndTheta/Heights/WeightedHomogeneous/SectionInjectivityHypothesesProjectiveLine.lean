import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Points
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ mCoordIdeal chartLat chartLatNm secM mcPts IsArithVar)

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

instance (P : ArithVariety n) : P.ideal.IsPrime := P.isPrime

abbrev CoordRing (P : ArithVariety n) : Type := MvPolynomial (Coord n) ℤ ⧸ P.ideal

def FunField (P : ArithVariety n) : Type := FractionRing (CoordRing P)

instance (P : ArithVariety n) : Field (FunField P) := inferInstanceAs (Field (FractionRing _))

instance (P : ArithVariety n) : Algebra (CoordRing P) (FunField P) :=
  inferInstanceAs (Algebra _ (FractionRing _))

instance (P : ArithVariety n) : IsFractionRing (CoordRing P) (FunField P) :=
  inferInstanceAs (IsFractionRing _ (FractionRing _))

def val (P : ArithVariety n) (f : MvPolynomial (Coord n) ℤ) : FunField P :=
  algebraMap (CoordRing P) (FunField P) (Ideal.Quotient.mk P.ideal f)

def genPt (P : ArithVariety n) : Coord n → FunField P := fun v ↦ val P (X v)

def IsLive (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) : Prop :=
  ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal

def chartRing (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) : Subalgebra ℤ (FunField P) :=
  chartRingZ (genPt P) c

def chartPow (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ) : FunField P :=
  ∏ k, genPt P ⟨k, c k⟩ ^ a k

def IsHomogOfDeg (P : ArithVariety n) (a : ι → ℤ) (x : FunField P) : Prop :=
  ∃ (f g : MvPolynomial (Coord n) ℤ) (df dg : ι → ℕ), IsWeightedHomogeneous (coordDeg n) f df ∧
    IsWeightedHomogeneous (coordDeg n) g dg ∧ g ∉ P.ideal ∧ (∀ k, (df k : ℤ) - dg k = a k) ∧
    x = val P f / val P g

def conePoints {κ : Type} [Fintype κ] [DecidableEq κ] {m : κ → ℕ}
    (I : Ideal (MvPolynomial (Coord m) ℤ)) (F : Type*) [CommRing F] : Set (Cone m F) :=
  {z | BlockNonzero z ∧ ∀ f ∈ I, evalCone z f = 0}

theorem points_eq_conePoints (P : ArithVariety n) (F : Type*) [CommRing F] :
    P.points F = conePoints P.ideal F := rfl

def IsSmallFor (P : ArithVariety n) (a : ι → ℤ) (h : Cone n ℂ → ℝ) (s : FunField P) : Prop :=
  ∀ (g f : MvPolynomial (Coord n) ℤ) (dg df : ι → ℕ), IsWeightedHomogeneous (coordDeg n) g dg →
    IsWeightedHomogeneous (coordDeg n) f df → (∀ k, (dg k : ℤ) = df k + a k) →
    val P g = s * val P f → ∀ z ∈ P.points ℂ, ‖evalCone z g‖ ≤ ‖evalCone z f‖ * h z

structure GenSystem (P : ArithVariety n) where

  r : ℕ

  f : Fin r → MvPolynomial (Coord n) ℤ

  δ : Fin r → ι → ℕ
  homog : ∀ i, IsWeightedHomogeneous (coordDeg n) (f i) (δ i)
  span_eq : Ideal.span (Set.range f) = P.ideal

structure AddBlockData (P : ArithVariety n) where

  deg : ι → ℤ

  m : ℕ

  x : Fin (m + 1) → FunField P
  homog : ∀ j, IsHomogOfDeg P deg (x j)
  chart : ∀ c, IsLive P c → ∀ j, x j * chartPow P c (-deg) ∈ chartRing P c
  unit : ∀ c, IsLive P c → ∃ u : Fin (m + 1) → FunField P, (∀ j, u j ∈ chartRing P c) ∧
    ∑ j, u j * (x j * chartPow P c (-deg)) = 1

namespace AddBlockData

variable {P : ArithVariety n} (D : AddBlockData P)

def ξ (c : (k : ι) → Fin (n k + 1)) (j : Fin (D.m + 1)) : FunField P :=
  D.x j * chartPow P c (-D.deg)

def dims : Option ι → ℕ := fun o ↦ o.elim D.m n

def yPlus : Coord D.dims → FunField P
  | ⟨none, j⟩ => D.x j
  | ⟨some k, i⟩ => genPt P ⟨k, i⟩

def ext : Ideal (MvPolynomial (Coord D.dims) ℤ) := mCoordIdeal D.yPlus

def eNew : Option ι → ℤ := fun o ↦ o.elim 1 (fun _ ↦ 0)

def degB : Option ι → ℤ := fun o ↦ o.elim 1 (fun k ↦ -D.deg k)

def oldCoord : Coord n → Coord D.dims := fun v ↦ ⟨some v.1, v.2⟩

def newCoord (j : Fin (D.m + 1)) : Coord D.dims := ⟨none, j⟩

def lift (f : MvPolynomial (Coord n) ℤ) : MvPolynomial (Coord D.dims) ℤ := rename D.oldCoord f

def chartPlus (c : (k : ι) → Fin (n k + 1)) (j : Fin (D.m + 1)) :
    (o : Option ι) → Fin (D.dims o + 1)
  | none => j
  | some k => c k

variable {D}

def basePart₂ {F : Type*} (w : Cone D.dims F) : Cone n F := fun k ↦ w (some k)

def newPart {F : Type*} (w : Cone D.dims F) : Fin (D.m + 1) → F := w none

variable (D) in

def join {F : Type*} (z : Cone n F) (z' : Fin (D.m + 1) → F) : Cone D.dims F
  | none => z'
  | some k => z k

end AddBlockData

open AddBlockData

structure ChartForms {P : ArithVariety n} (D : AddBlockData P) where

  d : ι → ℕ
  d_pos : ∀ k, 1 ≤ d k
  dn_nonneg : ∀ k, 0 ≤ (d k : ℤ) + D.deg k

  g : ((k : ι) → Fin (n k + 1)) → Fin (D.m + 1) → MvPolynomial (Coord n) ℤ
  g_homog : ∀ c, IsLive P c → ∀ j,
    IsWeightedHomogeneous (coordDeg n) (g c j) (fun k ↦ ((d k : ℤ) + D.deg k).toNat)
  g_val : ∀ c, IsLive P c → ∀ j, val P (g c j) = val P (chartMonomial c d) * D.x j
  g_dead : ∀ c, ¬ IsLive P c → ∀ j, g c j = 0

section Metric

variable {P : ArithVariety n} {D : AddBlockData P}

def den (G : ChartForms D) (Γ : GenSystem P) (z : Cone n ℂ) : ℝ :=
  (∑ c, ∑ j, ‖evalCone z (G.g c j)‖ ^ 2) +
    ∑ i, ‖evalCone z (Γ.f i)‖ ^ 2 *
      ∏ k, l2Norm (z k) ^ (2 * ((G.d k : ℤ) + D.deg k - Γ.δ i k))

def hPlus (G : ChartForms D) (Γ : GenSystem P) (N : HermLine n) (w : Cone D.dims ℂ) : ℝ :=
  N.metric (basePart₂ w) * l2Norm (newPart w) *
    Real.sqrt ((∑ c, ‖evalCone (basePart₂ w) (chartMonomial c G.d)‖ ^ 2) / den G Γ (basePart₂ w))

def hB (G : ChartForms D) (Γ : GenSystem P) (N : HermLine n) (w : Cone D.dims ℂ) : ℝ :=
  hPlus G Γ N w / N.metric (basePart₂ w)

end Metric

section Examples

variable (n)

omit [Fintype ι] in
theorem isLive_whole (c : (k : ι) → Fin (n k + 1)) : IsLive (ArithVariety.whole n) c :=
  fun k h ↦ X_ne_zero (⟨k, c k⟩ : Coord n) ((Submodule.mem_bot _).mp h)

omit [Fintype ι] in
theorem genPt_whole_ne_zero (v : Coord n) : genPt (ArithVariety.whole n) v ≠ 0 := by
  intro h
  have h1 : Ideal.Quotient.mk (ArithVariety.whole n).ideal (X v) = 0 :=
    IsFractionRing.injective (CoordRing _) (FunField _) (h.trans (map_zero _).symm)
  rw [Ideal.Quotient.eq_zero_iff_mem] at h1
  change X v ∈ (⊥ : Ideal (MvPolynomial (Coord n) ℤ)) at h1
  rw [Submodule.mem_bot] at h1
  exact X_ne_zero v h1

theorem powBlock_ξ_eq (k₀ : ι) (e : ℕ) (c : (k : ι) → Fin (n k + 1)) (j : Fin (n k₀ + 1)) :
    genPt (ArithVariety.whole n) ⟨k₀, j⟩ ^ e *
        chartPow (ArithVariety.whole n) c (-(fun k ↦ if k = k₀ then (e : ℤ) else 0)) =
      (genPt _ ⟨k₀, j⟩ / genPt (ArithVariety.whole n) ⟨k₀, c k₀⟩) ^ e := by
  unfold chartPow
  rw [Finset.prod_eq_single k₀ (fun k _ hk ↦ by simp [hk]) (by simp)]
  simp [zpow_neg, div_eq_mul_inv, mul_pow]

def powBlock (k₀ : ι) (e : ℕ) : AddBlockData (ArithVariety.whole n) where
  deg := fun k ↦ if k = k₀ then (e : ℤ) else 0
  m := n k₀
  x := fun j ↦ genPt _ ⟨k₀, j⟩ ^ e
  homog := fun j ↦ ⟨X ⟨k₀, j⟩ ^ e, 1, e • coordDeg n ⟨k₀, j⟩, 0,
    (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k₀, j⟩).pow e,
    isWeightedHomogeneous_one ℤ (coordDeg n),
    by
      intro h
      change (1 : MvPolynomial (Coord n) ℤ) ∈ (⊥ : Ideal (MvPolynomial (Coord n) ℤ)) at h
      rw [Submodule.mem_bot] at h
      exact one_ne_zero h,
    by
      intro k
      by_cases hk : k = k₀
      · subst hk; simp [coordDeg]
      · simp [coordDeg, hk],
    by simp [val, genPt, map_pow]⟩
  chart := fun c _ j ↦ by
    rw [powBlock_ξ_eq]
    unfold chartRing ReciprocityTheory.ChartRestriction.G.Geo.chartRingZ
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self (⟨k₀, j⟩ : Coord n))) e
  unit := fun c _ ↦ by
    refine ⟨fun j ↦ if j = c k₀ then 1 else 0, fun j ↦ ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    · simp only [powBlock_ξ_eq, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      rw [div_self (genPt_whole_ne_zero n _), one_pow]

def powChartForms (k₀ : ι) (e : ℕ) : ChartForms (powBlock n k₀ e) where
  d := fun _ ↦ 1
  d_pos := fun _ ↦ le_rfl
  dn_nonneg := fun k ↦ by
    change (0 : ℤ) ≤ ((1 : ℕ) : ℤ) + (if k = k₀ then (e : ℤ) else 0)
    split_ifs <;> omega
  g := fun c j ↦ chartMonomial c (fun _ ↦ 1) * X ⟨k₀, j⟩ ^ e
  g_homog := fun c _ j ↦ by
    have h := (isWeightedHomogeneous_chartMonomial c (fun _ ↦ 1)).mul
      ((isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k₀, j⟩).pow e)
    convert h using 1
    funext k
    change (((1 : ℕ) : ℤ) + (if k = k₀ then (e : ℤ) else 0)).toNat = _
    by_cases hk : k = k₀
    · subst hk; simp [coordDeg]; omega
    · simp [coordDeg, hk]
  g_val := fun c _ j ↦ by simp [val, genPt, map_mul, map_pow, powBlock]
  g_dead := fun c hc ↦ absurd (isLive_whole n c) hc

def wholeGens : GenSystem (ArithVariety.whole n) where
  r := 0
  f := Fin.elim0
  δ := Fin.elim0
  homog := fun i ↦ i.elim0
  span_eq := by
    rw [Set.range_eq_empty, Ideal.span_empty]
    rfl

def blockPowLine (k₀ : ι) (e : ℕ) : HermLine n where
  deg := fun k ↦ if k = k₀ then (e : ℤ) else 0
  metric z := l2Norm (z k₀) ^ e
  metric_pos z hz := pow_pos (vectorL2Norm_pos (hz k₀)) e
  metric_smul c z _ _ := by
    rw [vectorL2Norm_const_mul, mul_pow, Finset.prod_eq_single k₀ (fun k _ hk ↦ by simp [hk]) (by simp)]
    simp
  metric_smooth := (contDiffOn_l2Norm_block k₀).pow e

theorem powBlock_lift_not_mem (k₀ : ι) (e : ℕ) (c : (k : ι) → Fin (n k + 1))
    (j : Fin (n k₀ + 1)) :
    (powBlock n k₀ e).lift ((powChartForms n k₀ e).g c j) ∉ (powBlock n k₀ e).ext := by
  intro h
  unfold AddBlockData.ext ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal at h
  rw [RingHom.mem_ker] at h
  simp only [AddBlockData.lift, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap, aeval_rename, powChartForms,
    chartMonomial, map_mul, map_prod, map_pow, aeval_X, Function.comp_apply] at h
  simp only [mul_eq_zero, Finset.prod_eq_zero_iff, pow_eq_zero_iff', C_eq_zero, X_ne_zero,
    or_false] at h
  rcases h with ⟨k, -, h, -⟩ | ⟨h, -⟩
  · exact genPt_whole_ne_zero n _ h
  · exact genPt_whole_ne_zero n _ h

end Examples

def ChartFormsAlt.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P),
    ∃ d₀ : ι → ℕ, ∀ d : ι → ℕ, d₀ ≤ d → ∃ G : ChartForms D, G.d = d

def ChartCrossRatio.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (G : ChartForms D) (c c' : (k : ι) → Fin (n k + 1)) (j : Fin (D.m + 1)),
    chartMonomial c' G.d * G.g c j - chartMonomial c G.d * G.g c' j ∈ P.ideal

def ChartVanishing.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (G : ChartForms D), ∀ z ∈ P.points ℂ, ∀ c : (k : ι) → Fin (n k + 1),
      (∀ j, evalCone z (G.g c j) = 0) ↔ evalCone z (chartMonomial c G.d) = 0

def ChartPrimality.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P),
    ∃ Q : ArithVariety D.dims, Q.ideal = D.ext

def ExtensionDimension.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P),
    ringKrullDim (MvPolynomial (Coord D.dims) ℤ ⧸ D.ext) =
      ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) + 1

def ChartRingDescription.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (c : (k : ι) → Fin (n k + 1)), IsLive P c → ∀ j : Fin (D.m + 1),
      chartRingZ D.yPlus (D.chartPlus c j) =
          Algebra.adjoin ℤ ((chartRing P c : Set (FunField P)) ∪
            Set.range fun i ↦ D.ξ c i / D.ξ c j) ∧
        chartRingZ D.yPlus (D.chartPlus c j) =
          Algebra.adjoin ℤ ((chartRing P c : Set (FunField P)) ∪ {(D.ξ c j)⁻¹})

def ConePoints.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (G : ChartForms D),
    (∀ (c : (k : ι) → Fin (n k + 1)) (i j : Fin (D.m + 1)),
      D.lift (G.g c j) * X (D.newCoord i) - D.lift (G.g c i) * X (D.newCoord j) ∈ D.ext) ∧
    ∀ w ∈ conePoints D.ext ℂ, basePart₂ w ∈ P.points ℂ ∧ ∃ la : ℂ, la ≠ 0 ∧
      ∀ c : (k : ι) → Fin (n k + 1), evalCone (basePart₂ w) (chartMonomial c G.d) ≠ 0 →
        ∀ j, newPart w j =
          la * evalCone (basePart₂ w) (G.g c j) / evalCone (basePart₂ w) (chartMonomial c G.d)

def ConePointsConverse.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (G : ChartForms D), ∀ z ∈ P.points ℂ, ∀ c : (k : ι) → Fin (n k + 1),
      evalCone z (chartMonomial c G.d) ≠ 0 →
        D.join z (fun j ↦ evalCone z (G.g c j)) ∈ conePoints D.ext ℂ

def ChartDenominatorAlt.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (G : ChartForms D) (Γ : GenSystem P),
    ContDiffOn ℝ ∞ (den G Γ) {z | BlockNonzero z} ∧ ∀ z : Cone n ℂ, BlockNonzero z → 0 < den G Γ z

def ChartMetric.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (G : ChartForms D) (Γ : GenSystem P) (N : HermLine n), N.deg = D.deg →
    (∃ A : HermLine D.dims, A.deg = eNew ∧ A.metric = hPlus G Γ N) ∧
    ∀ w ∈ conePoints D.ext ℂ, ∀ (la : ℂ) (c : (k : ι) → Fin (n k + 1)),
      evalCone (basePart₂ w) (chartMonomial c G.d) ≠ 0 →
      (∀ j, newPart w j =
        la * evalCone (basePart₂ w) (G.g c j) / evalCone (basePart₂ w) (chartMonomial c G.d)) →
      hPlus G Γ N w = ‖la‖ * N.metric (basePart₂ w)

def SectionNorm.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (G : ChartForms D) (Γ : GenSystem P) (N : HermLine n), N.deg = D.deg →
    (∃ B : HermLine D.dims, B.deg = D.degB ∧ B.metric = hB G Γ N) ∧
    ∀ (c : (k : ι) → Fin (n k + 1)) (j : Fin (D.m + 1)), D.lift (G.g c j) ∉ D.ext →
      ∀ w ∈ conePoints D.ext ℂ, evalCone (basePart₂ w) (G.g c j) ≠ 0 →
        ‖newPart w j‖ * ‖evalCone (basePart₂ w) (chartMonomial c G.d)‖ /
          (‖evalCone (basePart₂ w) (G.g c j)‖ * hB G Γ N w) = 1

def SectionCycle.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (G : ChartForms D) (c : (k : ι) → Fin (n k + 1)) (j : Fin (D.m + 1)),
    D.lift (G.g c j) ∉ D.ext → ∀ W,
      NumbersDVR.ratDiv D.ext (X (D.newCoord j) * D.lift (chartMonomial c G.d)) (D.lift (G.g c j))
        W = 0

def SmallSections.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (G : ChartForms D) (Γ : GenSystem P) (N : HermLine n), N.deg = D.deg → ∀ τ : ℕ,
    (∀ μ : Fin (D.m + 1) → ℕ, ∑ j, μ j = τ → ∏ j, D.x j ^ μ j ∈ chartLat (genPt P) D.deg τ) ∧
    ∀ F : MvPolynomial (Fin (D.m + 1)) ℤ, F.IsHomogeneous τ →
      (∀ w ∈ conePoints D.ext ℂ, ‖eval₂ (Int.castRingHom ℂ) (newPart w) F‖ ≤ hPlus G Γ N w ^ τ) →
      ∀ (g h : MvPolynomial (Coord n) ℤ) (dg dh : ι → ℕ), IsWeightedHomogeneous (coordDeg n) g dg →
        IsWeightedHomogeneous (coordDeg n) h dh → (∀ k, (dg k : ℤ) = dh k + τ * D.deg k) →
        val P g = aeval D.x F * val P h →
        (∀ c, IsLive P c → chartMonomial c G.d ^ τ * g - bind₁ (G.g c) F * h ∈ P.ideal) ∧
        ∀ z ∈ P.points ℂ, ‖evalCone z g‖ ≤ ‖evalCone z h‖ * N.metric z ^ τ

section ExamplesT1

variable (n)

theorem chartForms_hypotheses_block_power (k₀ : ι) :
    (blockPowLine n k₀ 1).deg = (powBlock n k₀ 1).deg ∧
      ∀ c j, (powBlock n k₀ 1).lift ((powChartForms n k₀ 1).g c j) ∉ (powBlock n k₀ 1).ext :=
  ⟨rfl, fun c j ↦ powBlock_lift_not_mem n k₀ 1 c j⟩

theorem smallSections_hypotheses_block_power (k₀ : ι) :
    (MvPolynomial.IsHomogeneous (1 : MvPolynomial (Fin ((powBlock n k₀ 1).m + 1)) ℤ) 0) ∧
    (∀ w ∈ conePoints (powBlock n k₀ 1).ext ℂ,
      ‖eval₂ (Int.castRingHom ℂ) (newPart w) (1 : MvPolynomial (Fin ((powBlock n k₀ 1).m + 1)) ℤ)‖ ≤
        hPlus (powChartForms n k₀ 1) (wholeGens n) (blockPowLine n k₀ 1) w ^ 0) ∧
    val (ArithVariety.whole n) 1 =
      aeval (powBlock n k₀ 1).x (1 : MvPolynomial (Fin ((powBlock n k₀ 1).m + 1)) ℤ) *
        val (ArithVariety.whole n) 1 :=
  ⟨isHomogeneous_one _ _, fun w _ ↦ by simp, by simp [val]⟩

end ExamplesT1

def oneBlockIdeal (P : ArithVariety n) (k₀ : ι) : Ideal (MvPolynomial (Fin (n k₀ + 1)) ℤ) :=
  P.ideal.comap (rename fun i : Fin (n k₀ + 1) ↦ (⟨k₀, i⟩ : Coord n))

def oneBlockPoints (P : ArithVariety n) (k₀ : ι) : Set (Fin (n k₀ + 1) → ℂ) :=
  {w | w ≠ 0 ∧ ∀ f ∈ oneBlockIdeal P k₀, eval₂ (Int.castRingHom ℂ) w f = 0}

variable (n) in

def pullFS (k₀ : ι) : HermLine n :=
  HermLine.pullback (fun _ : Unit ↦ k₀) (fun _ _ _ ↦ Subsingleton.elim _ _)
    (HermLine.standard (n ∘ fun _ : Unit ↦ k₀))

def BlockSurjectivity.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (k₀ : ι),
    (fun z : Cone n ℂ ↦ z k₀) '' P.points ℂ = oneBlockPoints P k₀

def SupNormEquality.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (k₀ : ι),
    (∀ N : ℕ, secM (genPt P) (N • Pi.single k₀ 1) =
      (ReciprocityTheory.ChartRestriction.G.Geo.sec ℤ (fun i : Fin (n k₀ + 1) ↦ genPt P ⟨k₀, i⟩) N).toAddSubgroup) ∧
    ∀ (N : ℕ) (f : MvPolynomial (Fin (n k₀ + 1)) ℤ), f.IsHomogeneous N →
      sSup ((fun z : Cone n ℂ ↦
          ‖eval₂ (Int.castRingHom ℂ) (z k₀) f‖ / (pullFS n k₀).metric z ^ N) '' P.points ℂ) =
        sSup ((fun w ↦ ‖eval₂ (Int.castRingHom ℂ) w f‖ / l2Norm w ^ N) '' oneBlockPoints P k₀)

def powDivStd (M : HermLine n) (k : ℕ) : HermLine n where
  deg b := k * M.deg b - 1
  metric z := M.metric z ^ k / (HermLine.standard n).metric z
  metric_pos z hz :=
    div_pos (pow_pos (M.metric_pos z hz) k) ((HermLine.standard n).metric_pos z hz)
  metric_smul c z hc hz := by
    rw [M.metric_smul c z hc hz, (HermLine.standard n).metric_smul c z hc hz]
    have hS := ((HermLine.standard n).metric_pos z hz).ne'
    have hc' : ∀ b, ‖c b‖ ≠ 0 := fun b ↦ norm_ne_zero_iff.mpr (hc b)
    have hP : ∏ b, ‖c b‖ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun b _ ↦ hc' b
    have h : ∀ b, ‖c b‖ ^ ((k : ℤ) * M.deg b - 1) = (‖c b‖ ^ M.deg b) ^ k / ‖c b‖ := fun b ↦ by
      rw [zpow_sub₀ (hc' b), zpow_one, zpow_mul', zpow_natCast]
    have hs : ∀ b, (HermLine.standard n).deg b = 1 := fun _ ↦ rfl
    simp only [h, hs, zpow_one, Finset.prod_div_distrib, Finset.prod_pow, mul_pow]
    field_simp
  metric_smooth := (M.metric_smooth.pow k).div (HermLine.standard n).metric_smooth
    fun z hz ↦ ((HermLine.standard n).metric_pos z hz).ne'

def twistPow (M : HermLine n) (p a : ℕ) (C : ℝ) : HermLine n where
  deg b := a * (p * M.deg b + 1)
  metric z := Real.exp (-(a * C)) * (M.metric z ^ p * (HermLine.standard n).metric z) ^ a
  metric_pos z hz := mul_pos (Real.exp_pos _)
    (pow_pos (mul_pos (pow_pos (M.metric_pos z hz) p) ((HermLine.standard n).metric_pos z hz)) a)
  metric_smul c z hc hz := by
    rw [M.metric_smul c z hc hz, (HermLine.standard n).metric_smul c z hc hz]
    have hc' : ∀ b, ‖c b‖ ≠ 0 := fun b ↦ norm_ne_zero_iff.mpr (hc b)
    have h : ∀ b, ‖c b‖ ^ ((a : ℤ) * (p * M.deg b + 1)) = ((‖c b‖ ^ M.deg b) ^ p * ‖c b‖) ^ a :=
      fun b ↦ by
        rw [mul_comm, zpow_mul, zpow_add₀ (hc' b), zpow_one, zpow_mul', zpow_natCast,
          zpow_natCast]
    have hs : ∀ b, (HermLine.standard n).deg b = 1 := fun _ ↦ rfl
    simp only [h, hs, zpow_one, Finset.prod_pow, Finset.prod_mul_distrib, mul_pow]
    ring
  metric_smooth := contDiffOn_const.mul
    (((M.metric_smooth.pow p).mul (HermLine.standard n).metric_smooth).pow a)

def smallSec {P : ArithVariety n} {D : AddBlockData P} (G : ChartForms D) (Γ : GenSystem P)
    (N : HermLine n) (m : ℕ) : Set (FunField P) :=
  {s | ∃ F : MvPolynomial (Fin (D.m + 1)) ℤ, F.IsHomogeneous m ∧ s = aeval D.x F ∧
    ∀ w ∈ conePoints D.ext ℂ, ‖eval₂ (Int.castRingHom ℂ) (newPart w) F‖ ≤ hPlus G Γ N w ^ m}

def sectionVal {P : ArithVariety n} {a : ι → ℤ} (e : IntegralSection P a) : FunField P :=
  val P e.num / val P e.den

def SectionInjectivity.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (M : HermLine n)
    (k q a : ℕ) (C : ℝ), k < q → 1 ≤ a →
    ∀ e : IntegralSection P (powDivStd M k).deg, e.num ∉ P.ideal →
      IntegralSection.SupNormLE (powDivStd M k) e C →
    ∀ D : AddBlockData P, D.deg = (twistPow M (q - k) a C).deg →
    ∀ (G : ChartForms D) (Γ : GenSystem P) (m : ℕ),
      Set.InjOn (fun s ↦ s * sectionVal e ^ (a * m)) (smallSec G Γ (twistPow M (q - k) a C) m) ∧
      ∀ s ∈ smallSec G Γ (twistPow M (q - k) a C) m,
        s * sectionVal e ^ (a * m) ∈ chartLat (genPt P) M.deg (a * q * m) ∧
        IsSmallFor P (fun b ↦ ((a * q * m : ℕ) : ℤ) * M.deg b) (fun z ↦ M.metric z ^ (a * q * m))
          (s * sectionVal e ^ (a * m))

def LatticePacking.Statement : Prop :=
  ∀ (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (nrm : Λ → ℝ) (B : ℝ),
    0 ≤ B → (∀ x y, nrm (x + y) ≤ nrm x + nrm y) → (∀ (k : ℤ) x, nrm (k • x) = |(k : ℝ)| * nrm x) →
    (∀ x, x ≠ 0 → Real.exp (-B) ≤ nrm x) →
    {x | nrm x ≤ 1}.Finite ∧
      (({x | nrm x ≤ 1}.ncard : ℕ) : ℝ) ≤ Real.exp (Module.finrank ℤ Λ * (B + Real.log 5))

def gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r : ℕ} (v : Fin r → E) : ℝ :=
  Matrix.det (Matrix.of fun i j ↦ inner ℝ (v i) (v j))

def HadamardGramBound.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (r : ℕ) (v : Fin r → E),
    LinearIndependent ℝ v → (∀ i, ‖v i‖ ≤ 1) →
    0 ≤ -Real.log (Real.sqrt (gram v)) ∧
      ∀ b : Fin r → E, LinearIndependent ℝ b → (∀ i, v i ∈ AddSubgroup.closure (Set.range b)) →
        0 ≤ -Real.log (Real.sqrt (gram b))

def monomialOf (μ : Coord n → ℕ) : MvPolynomial (Coord n) ℤ := ∏ v, X v ^ μ v

def MonomialsBoundedBy (P : ArithVariety n) (L : HermLine n) (a : ι → ℕ) : Prop :=
  ∀ z ∈ P.points ℂ, ∀ μ : Coord n → ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) →
    ‖evalCone z (monomialOf μ)‖ ≤ L.metric z

def MonomialMap.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (L : HermLine n)
    (a : ι → ℕ), (∀ k, L.deg k = a k) → MonomialsBoundedBy P L a →
    ∀ (q m r : ℕ), r < q → ∀ μg μh : Coord n → ℕ, (∀ k, ∑ i, μg ⟨k, i⟩ = a k) →
      (∀ k, ∑ i, μh ⟨k, i⟩ = 1) → val P (monomialOf μg) ≠ 0 → val P (monomialOf μh) ≠ 0 →
      Set.InjOn (fun s ↦ s * val P (monomialOf μg) ^ (q - r) * val P (monomialOf μh) ^ (m + 1))
          {s | s ∈ chartLatNm (genPt P) (fun k ↦ (a k : ℤ)) (q * m + r) ∧
            IsSmallFor P (fun k ↦ ((q * m + r : ℕ) : ℤ) * a k) (fun z ↦ L.metric z ^ (q * m + r)) s} ∧
      ∀ s, s ∈ chartLatNm (genPt P) (fun k ↦ (a k : ℤ)) (q * m + r) →
        IsSmallFor P (fun k ↦ ((q * m + r : ℕ) : ℤ) * a k) (fun z ↦ L.metric z ^ (q * m + r)) s →
        s * val P (monomialOf μg) ^ (q - r) * val P (monomialOf μh) ^ (m + 1) ∈
            chartLatNm (genPt P) (fun k ↦ ((q * a k + 1 : ℕ) : ℤ)) (m + 1) ∧
          IsSmallFor P (fun k ↦ ((m + 1 : ℕ) : ℤ) * ((q * a k + 1 : ℕ) : ℤ))
            (fun z ↦ (L.metric z ^ q * (HermLine.standard n).metric z) ^ (m + 1))
            (s * val P (monomialOf μg) ^ (q - r) * val P (monomialOf μh) ^ (m + 1))

def LatticePointCount.Statement : Prop :=
  ∀ C : ℝ, 0 < C → ∃ K₀ : ℝ, ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (r : ℕ)
    (b : Fin r → E), LinearIndependent ℝ b → ∀ S : Finset E, (∀ s ∈ S, ‖s‖ ≤ C) →
      AddSubgroup.closure (S : Set E) = AddSubgroup.closure (Set.range b) →
      {x : E | x ∈ AddSubgroup.closure (Set.range b) ∧ ‖x‖ ≤ 1}.Finite ∧
        Real.log (({x : E | x ∈ AddSubgroup.closure (Set.range b) ∧ ‖x‖ ≤ 1}.ncard : ℕ) : ℝ) ≤
          -Real.log (Real.sqrt (gram b)) + K₀ * ((r + 1) * Real.log (r + 1))

def WeightedDegree.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : ℕ),
    ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) = ((D + 1 + Fintype.card ι : ℕ) : WithBot ℕ∞) →
    ∀ (a : Fin D → ι → ℤ) (p : ℕ) (hp : p.Prime),
      haveI := Fact.mk hp
      NumbersDVR.intNum ℚ (P.ideal.map (MvPolynomial.map (Int.castRingHom ℚ))) a =
        NumbersDVR.cycEval
          (fun V ↦ NumbersDVR.intNum (ZMod p) (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) a)
          (NumbersDVR.divCycle P.ideal (C (p : ℤ)))

def BoundedMonomials.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (M : HermLine n) (k : ℕ)
    (e : IntegralSection P (powDivStd M k).deg),
    (∀ z ∈ P.points ℂ, ∀ (c c' : (b : ι) → Fin (n b + 1)) (d d' : ι → ℕ)
      (e₁ e₂ : MvPolynomial (Coord n) ℤ),
      IsChartForm P (powDivStd M k).deg e.num e.den c d e₁ →
      IsChartForm P (powDivStd M k).deg e.num e.den c' d' e₂ →
      (∀ b, z b (c b) ≠ 0) → (∀ b, z b (c' b) ≠ 0) →
      ‖evalCone z e₁‖ / (‖evalCone z (chartMonomial c d)‖ * (powDivStd M k).metric z) =
        ‖evalCone z e₂‖ / (‖evalCone z (chartMonomial c' d')‖ * (powDivStd M k).metric z)) ∧
    ∃ C : ℝ, IntegralSection.SupNormLE (powDivStd M k) e C

section OneBlock

open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder

def affGen (K : Type) [Field K] (i : ℕ) : Fin (i + 1) → FractionRing (MvPolynomial (Fin i) K) :=
  Fin.cons 1 fun j ↦ algebraMap (MvPolynomial (Fin i) K) _ (X j)

def oneBlockPt {K : Type} [Field K] [NumberField K] {d : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K)) (i : ℕ) :
    (Σ _ : Unit, Fin d × Fin (i + 1)) → FractionRing (MvPolynomial (Fin i) K) :=
  fun p ↦ algebraMap K _ (om p.2.1 : K) * affGen K i p.2.2

def embMat {K : Type} [Field K] [NumberField K] {d : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K)) :
    Matrix (Fin d) (K →+* ℂ) ℂ :=
  Matrix.of fun m σ ↦ σ (om m : K)

def OneBlockModel.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (om : Module.Basis (Fin d) ℤ (𝓞 K)) (i : ℕ),
    IsArithVar (mCoordIdeal (oneBlockPt om i)) (i + 1) ∧
    ∀ N : ℕ, 1 ≤ N → ∀ s, s ∈ secM (oneBlockPt om i) (fun _ ↦ N) ↔
      ∃ F : MvPolynomial (Fin (i + 1)) (𝓞 K), F.IsHomogeneous N ∧
        s = eval₂ ((algebraMap K (FractionRing (MvPolynomial (Fin i) K))).comp
          (algebraMap (𝓞 K) K)) (affGen K i) F

open Classical in

def OneBlockPoints.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (om : Module.Basis (Fin d) ℤ (𝓞 K)) (i : ℕ),
    (∀ z ∈ mcPts (mCoordIdeal (oneBlockPt om i)), ∃! σ : K →+* ℂ, ∃ w : Fin (i + 1) → ℂ, w ≠ 0 ∧
      ∀ m j, z ⟨(), (m, j)⟩ = σ (om m : K) * w j) ∧
    (∃ Minv : Matrix (K →+* ℂ) (Fin d) ℂ, Minv * embMat om = 1 ∧ embMat om * Minv = 1) ∧
    ∀ Minv : Matrix (K →+* ℂ) (Fin d) ℂ, Minv * embMat om = 1 →
      ∀ (z : (Σ _ : Unit, Fin d × Fin (i + 1)) → ℂ) (σ : K →+* ℂ) (w : Fin (i + 1) → ℂ),
        (∀ m j, z ⟨(), (m, j)⟩ = σ (om m : K) * w j) → ∀ j, w j = ∑ m, Minv σ m * z ⟨(), (m, j)⟩

def hermNorm {i : ℕ} (H : Matrix (Fin i) (Fin i) ℂ) (w : Fin i → ℂ) : ℝ :=
  Real.sqrt (star w ⬝ᵥ (H *ᵥ w)).re

def satLine {K' : Type} [Field K'] [NumberField K'] {i : ℕ} (v : Fin i → 𝓞 K') :
    Submodule (𝓞 K') (Fin i → 𝓞 K') where
  carrier := {x | ∃ c : K', ∀ j, (x j : K') = c * v j}
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, fun j ↦ by simp [ha j, hb j, add_mul]⟩
  zero_mem' := ⟨0, fun j ↦ by simp⟩
  smul_mem' := by
    rintro r x ⟨a, ha⟩
    exact ⟨r * a, fun j ↦ by simp [ha j, mul_assoc]⟩

def PointHeightDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (om : Module.Basis (Fin d) ℤ (𝓞 K)) (i N : ℕ)
    (e : Fin d × Fin i ≃ Fin (N + 1)) (H : (K →+* ℂ) → Matrix (Fin i) (Fin i) ℂ),
    (∀ σ, (H σ).PosDef) → (∀ σ, H (ComplexEmbedding.conjugate σ) = (H σ).map (starRingEnd ℂ)) →
    ∀ A : HermLine (fun _ : Unit ↦ N), (∀ u, A.deg u = 1) →
    (∀ (σ : K →+* ℂ) (w : Fin i → ℂ), w ≠ 0 →
      A.metric (fun _ t ↦ σ (om (e.symm t).1 : K) * w (e.symm t).2) = hermNorm (H σ) w) →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (E : HermitianBundle.{0} K')
      (φ : E.carrier ≃ₗ[𝓞 K'] (Fin i → 𝓞 K')),
      (∀ (σ' : K' →+* ℂ) (x y : E.carrier),
        (E.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 K'] x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 K'] y) =
          star (fun j ↦ σ' (φ x j : K')) ⬝ᵥ
            (H (σ'.comp (algebraMap K K')) *ᵥ fun j ↦ σ' (φ y j : K'))) →
      ∀ (ψ : K' →+* AlgebraicClosure ℚ) (v : Fin i → 𝓞 K'), v ≠ 0 →
        HermitianBundle.normDegree E ((satLine v).comap φ.toLinearMap) =
          -height A (fun _ t ↦ ψ (algebraMap K K' (om (e.symm t).1 : K) * (v (e.symm t).2 : K')))

end OneBlock

section ExamplesRest

def constSection (P : ArithVariety n) (a : ι → ℤ) (ha : ∀ b, a b = 0) : IntegralSection P a where
  num := 1
  den := 1
  numDeg := 0
  denDeg := 0
  num_isHomogeneous := isWeightedHomogeneous_one ℤ (coordDeg n)
  den_isHomogeneous := isWeightedHomogeneous_one ℤ (coordDeg n)
  deg_eq b := by simp [ha b]
  den_not_mem := (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top
  regular _ _ := ⟨0, 1, ⟨0, isWeightedHomogeneous_one ℤ (coordDeg n), fun b ↦ by simp [ha b]⟩,
    by simp [chartMonomial]⟩

theorem val_monomialOf (P : ArithVariety n) (μ : Coord n → ℕ) :
    val P (monomialOf μ) = ∏ v, genPt P v ^ μ v := by
  simp [monomialOf, val, genPt, map_prod, map_pow]

abbrev projectiveLineSizes : Unit → ℕ := fun _ ↦ 1

abbrev projectivePointSizes : Unit → ℕ := fun _ ↦ 0

def exSection : IntegralSection (ArithVariety.whole projectiveLineSizes) (powDivStd (HermLine.standard projectiveLineSizes) 1).deg :=
  constSection _ _ fun _ ↦ by simp [powDivStd, HermLine.standard]

theorem exSection_supNormLE :
    IntegralSection.SupNormLE (powDivStd (HermLine.standard projectiveLineSizes) 1) exSection 0 := by
  intro z hz c d e' he _
  obtain ⟨-, hmem⟩ := he
  have h0 : e' = chartMonomial c d := by
    have := (Submodule.mem_bot _).mp hmem
    simpa [exSection, constSection, sub_eq_zero] using this
  subst h0
  have hS := ((HermLine.standard projectiveLineSizes).metric_pos z hz.1).ne'
  have hm : (powDivStd (HermLine.standard projectiveLineSizes) 1).metric z = 1 := by
    change (HermLine.standard projectiveLineSizes).metric z ^ 1 / (HermLine.standard projectiveLineSizes).metric z = 1
    rw [pow_one, div_self hS]
  rw [hm, mul_one, Real.exp_zero]
  exact div_self_le_one _

theorem sectionInjectivity_hypotheses_projectiveLine :
    1 < 2 ∧ 1 ≤ 1 ∧ exSection.num ∉ (ArithVariety.whole projectiveLineSizes).ideal ∧
      IntegralSection.SupNormLE (powDivStd (HermLine.standard projectiveLineSizes) 1) exSection 0 ∧
      (powBlock projectiveLineSizes () 2).deg = (twistPow (HermLine.standard projectiveLineSizes) (2 - 1) 1 0).deg := by
  refine ⟨by norm_num, le_rfl, ?_, exSection_supNormLE, ?_⟩
  · intro h
    have := (Submodule.mem_bot _).mp h
    simp [exSection, constSection] at this
  · funext b
    simp [powBlock, twistPow, HermLine.standard]

theorem monomialMap_hypotheses_point :
    (∀ k, (HermLine.standard projectivePointSizes).deg k = ((fun _ ↦ 1 : Unit → ℕ) k : ℤ)) ∧
      MonomialsBoundedBy (ArithVariety.whole projectivePointSizes) (HermLine.standard projectivePointSizes) (fun _ ↦ 1) ∧ 0 < 1 ∧
      (∀ k, ∑ i, (fun _ ↦ 1 : Coord projectivePointSizes → ℕ) ⟨k, i⟩ = 1) ∧
      val (ArithVariety.whole projectivePointSizes) (monomialOf (fun _ ↦ 1)) ≠ 0 := by
  refine ⟨fun _ ↦ rfl, ?_, Nat.one_pos, fun _ ↦ by simp, ?_⟩
  · intro z _ μ hμ
    have hv : ∀ v : Coord projectivePointSizes, v = ⟨(), 0⟩ := by
      rintro ⟨⟨⟩, i⟩
      rw [Fin.fin_one_eq_zero i]
    have h1 : μ ⟨(), 0⟩ = 1 := by
      have := hμ ()
      simp only [projectivePointSizes, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at this
      exact this
    have he : evalCone z (monomialOf μ) = z () 0 := by
      simp only [monomialOf, evalCone]
      rw [Fintype.prod_eq_single ⟨(), 0⟩ (fun v hv' ↦ absurd (hv v) hv'), h1, pow_one, eval₂_X]
    rw [he]
    change ‖z () 0‖ ≤ ∏ k, l2Norm (z k)
    rw [Fintype.prod_unique]
    exact norm_le_l2Norm (z ()) 0
  · rw [val_monomialOf]
    exact Finset.prod_ne_zero_iff.mpr fun v _ ↦ pow_ne_zero _ (genPt_whole_ne_zero projectivePointSizes v)

theorem weightedDegree_hypotheses_point :
    ringKrullDim (MvPolynomial (Coord projectivePointSizes) ℤ ⧸ (ArithVariety.whole projectivePointSizes).ideal) =
      ((0 + 1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ∧ Nat.Prime 2 := by
  refine ⟨?_, Nat.prime_two⟩
  rw [show (ArithVariety.whole projectivePointSizes).ideal = ⊥ from rfl,
    ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  have hc : Nat.card (Coord projectivePointSizes) = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp
  rw [hc, Fintype.card_unit]
  norm_cast

theorem hadamardGram_hypotheses_unit_basis :
    LinearIndependent ℝ (EuclideanSpace.basisFun (Fin 1) ℝ) ∧
      (∀ i, ‖EuclideanSpace.basisFun (Fin 1) ℝ i‖ ≤ 1) ∧
      ∀ i, EuclideanSpace.basisFun (Fin 1) ℝ i ∈
        AddSubgroup.closure (Set.range (EuclideanSpace.basisFun (Fin 1) ℝ)) :=
  ⟨(EuclideanSpace.basisFun (Fin 1) ℝ).orthonormal.linearIndependent,
    fun i ↦ ((EuclideanSpace.basisFun (Fin 1) ℝ).orthonormal.1 i).le,
    fun i ↦ AddSubgroup.subset_closure (Set.mem_range_self i)⟩

theorem latticePointCount_hypotheses_unit :
    (0 : ℝ) < 1 ∧ LinearIndependent ℝ (EuclideanSpace.basisFun (Fin 1) ℝ) ∧
      (∀ s ∈ ({EuclideanSpace.basisFun (Fin 1) ℝ 0} : Finset (EuclideanSpace ℝ (Fin 1))), ‖s‖ ≤ 1) ∧
      AddSubgroup.closure
          (({EuclideanSpace.basisFun (Fin 1) ℝ 0} : Finset (EuclideanSpace ℝ (Fin 1))) :
            Set (EuclideanSpace ℝ (Fin 1))) =
        AddSubgroup.closure (Set.range (EuclideanSpace.basisFun (Fin 1) ℝ)) := by
  refine ⟨one_pos, (EuclideanSpace.basisFun (Fin 1) ℝ).orthonormal.linearIndependent, ?_, ?_⟩
  · intro s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    exact ((EuclideanSpace.basisFun (Fin 1) ℝ).orthonormal.1 0).le
  · rw [Finset.coe_singleton, Set.range_unique]
    rfl

theorem latticePacking_hypotheses_integers :
    (0 : ℝ) ≤ 0 ∧ (∀ x y : ℤ, |((x + y : ℤ) : ℝ)| ≤ |(x : ℝ)| + |(y : ℝ)|) ∧
      (∀ k x : ℤ, |((k • x : ℤ) : ℝ)| = |(k : ℝ)| * |(x : ℝ)|) ∧
      ∀ x : ℤ, x ≠ 0 → Real.exp (-0) ≤ |(x : ℝ)| := by
  refine ⟨le_rfl, fun x y ↦ ?_, fun k x ↦ by simp [abs_mul], fun x hx ↦ ?_⟩
  · push_cast
    exact abs_add_le _ _
  · rw [neg_zero, Real.exp_zero]
    have : (1 : ℤ) ≤ |x| := Int.one_le_abs hx
    exact_mod_cast this

end ExamplesRest

section ExamplesOneBlock

open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder

def gaussianLinePt :=
  oneBlockPt ((NumberField.RingOfIntegers.basis GaussianField).reindex (Fintype.equivFin _)) 1

def ratBasis : Module.Basis (Fin 1) ℤ (𝓞 ℚ) :=
  (Module.Basis.singleton (Fin 1) ℤ).map Rat.ringOfIntegersEquiv.symm.toAddEquiv.toIntLinearEquiv

theorem ratBasis_apply (m : Fin 1) : ratBasis m = 1 := by
  simp [ratBasis]

def pairEquiv : Fin 1 × Fin 1 ≃ Fin (0 + 1) := finProdFinEquiv.trans (finCongr (by norm_num))

def stdPhi : (HermitianBundle.standard ℚ 1).carrier ≃ₗ[𝓞 ℚ] (Fin 1 → 𝓞 ℚ) := LinearEquiv.refl _ _

theorem pointHeightDegree_hypotheses_example :
    (∀ σ : ℚ →+* ℂ, ((fun _ : ℚ →+* ℂ ↦ (1 : Matrix (Fin 1) (Fin 1) ℂ)) σ).PosDef) ∧
    (∀ σ : ℚ →+* ℂ, (fun _ ↦ (1 : Matrix (Fin 1) (Fin 1) ℂ)) (ComplexEmbedding.conjugate σ) =
      (1 : Matrix (Fin 1) (Fin 1) ℂ).map (starRingEnd ℂ)) ∧
    (∀ u, (HermLine.standard (fun _ : Unit ↦ 0)).deg u = 1) ∧
    (∀ (σ : ℚ →+* ℂ) (w : Fin 1 → ℂ), w ≠ 0 →
      (HermLine.standard (fun _ : Unit ↦ 0)).metric
          (fun _ t ↦ σ (ratBasis (pairEquiv.symm t).1 : ℚ) *
            w (pairEquiv.symm t).2) =
        hermNorm 1 w) ∧
    (∀ (σ' : ℚ →+* ℂ) (x y : (HermitianBundle.standard ℚ 1).carrier),
      ((HermitianBundle.standard ℚ 1).metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 ℚ] x)
          ((1 : ComplexAt σ') ⊗ₜ[𝓞 ℚ] y) =
        star (fun j ↦ σ' (stdPhi x j : ℚ)) ⬝ᵥ
          ((1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ fun j ↦ σ' (stdPhi y j : ℚ))) ∧
    (fun _ ↦ (1 : 𝓞 ℚ) : Fin 1 → 𝓞 ℚ) ≠ 0 := by
  refine ⟨fun _ ↦ Matrix.PosDef.one, fun _ ↦ by simp, fun _ ↦ rfl, ?_, ?_, ?_⟩
  · intro σ w _
    change ∏ k : Unit, l2Norm _ = _
    rw [Fintype.prod_unique]
    generalize hp : (pairEquiv.symm 0).2 = t
    rw [Fin.fin_one_eq_zero t] at hp
    simp [l2Norm, hermNorm, ratBasis_apply, dotProduct, Complex.conj_mul', hp]
    rw [← Complex.ofReal_pow, Complex.ofReal_re, Real.sqrt_sq (norm_nonneg _)]
  · intro σ' x y
    refine (HermitianMetric.standard_inner (K := ℚ) (Fin 1) σ'
      ((1 : ComplexAt σ') ⊗ₜ[𝓞 ℚ] (x : Fin 1 → 𝓞 ℚ))
      ((1 : ComplexAt σ') ⊗ₜ[𝓞 ℚ] (y : Fin 1 → 𝓞 ℚ))).trans ?_
    show ∑ i : Fin 1, starRingEnd ℂ (σ' ((x : Fin 1 → 𝓞 ℚ) i : ℚ) * (ofComplex σ').symm 1) *
        (σ' ((y : Fin 1 → 𝓞 ℚ) i : ℚ) * (ofComplex σ').symm 1) = _
    simp [dotProduct, stdPhi, mul_comm]
    rfl
  · intro h
    have := congrFun h 0
    exact one_ne_zero this

end ExamplesOneBlock

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
