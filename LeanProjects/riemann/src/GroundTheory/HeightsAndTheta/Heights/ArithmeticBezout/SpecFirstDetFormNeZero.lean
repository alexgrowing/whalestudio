import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LatticePointLogCount
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix

section Objects

variable {n : ℕ}

def finIdeal (P : Ideal (MRing (PBlk n))) : Ideal (MvPolynomial (Fin n) ℤ) :=
  P.comap (rename fun i : Fin n => (⟨(), i⟩ : Σ _ : Unit, PBlk n ()))

def linForm (u : Fin n → ℤ) : MRing (PBlk n) :=
  ∑ i, C (u i) * Xc n i

def pointMetric (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) : ConeMetric ℂ (Fin n) where
  ρ z := ‖WithLp.toLp 2 (S *ᵥ z)‖
  pos z hz := by
    have h : S *ᵥ z ≠ 0 := fun h0 =>
      hz (Matrix.mulVec_injective_iff_isUnit.mpr hS (by rw [h0, Matrix.mulVec_zero]))
    exact norm_pos_iff.mpr (by simpa using h)
  smul c z := by rw [Matrix.mulVec_smul, WithLp.toLp_smul, norm_smul]

def formNorm (S : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) : ℝ :=
  ‖WithLp.toLp 2 ((S⁻¹)ᵀ *ᵥ u)‖

def hermLine (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) : HermLine (PBlk n) :=
  HermLine.ofMetrics (fun _ => pointMetric S hS) 1

def logFormNorm (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (u : Fin n → ℂ)
    (z : (Σ _ : Unit, PBlk n ()) → ℂ) : ℝ :=
  Real.log (‖∑ i, u i * z ⟨(), i⟩‖ / (hermLine S hS).h z)

def normSq (u : Fin n → ℂ) : ℝ :=
  ∑ i, ‖u i‖ ^ 2

variable (n) in

def sphereLaw : Measure (Fin n → ℂ) :=
  ((volume {u : Fin n → ℂ | normSq u ≤ 1})⁻¹ • volume.restrict {u : Fin n → ℂ | normSq u ≤ 1}).map
    fun u => (Real.sqrt (normSq u))⁻¹ • u

def formSphereLaw (S : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : Measure (Fin k × Fin n → ℂ) :=
  (Measure.pi fun _ : Fin k => sphereLaw n).map fun v p => (Sᵀ *ᵥ v p.1) p.2

def chowMean (S : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (g : MvPolynomial (Fin k × Fin n) ℂ) : ℝ :=
  ∫ u, Real.log ‖eval u g‖ ∂formSphereLaw S k

def chowHeight (S : Matrix (Fin n) (Fin n) ℂ) {e : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ)
    (δ : ℕ) : ℝ :=
  chowHt (fun _ : NumberField.InfinitePlace ℚ => formSphereLaw S (e + 1)) f δ

def finGaussLog {σ : Type*} (f : MvPolynomial σ ℚ) : ℝ :=
  ∑ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ), Real.log (coeffGaussNorm v.1 f)

def IsPrimitive {σ : Type*} (f : MvPolynomial σ ℤ) : Prop :=
  ∀ c : ℤ, (∀ m, c ∣ f.coeff m) → IsUnit c

def IsIntChowForm (P : Ideal (MRing (PBlk n))) (e δ : ℕ)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℤ) : Prop :=
  IsPrimitive f ∧ IsChowForm (Int.castRingHom ℂ) (finIdeal P) e δ (map (Int.castRingHom ℂ) f)

open Classical in

def chowFormZ (P : Ideal (MRing (PBlk n))) (e : ℕ) : MvPolynomial (Fin (e + 1) × Fin n) ℤ :=
  if h : ∃ f : MvPolynomial (Fin (e + 1) × Fin n) ℤ, ∃ δ, IsIntChowForm P e δ f then h.choose else 0

def cycleChowForm {ι R σ : Type*} [CommSemiring R] (Z : ι →₀ ℕ) (f : ι → MvPolynomial σ R) :
    MvPolynomial σ R :=
  Z.prod fun W m => f W ^ m

def specFirst {R : Type*} [CommRing R] {e : ℕ} (u : Fin n → R) :
    MvPolynomial (Fin (e + 1) × Fin n) R →ₐ[R] MvPolynomial (Fin e × Fin n) R :=
  aeval fun p => Fin.cases (motive := fun _ => MvPolynomial (Fin e × Fin n) R) (C (u p.2))
    (fun k => X (k, p.2)) p.1

open Classical in

def vertPart (P : Ideal (MRing (PBlk n))) (e : ℕ) (s : MRing (PBlk n)) : ℝ :=
  ∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
    (if IsHorizontal W then 0 else (geoNum e W (fun _ _ => 1) : ℝ) * Real.log (charOf W))

def detForm (R : Type*) [CommRing R] : MvPolynomial (Fin (1 + 1) × Fin 2) R :=
  X (0, 0) * X (1, 1) - X (0, 1) * X (1, 0)

end Objects

def SphereMeanLinear.Statement : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℂ), normSq p = 1 →
    ∫ z, Real.log ‖∑ i, z i * p i‖ ∂sphereLaw n = -(harmonic (n - 1) : ℝ) / 2

def ChowFormTransposition.Statement : Prop :=
  ∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (i j : Fin (e + 1)),
    IsArithVar P (e + 1) → IsChowForm (Int.castRingHom ℂ) (finIdeal P) e δ f →
      ∃ c : ℂ, c ^ 2 = 1 ∧ rename (fun p : Fin (e + 1) × Fin n => (Equiv.swap i j p.1, p.2)) f = C c * f

open Classical in

def ChowFormSection.Statement : Prop :=
  ∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℤ)
    (u : Fin n → ℤ),
    IsArithVar P (e + 1 + 1) → IsIntChowForm P (e + 1) δ f → linForm u ∉ P →
      ∃ ε : ℤ, IsUnit ε ∧ specFirst u f =
        C ε * cycleChowForm (divCycle P (linForm u)) fun W =>
          if IsHorizontal W then chowFormZ W e
          else C ((charOf W : ℤ) ^ (geoNum (e + 1) W fun _ _ => 1).toNat)

def ChowFormSectionPoint.Statement : Prop :=
  ∀ (n δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (0 + 1) × Fin n) ℤ) (u : Fin n → ℤ),
    IsArithVar P (0 + 1) → IsIntChowForm P 0 δ f → linForm u ∉ P →
      ∃ ε : ℤ, IsUnit ε ∧ specFirst u f =
        C ε * cycleChowForm (divCycle P (linForm u)) fun W =>
          C ((charOf W : ℤ) ^ (geoNum 0 W fun _ _ => 1).toNat)

def VerticalPartGauss.Statement : Prop :=
  ∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ)
    (u : Fin n → ℤ),
    IsArithVar P (e + 1) → IsChowForm (Int.castRingHom ℂ) (finIdeal P) e δ (map (Rat.castHom ℂ) f) →
      linForm u ∉ P →
        vertPart P e (linForm u) = finGaussLog f - finGaussLog (specFirst (fun i => (u i : ℚ)) f)

def LogNormIntegral.Statement : Prop :=
  ∀ (n e δ : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsArithVar P (e + 1) → IsChowForm (Int.castRingHom ℂ) (finIdeal P) e δ f → specFirst u f ≠ 0 →
      chowMean S e (specFirst u f) - chowMean S (e + 1) f - δ * (harmonic (n - 1) : ℝ) / 2 =
        ptsIntegral P (pot fun _ : Fin e => hermLine S hS) (logFormNorm S hS u)

def IntersectionEqChowHeight.Statement : Prop :=
  ∀ (n e δ : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (I : Ideal (MRing (PBlk n)) → (k : ℕ) → (Fin k → HermLine (PBlk n)) → ℝ)
    (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ),
    IsIntersectionFamily I → IsArithVar P (e + 1) →
      IsChowForm (Int.castRingHom ℂ) (finIdeal P) e δ (map (Rat.castHom ℂ) f) →
        I P (e + 1) (fun _ => hermLine S hS) = chowHeight S f δ

def ChowHeightLowerBound.Statement : Prop :=
  ∀ (n e δ : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (Λ : ℝ) (P : Ideal (MRing (PBlk n)))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ),
    IsUnit S → IsArithVar P (e + 1) →
      IsChowForm (Int.castRingHom ℂ) (finIdeal P) e δ (map (Rat.castHom ℂ) f) →
      (∃ G : Set (Fin n → ℤ), Submodule.span ℤ G = ⊤ ∧ ∀ u ∈ G, formNorm S (fun i => (u i : ℂ)) ≤ Λ) →
        -((e + 1 : ℝ) * δ * Real.log Λ) ≤ chowHeight S f δ

def GaussNormMul.Statement : Prop :=
  ∀ (K : Type) [Field K] (σ : Type) (v : AbsoluteValue K ℝ), IsNonarchimedean v →
    ∀ f g : MvPolynomial σ K, coeffGaussNorm v (f * g) = coeffGaussNorm v f * coeffGaussNorm v g

def LogMeanMul.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ), IsUnit S →
    ∀ f g : MvPolynomial (Fin (e + 1) × Fin n) ℂ, f ≠ 0 → g ≠ 0 →
      logMean (formSphereLaw S (e + 1)) (f * g) =
        logMean (formSphereLaw S (e + 1)) f + logMean (formSphereLaw S (e + 1)) g

def ChowHeightCycle.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ)
    (S : NumberField.InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ w, IsUnit (S w)) →
    ∀ (ι : Type) (Z : ι →₀ ℕ) (f : ι → MvPolynomial (Fin (e + 1) × Fin n) K) (δ : ι → ℕ),
      (∀ i ∈ Z.support, f i ≠ 0) →
        chowHt (fun w => formSphereLaw (S w) (e + 1)) (cycleChowForm Z f) (Z.sum fun i m => m * δ i) =
          Z.sum fun i m => (m : ℝ) * chowHt (fun w => formSphereLaw (S w) (e + 1)) (f i) (δ i)

theorem finIdeal_bot (n : ℕ) : finIdeal (⊥ : Ideal (MRing (PBlk n))) = ⊥ := by
  refine Ideal.comap_bot_of_injective _ (rename_injective _ fun a b h => ?_)
  simpa using h

theorem mem_conePts_bot {n : ℕ} (z : Fin n → ℂ) :
    z ∈ conePts (Int.castRingHom ℂ) (⊥ : Ideal (MvPolynomial (Fin n) ℤ)) ↔ z ≠ 0 := by
  simp [conePts]

theorem isMultihomog_detForm (R : Type*) [CommRing R] [Nontrivial R] :
    IsMultihomog (detForm R) 1 := by
  classical
  intro m hm k
  have hX : ∀ a b : Fin (1 + 1) × Fin 2, (X a * X b : MvPolynomial (Fin (1 + 1) × Fin 2) R) =
      monomial (Finsupp.single a 1 + Finsupp.single b 1) 1 := by
    intro a b
    simp [X, monomial_mul]
  rcases Finset.mem_union.mp (support_sub _ _ _ hm) with h | h <;>
  · rw [hX] at h
    have h' := support_monomial_subset h
    rw [Finset.mem_singleton] at h'
    subst h'
    fin_cases k <;> simp [Finsupp.single_apply]

theorem detForm_ne_zero : detForm ℂ ≠ 0 := by
  intro h
  have h' := congrArg (eval fun p : Fin (1 + 1) × Fin 2 => if p.1.val = p.2.val then (1 : ℂ) else 0) h
  simp [detForm] at h'

theorem degreeOf_detForm_le (x : Fin (1 + 1) × Fin 2) : degreeOf x (detForm ℂ) ≤ 1 := by
  classical
  refine (degreeOf_sub_le _ _ _).trans (max_le ?_ ?_) <;>
  refine (degreeOf_mul_le _ _ _).trans ?_ <;>
  simp only [degreeOf_X] <;> fin_cases x <;> simp

theorem squarefree_detForm : Squarefree (detForm ℂ) := by
  rintro a ⟨b, hb⟩
  have ha : a ≠ 0 := by
    rintro rfl
    exact detForm_ne_zero (by simpa using hb)
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact detForm_ne_zero (by simpa using hb)
  have hdeg : ∀ x, degreeOf x a = 0 := by
    intro x
    have h1 := degreeOf_detForm_le x
    rw [hb, degreeOf_mul_eq (mul_ne_zero ha ha) hb0, degreeOf_mul_eq ha ha] at h1
    omega
  have hC : a = C (a.coeff 0) := by
    ext m
    rw [coeff_C]
    split_ifs with hm
    · rw [← hm]
    · by_contra hne
      apply hm
      ext x
      have h2 := monomial_le_degreeOf x (mem_support_iff.mpr hne)
      rw [hdeg x] at h2
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
  have hc : a.coeff 0 ≠ 0 := fun h0 => ha (by rw [hC, h0, map_zero])
  rw [hC]
  exact (isUnit_iff_ne_zero.mpr hc).map C

theorem isChowForm_detForm :
    IsChowForm (Int.castRingHom ℂ) (finIdeal (⊥ : Ideal (MRing (PBlk 2)))) 1 1 (detForm ℂ) := by
  refine ⟨isMultihomog_detForm ℂ, squarefree_detForm, fun u => ?_⟩
  rw [finIdeal_bot]
  have key := Matrix.exists_mulVec_eq_zero_iff (M := (Matrix.of u : Matrix (Fin 2) (Fin 2) ℂ))
  rw [Matrix.det_fin_two] at key
  simp only [detForm, map_sub, map_mul, eval_X]
  constructor
  · intro h
    obtain ⟨z, hz, hz0⟩ := key.mpr (by simpa using h)
    exact ⟨z, (mem_conePts_bot z).mpr hz, fun j => by
      simpa [Matrix.mulVec, dotProduct] using congrFun hz0 j⟩
  · rintro ⟨z, hz, hj⟩
    have h := key.mp ⟨z, (mem_conePts_bot z).mp hz, funext fun j => by
      simpa [Matrix.mulVec, dotProduct] using hj j⟩
    simpa using h

theorem map_detForm_int : map (Int.castRingHom ℂ) (detForm ℤ) = detForm ℂ := by
  simp [detForm]

theorem map_detForm_rat : map (Rat.castHom ℂ) (detForm ℚ) = detForm ℂ := by
  simp [detForm]

theorem isPrimitive_detForm : IsPrimitive (detForm ℤ) := by
  classical
  intro c hc
  have h := hc (Finsupp.single (0, 0) 1 + Finsupp.single (1, 1) 1)
  have hne : (Finsupp.single ((0 : Fin (1 + 1)), (1 : Fin 2)) 1 + Finsupp.single (1, 0) 1 :
      Fin (1 + 1) × Fin 2 →₀ ℕ) ≠ Finsupp.single (0, 0) 1 + Finsupp.single (1, 1) 1 := by
    intro h
    have h' := DFunLike.congr_fun h (0, 1)
    simp at h'
  have h1 : (detForm ℤ).coeff (Finsupp.single (0, 0) 1 + Finsupp.single (1, 1) 1) = 1 := by
    simp [detForm, X, monomial_mul, coeff_monomial, hne]
  rw [h1] at h
  exact isUnit_of_dvd_one h

theorem isIntChowForm_detForm : IsIntChowForm (⊥ : Ideal (MRing (PBlk 2))) 1 1 (detForm ℤ) :=
  ⟨isPrimitive_detForm, by rw [map_detForm_int]; exact isChowForm_detForm⟩

theorem linForm_ne_zero : linForm (![1, 0] : Fin 2 → ℤ) ∉ (⊥ : Ideal (MRing (PBlk 2))) := by
  rw [Submodule.mem_bot]
  simp [linForm, Fin.sum_univ_two, Xc, X_ne_zero]

theorem specFirst_detForm : specFirst (e := 1) (![1, 0] : Fin 2 → ℂ) (detForm ℂ) = X (0, 1) := by
  simp [specFirst, detForm]
  rfl

theorem specFirst_detForm_ne_zero : specFirst (e := 1) (![1, 0] : Fin 2 → ℂ) (detForm ℂ) ≠ 0 := by
  rw [specFirst_detForm]
  exact X_ne_zero _

theorem isArithVar_projLine' : IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (1 + 1) :=
  GroundTheory.Heights₂.Heights.Inter.isArithVar_projLine

theorem SphereMeanLinear.hyps_inhabited : normSq (![1, 0] : Fin 2 → ℂ) = 1 := by
  simp [normSq, Fin.sum_univ_two]

theorem ChowFormTransposition.hyps_inhabited :
    IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (1 + 1) ∧
      IsChowForm (Int.castRingHom ℂ) (finIdeal (⊥ : Ideal (MRing (PBlk 2)))) 1 1 (detForm ℂ) :=
  ⟨isArithVar_projLine', isChowForm_detForm⟩

theorem ChowFormSection.hyps_inhabited :
    IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (0 + 1 + 1) ∧
      IsIntChowForm (⊥ : Ideal (MRing (PBlk 2))) (0 + 1) 1 (detForm ℤ) ∧
        linForm (![1, 0] : Fin 2 → ℤ) ∉ (⊥ : Ideal (MRing (PBlk 2))) :=
  ⟨isArithVar_projLine', isIntChowForm_detForm, linForm_ne_zero⟩

theorem VerticalPartGauss.hyps_inhabited :
    IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (1 + 1) ∧
      IsChowForm (Int.castRingHom ℂ) (finIdeal (⊥ : Ideal (MRing (PBlk 2)))) 1 1
        (map (Rat.castHom ℂ) (detForm ℚ)) ∧
        linForm (![1, 0] : Fin 2 → ℤ) ∉ (⊥ : Ideal (MRing (PBlk 2))) :=
  ⟨isArithVar_projLine', by rw [map_detForm_rat]; exact isChowForm_detForm, linForm_ne_zero⟩

theorem LogNormIntegral.hyps_inhabited :
    IsUnit (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧ IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (1 + 1) ∧
      IsChowForm (Int.castRingHom ℂ) (finIdeal (⊥ : Ideal (MRing (PBlk 2)))) 1 1 (detForm ℂ) ∧
        specFirst (e := 1) (![1, 0] : Fin 2 → ℂ) (detForm ℂ) ≠ 0 :=
  ⟨isUnit_one, isArithVar_projLine', isChowForm_detForm, specFirst_detForm_ne_zero⟩

theorem IntersectionEqChowHeight.hyps_inhabited :
    IsUnit (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧ IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (1 + 1) ∧
      IsChowForm (Int.castRingHom ℂ) (finIdeal (⊥ : Ideal (MRing (PBlk 2)))) 1 1
        (map (Rat.castHom ℂ) (detForm ℚ)) :=
  ⟨isUnit_one, isArithVar_projLine', by rw [map_detForm_rat]; exact isChowForm_detForm⟩

theorem span_basis_formNorm_le (n : ℕ) :
    ∃ G : Set (Fin n → ℤ), Submodule.span ℤ G = ⊤ ∧
      ∀ u ∈ G, formNorm (1 : Matrix (Fin n) (Fin n) ℂ) (fun i => (u i : ℂ)) ≤ 1 := by
  classical
  refine ⟨Set.range fun i => Pi.single i 1, ?_, ?_⟩
  · have h : (fun i : Fin n => (Pi.single i (1 : ℤ) : Fin n → ℤ)) = ⇑(Pi.basisFun ℤ (Fin n)) := by
      ext i j
      simp [Pi.basisFun_apply]
    rw [h]
    exact (Pi.basisFun ℤ (Fin n)).span_eq
  · rintro _ ⟨i, rfl⟩
    have hv : (fun j => ((Pi.single i (1 : ℤ) : Fin n → ℤ) j : ℂ)) = Pi.single i 1 := by
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [formNorm, hv, inv_one, transpose_one, one_mulVec, EuclideanSpace.norm_eq]
    simp [Pi.single_apply, apply_ite]

theorem ChowHeightLowerBound.hyps_inhabited :
    IsUnit (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧ IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (1 + 1) ∧
      IsChowForm (Int.castRingHom ℂ) (finIdeal (⊥ : Ideal (MRing (PBlk 2)))) 1 1
        (map (Rat.castHom ℂ) (detForm ℚ)) ∧
      ∃ G : Set (Fin 2 → ℤ), Submodule.span ℤ G = ⊤ ∧
        ∀ u ∈ G, formNorm (1 : Matrix (Fin 2) (Fin 2) ℂ) (fun i => (u i : ℂ)) ≤ 1 :=
  ⟨isUnit_one, isArithVar_projLine', by rw [map_detForm_rat]; exact isChowForm_detForm,
    span_basis_formNorm_le 2⟩

theorem GaussNormMul.hyps_inhabited : IsNonarchimedean (Rat.AbsoluteValue.padic 2) := by
  intro x y
  have h := padicNorm.nonarchimedean (p := 2) (q := x) (r := y)
  simp only [Rat.AbsoluteValue.padic_eq_padicNorm]
  exact_mod_cast h

theorem LogMeanMul.hyps_inhabited :
    IsUnit (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧ detForm ℂ ≠ 0 :=
  ⟨isUnit_one, detForm_ne_zero⟩

theorem ChowHeightCycle.hyps_inhabited :
    (∀ w : NumberField.InfinitePlace ℚ, IsUnit ((fun _ => 1 : NumberField.InfinitePlace ℚ →
      Matrix (Fin 2) (Fin 2) ℂ) w)) ∧
      ∀ i ∈ (Finsupp.single (0 : Fin 1) 2).support, (fun _ => detForm ℚ) i ≠ 0 := by
  refine ⟨fun _ => isUnit_one, fun _ _ => ?_⟩
  intro h
  apply detForm_ne_zero
  rw [← map_detForm_rat]
  simp only at h
  rw [h, map_zero]

theorem isArithVar_point : IsArithVar (⊥ : Ideal (MRing (PBlk 1))) (0 + 1) := by
  refine ⟨inferInstance, ⟨Ideal.isPrime_bot,
    ⟨∅, fun f hf => absurd hf (Set.notMem_empty f), Ideal.span_empty.symm⟩,
    fun _ => ⟨0, by rw [Submodule.mem_bot]; exact X_ne_zero _⟩⟩, ?_, ?_⟩
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

theorem isChowForm_point :
    IsChowForm (Int.castRingHom ℂ) (finIdeal (⊥ : Ideal (MRing (PBlk 1)))) 0 1
      (X (0, 0) : MvPolynomial (Fin (0 + 1) × Fin 1) ℂ) := by
  classical
  refine ⟨fun m hm k => ?_, (X_prime).squarefree, fun u => ?_⟩
  · rw [support_X, Finset.mem_singleton] at hm
    subst hm
    fin_cases k
    simp
  · rw [finIdeal_bot]
    simp only [eval_X]
    constructor
    · intro h
      refine ⟨1, (mem_conePts_bot _).mpr one_ne_zero, fun j => ?_⟩
      fin_cases j
      simpa using h
    · rintro ⟨z, hz, hj⟩
      have hz0 : z 0 ≠ 0 := by
        intro h0
        apply (mem_conePts_bot z).mp hz
        ext i
        fin_cases i
        simpa using h0
      have h := hj 0
      simp only [Fin.sum_univ_one] at h
      exact (mul_eq_zero.mp h).resolve_right hz0

theorem ChowFormSectionPoint.hyps_inhabited :
    IsArithVar (⊥ : Ideal (MRing (PBlk 1))) (0 + 1) ∧
      IsIntChowForm (⊥ : Ideal (MRing (PBlk 1))) 0 1 (X (0, 0)) ∧
        linForm (![1] : Fin 1 → ℤ) ∉ (⊥ : Ideal (MRing (PBlk 1))) := by
  classical
  refine ⟨isArithVar_point, ⟨fun c hc => ?_, by rw [map_X]; exact isChowForm_point⟩, ?_⟩
  · have h := hc (Finsupp.single (0, 0) 1)
    rw [coeff_X, if_pos rfl] at h
    exact isUnit_of_dvd_one h
  · rw [Submodule.mem_bot]
    simp [linForm, Xc, X_ne_zero]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout

end
