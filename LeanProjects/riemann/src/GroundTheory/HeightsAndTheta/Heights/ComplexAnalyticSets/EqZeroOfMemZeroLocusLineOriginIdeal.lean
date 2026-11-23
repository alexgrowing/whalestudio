import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerSectionBasic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff ENNReal

noncomputable section

variable {n d e : ℕ}

def zeroLocus {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : Set (Fin n → ℂ) :=
  {x | ∀ q ∈ J, eval x q = 0}

structure IsAffVariety (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) : Prop where
  isPrime : J.IsPrime
  dim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d

def linVal (u x : Fin n → ℂ) : ℂ := ∑ j, u j * x j

def IsFiniteProj (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) : Prop :=
  (aeval (R := ℂ) fun i : Fin d => Ideal.Quotient.mk J (linForm (A i))).Finite

def IsGraphChart (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (x : Fin n → ℂ) (σ : (Fin d → ℂ) → (Fin n → ℂ)) : Prop :=
  x ∈ zeroLocus J ∧ ∃ (U : Set (Fin n → ℂ)) (V : Set (Fin d → ℂ)), IsOpen U ∧ x ∈ U ∧ IsOpen V ∧
    AnalyticOnNhd ℂ σ V ∧ Set.BijOn σ V (zeroLocus J ∩ U) ∧ ∀ w ∈ V, A *ᵥ σ w = w

open Classical in

def sheetDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) : ℝ :=
  if h : ∃ σ, IsGraphChart J A x σ then
    ReciprocityTheory.AnForm.maDens (fun i => φ i ∘ h.choose) (A *ᵥ x)
  else 0

def fibre (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (w : Fin d → ℂ) :
    Set (Fin n → ℂ) :=
  {x | x ∈ zeroLocus J ∧ A *ᵥ x = w}

def projInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) : ℝ :=
  ∫ w : Fin d → ℂ, ∑ᶠ x ∈ fibre J A w, g x * sheetDens J A φ x

def ProjIntegrable (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) : Prop :=
  Integrable fun w : Fin d → ℂ => ∑ᶠ x ∈ fibre J A w, |g x * sheetDens J A φ x|

open Classical in

def varIntegral (J : Ideal (MvPolynomial (Fin n) ℂ)) (g : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : ℝ :=
  if h : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProj J A then projInt J h.choose g φ else 0

def withFirst (f : (Fin n → ℂ) → ℝ) (ψ : Fin e → (Fin n → ℂ) → ℝ) :
    Fin (e + 1) → (Fin n → ℂ) → ℝ :=
  Fin.cons (α := fun _ => (Fin n → ℂ) → ℝ) f ψ

def SmoothNear (Z : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) : Prop :=
  ∃ U, IsOpen U ∧ Z ⊆ U ∧ ContDiffOn ℝ ∞ f U

def eucNorm (v : Fin n → ℂ) : ℝ := √(∑ j, ‖v j‖ ^ 2)

def zarTangent (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) : Set (Fin n → ℂ) :=
  {v | ∀ q ∈ J, ∑ j, eval x (pderiv j q) * v j = 0}

def restrGradNorm (χ : (Fin n → ℂ) → ℝ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) : ℝ :=
  sSup ((fun v => |fderiv ℝ χ x v|) '' {v | v ∈ zarTangent J x ∧ eucNorm v ≤ 1})

def restrLeviNorm (χ : (Fin n → ℂ) → ℝ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) : ℝ :=
  sSup ((fun v => |ReciprocityTheory.AnForm.levi χ x v|) '' {v | v ∈ zarTangent J x ∧ eucNorm v ≤ 1})

def zLIntegral (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (B : Set (Fin n → ℂ))
    (g : (Fin n → ℂ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ y in {y : EuclideanSpace ℂ (Fin n) | (fun i => y i) ∈ zeroLocus J ∩ B},
    g (fun i => y i) ∂(Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ))

structure GoodPosition (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ)
    (π : Matrix (Fin e) (Fin n) ℂ) (U : Set (Fin n → ℂ)) (V : Set (Fin e → ℂ)) (ρ : ℝ) (N : ℕ) :
    Prop where
  isOpen_U : IsOpen U
  isBounded_U : Bornology.IsBounded U
  mem_U : p ∈ U
  mem_W : p ∈ zeroLocus W
  isOpen_V : IsOpen V
  mem_V : π *ᵥ p ∈ V
  pos : 0 < ρ
  zeros : ∀ q ∈ closure U, q ∈ zeroLocus J → linVal u q = 0 → π *ᵥ q ∈ V → q ∈ U ∧ q ∈ zeroLocus W
  injOn : ∀ q ∈ U ∩ zeroLocus W, ∀ q' ∈ U ∩ zeroLocus W, π *ᵥ q = π *ᵥ q' → q = q'
  count : ∀ w ∈ V, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ →
    {x | x ∈ U ∩ zeroLocus J ∧ π *ᵥ x = w ∧ linVal u x = t}.encard = N

def fsPot (h : HermNorm n) (y : Fin n → ℂ) : ℝ := Real.log (h.dualNorm y ^ 2)

def planeIdeal (n e : ℕ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span {q | ∃ j : Fin n, e + 1 ≤ (j : ℕ) ∧ q = X j}

def ProjectionIndependence.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    IsAffVariety J d → IsFiniteProj J A → IsFiniteProj J A' → Measurable f →
    (∀ i, SmoothNear (zeroLocus J) (φ i)) →
      projInt J A f φ = projInt J A' f φ

def VarIntegralFlat.Statement : Prop :=
  ∀ (d : ℕ) (f : (Fin d → ℂ) → ℝ) (φ : Fin d → (Fin d → ℂ) → ℝ), Measurable f →
    (∀ i, ContDiff ℝ ∞ (φ i)) →
      varIntegral (⊥ : Ideal (MvPolynomial (Fin d) ℂ)) f φ =
        ∫ x : Fin d → ℂ, f x * ReciprocityTheory.AnForm.maDens φ x

def CutOff.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (P : Ideal (MvPolynomial (Fin d) ℂ)), IsAffVariety J d → IsFiniteProj J A → P ≠ ⊥ →
    ∃ χ : ℝ → (Fin n → ℂ) → ℝ,
      (∀ ε, ContDiff ℝ ∞ (χ ε)) ∧ (∀ ε x, 0 ≤ χ ε x ∧ χ ε x ≤ 1) ∧
      (∀ ε, 0 < ε → ∃ U : Set (Fin n → ℂ), IsOpen U ∧
        {x | x ∈ zeroLocus J ∧ A *ᵥ x ∈ zeroLocus P} ⊆ U ∧ ∀ x ∈ U ∩ zeroLocus J, χ ε x = 0) ∧
      (∀ x ∈ zeroLocus J, A *ᵥ x ∉ zeroLocus P → Tendsto (fun ε => χ ε x) (𝓝[>] 0) (𝓝 1)) ∧
      ∀ B : Set (Fin n → ℂ), Bornology.IsBounded B →
        Tendsto (fun ε => zLIntegral J d B fun x => ENNReal.ofReal (restrGradNorm (χ ε) J x ^ 2))
            (𝓝[>] 0) (𝓝 0) ∧
          Tendsto (fun ε => zLIntegral J d B fun x => ENNReal.ofReal (restrLeviNorm (χ ε) J x))
            (𝓝[>] 0) (𝓝 0)

def StokesOnVariety.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
    (ψ : Fin e → (Fin n → ℂ) → ℝ), IsAffVariety J (e + 1) →
    SmoothNear (zeroLocus J) f → SmoothNear (zeroLocus J) g → (HasCompactSupport f ∨ HasCompactSupport g) →
    (∀ i, SmoothNear (zeroLocus J) (ψ i)) →
      varIntegral J f (withFirst g ψ) = varIntegral J g (withFirst f ψ)

def LogIntegrable.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (u : Fin n → ℂ) (B : Set (Fin n → ℂ)),
    IsAffVariety J d → IsFiniteProj J A → (∀ i, SmoothNear (zeroLocus J) (φ i)) →
    linForm u ∉ J → Bornology.IsBounded B →
      ProjIntegrable J A (B.indicator fun x => Real.log ‖linVal u x‖) φ

def LocalOrder.Statement : Prop :=
  ∀ (n e : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ)
    (π : Matrix (Fin e) (Fin n) ℂ) (U : Set (Fin n → ℂ)) (V : Set (Fin e → ℂ)) (ρ : ℝ) (N : ℕ),
    IsAffVariety J (e + 1) → linForm u ∉ J → W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
    GoodPosition J W u p π U V ρ N →
      localMult (J ⊔ Ideal.span {linForm u}) W = N

def PoincareLelong.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ)
    (ψ : Fin e → (Fin n → ℂ) → ℝ), IsAffVariety J (e + 1) → linForm u ∉ J →
    ContDiff ℝ ∞ f → HasCompactSupport f → (∀ i, SmoothNear (zeroLocus J) (ψ i)) →
      varIntegral J (fun x => Real.log ‖linVal u x‖) (withFirst f ψ) =
        ∑ᶠ W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes,
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varIntegral W f ψ

def ConeToProjective.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (g : (Fin n → ℂ) → ℝ), IsAffVariety J (e + 1) → IsHomogIdeal J → linForm ℓ ∉ J →
    Measurable g → (∀ c : ℂ, c ≠ 0 → ∀ y, g (c • y) = g y) →
      coneIntegral h J e g =
        ((2 : ℝ) ^ e)⁻¹ * varIntegral (J ⊔ Ideal.span {linForm ℓ - 1}) g (fun _ : Fin e => fsPot h)

def ConeSlicePlane.Statement : Prop :=
  ∀ (n e : ℕ) (hn : e + 1 ≤ n),
    coneIntegral (HermNorm.std n) (planeIdeal n e) e (fun _ => 1) = 1 ∧
      varIntegral (planeIdeal n e ⊔ Ideal.span {linForm (Pi.single (⟨0, by omega⟩ : Fin n) 1) - 1})
          (fun _ => (1 : ℝ)) (fun _ : Fin e => fsPot (HermNorm.std n)) = 2 ^ e

def GreenFromLelong.Statement : Prop :=
  PoincareLelong.Statement → ConeToProjective.Statement → GreenSymmetry.Statement

def MassFromLelong.Statement : Prop :=
  PoincareLelong.Statement → ConeToProjective.Statement → ConeIntegralMass.Statement

section Inhabitants

theorem mem_zeroLocus_bot {n : ℕ} (x : Fin n → ℂ) : x ∈ zeroLocus (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) := by
  intro q hq
  rw [Ideal.mem_bot] at hq
  simp [hq]

theorem isAffVariety_bot (n : ℕ) : IsAffVariety (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) n where
  isPrime := Ideal.isPrime_bot
  dim := by
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp

theorem linForm_one_line : linForm (fun _ : Fin 1 => (1 : ℂ)) = X 0 := by
  simp [linForm]

theorem isFiniteProj_one (n : ℕ) :
    IsFiniteProj (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hA : (aeval (R := ℂ) fun i : Fin n => Ideal.Quotient.mk (⊥ : Ideal (MvPolynomial (Fin n) ℂ))
      (linForm ((1 : Matrix (Fin n) (Fin n) ℂ) i))) = Ideal.Quotient.mkₐ ℂ ⊥ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [linForm, Matrix.one_apply]
  unfold IsFiniteProj
  rw [hA]
  exact AlgHom.Finite.of_surjective _ (Ideal.Quotient.mkₐ_surjective ℂ ⊥)

theorem contDiff_normSq_coord : ContDiff ℝ ∞ fun x : Fin 1 → ℂ => ‖x 0‖ ^ 2 :=
  (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ (0 : Fin 1))

theorem smoothNear_of_contDiff {n : ℕ} (Z : Set (Fin n → ℂ)) {f : (Fin n → ℂ) → ℝ}
    (hf : ContDiff ℝ ∞ f) : SmoothNear Z f :=
  ⟨Set.univ, isOpen_univ, Set.subset_univ _, hf.contDiffOn⟩

def lineBump : (Fin 1 → ℂ) → ℝ := fun x => (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℂ)) (x 0)

theorem contDiff_lineBump : ContDiff ℝ ∞ lineBump :=
  (ContDiffBump.contDiff _).comp (contDiff_apply ℝ ℂ (0 : Fin 1))

theorem hasCompactSupport_lineBump : HasCompactSupport lineBump :=
  (ContDiffBump.hasCompactSupport _).comp_homeomorph (Homeomorph.funUnique (Fin 1) ℂ)

theorem ProjectionIndependence.hypotheses_inhabited :
    IsAffVariety (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1 ∧
      IsFiniteProj (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) ∧
      Measurable lineBump ∧
      ∀ i : Fin 1, SmoothNear (zeroLocus (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)))
        ((fun _ x => ‖x 0‖ ^ 2 : Fin 1 → (Fin 1 → ℂ) → ℝ) i) :=
  ⟨isAffVariety_bot 1, isFiniteProj_one 1, contDiff_lineBump.continuous.measurable,
    fun _ => smoothNear_of_contDiff _ contDiff_normSq_coord⟩

theorem VarIntegralFlat.hypotheses_inhabited :
    Measurable lineBump ∧ ∀ i : Fin 1, ContDiff ℝ ∞ ((fun _ x => ‖x 0‖ ^ 2 : Fin 1 → (Fin 1 → ℂ) → ℝ) i) :=
  ⟨contDiff_lineBump.continuous.measurable, fun _ => contDiff_normSq_coord⟩

theorem CutOff.hypotheses_inhabited :
    IsAffVariety (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1 ∧
      IsFiniteProj (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) ∧
      Ideal.span {(X 0 : MvPolynomial (Fin 1) ℂ)} ≠ ⊥ :=
  ⟨isAffVariety_bot 1, isFiniteProj_one 1, by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact X_ne_zero 0⟩

theorem StokesOnVariety.hypotheses_inhabited :
    IsAffVariety (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (0 + 1) ∧
      SmoothNear (zeroLocus (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) lineBump ∧
      SmoothNear (zeroLocus (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) (fun x => ‖x 0‖ ^ 2) ∧
      (HasCompactSupport lineBump ∨ HasCompactSupport (fun x : Fin 1 → ℂ => ‖x 0‖ ^ 2)) :=
  ⟨isAffVariety_bot 1, smoothNear_of_contDiff _ contDiff_lineBump,
    smoothNear_of_contDiff _ contDiff_normSq_coord, Or.inl hasCompactSupport_lineBump⟩

theorem LogIntegrable.hypotheses_inhabited :
    IsAffVariety (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1 ∧
      IsFiniteProj (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) ∧
      (∀ i : Fin 1, SmoothNear (zeroLocus (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)))
        ((fun _ x => ‖x 0‖ ^ 2 : Fin 1 → (Fin 1 → ℂ) → ℝ) i)) ∧
      linForm (fun _ : Fin 1 => (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      Bornology.IsBounded (Metric.ball (0 : Fin 1 → ℂ) 1) :=
  ⟨isAffVariety_bot 1, isFiniteProj_one 1, fun _ => smoothNear_of_contDiff _ contDiff_normSq_coord,
    linForm_one_not_mem_point ℂ, Metric.isBounded_ball⟩

theorem PoincareLelong.hypotheses_inhabited :
    IsAffVariety (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (0 + 1) ∧
      linForm (fun _ : Fin 1 => (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      ContDiff ℝ ∞ lineBump ∧ HasCompactSupport lineBump :=
  ⟨isAffVariety_bot 1, linForm_one_not_mem_point ℂ, contDiff_lineBump, hasCompactSupport_lineBump⟩

def lineOriginIdeal : Ideal (MvPolynomial (Fin 1) ℂ) := RingHom.ker (eval (0 : Fin 1 → ℂ))

theorem lineOriginIdeal_le : lineOriginIdeal ≤ Ideal.span {(X 0 : MvPolynomial (Fin 1) ℂ)} := by
  intro q hq
  rw [lineOriginIdeal, RingHom.mem_ker, eval_zero] at hq
  have hs : Ideal.span {(X 0 : MvPolynomial (Fin 1) ℂ)} =
      Ideal.span (X '' {(0 : Fin 1)} : Set (MvPolynomial (Fin 1) ℂ)) := by
    rw [Set.image_singleton]
  rw [hs, mem_ideal_span_X_image]
  intro m hm
  refine ⟨0, rfl, fun hm0 => ?_⟩
  have hm' : m = 0 := Finsupp.ext fun i => by
    rw [Fin.fin_one_eq_zero i]
    simpa using hm0
  subst hm'
  exact (mem_support_iff.mp hm) (by rw [← constantCoeff_eq]; exact hq)

theorem X_mem_lineOriginIdeal : (X 0 : MvPolynomial (Fin 1) ℂ) ∈ lineOriginIdeal := by
  rw [lineOriginIdeal, RingHom.mem_ker]
  simp

theorem lineOriginIdeal_mem_minimalPrimes :
    lineOriginIdeal ∈ ((⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ⊔
      Ideal.span {linForm (fun _ : Fin 1 => (1 : ℂ))}).minimalPrimes := by
  rw [linForm_one_line, bot_sup_eq]
  refine ⟨⟨RingHom.ker_isPrime _, ?_⟩, ?_⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact X_mem_lineOriginIdeal
  · intro P hP _
    exact lineOriginIdeal_le.trans hP.2

theorem eq_zero_of_mem_zeroLocus_lineOriginIdeal {q : Fin 1 → ℂ} (hq : q ∈ zeroLocus lineOriginIdeal) : q = 0 := by
  have h := hq _ X_mem_lineOriginIdeal
  rw [eval_X] at h
  funext i
  rw [Fin.fin_one_eq_zero i]
  exact h

theorem zero_mem_zeroLocus_lineOriginIdeal : (0 : Fin 1 → ℂ) ∈ zeroLocus lineOriginIdeal := by
  intro q hq
  exact hq

theorem linVal_one_line (x : Fin 1 → ℂ) : linVal (fun _ => (1 : ℂ)) x = x 0 := by
  simp [linVal]

theorem goodPosition_line :
    GoodPosition (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) lineOriginIdeal (fun _ => 1) 0
      (0 : Matrix (Fin 0) (Fin 1) ℂ) (Metric.ball 0 1) Set.univ 1 1 where
  isOpen_U := Metric.isOpen_ball
  isBounded_U := Metric.isBounded_ball
  mem_U := Metric.mem_ball_self one_pos
  mem_W := zero_mem_zeroLocus_lineOriginIdeal
  isOpen_V := isOpen_univ
  mem_V := Set.mem_univ _
  pos := one_pos
  zeros q _ _ hq _ := by
    rw [linVal_one_line] at hq
    have hq0 : q = 0 := by
      funext i
      rw [Fin.fin_one_eq_zero i]
      exact hq
    subst hq0
    exact ⟨Metric.mem_ball_self one_pos, zero_mem_zeroLocus_lineOriginIdeal⟩
  injOn q hq q' hq' _ := by
    rw [eq_zero_of_mem_zeroLocus_lineOriginIdeal hq.2, eq_zero_of_mem_zeroLocus_lineOriginIdeal hq'.2]
  count w _ t _ ht := by
    have hset : {x | x ∈ Metric.ball (0 : Fin 1 → ℂ) 1 ∩ zeroLocus (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
        (0 : Matrix (Fin 0) (Fin 1) ℂ) *ᵥ x = w ∧ linVal (fun _ => (1 : ℂ)) x = t} =
        {fun _ => t} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_inter_iff, linVal_one_line]
      constructor
      · rintro ⟨-, -, hx⟩
        funext i
        rw [Fin.fin_one_eq_zero i]
        exact hx
      · rintro rfl
        refine ⟨⟨?_, mem_zeroLocus_bot _⟩, Subsingleton.elim _ _, rfl⟩
        rw [Metric.mem_ball, dist_zero_right, pi_norm_const]
        exact ht
    rw [hset, Set.encard_singleton]
    rfl

theorem LocalOrder.hypotheses_inhabited :
    IsAffVariety (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (0 + 1) ∧
      linForm (fun _ : Fin 1 => (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      lineOriginIdeal ∈ ((⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ⊔
        Ideal.span {linForm (fun _ : Fin 1 => (1 : ℂ))}).minimalPrimes ∧
      GoodPosition (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) lineOriginIdeal (fun _ => 1) 0
        (0 : Matrix (Fin 0) (Fin 1) ℂ) (Metric.ball 0 1) Set.univ 1 1 :=
  ⟨isAffVariety_bot 1, linForm_one_not_mem_point ℂ, lineOriginIdeal_mem_minimalPrimes, goodPosition_line⟩

theorem ConeToProjective.hypotheses_inhabited :
    IsAffVariety (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (1 + 1) ∧
      IsHomogIdeal (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      linForm (Pi.single (0 : Fin 2) (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      Measurable (fun _ : Fin 2 → ℂ => (1 : ℝ)) ∧
      (∀ c : ℂ, c ≠ 0 → ∀ y : Fin 2 → ℂ, (fun _ : Fin 2 → ℂ => (1 : ℝ)) (c • y) =
        (fun _ : Fin 2 → ℂ => (1 : ℝ)) y) := by
  refine ⟨isAffVariety_bot 2, ?_, ?_, measurable_const, fun _ _ _ => rfl⟩
  · intro f hf k
    rw [Ideal.mem_bot] at hf ⊢
    simp [hf]
  · rw [Ideal.mem_bot]
    simp [linForm, Pi.single_apply, X_ne_zero]

end Inhabitants

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
