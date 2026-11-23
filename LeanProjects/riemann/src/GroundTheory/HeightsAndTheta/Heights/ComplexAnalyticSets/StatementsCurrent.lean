import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerSectionBasic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

variable {n d : ℕ}

def IsSheetAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ)
    (s : (Fin d → ℂ) → Fin n → ℂ) : Prop :=
  ∃ U : Set (Fin d → ℂ), IsOpen U ∧ A *ᵥ x ∈ U ∧ DifferentiableOn ℂ s U ∧ s (A *ᵥ x) = x ∧
    (∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
    ∃ V ∈ 𝓝 x, ∀ x' ∈ zeroSet J ∩ V, A *ᵥ x' ∈ U → x' = s (A *ᵥ x')

open Classical in

def sheetSum (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  ∑ᶠ (x : Fin n → ℂ) (_ : x ∈ fibre J A y),
    if h : ∃ s, IsSheetAt J A x s then F x h.choose else 0

def chartDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  sheetSum J A (fun x s => f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) y

def chartAbsDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  sheetSum J A (fun x s => |f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y|) y

def chartInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) : ℝ :=
  ∫ y, chartDens J A f φ y

open Classical in

def varInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : ℝ :=
  if h : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J A then chartInt J h.choose f φ else 0

def SmoothNear (S : Set (Fin n → ℂ)) (φ : (Fin n → ℂ) → ℝ) : Prop :=
  ∃ U : Set (Fin n → ℂ), IsOpen U ∧ S ⊆ U ∧ ContDiffOn ℝ ∞ φ U

def linEval (u x : Fin n → ℂ) : ℂ := ∑ j, u j * x j

def euclPot (x : Fin n → ℂ) : ℝ := ∑ j, ‖x j‖ ^ 2

def energyInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (B : Set (Fin n → ℂ)) (χ : (Fin n → ℂ) → ℝ) : ℝ :=
  chartInt J A (B.indicator fun _ => 1) (vecCons (fun x => χ x ^ 2 / 2) fun _ => euclPot) -
    chartInt J A (B.indicator χ) (vecCons χ fun _ => euclPot)

structure VarBranch (J : Ideal (MvPolynomial (Fin n) ℂ)) (k : ℕ) (p : Fin n → ℂ) where

  radius : ℝ
  radius_pos : 0 < radius

  toFun : (Fin k → ℂ) → Fin n → ℂ
  differentiableOn : DifferentiableOn ℂ toFun (Metric.ball 0 radius)
  injOn : Set.InjOn toFun (Metric.ball 0 radius)
  map_zero : toFun 0 = p
  mapsTo : Set.MapsTo toFun (Metric.ball 0 radius) (zeroSet J)

def VarBranch.image {J : Ideal (MvPolynomial (Fin n) ℂ)} {k : ℕ} {p : Fin n → ℂ}
    (b : VarBranch J k p) : Set (Fin n → ℂ) :=
  b.toFun '' Metric.ball 0 b.radius

def VarBranch.slice {J : Ideal (MvPolynomial (Fin n) ℂ)} {k : ℕ} {p : Fin n → ℂ}
    (b : VarBranch J (k + 1) p) : Set (Fin n → ℂ) :=
  b.toFun '' (Metric.ball 0 b.radius ∩ {t | t 0 = 0})

def VanishesToOrder {k : ℕ} (F : (Fin (k + 1) → ℂ) → ℂ) (r : ℝ) (m : ℕ) : Prop :=
  ∃ H : (Fin (k + 1) → ℂ) → ℂ, DifferentiableOn ℂ H (Metric.ball 0 r) ∧
    (∀ t ∈ Metric.ball 0 r, H t ≠ 0) ∧ ∀ t ∈ Metric.ball 0 r, F t = t 0 ^ m * H t

def IntegralIndep.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    IsFiniteProjection J A' → Measurable f →
    (∀ k, SmoothNear (zeroSet J) (φ k)) → Integrable (chartAbsDens J A f φ) →
      Integrable (chartAbsDens J A' f φ) ∧ chartInt J A f φ = chartInt J A' f φ

def PointIntegral.Statement : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ) (φ : Fin 0 → (Fin n → ℂ) → ℝ),
    varInt (RingHom.ker (MvPolynomial.eval p)) 0 f φ = f p

def LineSliceMass.Statement : Prop :=
  varInt (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ)) 1 (fun _ => 1)
    (fun _ x => Real.log ((HermNorm.std 2).dualNorm x)) = 1

def CutOff.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      ∃ χ : ℕ → (Fin n → ℂ) → ℝ,
        (∀ k, ContDiff ℝ ∞ (χ k)) ∧ (∀ k x, χ k x ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ k, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ {x | eval (A *ᵥ x) P = 0} ⊆ U ∧
          ∀ x ∈ U ∩ zeroSet J, χ k x = 0) ∧
        (∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → Tendsto (fun k => χ k x) atTop (𝓝 1)) ∧
        (∀ R : ℝ, Tendsto (fun k => energyInt J A (Metric.closedBall 0 R) (χ k)) atTop (𝓝 0)) ∧
        (∀ (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ), (∀ i, SmoothNear (zeroSet J) (φ i)) →
          Tendsto (fun k => ∫ y, chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
            (vecCons (χ k) φ) y) atTop (𝓝 0))

def StokesOnVariety.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) →
    SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → (HasCompactSupport f ∨ HasCompactSupport g) →
      varInt J (d + 1) f (vecCons g φ) = varInt J (d + 1) g (vecCons f φ)

def LogIntegrable.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    linForm u ∉ J → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      Integrable (chartAbsDens J A
        ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval u x‖) φ)

def LocalOrder.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) p) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes → p ∈ zeroSet W →
    (∃ N ∈ 𝓝 p, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 p, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
      localMult (J ⊔ Ideal.span {linForm u}) W = ∑ b, ord b

def PoincareLelong.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    ContDiff ℝ ∞ f → HasCompactSupport f → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      varInt J (d + 1) (fun x => Real.log ‖linEval u x‖) (vecCons f φ) =
        ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ

def ConeToProjective.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (ℓ : Fin n → ℂ) (g : (Fin n → ℂ) → ℝ),
    IsProjPrime J → IsChowForm J (e + 1) F → linForm ℓ ∉ J →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x) → ContinuousOn g {x | x ≠ 0} →
      coneIntegral h J e g =
        varInt (J ⊔ Ideal.span {linForm ℓ - 1}) e g (fun _ x => Real.log (h.dualNorm x))

def GreenFromLelong.Statement : Prop :=
  IntegralIndep.Statement → CutOff.Statement → StokesOnVariety.Statement →
    LogIntegrable.Statement → PoincareLelong.Statement → ConeToProjective.Statement →
      GreenSymmetry.Statement

def MassFromLelong.Statement : Prop :=
  IntegralIndep.Statement → CutOff.Statement → StokesOnVariety.Statement →
    LogIntegrable.Statement → PoincareLelong.Statement → ConeToProjective.Statement →
      ChowFormSection.Statement → ConeIntegralMass.Statement

section Inhabitants

theorem linForm_single {n : ℕ} (i : Fin n) : linForm (Pi.single i (1 : ℂ)) = X i := by
  classical
  simp [linForm, Pi.single_apply]

theorem projHom_space (n : ℕ) :
    projHom (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) =
      Ideal.Quotient.mkₐ ℂ ⊥ := by
  classical
  apply MvPolynomial.algHom_ext
  intro i
  simp [projHom, pullback, linPoly, Matrix.one_apply]

theorem isFiniteProjection_space (n : ℕ) :
    IsFiniteProjection (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [projHom_space]
    intro a b h
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] at h
    exact h
  · rw [projHom_space]
    exact RingHom.Finite.of_surjective _ (Ideal.Quotient.mkₐ_surjective ℂ _)

theorem space_dim (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin n) ℂ))) = (n : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem mk_ker_eval_eq {n : ℕ} (p : Fin n → ℂ) (q : MvPolynomial (Fin n) ℂ) :
    Ideal.Quotient.mk (RingHom.ker (MvPolynomial.eval p)) q =
      algebraMap ℂ _ (MvPolynomial.eval p q) := by
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, RingHom.mem_ker, map_sub]
  simp

theorem eval_surjective {n : ℕ} (p : Fin n → ℂ) : Function.Surjective (MvPolynomial.eval p) :=
  fun c => ⟨C c, eval_C c⟩

theorem point_dim {n : ℕ} (p : Fin n → ℂ) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ RingHom.ker (MvPolynomial.eval p)) = (0 : ℕ) := by
  have : (RingHom.ker (MvPolynomial.eval p)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (eval_surjective p)
  let := Ideal.Quotient.field (RingHom.ker (MvPolynomial.eval p))
  rw [ringKrullDim_eq_zero_of_field]
  rfl

theorem isFiniteProjection_point {n : ℕ} (p : Fin n → ℂ) (A : Matrix (Fin 0) (Fin n) ℂ) :
    IsFiniteProjection (RingHom.ker (MvPolynomial.eval p)) A := by
  have hC : ∀ a : MvPolynomial (Fin 0) ℂ, a = C (MvPolynomial.eval (fun i => i.elim0) a) := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c => simp
    | add a b ha hb => rw [map_add, C_add, ← ha, ← hb]
    | mul_X a i _ => exact i.elim0
  have hproj : ∀ c : ℂ, projHom (RingHom.ker (MvPolynomial.eval p)) A (C c) = algebraMap ℂ _ c := by
    intro c
    simp [projHom, pullback]
  have : (RingHom.ker (MvPolynomial.eval p)).IsPrime := RingHom.ker_isPrime _
  refine ⟨?_, ?_⟩
  · intro a b h
    rw [hC a, hC b, hproj, hproj] at h
    rw [hC a, hC b, (algebraMap ℂ _).injective h]
  · refine RingHom.Finite.of_surjective _ fun z => ?_
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨C (MvPolynomial.eval p q), by
      show projHom _ A (C (MvPolynomial.eval p q)) = _
      rw [hproj, mk_ker_eval_eq]⟩

theorem exists_smooth_bump (n : ℕ) :
    ∃ f : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ f 0 = 1 := by
  obtain ⟨f, -, hc, hs, -, h0⟩ := exists_contDiff_tsupport_subset (E := Fin n → ℂ) (n := ⊤)
    (s := Metric.ball 0 1) (x := 0) (Metric.ball_mem_nhds 0 one_pos)
  exact ⟨f, hs, hc, h0⟩

theorem smoothNear_of_contDiff {n : ℕ} {S : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ}
    (h : ContDiff ℝ ∞ φ) : SmoothNear S φ :=
  ⟨Set.univ, isOpen_univ, Set.subset_univ _, h.contDiffOn⟩

theorem contDiff_euclPot (n : ℕ) : ContDiff ℝ ∞ (euclPot : (Fin n → ℂ) → ℝ) := by
  unfold euclPot
  exact ContDiff.sum fun j _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ j)

theorem linForm_single_not_mem_bot {n : ℕ} (i : Fin n) :
    linForm (Pi.single i (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) := by
  rw [linForm_single, Ideal.mem_bot]
  exact X_ne_zero i

theorem isSheetAt_space {n : ℕ} (x : Fin n → ℂ) :
    IsSheetAt (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) x id := by
  have hZ : ∀ y : Fin n → ℂ, y ∈ zeroSet (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) := by
    intro y q hq
    rw [Ideal.mem_bot] at hq
    simp [hq]
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, differentiableOn_id, by simp,
    fun y _ => ⟨by simp, hZ y⟩, Set.univ, Filter.univ_mem, fun x' _ _ => by simp⟩

def lineBranch : VarBranch (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1 0 where
  radius := 1
  radius_pos := one_pos
  toFun := id
  differentiableOn := differentiableOn_id
  injOn := Set.injOn_id _
  map_zero := rfl
  mapsTo := fun _ _ q hq => by
    rw [Ideal.mem_bot] at hq
    simp [hq]

theorem IntegralIndep.hypotheses_inhabited (p : Fin 2 → ℂ) (A : Matrix (Fin 0) (Fin 2) ℂ)
    (f : (Fin 2 → ℂ) → ℝ) (hf : Measurable f) (φ : Fin 0 → (Fin 2 → ℂ) → ℝ) :
    (RingHom.ker (MvPolynomial.eval p)).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin 2) ℂ ⧸ RingHom.ker (MvPolynomial.eval p)) = (0 : ℕ) ∧
      IsFiniteProjection (RingHom.ker (MvPolynomial.eval p)) A ∧ Measurable f ∧
      (∀ k, SmoothNear (zeroSet (RingHom.ker (MvPolynomial.eval p))) (φ k)) ∧
      Integrable (chartAbsDens (RingHom.ker (MvPolynomial.eval p)) A f φ) := by
  refine ⟨RingHom.ker_isPrime _, point_dim p, isFiniteProjection_point p A, hf,
    fun k => k.elim0, ?_⟩
  have hconst : chartAbsDens (RingHom.ker (MvPolynomial.eval p)) A f φ =
      fun _ => chartAbsDens (RingHom.ker (MvPolynomial.eval p)) A f φ 0 :=
    funext fun y => congrArg _ (Subsingleton.elim y 0)
  rw [hconst]
  have : IsFiniteMeasure (volume : Measure (Fin 0 → ℂ)) := by
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty (x := 0)]
    infer_instance
  exact integrable_const _

theorem CutOff.hypotheses_inhabited :
    (coneIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (1 + 1 : ℕ) ∧
      IsFiniteProjection coneIdeal coneProj) ∧ (X 0 : MvPolynomial (Fin (1 + 1)) ℂ) ≠ 0 :=
  ⟨cone_hyps, X_ne_zero 0⟩

theorem StokesOnVariety.hypotheses_inhabited :
    ∃ f : (Fin 2 → ℂ) → ℝ, (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin 2) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ))) = (1 + 1 : ℕ) ∧
      SmoothNear (zeroSet (⊥ : Ideal (MvPolynomial (Fin 2) ℂ))) f ∧
      SmoothNear (zeroSet (⊥ : Ideal (MvPolynomial (Fin 2) ℂ))) euclPot ∧
      (∀ i : Fin 1, SmoothNear (zeroSet (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)))
        ((fun _ => euclPot) i)) ∧
      (HasCompactSupport f ∨ HasCompactSupport (euclPot : (Fin 2 → ℂ) → ℝ)) ∧ f 0 = 1 := by
  obtain ⟨f, hs, hc, h0⟩ := exists_smooth_bump 2
  exact ⟨f, Ideal.isPrime_bot, space_dim 2, smoothNear_of_contDiff hs,
    smoothNear_of_contDiff (contDiff_euclPot 2), fun _ => smoothNear_of_contDiff (contDiff_euclPot 2),
    Or.inl hc, h0⟩

theorem LogIntegrable.hypotheses_inhabited :
    (coneIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ) ∧
      IsFiniteProjection coneIdeal coneProj) ∧
      linForm (Pi.single 0 (1 : ℂ)) ∉ coneIdeal ∧
      (∀ i : Fin 2, SmoothNear (zeroSet coneIdeal) ((fun _ => euclPot) i)) := by
  refine ⟨cone_hyps, ?_, fun _ => smoothNear_of_contDiff (contDiff_euclPot 3)⟩
  rw [linForm_single]
  exact X_zero_not_mem_coneIdeal

theorem PoincareLelong.hypotheses_inhabited :
    ∃ f : (Fin 2 → ℂ) → ℝ, (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin 2) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ))) = (1 + 1 : ℕ) ∧
      linForm (Pi.single 0 (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ i : Fin 1, SmoothNear (zeroSet (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)))
        ((fun _ => euclPot) i)) ∧ f 0 = 1 := by
  obtain ⟨f, hs, hc, h0⟩ := exists_smooth_bump 2
  exact ⟨f, Ideal.isPrime_bot, space_dim 2, linForm_single_not_mem_bot 0, hs, hc,
    fun _ => smoothNear_of_contDiff (contDiff_euclPot 2), h0⟩

theorem LocalOrder.hypotheses_inhabited :
    (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin 1) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) = (0 + 1 : ℕ) ∧
      linForm (fun _ : Fin 1 => (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      (Ideal.span {X 0} : Ideal (MvPolynomial (Fin 1) ℂ)) ∈
        ((⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ⊔ Ideal.span {linForm fun _ : Fin 1 => (1 : ℂ)}).minimalPrimes ∧
      (0 : Fin 1 → ℂ) ∈ zeroSet (Ideal.span {X 0} : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      (∃ N ∈ 𝓝 (0 : Fin 1 → ℂ), zeroSet (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∩ N ⊆
        ⋃ b : Fin 1, ((fun _ => lineBranch) b).image) ∧
      (∃ N ∈ 𝓝 (0 : Fin 1 → ℂ), ∀ b : Fin 1,
        zeroSet (Ideal.span {X 0} : Ideal (MvPolynomial (Fin 1) ℂ)) ∩ N ⊆
          ((fun _ => lineBranch) b).slice) ∧
      (∀ b b' : Fin 1, b ≠ b' → ((fun _ => lineBranch) b).image ∩ ((fun _ => lineBranch) b').image ⊆
        {x | linEval (fun _ => 1) x = 0}) ∧
      (∀ b : Fin 1, VanishesToOrder (fun t => linEval (fun _ => 1) (((fun _ => lineBranch) b).toFun t))
        ((fun _ => lineBranch) b).radius ((fun _ => 1) b)) := by
  have hl : linForm (fun _ : Fin 1 => (1 : ℂ)) = X 0 := by simp [linForm]
  have hW : (Ideal.span {X 0} : Ideal (MvPolynomial (Fin 1) ℂ)).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime
  have hZ : ∀ x : Fin 1 → ℂ, x ∈ zeroSet (Ideal.span {X 0} : Ideal (MvPolynomial (Fin 1) ℂ)) →
      x = 0 := by
    intro x hx
    have h0 := hx (X 0) (Ideal.subset_span rfl)
    simp only [eval_X] at h0
    funext i
    fin_cases i
    exact h0
  refine ⟨Ideal.isPrime_bot, space_dim 1, linForm_one_not_mem_point ℂ, ?_, ?_,
    ⟨Metric.ball 0 1, Metric.ball_mem_nhds 0 one_pos, fun x hx => Set.mem_iUnion.mpr ⟨0, x, hx.2, rfl⟩⟩,
    ⟨Set.univ, Filter.univ_mem, fun _ x hx => ?_⟩, fun b b' h => absurd (Subsingleton.elim b b') h,
    fun _ => ⟨fun _ => 1, differentiableOn_const _, fun _ _ => one_ne_zero, fun t _ => ?_⟩⟩
  · rw [hl, bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  · intro q hq
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hq
    simp
  · obtain rfl := hZ x hx.1
    exact ⟨0, ⟨Metric.mem_ball_self lineBranch.radius_pos, rfl⟩, rfl⟩
  · simp [linEval, lineBranch]

theorem ConeToProjective.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (1 + 1) LineChowForm.D2 ∧
      linForm (fun j : Fin 2 => if j = 0 then (1 : ℂ) else 0) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      (∀ (t : ℂ) (x : Fin 2 → ℂ), t ≠ 0 → (fun _ => (1 : ℝ)) (t • x) = (fun _ => (1 : ℝ)) x) ∧
      ContinuousOn (fun _ : Fin 2 → ℂ => (1 : ℝ)) {x | x ≠ 0} :=
  ⟨LineChowForm.isProjPrime_line, LineChowForm.isChowForm_line, LineChowForm.linForm_line,
    fun _ _ _ => rfl, continuousOn_const⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights
