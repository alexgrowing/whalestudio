import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm

open Matrix Complex ComplexConjugate
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m l n k : Type*} [Fintype m] [Fintype l] [Fintype n] [DecidableEq m] [DecidableEq l]
  [DecidableEq n]

def wedgeHolAnti {V p q : Type*} (A : V → Matrix p n ℂ) (B : V → Matrix n q ℂ) (ξ η : V) :
    Matrix p q ℂ := A ξ * B η

def wedgeAntiHol {V p q : Type*} (B : V → Matrix p n ℂ) (A : V → Matrix n q ℂ) (ξ η : V) :
    Matrix p q ℂ := -(B η * A ξ)

def covDbar (s : E → n → ℂ) (z η : E) : n → ℂ := fun a => dbar (fun x => s x a) z η

def homCovDel (A : E → Matrix m m ℂ) (B : E → Matrix l l ℂ) (T : E → Matrix l m ℂ) (z ξ : E) :
    Matrix l m ℂ := mdel T z ξ + conn B z ξ * T z - T z * conn A z ξ

def delOfAnti (A : E → Matrix m m ℂ) (B : E → Matrix l l ℂ) (β : E → E → Matrix l m ℂ)
    (z ξ η : E) : Matrix l m ℂ := homCovDel A B (fun x => β x η) z ξ

def delOfHol (A : E → Matrix m m ℂ) (B : E → Matrix l l ℂ) (γ : E → E → Matrix l m ℂ)
    (z ξ₁ ξ₂ : E) : Matrix l m ℂ :=
  homCovDel A B (fun x => γ x ξ₂) z ξ₁ - homCovDel A B (fun x => γ x ξ₁) z ξ₂

def dbarOfHol {p q : Type*} (γ : E → E → Matrix p q ℂ) (z ξ η : E) : Matrix p q ℂ :=
  -mdbar (fun x => γ x ξ) z η

def dbarOfAnti {p q : Type*} (β : E → E → Matrix p q ℂ) (z η₁ η₂ : E) : Matrix p q ℂ :=
  mdbar (fun x => β x η₂) z η₁ - mdbar (fun x => β x η₁) z η₂

def subField (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (x : E) : Matrix m m ℂ := subGram (H x)

def quotField (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (x : E) : Matrix l l ℂ := quotGram (H x)

def pairSection (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (s : E → m → ℂ) (q : E → l → ℂ) (x : E) :
    m ⊕ l → ℂ := incl m l *ᵥ s x + orthLift (H x) *ᵥ q x

def IsHolFormAt {p q : Type*} (A : E → E → Matrix p q ℂ) (z : E) : Prop :=
  IsLinearMap ℂ (A z) ∧ ∀ ξ, MContDiffAt ∞ (fun x => A x ξ) z

def IsAntiFormAt {p q : Type*} (B : E → E → Matrix p q ℂ) (z : E) : Prop :=
  (∀ η η', B z (η + η') = B z η + B z η') ∧ (∀ (c : ℂ) η, B z (c • η) = conj c • B z η) ∧
    ∀ η, MContDiffAt ∞ (fun x => B x η) z

def ConnBlocks (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (A : E → Matrix l m ℂ) (B : E → Matrix m l ℂ)
    (z : E) : Prop :=
  ∀ (s : E → m → ℂ) (q : E → l → ℂ), (∀ a, ContDiffAt ℝ 1 (fun x => s x a) z) →
    (∀ a, ContDiffAt ℝ 1 (fun x => q x a) z) → ∀ ξ : E,
      orthProj (H z) *ᵥ covDel H (pairSection H s q) z ξ = covDel (subField H) s z ξ ∧
      quotMap m l *ᵥ covDel H (pairSection H s q) z ξ =
        A ξ *ᵥ s z + covDel (quotField H) q z ξ ∧
      orthProj (H z) *ᵥ covDbar (pairSection H s q) z ξ = covDbar s z ξ + B ξ *ᵥ q z ∧
      quotMap m l *ᵥ covDbar (pairSection H s q) z ξ = covDbar q z ξ

def IsNonnegForm {V : Type*} [AddCommGroup V] [Module ℂ V] (α : V → V → ℂ) : Prop :=
  IsSesq α ∧ (∀ ξ η, conj (α ξ η) = -α η ξ) ∧ FormLe (fun _ _ => 0) α

def SubQuotAt (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : E) : Prop :=
  IsHolFormAt (secondForm H) z ∧ IsAntiFormAt (secondFormAdj H) z ∧
  (∀ ξ s q, form (quotField H z) (secondForm H z ξ *ᵥ s) q =
    form (subField H z) s (secondFormAdj H z ξ *ᵥ q)) ∧
  ConnBlocks H (secondForm H z) (fun η => -secondFormAdj H z η) z ∧
  (∀ ξ η, curv (subField H) z ξ η =
    blockSS (H z) (curv H z ξ η) + wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η) ∧
  (∀ ξ η, curv (quotField H) z ξ η =
    blockQQ (H z) (curv H z ξ η) + wedgeHolAnti (secondForm H z) (secondFormAdj H z) ξ η) ∧
  ((H z).PosDef → ∀ ξ s,
    form (subField H z) (wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ ξ *ᵥ s) s =
      -((gnorm (quotField H z) (secondForm H z ξ *ᵥ s) ^ 2 : ℝ) : ℂ))

def ExtBlocksAt (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : E) : Prop :=
  IsAntiFormAt (extForm H) z ∧ IsHolFormAt (extFormAdj H) z ∧
  ConnBlocks H (fun ξ => -extFormAdj H z ξ) (extForm H z) z ∧
  (∀ ξ η, blockSS (H z) (curv H z ξ η) =
    curv (subField H) z ξ η - wedgeAntiHol (extForm H z) (extFormAdj H z) ξ η) ∧
  (∀ ξ η, blockSQ (H z) (curv H z ξ η) =
    delOfAnti (quotField H) (subField H) (extForm H) z ξ η) ∧
  (∀ ξ η, blockQS (curv H z ξ η) = -dbarOfHol (extFormAdj H) z ξ η) ∧
  (∀ ξ η, blockQQ (H z) (curv H z ξ η) =
    curv (quotField H) z ξ η - wedgeHolAnti (extFormAdj H z) (extForm H z) ξ η) ∧
  (∀ η₁ η₂, dbarOfAnti (extForm H) z η₁ η₂ = 0) ∧
  (∀ ξ₁ ξ₂, delOfHol (subField H) (quotField H) (extFormAdj H) z ξ₁ ξ₂ = 0)

def ChTwoAt (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : E) : Prop :=
  IsNonnegForm (extTrace H z) ∧
  ∀ ξ₁ η₁ ξ₂ η₂, ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ =
    chTwo (subField H) z ξ₁ η₁ ξ₂ η₂ + chTwo (quotField H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂

def vertForm [Unique m] [Unique l] (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ η : E) : ℂ :=
  kappa * (extFormAdj H z ξ default default * extForm H z η default default)

def RankTwoAt [Unique m] [Unique l] (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : E) : Prop :=
  IsNonnegForm (vertForm H z) ∧
  (∀ ξ₁ η₁ ξ₂ η₂, wedge (vertForm H z) (vertForm H z) ξ₁ η₁ ξ₂ η₂ = 0) ∧
  (∀ s : m → ℂ, s ≠ 0 → ∀ ξ η,
    chernOne (subField H) z ξ η = lineCurv H z (incl m l *ᵥ s) ξ η - vertForm H z ξ η ∧
    chernOne (quotField H) z ξ η =
      chernOne H z ξ η - lineCurv H z (incl m l *ᵥ s) ξ η + vertForm H z ξ η) ∧
  (∀ ξ₁ η₁ ξ₂ η₂, ddcForm (vertForm H) z ξ₁ η₁ ξ₂ η₂ = chernTwo H z ξ₁ η₁ ξ₂ η₂ -
    wedge (chernOne (subField H) z) (chernOne (quotField H) z) ξ₁ η₁ ξ₂ η₂) ∧
  vertForm H z = extTrace H z

end Defs

def SubQuotCurvature : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (m l : Type) [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    (U : Set E) (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ), IsHermFrame U H →
    (∀ z ∈ U, IsUnit (subField H z).det) →
      IsHermFrame U (subField H) ∧ IsHermFrame U (quotField H) ∧ ∀ z ∈ U, SubQuotAt H z

def AnyRankCurvature : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (m l : Type) [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    (U : Set E) (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ), IsPosFrame U H →
      ∀ z ∈ U, ExtBlocksAt H z ∧ ChTwoAt H z

def RankTwoCurvature : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (m l : Type) [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] [Unique m] [Unique l]
    (U : Set E) (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ), IsPosFrame U H →
      ∀ z ∈ U, ExtBlocksAt H z ∧ RankTwoAt H z

def Statement : Prop := SubQuotCurvature ∧ RankTwoCurvature ∧ AnyRankCurvature

section Basic₂

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m l k : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem homCovDel_leibniz (A : E → Matrix m m ℂ) (B : E → Matrix l l ℂ) {T : E → Matrix l m ℂ}
    {S : E → Matrix m k ℂ} {z : E} (hT : MContDiffAt 1 T z) (hS : MContDiffAt 1 S z) (ξ : E) :
    mdel (fun x => T x * S x) z ξ + conn B z ξ * (T z * S z) =
      homCovDel A B T z ξ * S z + T z * (mdel S z ξ + conn A z ξ * S z) := by
  rw [mdel_mul hT hS, homCovDel]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel

theorem contDiff_tautPairGram (a b : Unit ⊕ Unit) :
    ContDiff ℝ ∞ fun x => tautPairGram x a b := by
  have hc : ContDiff ℝ ∞ fun x : ℂ => conj x := conjCLE.contDiff
  rcases a with a | a <;> rcases b with b | b
  · exact contDiff_const.add (contDiff_id.mul hc)
  · exact contDiff_id
  · exact hc
  · exact contDiff_const

theorem isPosFrame_tautPairGram : IsPosFrame Set.univ tautPairGram := by
  refine ⟨isOpen_univ, fun a b => (contDiff_tautPairGram a b).contDiffOn, fun z _ => ?_⟩
  let P : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ := fromBlocks 1 (of fun _ _ => z) 0 1
  have hP : IsUnit P := by
    rw [isUnit_iff_isUnit_det, det_fromBlocks_zero₂₁]; simp
  have e : tautPairGram z = P * 1 * Pᴴ := by
    ext (a | a) (b | b) <;> simp [tautPairGram, P, mul_apply]
  rw [e]
  exact PosDef.one.mul_mul_conjTranspose_same (vecMul_injective_iff_isUnit.2 hP)

theorem vertForm_tautPairGram_zero (ξ η : ℂ) :
    vertForm tautPairGram 0 ξ η = kappa * (ξ * conj η) := by
  have hF := isPosFrame_tautPairGram.isHermFrame
  have h : tautPairGram 0 = 1 := by
    rw [← fromBlocks_one]; ext (a | a) (b | b) <;> simp [tautPairGram]
  have hs : subGram (tautPairGram 0) = 1 := by rw [h]; ext a b; simp [subGram, toBlocks₁₁]
  have hq : quotGram (tautPairGram 0) = 1 := by
    rw [h, ← fromBlocks_one, quotGram, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₂₁]; simp
  have hb : ∀ ξ : ℂ, secondForm tautPairGram 0 ξ () () = ξ := fun ξ => by
    rw [secondForm_eq, conn, h, transpose_one, inv_one, Matrix.one_mul]
    change del (fun x : ℂ => x) 0 ξ = ξ
    rw [del_eq_fderiv differentiableAt_fun_id]; simp
  have hu : IsUnit (subGram (tautPairGram 0)).det := by rw [hs]; simp
  rw [vertForm, extFormAdj_eq_neg_secondForm (hF.one trivial) (hF.eventually_herm trivial)
    (hF.isUnit 0 trivial) hu, extForm_eq_neg_secondFormAdj (hF.one trivial)
    (hF.eventually_herm trivial) (hF.isUnit 0 trivial) hu, secondFormAdj, hs, hq, adj]
  simp [hb]

def lorentzPairGram (z : ℂ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ :=
  fromBlocks (of fun _ _ => 1 - z * conj z) (of fun _ _ => -z) (of fun _ _ => -conj z) (-1)

theorem lorentzPairGram_spec : IsHermFrame (Metric.ball 0 1) lorentzPairGram ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, IsUnit (subField lorentzPairGram z).det) ∧
    ¬ (lorentzPairGram 0).PosDef := by
  have hc : ContDiff ℝ ∞ fun x : ℂ => conj x := conjCLE.contDiff
  have hs : ∀ z ∈ Metric.ball (0 : ℂ) 1, (1 - z * conj z) ≠ 0 := fun z hz h => by
    have h1 : ‖z‖ < 1 := by simpa using hz
    rw [mul_conj', sub_eq_zero] at h
    have h2 : (1 : ℝ) = ‖z‖ ^ 2 := by exact_mod_cast h
    nlinarith [norm_nonneg z]
  refine ⟨⟨Metric.isOpen_ball, fun a b => ContDiff.contDiffOn ?_, fun z _ => ?_, fun z _ => ?_⟩,
    fun z hz => ?_, fun h => ?_⟩
  · rcases a with a | a <;> rcases b with b | b
    · exact contDiff_const.sub (contDiff_id.mul hc)
    · exact contDiff_id.neg
    · exact hc.neg
    · exact contDiff_const
  · ext (a | a) (b | b) <;> simp [lorentzPairGram, mul_comm]
  · let P : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ := fromBlocks 1 (of fun _ _ => z) 0 1
    let Q : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ := fromBlocks 1 0 (of fun _ _ => -conj z) (-1)
    have e : lorentzPairGram z = P * Q := by
      ext (a | a) (b | b) <;> simp [lorentzPairGram, P, Q, mul_apply, sub_eq_add_neg]
    rw [e, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂]
    simp
  · rw [det_unique]; exact (hs z hz).isUnit
  · have := h.diag_pos (i := Sum.inr ())
    simp [lorentzPairGram] at this
    exact absurd this (by norm_num)

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz
