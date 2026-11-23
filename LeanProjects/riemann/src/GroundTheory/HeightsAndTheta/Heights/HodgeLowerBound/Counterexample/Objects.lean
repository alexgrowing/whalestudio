import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveDivVertical
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder

namespace Line

def lineMetricScaled (c : ℝ) (hc : 0 < c) : HermMetric yLine (trivialBundle (segreCoord yLine) 2)
    (mcPts (mCoordIdeal yLine) \ ∅) lineChart where
  m := 2
  chart l := fun _ => l
  fr _ := 1
  b _ := Pi.basisFun Ω (Fin 2)
  isFrame l := lineMetric.isFrame l
  gram _ _ := (c : ℂ) • 1
  cover := lineMetric.cover
  posDef _ _ _ _ := Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hc)
  compat l l' z hz hl hl' S hS Sz hSz := by
    have h : (1 : Matrix (Fin 2) (Fin 2) ℂ) = Szᴴ * 1 * Sz :=
      lineMetric.compat l l' z hz hl hl' S hS Sz hSz
    show (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) = Szᴴ * ((c : ℂ) • 1) * Sz
    rw [Matrix.mul_smul, Matrix.smul_mul, ← h]
  torus _ _ _ _ _ _ := rfl
  conj _ _ _ _ := by
    ext p q
    by_cases h : p = q <;> simp [h]
  smooth _ _ _ _ _ _ _ _ := contDiffAt_const
  logBound a t₀ _ := by
    have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have hinv : ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹ = (c : ℂ)⁻¹ • 1 := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    refine ⟨a, inFrameDomain_line (by rw [lineChart_γ, chartMap_apply, if_pos rfl]; exact one_ne_zero),
      1, one_pos, c⁻¹, inv_pos.mpr hc, c⁻¹, inv_pos.mpr hc, fun t _ _ _ _ => ⟨?_, ?_, ?_⟩⟩
    · show (((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹ - ((c⁻¹ : ℝ) : ℂ) • 1).PosSemidef
      rw [hinv, Complex.ofReal_inv, sub_self]
      exact Matrix.PosSemidef.zero
    · show ((((c⁻¹ * (lineChart a).logR t : ℝ)) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
        ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹).PosSemidef
      rw [logR_lineChart, hinv]
      have : (((c⁻¹ * Real.exp 1 : ℝ)) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (c : ℂ)⁻¹ • 1 =
          ((c⁻¹ * (Real.exp 1 - 1) : ℝ) : ℂ) • 1 := by
        rw [← sub_smul]
        congr 1
        push_cast
        ring
      rw [this]
      refine Matrix.PosSemidef.one.smul ?_
      refine Complex.zero_le_real.mpr (mul_nonneg (inv_nonneg.mpr hc.le) ?_)
      exact sub_nonneg.mpr (Real.one_le_exp (by norm_num))
    · intro p q
      show ‖fderiv ℝ (fun _ : Fin 1 → ℂ => ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) p q) t‖ ≤ _
      rw [fderiv_const_apply, norm_zero]
      positivity

def lineDataScaled (II : IntersectionSystem)
    (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])
    (c : ℝ) (hc : 0 < c) : ComponentData II Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) :=
  { lineData II hII with h := fun _ => lineMetricScaled c hc }

def lineHodgeScaled (II : IntersectionSystem)
    (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])
    (c : ℝ) (hc : 0 < c) : HodgeData (lineDataScaled II hII c hc) where
  F _ := lineF
  aMu := 0
  Λ := (lineHodge II hII).Λ
  locally := (lineHodge II hII).locally

theorem lineDataScaled_f (II : IntersectionSystem) (hII) (c : ℝ) (hc : 0 < c) :
    (lineDataScaled II hII c hc).f = 1 := rfl

theorem lineDataScaled_N (II : IntersectionSystem) (hII) (c : ℝ) (hc : 0 < c) :
    (lineDataScaled II hII c hc).N = 2 := rfl

theorem lineDataScaled_j' (II : IntersectionSystem) (hII) (c : ℝ) (hc : 0 < c) :
    (lineDataScaled II hII c hc).j' = 1 := rfl

end Line

section FS

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet in

theorem fsHeight_nonneg (II : IntersectionSystem) (hII : IsIntersectionSystem II) :
    ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2] := by
  intro W hW
  obtain ⟨c, hc⟩ := exists_chartMon_notMem hW
  refine inter_nonneg (II Unit (PBlk 2)) CurveDivVertical.full (hII Unit (PBlk 2)) hW
    (Inter.isSmoothHerm_fsLine 2) (d := fun _ => 1) (fun _ => rfl) c (hc _) fun z _ => ?_
  have hfs : (fsLine 2).h z = ∏ k : Unit, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ ((1 : Unit → ℤ) k) :=
    Inter.ofMetrics_fs_h (ι := PBlk 2) 1 z
  rw [hfs]
  simp only [Fintype.prod_unique, Pi.one_apply, zpow_one, pow_one]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun i => ‖z ⟨(), i⟩‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ (c ()))

end FS

section Reg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure WeightReg (ι : K → Type) [∀ k, Fintype (ι k)] where

  reg : ℝ → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι
  deg : ∀ t A, (reg t A).a = A.a
  smooth : ∀ t A, IsSmoothHerm A → IsSmoothHerm (reg t A)
  shift : ∀ t (A A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (k : ℝ), 0 < k → A'.a = A.a →
    (∀ z : (Σ b, ι b) → ℂ, (∀ b, ∃ i, z ⟨b, i⟩ ≠ 0) → A'.h z = k * A.h z) →
    ∀ z : (Σ b, ι b) → ℂ, (∀ b, ∃ i, z ⟨b, i⟩ ≠ 0) → (reg t A').h z = k * (reg t A).h z

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet in

def weightRegRef : WeightReg (PBlk 2) where
  reg _ A := (HermLine.ofMetrics (fun k => fsMetric (PBlk 2 k)) A.a).tensor
    (constLine (A.h (fun _ => 1) / (HermLine.ofMetrics (fun k => fsMetric (PBlk 2 k)) A.a).h (fun _ => 1))
      (div_pos (A.pos _ fun _ => ⟨0, one_ne_zero⟩)
        ((HermLine.ofMetrics (fun k => fsMetric (PBlk 2 k)) A.a).pos _ fun _ => ⟨0, one_ne_zero⟩)))
  deg _ A := by simp [HermLine.tensor, constLine, HermLine.ofMetrics]
  smooth _ A _ := isSmoothHerm_tensor (Inter.isSmoothHerm_ofMetrics_fs _) (isSmoothHerm_constLine _ _)
  shift _ A A' k hk ha hh z _ := by
    have h1 := hh (fun _ => 1) fun _ => ⟨0, one_ne_zero⟩
    simp only [HermLine.tensor, constLine, ha, h1]
    ring

end Reg

section Heights

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

def heightMU (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (R : WeightReg ι) (eps t' : ℝ)
    (W : Ideal (MRing ι)) : ℝ :=
  (II K ι W 1 ![R.reg t' (muLine H)] + eps * II K ι W 1 ![D.A']) / degC W

def HtInteriorArch (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (R : WeightReg ι)
    (Ch rd Lval : ℝ) : Prop :=
  ∀ B : ℝ, 4 * (D.f : ℝ) * (D.N : ℝ) ^ 2 ≤ B → ∀ eps t' : ℝ, 0 < eps → eps ≤ 1 → 0 < t' → t' ≤ 1 →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → D.PX ≤ W → (∀ z ∈ mcPts W, z ∉ D.Bd) →
      -Ch * D.f * D.j' * abelian₂ B rd Lval - eps * D.KA ≤ heightMU D H R eps t' W

end Heights

end GroundTheory.Heights₂.Heights.LowerBoundFree
