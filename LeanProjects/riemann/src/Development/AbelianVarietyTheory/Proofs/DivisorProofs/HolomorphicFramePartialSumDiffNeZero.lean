import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCubeAbelianPointThetaFaceEqPartialSum
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CmFieldHostElementAddConjEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem wI_mem_chart (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (j : thK → D.P.L.ι) (I : thK)
    (hz : ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j) :
    ⊤ ≤ (ν.eA (d.ex (wI x y z I))).left ⁻¹ᵁ D.P.L.U (j I) := by
  have h1 : ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ (thφ D.P.A (x3 D.P.A) I ⁻¹ᵁ D.P.L.U (j I)) :=
    fun q hq => LB.wchart_le D.P.L (thφ D.P.A (x3 D.P.A)) j I (hz hq)
  rw [← complexCubeAbelianPoint_thetaFace_eq_partialSum ν d x y z I]
  exact fun q hq => h1 hq

theorem differentiable_wI (x y : Fin g → ℂ) (I : thK) : Differentiable ℂ (fun z => wI x y z I) := by
  unfold wI
  refine Differentiable.fun_sum fun a _ => ?_
  fin_cases a
  · exact differentiable_const _
  · exact differentiable_const _
  · exact differentiable_id

theorem frG_wI_hol_ne (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y : Fin g → ℂ)
    (j : thK → D.P.L.ι) (I : thK) :
    DifferentiableOn ℂ (fun z => geo.frG (j I) (wI x y z I)) {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} ∧
      ∀ z, ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j → geo.frG (j I) (wI x y z I) ≠ 0 := by
  refine ⟨(geo.fr_hol (j I)).comp (differentiable_wI x y I).differentiableOn
    fun z hz => wI_mem_chart ν d x y z j I hz, fun z hz => ?_⟩
  set w := wI x y z I
  have hj := wI_mem_chart ν d x y z j I hz
  have hp := ν.good (ν.eA (d.ex w)).left
  have hpj : ⊤ ≤ (ν.eA (d.ex w)).left ⁻¹ᵁ (D.P.L.U (ν.J (ν.eA (d.ex w)).left) ⊓ D.P.L.U (j I)) :=
    fun q hq => ⟨hp hq, hj hq⟩
  have hc := geo.fr_compat _ (j I) w hpj
  have hne : geo.frG (ν.J (ν.eA (d.ex w)).left) w ≠ 0 := by
    rw [← geo.fr_eq w]
    exact mul_ne_zero (Units.ne_zero _) (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  rw [hc] at hne
  exact right_ne_zero_of_mul hne

end GlobalTheory.MBLow.Cl.CubHol

end
