import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompAddEquivRescaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompactOpenPiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenSubgroupExhaustionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralNormFormScaledEqSignAbsInvStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem hasGauss_diag_norm : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ g : ℂ, ∀ t : α → ν → Fˣ, HasGauss μ (fun x => ψ (∑ i, ∑ j, (t i j : F) * Algebra.norm F (x i j))) (g * ∏ i, ∏ j, (sgn E (t i j) * ((nabs F (t i j))⁻¹ : ℝ))) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ ψ hψ hn h1 _ _ μ _
  obtain ⟨hfd, -, -, -, -, -, -, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  haveI : FiniteDimensional F E := hfd
  have hGE : Good E := GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional F E
  haveI := hGE.grp; haveI := hGE.lc; haveI := hGE.sc; haveI := hGE.t2
  let μE : Measure E := Measure.addHaar
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.gaussIntegral_normForm_scaled_eq_sign_abs_inv F E c δ hE ψ hψ hn h1 μE
  have hGM : Good (Matrix α ν E) := (hmat α ν).2
  haveI := hGM.grp; haveI := hGM.lc; haveI := hGM.sc
  let T : Matrix α ν E ≃ₜ+ (α × ν → E) :=
    { toFun := fun x p => x p.1 p.2
      invFun := fun y i j => y (i, j)
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_add' := fun x y => rfl
      continuous_toFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
      continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j) }
  haveI : BorelSpace (α × ν → E) := Pi.borelSpace
  haveI : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  have hr : μ.map T = (μ.map T).addHaarScalarFactor (Measure.pi fun _ : α × ν => μE) •
      Measure.pi fun _ : α × ν => μE := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨(((μ.map T).addHaarScalarFactor (Measure.pi fun _ : α × ν => μE) : ℝ) : ℂ) *
    g₁ ^ Fintype.card (α × ν), fun t => ?_⟩
  have hpi := GlobalTheory.T.hasGaussIntegralCompactOpen_pi E hGE μE (α × ν) (fun p z => ψ ((t p.1 p.2 : F) * Algebra.norm F z))
    (fun p => g₁ * (sgn E (t p.1 p.2) * ((nabs F (t p.1 p.2))⁻¹ : ℝ))) (fun p => hg₁ _)
  have hm := GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale _ _ μ _ T _ _ _ hr hpi
  have hsum : ∀ (s : Finset (α × ν)) (f : α × ν → F), ψ (∑ p ∈ s, f p) = ∏ p ∈ s, ψ (f p) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  convert hm using 1
  · funext x
    rw [← Fintype.sum_prod_type', hsum]
    rfl
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.prod_prod_type, mul_assoc]

end GlobalTheory.KSp
