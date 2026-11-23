import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFamOfNotMem
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

theorem smoothOp_normInd_of_fixed : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G), IsOpen (H : Set G) → IsCompact (H : Set G) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), GlobalTheory.PRep.IsSmooth ρ → ∀ x : W, (∀ h ∈ H, ρ h x = x) → smoothOp ρ μ (normInd μ (H : Set G)) x = x := by
  intro G _ _ _ _ _ _ μ _ H ho hK W _ _ ρ hρ x hx
  have hf : IsLocallyConstant ((H : Set G).indicator (1 : G → ℂ)) := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun g => ?_
    by_cases hg : g ∈ (H : Set G)
    · exact ⟨H, ho, hg, fun y hy => by simp [Set.indicator_of_mem hy, Set.indicator_of_mem hg]⟩
    · exact ⟨(H : Set G)ᶜ, (H.isClosed_of_isOpen ho).isOpen_compl, hg, fun y hy => by
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hg]⟩
  have hc : HasCompactSupport ((H : Set G).indicator (1 : G → ℂ)) :=
    HasCompactSupport.intro hK fun y hy => Set.indicator_of_notMem hy _
  have h0 : (μ.real H : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, Ne, measureReal_eq_zero_iff hK.measure_lt_top.ne]
    exact (ho.measure_pos μ ⟨1, one_mem H⟩).ne'
  have hf' : IsLocallyConstant (normInd μ (H : Set G)) := by
    unfold normInd; exact hf.comp ((μ.real H : ℂ)⁻¹ • ·)
  have hc' : HasCompactSupport (normInd μ (H : Set G)) := by
    unfold normInd; exact hc.comp_left (g := ((μ.real H : ℂ)⁻¹ • ·)) (smul_zero _)
  refine eq_of_forall_dual fun l => ?_
  have h1 : (fun g => normInd μ (H : Set G) g • l (ρ g x)) =
      (H : Set G).indicator fun _ => (μ.real H : ℂ)⁻¹ * l x := by
    ext g
    by_cases hg : g ∈ (H : Set G)
    · have : ρ g x = x := hx g hg
      simp [normInd, Set.indicator_of_mem hg, this]
    · simp [normInd, Set.indicator_of_notMem hg]
  rw [hρ.map_smoothOp hf' hc', h1, integral_indicator_const _ ho.measurableSet]
  rw [Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]

end GlobalTheory.TrIdem
