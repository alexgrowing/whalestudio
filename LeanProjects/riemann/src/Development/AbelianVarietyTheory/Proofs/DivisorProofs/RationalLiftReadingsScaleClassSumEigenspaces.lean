import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.PhaseBreaksTargetParts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemilinearInjectiveOfIndep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumLiftJointEigenspaceIntoOnePartStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqZeroOfMemRangeAdjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerConjFormsEqCsumAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointApplyOfOrthogonalKer

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

set_option maxHeartbeats 2000000 in

theorem readings_scale_core : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (F : Face D A) (ph : ℂ), GlobalTheory.Hk3.Core R F → IsStdChar D R.ψ (-1) → GlobalTheory.ConjScalar.ConjScalarAt R → ∀ fw : FWTie T R κ v₀, BarTie fw → IoExt R → R.LUnif → (∀ i, OMPins T R κ v₀ O i) → ∀ i : Fin D.R.m, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ (ℓ : Lvl D.what₂.LL G) (Z : Submodule D.what₂.LL (A.fam.L i A.μ0).S.Forms), Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A.fam.L i A.μ0).HZ ℓ Z) ((A.fam.L i A.μ0).XQ ℓ Z) → (∀ a k, (A.fam.L i A.μ0).fE ℓ Z a k ∈ Formalism.DivisionValues.cmMax D.what₂.LL) → (∀ z ∈ Z, R.jV i A.μ0 z ∈ LinearMap.range (LinearMap.adjoint (R.thG i A.μ0))) → ∀ (σ : D.what₂.LL →+* ℂ) (a : Pl D.host.E → List ℤ → D.what₂.LL), ∃ l : ℝ, ∀ x x' y y', GlobalTheory.ConjScalar.EigK R i a ((A.fam.L i A.μ0).toF ℓ Z x) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph ((A.fam.L i A.μ0).toF ℓ Z x) y → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x' y' → ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = (l : ℂ) * GlobalTheory.LiftLower.csumAt (A.fam.L i A.μ0).S σ ((A.fam.L i A.μ0).toF ℓ Z x) x' := by
  intro hH hCR D G _ _ Pl0 T0 A T _ R κ v₀ O F ph hC hψ hS fw hbar hio hU hpins i hom ℓ Z hHz hE hZ
  obtain ⟨gramR, c0R, c0L, tie⟩ := hC.fam.tie
  obtain ⟨hex, hconj, hbarσ⟩ := hCR D G Pl0 T0 A T R F κ v₀ O ph (GlobalTheory.Core5.of_core hC) hψ fw hbar hio hU hpins i hom
  have hph : ph ≠ 0 := by
    intro h0
    have h1 : ‖ph‖ = 1 := hom.2.1.2.2.2.2.1
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hcore : GlobalTheory.Hk3.Core R F := hC
  have key : ∀ σ : D.what₂.LL →+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → ∀ a : Pl D.host.E → List ℤ → D.what₂.LL, ∃ l : ℝ, ∀ x x' y y',
      GlobalTheory.ConjScalar.EigK R i a ((A.fam.L i A.μ0).toF ℓ Z x) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph ((A.fam.L i A.μ0).toF ℓ Z x) y →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x' y' →
      ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = (l : ℂ) * GlobalTheory.LiftLower.csumAt (A.fam.L i A.μ0).S σ ((A.fam.L i A.μ0).toF ℓ Z x) x' := by
    intro σ hσ a
    have hCA := hconj gramR c0R c0L tie σ hσ
    obtain ⟨μ', η', c, c₁, H, j, th, hD⟩ := hCA.2.1
    have hyp : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.HypConj R i σ μ' η' := by
      obtain ⟨-, -, u, U, z, ζ, -, -, -, hall⟩ := hCA
      exact (hall μ' η' c c₁ H j th hD).1
    obtain ⟨ev, hev⟩ := GlobalTheory.T.conjugateDatumLift_jointEigenspace_into_one_part hH R F hcore gramR c0R c0L tie i σ c c₁ H j hσ μ' η' th hD hyp (fun P d => σ (a P d))
    obtain ⟨l, hl⟩ := hS gramR c0R c0L tie i σ hσ μ' η' c c₁ H j th hD ev
    refine ⟨l, fun x x' y y' hx hy hy' => ?_⟩
    have hE' := eigF_conj R hC.models.jV gramR c0R c0L tie i σ c c₁ H j hD.2.2.1 a _ hx
    have hp := hev _ hE'
    have hperp := conjForms_mem_orthogonal_ker R hC.models hU gramR c0R c0L tie i σ c c₁ H j μ' η' th ph hph hex hCA hD ℓ Z hHz hE hZ x
    have hadj := adjoint_apply_of_orthogonal_ker th hperp (hl _ hp)
    refine (GlobalTheory.ConjLiftCounterexample.gram_of_conjAt hCA hD hy hy').trans ?_
    refine (inner_apply_of_adjoint_eq th hadj _).trans ?_
    rw [GlobalTheory.LiftLower.inner_conjForms_eq_csumAt R hC.models.jV gramR c0R c0L tie i σ c c₁ H j hD.2.2.1]
    rfl
  intro σ a
  by_cases hσ : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ
  · exact key σ hσ a
  · obtain ⟨hσ', hbar'⟩ := hbarσ σ hσ
    obtain ⟨l, hl⟩ := key _ hσ' a
    refine ⟨l, fun x x' y y' hx hy hy' => ?_⟩
    rw [hbar' y y', hl x x' y y' hx hy hy', map_mul, Complex.conj_ofReal, conj_csumAt]

end GlobalTheory.ConjScalar
