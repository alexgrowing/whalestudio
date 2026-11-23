import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockTop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCoordArithOfFnField
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockFnField
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMetricTransportSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace TwoBlockTop

variable {κ : Type}

theorem isPullHerm_blockLine [Fintype κ] (m : ConeMetric ℂ (Ix κ)) (b : Fin 2) :
    IsPullHerm (blkOf b) (blkV κ b) (HermLine.ofCone m) (blockLine m b) := by
  refine ⟨?_, fun z => rfl⟩
  funext k
  show (Pi.single b 1 : Fin 2 → ℤ) k = Function.extend (blkOf b) (fun _ : Unit => (1 : ℤ)) 0 k
  by_cases hk : k = b
  · subst hk
    rw [Pi.single_eq_same]
    exact (Function.Injective.extend_apply (f := blkOf k) (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ => (1 : ℤ)) (0 : Fin 2 → ℤ) ()).symm
  · rw [Pi.single_eq_of_ne hk, Function.extend_apply' _ _ _ (fun ⟨_, hu⟩ => hk hu.symm)]
    rfl

theorem pair_comp_blkV_zero {Ω : Type} [Field Ω] (x x' : Ix κ → Ω) : pair x x' ∘ blkV κ 0 = x := by
  funext p
  obtain ⟨⟨⟩, i⟩ := p
  simp [pair, blkV]

theorem pair_comp_blkV_one {Ω : Type} [Field Ω] (x x' : Ix κ → Ω) : pair x x' ∘ blkV κ 1 = x' := by
  funext p
  obtain ⟨⟨⟩, i⟩ := p
  simp [pair, blkV]

end TwoBlockTop

open TwoBlockTop in

theorem TwoBlockTop.proof (hPF : PFCoordStatement) (hIm : ImageCoordStatement) (hA : CoordArithOfFnField.Statement)
    (hF : TwoBlockFnField.Statement) (hS : MetricTransportSmooth.Statement) : TwoBlockTop.Statement := by
  classical
  intro D Ω _ _ κ _ I x B m m' hI hx _ hB hm hm'
  obtain ⟨hFp, hFB⟩ := hF Ω κ x B hB
  have hxA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hx

  obtain ⟨i, hi⟩ := hx.2.1.2.2 ()
  have hx0 : x ≠ 0 := fun h => hi ((X_mem_coordIdeal_iff x _).mpr (by rw [h]; rfl))
  obtain ⟨B', -, hB'⟩ := isInvMat_mul hB
  have hBx0 : matAct B x ≠ 0 := fun h => hx0 ((matAct_eq_zero_iff hB' x).mp h)
  obtain ⟨⟨⟨⟩, i₀⟩, hi₀⟩ := Function.ne_iff.mp hx0
  obtain ⟨⟨⟨⟩, i₁⟩, hi₁⟩ := Function.ne_iff.mp hBx0

  have hpA : IsArithVar (mCoordIdeal (ι := FinTwoTypeFamily κ) (pair x (matAct B x))) (D + 1) :=
    hA Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x (matAct B x)) (D + 1) ⟨0⟩
      (fun k => by
        fin_cases k
        · exact ⟨i₀, by simpa [pair] using hi₀⟩
        · exact ⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA
  have hBA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) (matAct B x)) (D + 1) :=
    hA Unit (GlobalTheory κ) Unit (GlobalTheory κ) Ω x (matAct B x) (D + 1) ⟨()⟩ (fun _ => ⟨i₁, hi₁⟩) hFB.symm hxA

  have key : ∀ (b : Fin 2) (z : Ix κ → Ω) (μ : ConeMetric ℂ (Ix κ)), pair x (matAct B x) ∘ blkV κ b = z →
      IsArithVar (mCoordIdeal (ι := GlobalTheory κ) z) (D + 1) →
      blockFnField (ι := GlobalTheory κ) z = blockFnField (ι := GlobalTheory κ) x → IsSmoothMetric μ →
      I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine μ b) = top I z μ D := by
    intro b z μ hz hzA hzF hμ
    have himg : imageZ (blkV κ b) (mCoordIdeal (ι := FinTwoTypeFamily κ) (pair x (matAct B x))) = coordIdeal ℤ z := by
      rw [hIm Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) (blkOf b) (blkV κ b) Ω _ (isBlockMap_blkV κ b), hz,
        coordIdeal_eq_mCoordIdeal]
    have h := hPF I hI Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) (blkOf b) (blkV κ b) Ω (pair x (matAct B x)) (D + 1)
      (fun _ => HermLine.ofCone μ) (fun _ => blockLine μ b) (isBlockMap_blkV κ b) hpA
      (by rw [himg, coordIdeal_eq_mCoordIdeal]; exact hzA)
      (fun _ => gbamix_smoothHerm_ofCone hμ) (fun _ => isPullHerm_blockLine μ b)
    rw [IntermediateField.relfinrank_eq_one_iff.mpr (by rw [hz, hzF, hFp]), Nat.cast_one, one_mul] at h
    rw [top, ← himg]
    exact h
  exact ⟨key 0 x m (pair_comp_blkV_zero _ _) hxA rfl hm,
    key 1 (matAct B x) m' (pair_comp_blkV_one _ _) hBA hFB (hS κ B m m' hB hm hm')⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
