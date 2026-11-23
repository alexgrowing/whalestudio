import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory OnePoint
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real ComplexOrder

open GlobalTheory.HermFrame Filter Topology

namespace GlobalTheory.BcUnique

theorem extTrace_fromBlocks_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {r s : ℕ} (S : E → Matrix (Fin r) (Fin r) ℂ) (Q : E → Matrix (Fin s) (Fin s) ℂ) (z : E) :
    extTrace (fun v => fromBlocks (S v) 0 0 (Q v)) z = fun _ _ => 0 := by
  have hl : (fun v => orthLift (fromBlocks (S v) 0 0 (Q v))) = fun _ => fromRows 0 1 := by
    funext v
    simp [orthLift, orthCoeff]
  funext ξ η
  simp [extTrace, extForm, hl]

theorem bcFld_eq_zero_of_isSplit {M : Type} [TopologicalSpace M] {n r s : ℕ} (A : HolAtlas M n) (T : HermSeq A r s)
    (hT : T.IsSplit) : bcFld T = 0 := by
  funext x
  set a := (T.cover x.pt).choose with ha_def
  have hxa : x.pt ∈ T.U a := (T.cover x.pt).choose_spec
  obtain ⟨t, htH, htE⟩ := hT a
  set W := (A.e x.1.1).target ∩ (A.e x.1.1).symm ⁻¹' T.U a with hW
  have hWo : IsOpen W := (A.e x.1.1).isOpen_inter_preimage_symm (T.isOpen a)
  have hzW : x.crd ∈ W := ⟨x.ch.map_source x.2, by
    show x.ch.symm (x.ch x.pt) ∈ T.U a
    rw [x.ch.left_inv x.2]; exact hxa⟩
  have hWn : W ∈ 𝓝 x.crd := hWo.mem_nhds hzW
  set K : V n → Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := fun v => T.mid a (x.ch.symm v) with hK
  set P : V n → Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := fun v => fromBlocks 1 (t (x.ch.symm v)) 0 1 with hP
  have hKs : MContDiffAt 1 K x.crd := fun i j =>
    (((T.smooth a).2.1 i j x.1.1).contDiffAt hWn).of_le (by exact_mod_cast le_top)
  have hKp : ∀ᶠ v in 𝓝 x.crd, (K v).PosDef := by
    filter_upwards [hWn] with v hv
    exact (T.posDef a _ hv.2).2.1
  have htd : ∀ i j, ContDiffAt ℂ 1 (fun v => t (x.ch.symm v) i j) x.crd := fun i j =>
    by
      have h1 : ContDiffOn ℂ 1 ((fun y => t y i j) ∘ (A.e x.1.1).symm) W :=
        (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ W hWo (htH i j x.1.1)).of_le (by exact_mod_cast le_top)
      exact h1.contDiffAt hWn
  have hPs : MContDiffAt 1 P x.crd := by
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact contDiffAt_const
    · exact (htd i j).restrict_scalars ℝ
    · exact contDiffAt_const
    · exact contDiffAt_const
  have hPu : IsUnit (P x.crd).det := by
    simp [hP, det_fromBlocks_zero₂₁]
  have hP0 : ∀ η, mdbar P x.crd η = 0 := by
    intro η
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [hP]
    · simp only [hP, mdbar_apply, fromBlocks_apply₁₂, Matrix.zero_apply]
      rw [dbar_eq_zero ((htd i j).differentiableAt one_ne_zero)]
      rfl
    · simp [hP]
    · simp [hP]
  have hPt : ∀ᶠ v in 𝓝 x.crd, (P v).toBlocks₂₁ = 0 :=
    Eventually.of_forall fun v => by simp [hP]
  have hch := extTrace_chg hKs hKp hPs hPu hP0 hPt
  have heq : (fun v => chg (P v) (K v)) =ᶠ[𝓝 x.crd]
      fun v => fromBlocks (T.sub a (x.ch.symm v)) 0 0 (T.quot a (x.ch.symm v)) := by
    filter_upwards [hWn] with v hv
    exact htE _ hv.2
  have h0 : extTrace K x.crd = fun _ _ => 0 := by
    rw [← hch, extTrace_congr heq, extTrace_fromBlocks_zero]
  show ((ofValues (extTrace K x.crd) : Ev n) : Alt n) = 0
  rw [h0]
  simp [ofValues]

end GlobalTheory.BcUnique
