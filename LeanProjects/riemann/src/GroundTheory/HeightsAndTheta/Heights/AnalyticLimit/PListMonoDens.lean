import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureA
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMonoDens
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Topology
open scoped ComplexOrder Matrix
open ReciprocityTheory.AnForm (levi hessC maDens)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens)

theorem ListMonoDens.proof : ListMonoDens.Statement := by
  intro D X _ A Yo th Om u hYo hth hOm hu hle hnn j y hy hyY
  set p := (A.chart j).symm y with hp

  set f : Fin D → (Fin D → ℂ) → ℝ := fun i y' => (th i).φ p ((A.chart j).symm y') with hf
  set v : Fin D → (Fin D → ℂ) → ℝ := fun i y' => u i ((A.chart j).symm y') with hv
  set o : (Fin D → ℂ) → ℝ := fun y' => Om.φ p ((A.chart j).symm y') with ho
  have hfC : ∀ i, ContDiffAt ℝ 2 (f i) y := fun i =>
    ReciprocityTheory.AnForm.M.pot_contDiffAt_two (hth i) p j hy ((th i).mem_U p)
  have hoC : ContDiffAt ℝ 2 o y :=
    ReciprocityTheory.AnForm.M.pot_contDiffAt_two hOm p j hy (Om.mem_U p)
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Yo) :=
    (A.chart j).isOpen_inter_preimage_symm hYo
  have hvC : ∀ i, ContDiffAt ℝ 2 (v i) y := fun i =>
    ((hu i j).contDiffAt (hopen.mem_nhds ⟨hy, hyY⟩)).of_le (by first | simp | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.mpr le_top)
  have hgC : ∀ i, ContDiffAt ℝ 2 (fun y' => o y' + (-1) * f i y') y := fun i =>
    hoC.add (contDiffAt_const.mul (hfC i))

  have hA : ∀ i, (hessC (fun y' => f i y' + v i y') y).PosSemidef := fun i =>
    ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi _ y ((hfC i).add (hvC i)) fun w =>
      hnn i p j y ⟨hy, hyY, (th i).mem_U p, Set.mem_univ _⟩ w

  have hB : ∀ i, (hessC (fun y' => o y' + (-1) * f i y') y).PosSemidef := fun i => by
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi _ y (hgC i)
      fun w => ?_
    rw [ReciprocityTheory.AnForm.levi_add_smul (-1) hoC (hfC i) w]
    have h := hle i p j y ⟨hy, ⟨⟨Set.mem_univ _, (th i).mem_U p⟩, Om.mem_U p⟩⟩ w
    have h' : 1 * levi (f i) y w ≤ 1 * levi o y w := h
    linarith

  have hsum : ∀ i, hessC (fun y' => o y' + v i y') y =
      hessC (fun y' => f i y' + v i y') y + hessC (fun y' => o y' + (-1) * f i y') y := fun i => by
    rw [← ReciprocityTheory.AnForm.A.hessC_add _ _ y ((hfC i).add (hvC i))
      (hgC i)]
    congr 1
    funext y'
    ring
  have e1 : locDens A (fun i => potForm (th i) (u i)) j y =
      maDens (fun i y' => f i y' + v i y') y := rfl
  have e2 : locDens A (fun i => potForm Om (u i)) j y = maDens (fun i y' => o y' + v i y') y := rfl
  rw [e1, e2]
  refine ⟨ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y hA, ?_⟩
  unfold maDens
  refine mul_le_mul_of_nonneg_left (ReciprocityTheory.AnForm.A.mdisc_re_mono _ _ hA fun i => ?_) (by positivity)
  simpa [hsum i] using hB i

end GroundTheory.Heights₂.Heights.AnalyticLimit
