import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeriodicSecAlg

open GlobalTheory.CxPts GlobalTheory.HolUnifSec

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ (M : LB A.left), M.IsLB → ∀ σ : M.ι → (Fin g → ℂ) → ℂ, (∀ i, DifferentiableOn ℂ (σ i) (pre u.ex (M.U i))) →
    (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (M.U i), σ i (z + l) = σ i z) →
    (∀ i j, ∀ z ∈ pre u.ex (M.U i ⊓ M.U j), σ i z = val u.ex _ (M.g i j).val z * σ j z) →
    ∀ i, IsReg u.ex (M.U i) (σ i) := by
  intro A _ g L u hA M hM σ hσ hper hcomp
  classical
  have := hA.comm
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  obtain ⟨D, hD⟩ := AbelianDim.exists_relDim ℂ A hA
  let r := Function.surjInv (pt_surjective u)
  have hr : ∀ y, pt u (r y) = y := Function.surjInv_eq (pt_surjective u)
  let s : M.ι → CxPts A.hom (RingHom.id ℂ) → ℂ := fun i y =>
    if y ∈ ptsIn _ _ (M.U i) then σ i (r y) else 0
  have hs : ∀ i z, pt u z ∈ ptsIn _ _ (M.U i) → s i (pt u z) = σ i z := fun i z hz => by
    have := hper i ⟨_, sub_mem_of_pt_eq u (hr (pt u z))⟩ z hz
    simp only [add_sub_cancel] at this
    exact (if_pos hz).trans this
  have hmem : s ∈ (AnRead.all A.hom (RingHom.id ℂ) D).holSec M := by
    refine ⟨⟨fun i j y hi hj => ?_, fun i y h => if_neg h⟩, fun i => holoOn_of_comp u _ (isOpen_ptsIn _) ?_⟩
    · obtain ⟨z, rfl⟩ := pt_surjective u y
      have hij : pt u z ∈ ptsIn _ _ (M.U i ⊓ M.U j) := mem_ptsIn_inf.2 ⟨hi, hj⟩
      have e : σ i z = gv _ _ M i j (pt u z) * σ j z := hcomp i j z hij
      rw [hs i z hi, hs j z hj, e]
    · exact (hσ i).congr fun z hz => hs i z hz
  obtain ⟨τ, hτ⟩ := (GlobalTheory.Published.serreHolomorphicSections_holds A.left A.hom D hD hp _ M hM).2 ⟨s, hmem⟩
  intro i
  exact ⟨τ.f i, fun z hz => ((congrFun₂ (congrArg Subtype.val hτ) i (pt u z)).trans (hs i z hz)).symm⟩

end GlobalTheory.PeriodicSecAlg
