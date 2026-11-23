import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleSectionsAvoidClosedPoints
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

namespace GlobalTheory.FibreProj

theorem pol_topSelf_comb_pull : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (κ : Type) [Field κ] (Z : Scheme.{0}) [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ Z) → ∀ (ι : Type) [Fintype ι] (D : ℕ), Fintype.card ι = D → topologicalKrullDim Z ≤ D → ∀ (i : Z ⟶ X) (N : ι → HermLB p), pol (fun n : ι → ℤ => (topSelfIntersection κ ((comb N n).B.pull i) D : ℝ)) = D.factorial * (interNum κ (structureModule Z) (fun a => (N a).B.pull i) : ℝ) := by
  intro k _ X p κ _ Z _ hp ι _ D hcard hdim i N
  classical
  have HD := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom κ Z) (structureModule Z) hp (d := D)
    (by rw [QCoh.suppDim_structureModule]; exact hdim)
  have hL : ∀ a, ((N a).B.pull i).IsLB := fun a => LB.isLB_pull (N a).isLB i
  let c : ι → CechPic.Pic Z := fun a => CechPic.cls ((N a).B.pull i) (hL a)
  let g : (ι → ℤ) →+ CechPic.Pic Z := AddMonoidHom.mk' (fun n => ∑ a, n a • c a) fun u v => by
    simp [add_smul, Finset.sum_add_distrib]
  have hg (a : ι) : g (Pi.single a 1) = c a := by
    simp [g, Pi.single_apply, Finset.sum_ite_eq']
  have key : (fun n : ι → ℤ => (topSelfIntersection κ ((comb N n).B.pull i) D : ℝ)) =
      (Int.castAddHom ℝ) ∘ ((fun y => HD.form fun _ => y) ∘ g) := by
    funext n
    rw [topSelf_def, ← HD.form_cls (P := fun _ => (comb N n).B.pull i) (fun _ => LB.isLB_pull (comb N n).isLB i)]
    simp only [Function.comp_apply, Int.coe_castAddHom]
    congr 2
    funext j
    rw [CechPic.cls_pull (comb N n).isLB, GenFibreSecs.cls_comb, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_zsmul]
    simp only [c]
    rw [CechPic.cls_pull (N a).isLB]
  let e : Fin D ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  have h₁ := congrFun (multiDiff_comap g (fun a => (Pi.single a 1 : ι → ℤ)) (fun y => HD.form fun _ => y)) 0
  have h₂ := congrFun (multiDiff_map (Int.castAddHom ℝ) (fun a => (Pi.single a 1 : ι → ℤ))
    ((fun y => HD.form fun _ => y) ∘ g)) 0
  rw [key, pol_eq_multiDiff]
  refine h₂.trans ?_
  have hc : (g ∘ fun a => (Pi.single a 1 : ι → ℤ)) = c := funext hg
  rw [Function.comp_apply, h₁, Function.comp_apply, hc, ← multiDiff_comp_equiv e, HD.multiDiff_form_diag,
    show c ∘ e = fun j => CechPic.cls ((N (e j)).B.pull i) (hL (e j)) from rfl, HD.form_cls (P := fun j => (N (e j)).B.pull i) (fun j => hL (e j)),
    ← interNum_comp_equiv κ (structureModule Z) (L := fun a => (N a).B.pull i) hL e]
  simp [Function.comp_def]

end GlobalTheory.FibreProj
