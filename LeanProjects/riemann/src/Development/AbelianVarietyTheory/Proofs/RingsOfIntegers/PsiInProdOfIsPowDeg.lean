import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPowDeg

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiInProd

theorem map_ideal_prod {A B K : Type} [CommRing A] [CommRing B] [Fintype K] (f : A →+* B) (J : K → Ideal A) :
    (∏ i, J i).map f = ∏ i, (J i).map f :=
  map_prod (Ideal.mapHom f) J Finset.univ

end PsiInProd

open PsiInPull PsiInPow PsiInProd in

theorem psiIn_prod_of_isPowDeg : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R)
    (pD : IsPowDeg D' D j) (x : D'.X) (J : Fin j → Ideal R),
    (∀ i, D.PsiIn (pD.xe x i) (J i)) → D'.PsiIn x (∏ i, J i) := by
  intro R _ _ j D D' pD χ J H
  classical
  refine psiIn_of_gs D' χ _ fun q V' hV' hle' z hz => exists_of_locally _ z _ V' hV' hz fun v hv => ?_
  have : IsDominant (jK R) := isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ D.P.A.left => exists_chart D.P.isLB (p v)
  have hcp : ∀ i, (D'.c χ).left ≫ (pD.pw.pr i).left = (D.c (pD.xe χ i)).left := fun i =>
    congrArg (fun m => m.left) (pD.c_pr χ i)
  have hxp : ∀ i, D'.xK χ ≫ (pD.pw.pr i).left = D.xK (pD.xe χ i) := fun i =>
    (Category.assoc (jK R) _ _).trans (congrArg (jK R ≫ ·) (hcp i))
  let p : Fin j → D.P.L.ι := fun i => pick (D.c (pD.xe χ i)).left
  obtain ⟨_, ⟨V, hV, rfl⟩, hvV, hVp⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
    (show v ∈ (V' ⊓ LB.wchart D.P.L (fun i => (D.c (pD.xe χ i)).left) p : (Spec (CommRingCat.of R)).Opens) from
      ⟨hv, Set.mem_iInter.2 fun i => hpk _⟩)
    (V' ⊓ LB.wchart D.P.L (fun i => (D.c (pD.xe χ i)).left) p : (Spec (CommRingCat.of R)).Opens).isOpen
  have hVV : V ≤ V' := fun y hy => (hVp hy).1
  have hVi : ∀ i, V ≤ (D.c (pD.xe χ i)).left ⁻¹ᵁ D.P.L.U (p i) := fun i y hy => Set.mem_iInter.1 (hVp hy).2 i
  have hzV : jK R z ∈ V := jK_mem z _ (fun h0 => (h0.le hvV : v ∈ (⊥ : (Spec (CommRingCat.of R)).Opens)))
  choose r hr er using fun i => gs_of_psiIn D _ _ (H i) (p i) V hV (hVi i) z hzV
  obtain ⟨I, hI, eI⟩ := exists_good D.P.L D.P.isLB (Z := (TK R).left) z (fun i => D.xK (pD.xe χ i)) p
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R)) D.P.A.hom
      ((Over.w (D.c (pD.xe χ a))).trans (Over.w (D.c (pD.xe χ b))).symm) (jK R) h))
    (fun i => hVi i hzV)
  obtain ⟨I', hI', eI'⟩ := exists_good D'.P.L D'.P.isLB (Z := (TK R).left) z (K := PUnit) (fun _ => D'.xK χ)
    (fun _ => q) (fun _ _ _ => rfl) (fun _ => hle' hz)
  have e0 : I' (D'.xK χ) = q := eI' PUnit.unit
  obtain ⟨b, hb, hcorr⟩ := pD.w_psi χ
  have e1 := QBox.mapsAt_val pD.w _ _ _ b hb z hI hI'
  have e2 := (val_corr hI hcorr (𝟙 _)).trans (QBox.val_finProdGen _ _ _ _ _ hI)
  have ep : (fun i => I (D'.xK χ ≫ (pD.pw.pr i).left)) = p := funext fun i => (congrArg I (hxp i)).trans (eI i)
  rw [ep, e0, zpow_neg_one, eq_inv_mul_iff_mul_eq, e2,
    val_of (D'.psi χ) _ z I' (fun _ => q) (fun _ => (congrArg I' (Category.id_comp _)).trans e0)] at e1
  have hU : V ≤ (D'.c χ).left ⁻¹ᵁ (LB.wchart D.P.L (fun i => (pD.pw.pr i).left) p ⊓ D'.P.L.U q) := fun y hy =>
    ⟨Set.mem_iInter.2 fun i => (congrArg (fun m => m y ∈ D.P.L.U (p i)) (hcp i)).mpr (hVi i hy), hle' (hVV hy)⟩
  refine ⟨V, hVV, hvV, (res hU (pullU (D'.c χ).left _ (pD.w.s (p, q)))).val * ∏ i, r i,
    Ideal.mul_mem_left _ _ ?_, ?_⟩
  · rw [map_ideal_prod]
    exact Ideal.prod_mem_prod fun i _ => hr i
  · refine Eq.trans ?_ (congrArg Units.val e1)
    refine (gs_mul _ _ _ hzV _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · exact (gs_unit _ _ _ hzV _).trans (congrArg Units.val ((gm_res _ _ hU hzV _).trans
        (gm_pull (jK R) (D'.c χ).left z _ (hU hzV) _)))
    · rw [gs_prod _ _ _ hzV, Units.coe_prod]
      refine Finset.prod_congr rfl fun i _ => (er i).trans (congrArg Units.val ?_)
      exact (val_of (D.psi (pD.xe χ i)) _ z I (fun _ => p i) (fun _ => (congrArg I (Category.id_comp _)).trans (eI i))).symm

end GlobalTheory
