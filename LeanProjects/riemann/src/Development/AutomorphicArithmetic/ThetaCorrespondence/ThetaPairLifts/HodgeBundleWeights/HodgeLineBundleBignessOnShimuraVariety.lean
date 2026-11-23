import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleHodgeClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IsNefHodgeBundleUnitWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleHodgeClassStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option autoImplicit false
namespace GlobalTheory.HodgeBig
theorem hodgeLineBundle_isBig : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p → 1 ≤ Dw.q → FnAlgClosed Xo c → ∀ (δ : LB (X₀ TF.Y Z)) (hδ : δ.IsLB), CechPic.pull (π₀ TF.X Z) (cls δ hδ) = cls (L₀ TF.X Z (hodgeWt Dw)) (isLB_L₀ TF.X Z _) → letI := algebraΓOfHom (s₀ TF.Y Z); IsBig c.F δ := by
  intro hP _ _ hS hK E _ _ _ H Dw l Xo c TF Z _ _ hF δ hδ hpull
  classical
  obtain ⟨ω, hω, e, hdom⟩ := HodgeDominates.exists_lb_dominates hP.p22 hS hK.toroidalChartsForFan TF
  obtain ⟨_, -, hproj, -, hsurj, -⟩ := GlobalTheory.BaseVar.isVariety_barComp E H Dw l Xo c TF Z hF
  have hprojY : IsProjOver (str₀ TF.X Z) := (GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF).2.1
  have hN := hP.q7
  let χ : AllWt.Weight Dw := fun _ i => if (i : ℕ) < Dw.p then (1 : ℤ) else -1
  have hB : (ω.pull (barComp TF.Y Z).ι).IsLB := pull_isLB hω _
  have hBp : CechPic.pull (π₀ TF.X Z) (cls _ hB) = cls (L₀ TF.X Z χ) (isLB_L₀ TF.X Z _) := by
    rw [cls_pull hω _ hB, ← CechPic.pull_comp, morphismRestrict_ι, CechPic.pull_comp, ← e]
    exact (cls_pull (TF.X.isLB_Llam _) _ _).symm
  let C := common₀ TF.X Z
  let φ := AddMonoidHom.mk' (fun a => cls (L₀ TF.X Z a) (C.isLB a)) (cls_common_add C)
  have hφ : ∀ a, cls (L₀ TF.X Z a) (isLB_L₀ TF.X Z a) = φ a := fun _ => rfl
  let w : AllWt.Weight Dw := ∑ τ : Psi H, NefWt.unitWt τ (-1)
  have ew : 2 • hodgeWt Dw - χ = w := by
    funext τ i
    simp only [w, Finset.sum_apply, NefWt.unitWt_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply,
      Pi.smul_apply, hodgeWt, CompHt.barWt, χ, smul_eq_mul]
    split_ifs <;> norm_num
  have hwnef : (letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z w)) := by
    letI := algebraΓOfHom (str₀ TF.X Z)
    obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hprojY
    refine IsNef.of_cls_eq_sum Finset.univ
      (fun τ : Psi H => (_root_.GlobalTheory.NefUnit.isNef_hodgeBundle_unitWeight (_root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems.toClassicalTheorems hP) hN E H Dw l Xo c TF Z hF τ).2) (fun _ => 1) hA
      (isLB_L₀ TF.X Z w) ?_
    rw [hφ, map_sum]
    exact Finset.sum_congr rfl fun τ _ => (one_smul _ _).symm
  letI := algebraΓOfHom (s₀ TF.Y Z)
  have hf : ∀ r : c.F, algebraMap c.F Γ(X₀ TF.Y Z, ⊤) r =
      (s₀ TF.Y Z).appTop ((Scheme.ΓSpecIso (.of c.F)).inv r) := fun _ => rfl
  have hp' : IsProjOver (strHom c.F (X₀ TF.Y Z)) := by rw [strHom_eq hf]; exact hproj
  have h2 := isLB_lbPow hδ 2
  have hNl := LB.isLB_div h2 hB
  have hNp : CechPic.pull (π₀ TF.X Z) (cls _ hNl) = cls (L₀ TF.X Z w) (isLB_L₀ TF.X Z _) := by
    rw [cls_div h2 hB hNl, map_sub, cls_lbPow hδ 2 h2, map_nsmul, hpull, hBp, hφ, hφ, hφ, ← ew, map_sub, map_nsmul]
  have hNnef : IsNef c.F (LB.div (lbPow δ 2) (ω.pull (barComp TF.Y Z).ι)) :=
    GlobalTheory.NefDescent.isNef_of_pull c.F _ _ (π₀ TF.X Z) (s₀ TF.Y Z) (str₀ TF.X Z) _ hNl _
      (isLB_L₀ TF.X Z w) (π₀_s₀ TF.X Z) hproj hprojY hsurj hNp hwnef
  have : IsProper (s₀ TF.Y Z) := ThetaDescent.isProper_of_isProjOver hproj
  have : CompactSpace (X₀ TF.Y Z) := QuasiCompact.compactSpace_of_compactSpace (s₀ TF.Y Z)
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver TF.Y.proj
  have hA₀ : IsAmpleLB (A.pull (barComp TF.Y Z).ι) := hA.pull_of_isOpenImmersion _
  have hw : TF.Y.j (genPt Z) ∈ barComp TF.Y Z := (j_mem_barComp Z _).2 (CompSplitPfB.cspB_genPt_mem Z)
  obtain ⟨m, hm, s, hs⟩ := hdom (genPt Z) A hA.isLB
  have hD := LB.isLB_div (isLB_lbPow hω m) hA.isLB
  have ht : (⟨_, hw⟩ : X₀ TF.Y Z) ∈ nonzeroLocus (lbSecPull _ s (barComp TF.Y Z).ι) := by
    rw [HodgeDominates.nonzeroLocus_lbSecPull]
    exact hs
  have hNm := hNnef.pow hA₀ m
  have hbig := hNm.isBig_tens_ample hN hp' hA₀
  have hδm : IsBig c.F (lbPow δ (2 * m)) :=
    hbig.of_cls_eq_add hf hproj (pull_isLB hD _) ⟨_, sec_ne_zero_of_mem ht⟩ (isLB_lbPow hδ _) (by
      rw [cls_tens hNm.isLB hA₀.isLB, cls_lbPow hNl, cls_div h2 hB hNl, cls_lbPow hδ, cls_lbPow hδ, cls_pull hω,
        cls_pull hA.isLB, cls_pull hD, cls_div (isLB_lbPow hω m) hA.isLB, cls_lbPow hω, map_sub, map_nsmul,
        smul_sub, mul_comm, mul_smul]
      abel)
  exact hδm.of_pow hδ (by omega) fun n => finite_coh_zero_twist_of_isProjOver hf hproj (isLB_lbPow hδ n)
end GlobalTheory.HodgeBig
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeLineBundle_bigness_on_shimuraVariety : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p → 1 ≤ Dw.q → FnAlgClosed Xo c → ∀ (δ : LB (X₀ TF.Y Z)) (hδ : δ.IsLB), CechPic.pull (π₀ TF.X Z) (cls δ hδ) = cls (L₀ TF.X Z (hodgeWt Dw)) (isLB_L₀ TF.X Z _) → letI := algebraΓOfHom (s₀ TF.Y Z); IsBig c.F δ := by
  first | exact @_root_.GlobalTheory.HodgeBig.hodgeLineBundle_isBig | exact _root_.GlobalTheory.HodgeBig.hodgeLineBundle_isBig | (intros; apply _root_.GlobalTheory.HodgeBig.hodgeLineBundle_isBig <;> assumption)
end
