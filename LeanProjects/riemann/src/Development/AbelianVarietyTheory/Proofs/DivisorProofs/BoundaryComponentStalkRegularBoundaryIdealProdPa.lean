import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapCompStalkAlg
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
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

theorem GlobalTheory.LogKSDiv.boundary_germ_snc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1), x ∉ (j₀ TF.Y Z).opensRange → IsRegularLocalRing ((X₀ TF.Y Z).presheaf.stalk x) ∧ ∃ (n : ℕ) (f : Fin n → (X₀ TF.Y Z).presheaf.stalk x) (J : Finset (Fin n)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp ((X₀ TF.Y Z).presheaf.stalk x) n f ∧ J.Nonempty ∧ Ideal.map (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx) ((Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U) = Ideal.span {∏ i ∈ J, f i} := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hx hnot
  classical
  obtain ⟨hreg, V, hyV, n, f', J, hrsp, hV⟩ := TF.snc ((barComp TF.Y Z).ι x)
  let φ : TF.Y.X.presheaf.stalk ((barComp TF.Y Z).ι x) ≃+* (X₀ TF.Y Z).presheaf.stalk x :=
    (asIso ((barComp TF.Y Z).ι.stalkMap x)).commRingCatIsoToRingEquiv
  have hφ : ∀ a, φ a = ((barComp TF.Y Z).ι.stalkMap x).hom a := fun _ => rfl
  refine ⟨IsRegularLocalRing.of_ringEquiv φ, n, fun i => φ (TF.Y.X.presheaf.germ V.1 _ hyV (f' i)), J, ?_, ?_, ?_⟩
  · obtain ⟨hspan, hdim⟩ := hrsp
    refine ⟨?_, hdim.trans (ringKrullDim_eq_of_ringEquiv φ)⟩
    have hr : Set.range (fun i => φ (TF.Y.X.presheaf.germ V.1 _ hyV (f' i))) =
        φ '' Set.range (fun i => TF.Y.X.presheaf.germ V.1 _ hyV (f' i)) := Set.range_comp _ _
    rw [hr, ← Ideal.map_span, hspan]
    exact (IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv φ))
  · rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hnot
    rw [Finset.prod_empty, Ideal.span_singleton_one] at hV
    have hst : ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (LogKS.boundary TF.Y) ((barComp TF.Y Z).ι x) = ⊤ := by
      rw [ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ V _ hyV, hV, Ideal.map_top]
    have hns := (ReciprocityTheory.AnForm.R.mem_support_iff_stalkId (LogKS.boundary TF.Y) ((barComp TF.Y Z).ι x)).not.mpr
      (not_not.mpr hst)
    rw [LogKS.boundary, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hns
    have hin : (barComp TF.Y Z).ι x ∈ LogKS.interior TF.Y := by
      simpa using hns
    rw [LogKS.interior] at hin
    obtain ⟨z, hz⟩ := hin
    have hzB : z ∈ TF.Y.j ⁻¹ᵁ barComp TF.Y Z := by
      show TF.Y.j z ∈ barComp TF.Y Z
      rw [hz]; first | exact x.2 | simp | exact (barComp TF.Y Z).range_ι.le ⟨x, rfl⟩
    refine ⟨⟨z, hzB⟩, (barComp TF.Y Z).ι.isOpenEmbedding.injective ?_⟩
    have h2 := congrArg (fun f => f.base ⟨z, hzB⟩) (j₀_ι TF.Y Z)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
    first | exact h2.trans hz | (refine Eq.trans ?_ hz; exact h2) | (rw [Scheme.Hom.comp_apply] at h2; exact h2.trans hz)
  · have e1 : Ideal.map (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx)
        ((Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U) =
        Ideal.map (φ : _ →+* _) (Ideal.map (TF.Y.X.presheaf.germ U.1 _ hx).hom
          ((Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U)) := by
      rw [Ideal.map_map]
      congr 1
      ext r
      simp only [GlobalTheory.LogKSDiv.stalkHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hφ]
      rw [Scheme.Hom.germ_stalkMap_apply]
    have hVb : (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal V =
        Ideal.span {∏ i ∈ J, f' i} := hV
    rw [e1, ← ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ U _ hx, ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ V _ hyV, hVb,
      Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_prod]
    rw [map_prod]
    rfl
