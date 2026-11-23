import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem nonempty_psiOn_field {K : Type} [Field K] (D : DegPre K) : Nonempty (PsiOn D ⊤) := by
  refine nonempty_psiOn_top D fun χ => (psiUnitOn_univ_iff D χ).2 ?_
  let σ : FractionRing K ≃+* K := (FractionRing.algEquiv K K).toRingEquiv
  let s : Sp K ⟶ (TK K).left := spMap σ.toRingHom
  have h₁ : s ≫ jK K = 𝟙 _ := by
    refine (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun x => ?_)).trans (Spec.map_id (CommRingCat.of K)))
    exact (FractionRing.algEquiv K K).commutes x
  have h₂ : jK K ≫ s = 𝟙 _ := by
    refine (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun x => ?_)).trans (Spec.map_id (CommRingCat.of (FractionRing K))))
    exact (FractionRing.algEquiv K K).injective ((FractionRing.algEquiv K K).commutes _)
  obtain ⟨t, ht, vt⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => ((D.c χ).left : Sp K ⟶ _)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (by
      show s ≫ jK K ≫ (D.c χ).left = _
      rw [← Category.assoc, h₁, Category.id_comp]))
    (LB.pullGen D.P.L _ _ (D.psi χ) s) (DVR.pullGen_isGen _ _ _ _ (D.psi_gen χ) s)
  refine ⟨t, ht, corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (val_pull hJ _ _ _).trans ((vt _ _ y J hJ).trans ((val_pull hJ _ _ _).trans ?_))
  exact congrArg (fun q => val (D.psi χ) q y J) ((Category.assoc _ _ _).trans
    ((congrArg (𝟙 _ ≫ ·) h₂).trans (Category.id_comp _)))

theorem exists_isPullDeg_of_val {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK K).left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) (genMap i.injective) z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ ∧ hD.xe = xe ∧ HEq hD.w w := by
  obtain ⟨ψW⟩ := nonempty_psiOn_field D
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨g, hg⟩ : ∃ g : (TK K).left ⟶ (TW (⊤ : (Sp K₀).Opens)).left, g ≫ (⊤ : (Sp K₀).Opens).ι = jK K ≫ specOf i :=
    ⟨IsOpenImmersion.lift (⊤ : (Sp K₀).Opens).ι (jK K ≫ specOf i) (by
      rw [Scheme.Opens.range_ι]; exact Set.subset_univ _), IsOpenImmersion.lift_fac _ _ _⟩
  have sq : g ≫ (⊤ : (Sp K₀).Opens).ι = genMap i.injective ≫ jK K₀ :=
    hg.trans ((Category.id_comp _).symm.trans (fracMap_sq i.injective))
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK K).left ⟶ (jK K₀ ⁻¹ᵁ ⊤).toScheme, lam ≫ (jK K₀ ⁻¹ᵁ ⊤).ι = genMap i.injective ∧
      lam ≫ (jK K₀ ∣_ ⊤) = g :=
    ⟨(isPullback_morphismRestrict (jK K₀) ⊤).lift _ _ sq,
      (isPullback_morphismRestrict (jK K₀) ⊤).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK K₀) ⊤).lift_fst _ _ _⟩
  have hx : ∀ x, g ≫ (toUnit (TW ⊤) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ (⊤ : (Sp K₀).Opens).ι ≫ (D.c (xe x)).left = (jK K ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))
    rw [l₁, l₂, hψ x y J J' hJ hJ'] at u
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, ⊤, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, rfl, HEq.rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

theorem pmaps_rig {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
    {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    PMaps hD.w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap φ) :=
  (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
    (rigPull_le (proj hD) (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig

end GlobalTheory.FieldPull
end
