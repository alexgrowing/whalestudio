import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricDataComparePolarisedUpToFunction
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioDescendsDegenerationPsiFamily
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LiftThreeOverMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselSmoothSectionLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationRescaleEvenBimultExistsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PreLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_rescale_isPullDeg {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left) :
    ∃ (κ : D'.X → (FractionRing R')ˣ) (hD : IsPullDeg i D (GlobalTheory.PolDeg.rescale D' κ)), hD.W = W := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  choose u hu using GlobalTheory.FieldPull.exists_psi_ratio D' psi hpsi
  refine ⟨fun x => (u x)⁻¹, ?_⟩
  have eψ : ∀ x, psi x = (GlobalTheory.PolDeg.rescale D' fun x => (u x)⁻¹).psi x := fun x =>
    GlobalTheory.TorusExt.gen_ext_val D'.P.isLB (hpsi x) ((GlobalTheory.PolDeg.rescale D' fun x => (u x)⁻¹).psi_gen x)
      fun y J' hJ' => by
        refine Eq.trans ?_ (GlobalTheory.UU.val_scaleGen _ _ _ hJ').symm
        have h1 : unitOn (u x)⁻¹ * unitOn (u x) = 1 := (map_mul _ _ _).symm.trans
          ((congrArg unitOn (inv_mul_cancel (u x))).trans (map_one _))
        rw [hu x y J' hJ', GlobalTheory.TauTwist.unitAt_apply, ← _root_.mul_assoc, ← map_mul]
        erw [h1]
        rw [map_one, _root_.one_mul]
  have key : ∀ x, GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit)
      (fun _ => e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) w (D'.xK x) (-1) (psi x) (b x) := fun x jN jL => by
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, eψ x ▸ key x,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl⟩
  exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
    (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr

end GlobalTheory.PreLift

namespace GlobalTheory.PreLift

theorem exists_lift_c (R₁ R : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R]
    [IsDomain R] [IsLocalRing R] (hR₁ : IsAdicComplete (maximalIdeal R₁) R₁) (π : R₁ →+* R)
    (hπ : Function.Surjective π) (D : DegPre R) (P : PolAV (Sp R₁)) (i : D.P.A.left ⟶ P.A.left)
    (gp : IsGrpPullback D.P.A P.A (spMap π) i) :
    ∃ c : D.X → (𝟙_ (Over (Sp R₁)) ⟶ P.A), (∀ a b, c (a + b) = padd P.A (c a) (c b)) ∧
      ∀ x, (D.c x).left ≫ i = spMap π ≫ (c x).left := by
  letI := P.isAb.comm
  haveI := P.smoothDim
  have hsm : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g P.A.hom
  have hx₀ : ∀ x, ((D.c x).left ≫ i) ≫ P.A.hom = spMap π := fun x => by
    rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w]
    exact Category.id_comp _
  choose s hs₁ hs₂ using fun x => GlobalTheory.T.hensel_smooth_section_lift R₁ R hR₁ π hπ P.A hsm _ (hx₀ x)
  let sec : D.X → (𝟙_ (Over (Sp R₁)) ⟶ P.A) := fun x => Over.homMk (s x) (hs₁ x)
  let bs := Module.Free.chooseBasis ℤ D.X
  let f : D.X →ₗ[ℤ] Additive (𝟙_ (Over (Sp R₁)) ⟶ P.A) := bs.constr ℤ fun j => Additive.ofMul (sec (bs j))
  refine ⟨fun x => (f x).toMul, fun a b => ?_, ?_⟩
  · show Additive.toMul (f (a + b)) = _
    rw [map_add]; rfl
  let T := 𝟙_ (Over (Sp R))
  let q : Over.mk (T.hom ≫ spMap π) ⟶ 𝟙_ (Over (Sp R₁)) := Over.homMk (spMap π) (by
    show spMap π ≫ 𝟙 _ = 𝟙 _ ≫ spMap π
    rw [Category.comp_id, Category.id_comp])
  let h₁ : D.X → (Over.mk (T.hom ≫ spMap π) ⟶ P.A) := fun x =>
    Over.homMk ((D.c x).left ≫ i) ((hx₀ x).trans (Category.id_comp _).symm)
  let F₁ : D.X →+ Additive (Over.mk (T.hom ≫ spMap π) ⟶ P.A) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (h₁ x)) fun a b => by
      show h₁ (a + b) = h₁ a * h₁ b
      refine Over.OverMorphism.ext ?_
      rw [gp.2 T (D.c a) (D.c b) _ _ rfl rfl]
      show (D.c (a + b)).left ≫ i = _
      rw [D.c_add]
      rfl
  let F₂ : D.X →+ Additive (Over.mk (T.hom ≫ spMap π) ⟶ P.A) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (q ≫ (f x).toMul)) fun a b => by
      show q ≫ Additive.toMul (f (a + b)) = (q ≫ Additive.toMul (f a)) * (q ≫ Additive.toMul (f b))
      rw [map_add, toMul_add, MonObj.comp_mul]
  have hF : F₁ = F₂ := by
    refine AddMonoidHom.toIntLinearMap_injective (bs.ext fun j => ?_)
    show Additive.ofMul (h₁ (bs j)) = Additive.ofMul (q ≫ Additive.toMul (f (bs j)))
    have e : f (bs j) = Additive.ofMul (sec (bs j)) := bs.constr_basis ℤ _ j
    rw [e]
    refine congrArg Additive.ofMul (Over.OverMorphism.ext ?_)
    exact (hs₂ (bs j)).symm
  intro x
  have := congrArg (fun φ => (Additive.toMul (φ x)).left) hF
  exact this

end GlobalTheory.PreLift

namespace GlobalTheory.PreLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ

theorem prelift : ∀ (R₁ R : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R] [IsDomain R] [IsLocalRing R], IsAdicComplete (maximalIdeal R₁) R₁ → ∀ π : R₁ →+* R, Function.Surjective π → ∀ (D : DegPre R) (P : PolAV (Sp R₁)) (i : D.P.A.left ⟶ P.A.left), IsGrpPullback D.P.A P.A (spMap π) i → LBIso D.P.L (P.L.pull i) → ∃ (D₁ : DegPre R₁) (κ : D.X → (FractionRing R)ˣ) (h : IsPullDeg π D₁ (GlobalTheory.PolDeg.rescale D κ)), h.W = ⊤ ∧ D₁.PsiEven ∧ D₁.TauBimult := by
  intro R₁ R _ _ _ _ _ _ _ hR₁ π hπ D P i gp hL
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (GlobalTheory.T.all_six_abelian_scheme_laws_hold.1.cube _ P ⟨P.L, rig, P.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := GlobalTheory.SelfUnif.exists_sym P
  obtain ⟨c, cadd, hc⟩ := exists_lift_c R₁ R hR₁ π hπ D P i gp
  choose psi hpsi using fun x : D.X => GlobalTheory.SS.HtForm.gen_field _
    (DVR.linComb_isLB P.L P.isLB (K := PUnit) (fun _ => ptK (c x)) (fun _ => -1))
  let E : DegPre R₁ :=
    { P := P, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D.X,
      c := c, c_add := cadd, psi := psi, psi_gen := hpsi }
  obtain ⟨g, hev, htb, ⟨ψW⟩⟩ := GlobalTheory.T.degeneration_rescale_even_bimult_exists R₁ E
  obtain ⟨w₀, hw₀⟩ := hL
  have he : eSec D.P.A ≫ i = spMap π ≫ eSec P.A := (cubeMapOf gp).e_comm
  have hσ : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A]
  obtain ⟨w, hw, hr⟩ := GlobalTheory.UnifPreCompare.exists_rigidified P.isLB D.P.isLB D.P.A.hom (eSec D.P.A) hσ w₀ hw₀
    D.rig D.rig_gen (φ := eSec P.A) rig hrig (spMap π) he
  let gg : (TK R).left ⟶ (TW (⊤ : (Sp R₁).Opens)).left := (jK R ≫ specOf π) ≫ (Sp R₁).topIso.inv
  have hg : gg ≫ (⊤ : (Sp R₁).Opens).ι = jK R ≫ specOf π := by
    rw [Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨κ, hD, hW⟩ := exists_rescale_isPullDeg (i := π) (GlobalTheory.PolDeg.rescale E g) D ψW gg hg (Φ := i) gp w
    ((isGen_iff w).1 hw) hr (AddEquiv.refl _) hc
  exact ⟨GlobalTheory.PolDeg.rescale E g, κ, hD, hW, hev, htb⟩

end GlobalTheory.PreLift
