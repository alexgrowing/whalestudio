import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Semi CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiUnitOfPsiOn

theorem injective_of_isIso {A B : CommRingCat} (f : A ⟶ B) [IsIso f] : Function.Injective f.hom := by
  intro a b e
  have := congrArg (inv f).hom e
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply,
    CommRingCat.id_apply] at this

theorem mem_wchart1 {Y B : Scheme.{0}} (M : LB B) (φ : Y ⟶ B) (z : Y) (i : M.ι) (hz : φ z ∈ M.U i) :
    z ∈ LB.wchart M (fun _ : PUnit => φ) (fun _ => i) := Set.mem_iInter.2 fun _ => hz

theorem psiUnitOn_of_psiOn : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens), PsiOn D W → ∀ y : D.X, PsiUnitOn D y (W : Set (Spec (CommRingCat.of R))) := by
  intro R _ _ D W ψ y j V _ hVW hj h
  obtain ⟨p, rfl⟩ : ∃ p, j = fun _ => p := ⟨j PUnit.unit, funext fun _ => rfl⟩
  have hle : W.ι ⁻¹ᵁ V ≤ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c y).left) (fun _ => p) :=
    fun z hz => mem_wchart1 _ _ _ _ (hj hz)
  have hVr : V ≤ W.ι.opensRange := by rw [Scheme.Opens.opensRange_ι]; exact hVW
  haveI := W.ι.isIso_app V hVr
  set u : Γ(W.toScheme, W.ι ⁻¹ᵁ V)ˣ := res hle ((ψ.psi y).s (fun _ => p)) with hu
  set r : Γ(Spec (CommRingCat.of R), V) := (inv (W.ι.app V)).hom u.val with hr
  have hr' : (W.ι.app V).hom r = u.val := by
    rw [hr, ← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
  refine ⟨r, u.isUnit.map (inv (W.ι.app V)).hom, ?_⟩
  have hKr : jK R ⁻¹ᵁ V ≤ (jK R ⁻¹ᵁ W).ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]; exact fun z hz => hVW hz
  haveI := (jK R ⁻¹ᵁ W).ι.isIso_app (jK R ⁻¹ᵁ V) hKr
  apply injective_of_isIso ((jK R ⁻¹ᵁ W).ι.app (jK R ⁻¹ᵁ V))
  apply fn_ext
  intro z hz
  have hι : (jK R ∣_ W) ≫ W.ι = (jK R ⁻¹ᵁ W).ι ≫ jK R := morphismRestrict_ι _ _
  have hzV : jK R ((jK R ⁻¹ᵁ W).ι z) ∈ V := hz
  have hpt : W.ι ((jK R ∣_ W) z) = jK R ((jK R ⁻¹ᵁ W).ι z) := congrArg (fun q => q z) hι
  have hm : (jK R ∣_ W) z ∈ W.ι ⁻¹ᵁ V := by
    show W.ι ((jK R ∣_ W) z) ∈ V
    rw [hpt]; exact hzV
  have h₁ : (𝟙 _ : (jK R ⁻¹ᵁ W).toScheme ⟶ _) z ∈
      LB.wchart D.P.L (fun _ : PUnit => (jK R ∣_ W) ≫ (toUnit (TW W) ≫ D.c y).left) (fun _ => p) :=
    mem_wchart1 _ _ _ _ (hj hm)
  have h₂ : (𝟙 _ : (jK R ⁻¹ᵁ W).toScheme ⟶ _) z ∈
      LB.wchart D.P.L (fun _ : PUnit => (jK R ⁻¹ᵁ W).ι ≫ D.xK y) (fun _ => p) :=
    mem_wchart1 _ _ _ _ (hj hzV)
  have e₃ := (gm_pullGen D.P.L _ _ (ψ.psi y) (jK R ∣_ W) (𝟙 _) z (fun _ => p) h₁).symm.trans
    ((gm_corr D.P.L (ψ.psi_eq y) (𝟙 _) z p h₁ h₂).trans
      (gm_pullGen D.P.L _ _ (D.psi y) (jK R ⁻¹ᵁ W).ι (𝟙 _) z (fun _ => p) h₂))
  rw [Category.id_comp, Category.id_comp] at e₃
  have l₁ := gs_pull (𝟙 _) (jK R ⁻¹ᵁ W).ι z (jK R ⁻¹ᵁ V) hz ((jK R).app V |>.hom r)
  have l₂ := gs_pull (𝟙 _) (jK R ⁻¹ᵁ W).ι z (jK R ⁻¹ᵁ V) hz
    (((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi y).s (fun _ => p)).val)
  rw [Category.id_comp] at l₁ l₂
  rw [l₁, l₂, gs_pull _ _ z V hzV r, ← hι, ← gs_pull _ _ z V hm r, hr', hu,
    gs_unit _ z _ hm]
  erw [gm_res _ z hle hm]
  erw [gs_res _ z h hz]
  rw [gs_unit _ z _ (h hz)]
  exact congrArg Units.val e₃

end GlobalTheory.PsiUnitOfPsiOn
