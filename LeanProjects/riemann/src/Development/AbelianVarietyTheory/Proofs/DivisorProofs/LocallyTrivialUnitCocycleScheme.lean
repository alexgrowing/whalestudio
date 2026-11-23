import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyTrivialUnitCocycleFaithfullyFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfullyFlatAppOfIsAffineHomFlatSurjectiveStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CharKer

theorem appLE_eq_of_eq' {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem app_map_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.app U).hom x) = (f.appLE U V h).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]

theorem appLE_map_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V V' : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ V) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h').op).hom ((f.appLE U V h).hom x) = (f.appLE U V' (h'.trans h)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem map_app_map_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} (hU : U' ≤ U)
    (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U') (h' : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.app U').hom ((Y.presheaf.map (homOfLE hU).op).hom x)) =
      (f.appLE U V h').hom x := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
    ← Category.assoc, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem appLE_map_top {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
    (x : Γ(Y, ⊤)) :
    (f.appLE U V e).hom ((Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom x) =
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (f.appTop.hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 2
  simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
  rw [Scheme.Hom.naturality_assoc, ← Functor.map_comp]
  rfl

theorem map_map_apply {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (h₃ : W ≤ U)
    (x : Γ(X, U)) : (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom x) =
      (X.presheaf.map (homOfLE h₃).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.CharKer

namespace GlobalTheory.CharKer

theorem exists_local_charUnit : ∀ (X Y Z W : Scheme.{0}) (p : X ⟶ Y) (a b : Z ⟶ X) (m₁₂ m₂₃ m₁₃ : W ⟶ Z) (χ : Γ(Z, ⊤)ˣ), IsAffineHom p → Flat p → Surjective p → IsPullback b a p p → IsPullback m₁₂ m₂₃ a b → m₁₃ ≫ b = m₁₂ ≫ b → m₁₃ ≫ a = m₂₃ ≫ a → pullTop m₁₃ χ = pullTop m₁₂ χ * pullTop m₂₃ χ → ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ e : Γ(X, p ⁻¹ᵁ V)ˣ, ∀ (W' : Z.Opens) (h₁ : W' ≤ a ⁻¹ᵁ (p ⁻¹ᵁ V)) (h₂ : W' ≤ b ⁻¹ᵁ (p ⁻¹ᵁ V)), res h₁ (pullU a _ e) = res le_top χ * res h₂ (pullU b _ e) := by
  intro X Y Z W p a b m₁₂ m₂₃ m₁₃ χ hpA hpF hpS sq₁ sq₂ e₁₃b e₁₃a hχ y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  have ha : IsAffineHom a := MorphismProperty.of_isPullback (P := @IsAffineHom) sq₁ hpA
  have hab : a ⁻¹ᵁ (p ⁻¹ᵁ V) = b ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq₁.w]
  have h12 : m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) ≤ m₁₂ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) := by
    rw [← Scheme.Hom.comp_preimage m₁₂ a, sq₂.w, Scheme.Hom.comp_preimage, ← hab]
  have h13 : m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) ≤ m₁₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) := by
    rw [← Scheme.Hom.comp_preimage m₁₃ a, e₁₃a, Scheme.Hom.comp_preimage]
  have hV₀ : IsAffineOpen (p ⁻¹ᵁ V) := hV.preimage p
  have hV₁ : IsAffineOpen (a ⁻¹ᵁ (p ⁻¹ᵁ V)) := hV₀.preimage a
  have P₁ := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq₁ hpA hV hV₀ le_rfl hab.le
  rw [Scheme.Hom.appLE_eq_app] at P₁
  have P₂ := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq₂ ha hV₀ hV₁ hab.le h12
  have E₁ : b.appLE (p ⁻¹ᵁ V) (a ⁻¹ᵁ (p ⁻¹ᵁ V)) hab.le ≫ m₁₃.appLE _ _ h13 =
      b.appLE (p ⁻¹ᵁ V) (a ⁻¹ᵁ (p ⁻¹ᵁ V)) hab.le ≫ m₁₂.appLE _ _ h12 := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_of_eq' e₁₃b _ _ _ _
  have E₂ : a.app (p ⁻¹ᵁ V) ≫ m₁₃.appLE _ _ h13 = a.app (p ⁻¹ᵁ V) ≫ m₂₃.app _ := by
    rw [Scheme.Hom.app_eq_appLE a, Scheme.Hom.app_eq_appLE m₂₃, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_of_eq' e₁₃a _ _ _ _
  have FF := GlobalTheory.T.faithfullyFlat_app_of_isAffineHom_flat_surjective' X Y p V hpA hpF hpS hV
  let c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))ˣ := res le_top χ
  have hc : (m₁₃.appLE _ _ h13).hom (c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))) =
      (m₁₂.appLE _ _ h12).hom (c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))) * (m₂₃.app _).hom (c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))) := by
    have := congrArg (fun u => ((res (le_top : m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) ≤ ⊤) u : Γ(W, _)ˣ) :
      Γ(W, m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V))))) hχ
    simp only [map_mul, Units.val_mul, res, pullTop, Units.coe_map, MonoidHom.coe_coe] at this
    rw [Scheme.Hom.app_eq_appLE m₂₃]
    simp only [c, res, Units.coe_map, MonoidHom.coe_coe]
    rw [appLE_map_top, appLE_map_top, appLE_map_top]
    exact this
  obtain ⟨s, hs, x, x', hxx', hx⟩ := GlobalTheory.T.locally_trivial_unit_cocycle_faithfully_flat _ _ _ _ (p.app V) _ _ _ _ _ P₁ P₂ E₁ E₂ FF c hc
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal inferInstance
  have hyS : y ∈ Y.basicOpen s := by
    have h0 : hV.primeIdealOf ⟨y, hyV⟩ ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen s := by
      rw [hV.fromSpec_preimage_basicOpen]; exact hs
    have h1 := hV.fromSpec_primeIdealOf ⟨y, hyV⟩
    have h0' : hV.fromSpec (hV.primeIdealOf ⟨y, hyV⟩) ∈ Y.basicOpen s := h0
    rwa [h1] at h0'
  refine ⟨Y.basicOpen s, hyS, ?_⟩
  have hle : p ⁻¹ᵁ Y.basicOpen s ≤ p ⁻¹ᵁ V := fun z hz => Y.basicOpen_le s hz
  have hpre := Scheme.preimage_basicOpen p s
  have hu : IsUnit ((X.presheaf.map (homOfLE hle).op).hom x) := by
    apply isUnit_of_mul_isUnit_left (y := (X.presheaf.map (homOfLE hle).op).hom x')
    rw [← map_mul, hxx']
    have h2 := RingedSpace.isUnit_res_basicOpen X.toRingedSpace ((p.app V).hom s)
    have h3 := h2.map (X.presheaf.map (homOfLE hpre.le).op).hom
    rw [← map_map_apply (X.basicOpen_le ((p.app V).hom s)) hpre.le hle]
    exact h3
  refine ⟨hu.unit, fun W' h₁ h₂ => ?_⟩
  have hW : W' ≤ a ⁻¹ᵁ (p ⁻¹ᵁ V) := fun z hz => hle (h₁ hz)
  have hWb : W' ≤ b ⁻¹ᵁ (p ⁻¹ᵁ V) := hW.trans hab.le
  apply Units.ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec, Units.val_mul]
  rw [map_app_map_eq_appLE a hle W' h₁ hW, map_app_map_eq_appLE b hle W' h₂ hWb]
  have := congrArg (Z.presheaf.map (homOfLE hW).op).hom hx
  rw [map_mul, app_map_eq_appLE, appLE_map_eq_appLE] at this
  rw [this]
  congr 1
  simp only [c, res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.CharKer
