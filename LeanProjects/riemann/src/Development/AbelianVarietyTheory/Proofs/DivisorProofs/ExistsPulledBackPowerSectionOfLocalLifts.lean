import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLIPreimageMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreimageOfLocalPreimagesInjectiveStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum
theorem secLift_app_res {X Y : Scheme.{0}} (a : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (a.app V).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (Y.presheaf.map (homOfLE (extLI_preimage_mono a h)).op).hom ((a.app U).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

theorem secLift_comp_app {X Y Z : Scheme.{0}} (a : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)) :
    ((a ≫ f).app U).hom x = (a.app (f ⁻¹ᵁ U)).hom ((f.app U).hom x) := by
  simp [Scheme.Hom.comp_app]
  rfl

theorem secLift_g {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (i j : Fin 1 → L.ι) :
    ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (k : ℤ))).g i j).val =
      ((Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i 0))
        (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) j 0)) :
        LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) j ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)))).op).hom
        ((φ.app (L.U (i 0) ⊓ L.U (j 0))).hom (L.g (i 0) (j 0)))) ^ k := by
  simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
  rfl
theorem secLift_rr {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
theorem secLift_res_comp {X Y Z : Scheme.{0}} (a : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) {V : Z.Opens}
    (h : V ≤ (a ≫ f) ⁻¹ᵁ U) (h' : V ≤ a ⁻¹ᵁ (f ⁻¹ᵁ U)) (x : Γ(X, U)) :
    (Z.presheaf.map (homOfLE h).op).hom (((a ≫ f).app U).hom x) =
      (Z.presheaf.map (homOfLE h').op).hom ((a.app (f ⁻¹ᵁ U)).hom ((f.app U).hom x)) := by
  rw [secLift_comp_app]
  rfl
end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secLift_compat {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (s : SecK L φ k) (i i' : Fin 1 → L.ι) :
    (Y.presheaf.map (homOfLE (inf_le_left : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i)).op).hom (s.f i) =
      ((Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i 0))
        (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i' 0)) :
        LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i' 0)))).op).hom
        ((φ.app (L.U (i 0) ⊓ L.U (i' 0))).hom (L.g (i 0) (i' 0)))) ^ k *
      (Y.presheaf.map (homOfLE (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i')).op).hom (s.f i') := by
  have h := s.compat i i'
  rw [secLift_g] at h
  exact h

def secLift_ofCompat {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (σf : ∀ i : Fin 1 → L.ι, Γ(Y, LB.wchart L (K := Fin 1) (fun _ => φ) i))
    (h : ∀ i i' : Fin 1 → L.ι, (Y.presheaf.map (homOfLE (inf_le_left : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i)).op).hom (σf i) =
      ((Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i 0))
        (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i' 0)) :
        LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i' 0)))).op).hom
        ((φ.app (L.U (i 0) ⊓ L.U (i' 0))).hom (L.g (i 0) (i' 0)))) ^ k *
      (Y.presheaf.map (homOfLE (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i')).op).hom (σf i')) :
    SecK L φ k where
  f := σf
  compat i i' := (h i i').trans (congrArg (· * _) (secLift_g L φ k i i').symm)

set_option maxHeartbeats 1000000 in
theorem secK_lift_of_local_lift : ∀ {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α) (k : ℕ), (∀ U : X'.Opens, Function.Injective (a.app U).hom) → ∀ (s : SecK L α k) (n : ℕ) (j : Fin n → L.ι) (W : Fin n → X'.Opens), (⨆ b, W b = ⊤) → ∀ (hW : ∀ b, W b ≤ f ⁻¹ᵁ L.U (j b)), (∀ b, ∃ y : Γ(X', W b), (a.app (W b)).hom y = (Y.presheaf.map (homOfLE (extLI_le_chart L f a α e (W b) (j b) (hW b))).op).hom (s.f (fun _ => j b))) → ∃ σ : SecK L f k, ∀ j' : Fin 1 → L.ι, (a.app (LB.wchart L (K := Fin 1) (fun _ => f) j')).hom (σ.f j') = (Y.presheaf.map (homOfLE (extLI_le_wchart L f a α e j')).op).hom (s.f j') := by
  intro X X' Y L f a α e k hinj s n j W hWtop hW hloc
  subst e
  have step1 : ∀ j' : Fin 1 → L.ι, ∃ y : Γ(X', LB.wchart L (K := Fin 1) (fun _ => f) j'),
      (a.app _).hom y = (Y.presheaf.map (homOfLE (extLI_le_wchart L f a (a ≫ f) rfl j')).op).hom (s.f j') := by
    intro j'
    refine GlobalTheory.T.exists_preimage_of_local_preimages_injective a hinj _ W (by rw [hWtop]; exact le_top) _ ?_
    intro b
    obtain ⟨y, hy⟩ := hloc b
    have h1 : LB.wchart L (K := Fin 1) (fun _ => f) j' ⊓ W b ≤ f ⁻¹ᵁ (L.U (j' 0) ⊓ L.U (j b)) :=
      fun x hx => ⟨LB.wchart_le L (K := Fin 1) (fun _ => f) j' 0 hx.1, hW b hx.2⟩
    refine ⟨(X'.presheaf.map (homOfLE h1).op).hom ((f.app _).hom (L.g (j' 0) (j b))) ^ k *
      (X'.presheaf.map (homOfLE (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => f) j' ⊓ W b ≤ W b)).op).hom y, ?_⟩
    have hc2 := congrArg (Y.presheaf.map (homOfLE (show a ⁻¹ᵁ (LB.wchart L (K := Fin 1) (fun _ => f) j' ⊓ W b) ≤
      LB.wchart L (K := Fin 1) (fun _ => a ≫ f) j' ⊓ LB.wchart L (K := Fin 1) (fun _ => a ≫ f) (fun _ => j b) from
      fun x hx => ⟨extLI_le_wchart L f a (a ≫ f) rfl j' hx.1, extLI_le_chart L f a (a ≫ f) rfl (W b) (j b) (hW b) hx.2⟩)).op).hom
      (secLift_compat L (a ≫ f) k s j' (fun _ => j b))
    rw [map_mul, map_pow] at hc2
    erw [secLift_rr, secLift_rr, secLift_rr] at hc2
    rw [map_mul, map_pow, secLift_app_res, secLift_app_res, hy]
    erw [secLift_rr, secLift_rr]
    rw [hc2]
    exact congrArg (fun t => t ^ k * _) (secLift_res_comp a f _ _ _ _).symm
  choose σf hσ using step1
  refine ⟨secLift_ofCompat L f k σf fun i i' => ?_, hσ⟩
  apply hinj (LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i')
  have hG : LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i' ≤ f ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i' 0)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => f) i 0))
      (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => f) i' 0))
  have e1 := secLift_app_res a (inf_le_left : LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i' ≤ LB.wchart L (K := Fin 1) (fun _ => f) i) (σf i)
  have e2 := secLift_app_res a hG ((f.app (L.U (i 0) ⊓ L.U (i' 0))).hom (L.g (i 0) (i' 0)))
  have e3 := secLift_app_res a (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i' ≤ LB.wchart L (K := Fin 1) (fun _ => f) i') (σf i')
  rw [map_mul, map_pow, e1]
  erw [e2, e3]
  rw [hσ, hσ]
  erw [secLift_rr, secLift_rr]
  have hc := congrArg (Y.presheaf.map (homOfLE (show a ⁻¹ᵁ (LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i') ≤
      LB.wchart L (K := Fin 1) (fun _ => a ≫ f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => a ≫ f) i' from
      fun x hx => ⟨extLI_le_wchart L f a (a ≫ f) rfl i hx.1, extLI_le_wchart L f a (a ≫ f) rfl i' hx.2⟩)).op).hom
      (secLift_compat L (a ≫ f) k s i i')
  rw [map_mul, map_pow] at hc
  erw [secLift_rr, secLift_rr, secLift_rr] at hc
  rw [hc]
  exact congrArg (fun t => t ^ k * _) (secLift_res_comp a f (L.U (i 0) ⊓ L.U (i' 0)) _ _ _)
end GlobalTheory.Mum
