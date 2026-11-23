import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RestrictTensor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory TensorProduct

universe u

noncomputable section

variable {X : Scheme.{u}}

lemma bijective_app_of_factor {A B : X.Modules} (φ : A ⟶ B) {P : PMod X}
    (p : (preMod X).obj A ⟶ P) (q : P ⟶ (preMod X).obj B)
    (hq : ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj q)
    (hφ : (preMod X).map φ = p ≫ q) {W : X.Opens}
    (hp : ∀ V ≤ W, Function.Bijective (p.app (op V))) :
    ∀ V ≤ W, Function.Bijective (φ.app V) := by
  obtain ⟨hq₁, hq₂⟩ := (ModulesTensor.W_toPresheaf_iff q).1 hq
  have hφapp : ∀ (V : X.Opens) (a : Γ(A, V)), φ.app V a = q.app (op V) (p.app (op V) a) :=
    fun V a => congrArg (fun g => g.app (op V) a) hφ |>.trans rfl
  have nat : ∀ {V V' : X.Opens} (i : V' ≤ V) (σ : Γ(A, V)),
      φ.app V' (A.presheaf.map (homOfLE i).op σ) = B.presheaf.map (homOfLE i).op (φ.app V σ) :=
    fun i σ => NatTrans.naturality_apply φ.mapPresheaf (homOfLE i).op σ
  have inj : ∀ V ≤ W, Function.Injective (φ.app V) := by
    intro V hV
    rw [injective_iff_map_eq_zero]
    intro a ha
    rw [hφapp] at ha
    have hS := hq₁ (op V) _ ha
    rw [Opens.mem_grothendieckTopology] at hS
    apply sheaf_eq_of_locally ⟨A.presheaf, A.isSheaf⟩ (V := V)
    intro x hx
    obtain ⟨V', i, hi, hxV'⟩ := hS x hx
    refine ⟨V', i.le, hxV', ?_⟩
    have h0 : p.app (op V') (A.presheaf.map (homOfLE i.le).op a) = 0 := by
      have := PresheafOfModules.naturality_apply p (homOfLE i.le).op a
      exact this.trans hi
    apply (hp V' (i.le.trans hV)).1
    exact h0.trans (map_zero _).symm |>.trans (congrArg _ (map_zero _).symm)
  intro V hV
  refine ⟨inj V hV, fun b => ?_⟩
  have hS := hq₂ (op V) b
  rw [Opens.mem_grothendieckTopology] at hS
  choose V' i hi hxV' using hS
  choose w hw using hi
  choose a₀ ha using fun x (hx : x ∈ V) => (hp (V' x hx) ((i x hx).le.trans hV)).2 (w x hx)
  let a : ∀ x (hx : x ∈ V), Γ(A, V' x hx) := fun x hx => a₀ x hx
  have key : ∀ x hx, φ.app (V' x hx) (a x hx) = B.presheaf.map (homOfLE (i x hx).le).op b :=
    fun x hx => (hφapp _ (a x hx)).trans ((congrArg _ (ha x hx)).trans (hw x hx))
  obtain ⟨g, hg⟩ := sheaf_exists_glue ⟨A.presheaf, A.isSheaf⟩ (V := V) (ι := {x : X // x ∈ V})
    (fun c => V' c.1 c.2) (fun c => (i c.1 c.2).le) (fun x hx => ⟨⟨x, hx⟩, hxV' x hx⟩)
    (fun c => a c.1 c.2) (by
      intro c d
      apply inj _ (inf_le_left.trans ((i c.1 c.2).le.trans hV))
      change φ.app _ (A.presheaf.map _ (a c.1 c.2)) = φ.app _ (A.presheaf.map _ (a d.1 d.2))
      rw [nat, nat, key, key]
      change ((B.presheaf.map _ ≫ B.presheaf.map _) b) = ((B.presheaf.map _ ≫ B.presheaf.map _) b)
      rw [← B.presheaf.map_comp, ← B.presheaf.map_comp]
      rfl)
  refine ⟨g, ?_⟩
  apply sheaf_eq_of_locally ⟨B.presheaf, B.isSheaf⟩ (V := V)
  intro x hx
  refine ⟨V' x hx, (i x hx).le, hxV' x hx, ?_⟩
  change B.presheaf.map _ (φ.app V g) = _
  rw [← nat]
  have := hg ⟨x, hx⟩
  simp only at this
  rw [this]
  exact key x hx

def homOfPreMod {M S : X.Modules} (g : (preMod X).obj M ⟶ (preMod X).obj S) : M ⟶ S :=
  inv ((sheafifyModAdj X).counit.app M) ≫ ((sheafifyModAdj X).homEquiv _ _).symm g

lemma preMod_map_homOfPreMod {M S : X.Modules} (g : (preMod X).obj M ⟶ (preMod X).obj S) :
    (preMod X).map (homOfPreMod g) = g := by
  have h1 : (preMod X).map (inv ((sheafifyModAdj X).counit.app M)) =
      (sheafifyModAdj X).unit.app ((preMod X).obj M) := by
    rw [Functor.map_inv]
    exact (IsIso.eq_inv_of_inv_hom_id ((sheafifyModAdj X).right_triangle_components M)).symm
  rw [homOfPreMod, Functor.map_comp, h1, Adjunction.homEquiv_counit, Functor.map_comp,
    ← Category.assoc]
  erw [← (sheafifyModAdj X).unit.naturality g]
  rw [Category.assoc]
  erw [(sheafifyModAdj X).right_triangle_components S]
  exact Category.comp_id g

variable (M L : X.Modules) (s : Γ(L, ⊤))

def tensorSection : (preMod X).obj M ⟶ (preMod X).obj M ⊗ (preMod X).obj L :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun m => (m : ((preMod X).obj M).obj U) ⊗ₜ
            resM ((preMod X).obj L) (le_top : U.unop ≤ ⊤) s
          map_zero' := zero_tmul _ _
          map_add' := fun a b => add_tmul _ _ _ }
      naturality := fun U V g => by
        ext m
        change (((preMod X).obj M).map g m) ⊗ₜ resM ((preMod X).obj L) (le_top : V.unop ≤ ⊤) s =
          (((preMod X).obj M).map g m) ⊗ₜ ((preMod X).obj L).map g
            (resM ((preMod X).obj L) (le_top : U.unop ≤ ⊤) s)
        congr 1
        change ((preMod X).obj L).map (homOfLE (le_top : V.unop ≤ ⊤)).op s =
          ((preMod X).obj L).map g (((preMod X).obj L).map (homOfLE (le_top : U.unop ≤ ⊤)).op s)
        exact PresheafOfModules.map_comp_apply ((preMod X).obj L) (homOfLE (le_top : U.unop ≤ ⊤)).op g s }
    (fun U r m => (smul_tmul' r m _).symm)

def mulSection : M ⟶ M ⊗ L :=
  homOfPreMod (tensorSection M L s ≫ tensorToSheaf M L)

lemma preMod_map_mulSection :
    (preMod X).map (mulSection M L s) = tensorSection M L s ≫ tensorToSheaf M L :=
  preMod_map_homOfPreMod _

theorem bijective_mulSection_app {W : X.Opens}
    (hs : IsBasisOn ((preMod X).obj L) W (resM ((preMod X).obj L) le_top s)) :
    ∀ V ≤ W, Function.Bijective ((mulSection M L s).app V) := by
  refine bijective_app_of_factor _ (tensorSection M L s) (tensorToSheaf M L) (W_tensorToSheaf M L)
    (preMod_map_mulSection M L s) ?_
  intro V hV
  have e0 : resM ((preMod X).obj L) hV (resM ((preMod X).obj L) le_top s) =
      resM ((preMod X).obj L) (le_top : V ≤ ⊤) s := resM_resM _ le_top hV s
  let e : ringOn X V ≃ₗ[ringOn X V] ((preMod X).obj L).obj (op V) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton (ringOn X V) _
      (resM ((preMod X).obj L) hV (resM ((preMod X).obj L) le_top s))) (hs V hV)
  let E := (TensorProduct.rid (ringOn X V) (((preMod X).obj M).obj (op V))).symm ≪≫ₗ
    e.lTensor (((preMod X).obj M).obj (op V))
  have hE : ∀ m, E m = (tensorSection M L s).app (op V) m := by
    intro m
    change m ⊗ₜ e 1 = m ⊗ₜ resM ((preMod X).obj L) (le_top : V ≤ ⊤) s
    congr 1
    exact (one_smul (ringOn X V) _).trans e0
  have : ⇑((tensorSection M L s).app (op V)) = E := funext fun m => (hE m).symm
  rw [this]
  exact E.bijective

end

end GroundTheory.Arith.SchemeCoh
