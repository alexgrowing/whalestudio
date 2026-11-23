import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafRepCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut

namespace UpperTheory.Et.Loc

variable {B : Scheme.{0}} {q : ℕ}

def HP (P : B.Etale ⥤ Shv (ZMod q)) (J : Shv (ZMod q)) : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) :=
  P.op ⋙ (linearYoneda (ULift.{1} (ZMod q)) (Shv (ZMod q))).obj J

def Good (P : B.Etale ⥤ Shv (ZMod q)) : Prop :=
  ∀ J : Shv (ZMod q), Injective J → ∃ h : Presheaf.IsSheaf (EtTop B) (HP P J), Injective (⟨HP P J, h⟩ : SShv B q)

def preL {K K' : Cx (ZMod q)} (f : K' ⟶ K) (I : Cx (ZMod q)) (n : ℤ) :
    Cochain K I n →ₗ[ULift.{1} (ZMod q)] Cochain K' I n where
  toFun α := (Cochain.ofHom f).comp α (zero_add n)
  map_add' _ _ := Cochain.comp_add _ _ _ _
  map_smul' _ _ := Cochain.comp_smul _ _ _ _

theorem preL_comp {K K' K'' : Cx (ZMod q)} (g : K'' ⟶ K') (f : K' ⟶ K) (I : Cx (ZMod q)) (n : ℤ) (α : Cochain K I n) :
    preL (g ≫ f) I n α = preL g I n (preL f I n α) := by
  simp [preL, Cochain.ofHom_comp]

def TP (C : B.Etale ⥤ Cx (ZMod q)) (I : Cx (ZMod q)) (n : ℤ) : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) where
  obj U := ModuleCat.of _ (Cochain (C.obj U.unop) I n)
  map a := ModuleCat.ofHom (preL (C.map a.unop) I n)
  map_id U := by
    ext α
    simp [preL]
  map_comp a b := by
    ext α
    simp [preL, Cochain.ofHom_comp]

def TC (C : B.Etale ⥤ Cx (ZMod q)) (I : Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n)) :
    CochainComplex (SShv B q) ℤ where
  X n := ⟨TP C I n, h n⟩
  d n m := ⟨{ app := fun U => ModuleCat.ofHom (δ_hom (ULift.{1} (ZMod q)) (C.obj U.unop) I n m)
              naturality := fun U V a => by
                ext α
                exact δ_ofHom_comp (C.map a.unop) α m }⟩
  shape n m hnm := by
    ext U α
    exact δ_shape n m hnm α
  d_comp_d' n m p _ _ := by
    ext U α
    exact δ_δ n m p α

def TM {C C' : B.Etale ⥤ Cx (ZMod q)} (φ : C' ⟶ C) (I : Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n))
    (h' : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C' I n)) : TC C I h ⟶ TC C' I h' where
  f n := ⟨{ app := fun U => ModuleCat.ofHom (preL (φ.app U.unop) I n)
            naturality := fun U V a => by
              refine ModuleCat.hom_ext (LinearMap.ext fun α => ?_)
              change preL (φ.app V.unop) I n (preL (C.map a.unop) I n α) = preL (C'.map a.unop) I n (preL (φ.app U.unop) I n α)
              exact (preL_comp _ _ I n α).symm.trans ((congrArg (fun t => preL t I n α) (φ.naturality a.unop).symm).trans (preL_comp _ _ I n α)) }⟩
  comm' n m _ := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun α => ?_)))
    exact δ_ofHom_comp (φ.app U.unop) α m

def coneF {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) : B.Etale ⥤ Cx (ZMod q) where
  obj U := mappingCone ((chains (ZMod q)).map (sch.map (F.app U)))
  map {U' U} a := rmap (ZMod q) (sch.map (F.app U)) (sch.map (F.app U')) (sch.map (G₁.map a)) (sch.map (G₂.map a))
    (by rw [← Functor.map_comp, ← Functor.map_comp, F.naturality])
  map_id U := by
    simp only [rmap, CategoryTheory.Functor.map_id]
    exact mappingCone.map_id _
  map_comp a b := by
    simp only [rmap, Functor.map_comp]
    exact mappingCone.map_comp _ _ _ _ _ _ _ _ _

theorem id_left' (U : B.Etale) : (𝟙 U : U ⟶ U).left = 𝟙 U.left := rfl

theorem comp_left' {U V W : B.Etale} (a : U ⟶ V) (b : V ⟶ W) : (a ≫ b).left = a.left ≫ b.left := rfl

def gY {Y : Scheme.{0}} (p : Y ⟶ B) : B.Etale ⥤ Scheme.{0} where
  obj U := YU p U
  map a := resY p a
  map_id U := by apply pullback.hom_ext <;> simp [resY, resYW, resBW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, id_left', comp_left']
  map_comp a b := by apply pullback.hom_ext <;> simp [resY, resYW, resBW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, id_left', comp_left']

def gYW {Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) : B.Etale ⥤ Scheme.{0} where
  obj U := pullback (pullback.snd p U.hom ≫ U.hom) ι
  map a := resYW p ι a
  map_id U := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [resY, resYW, resBW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, id_left', comp_left']
    · simp [resY, resYW, resBW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, id_left', comp_left']
  map_comp a b := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [resY, resYW, resBW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, id_left', comp_left']
    · simp [resY, resYW, resBW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, id_left', comp_left']

def gB (B : Scheme.{0}) : B.Etale ⥤ Scheme.{0} where
  obj U := U.left
  map a := a.left

def gBW {W : Scheme.{0}} (ι : W ⟶ B) : B.Etale ⥤ Scheme.{0} where
  obj U := pullback U.hom ι
  map a := resBW ι a
  map_id U := by apply pullback.hom_ext <;> simp [resY, resYW, resBW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, id_left', comp_left']
  map_comp a b := by apply pullback.hom_ext <;> simp [resY, resYW, resBW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, id_left', comp_left']

def fY {Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) : gYW p ι ⟶ gY p where
  app U := prU p ι U
  naturality _ _ _ := pullback.lift_fst _ _ _

def fB {W : Scheme.{0}} (ι : W ⟶ B) : gBW ι ⟶ gB B where
  app U := prB ι U
  naturality _ _ _ := pullback.lift_fst _ _ _

abbrev Sc (F : SShv B q) (U : B.Etale) : Type 1 := F.obj.obj (op U)

abbrev dS (T : CochainComplex (SShv B q) ℤ) (n m : ℤ) (U : B.Etale) (s : Sc (T.X n) U) : Sc (T.X m) U :=
  ((T.d n m).hom.app (op U)).hom s

def Yon (B : Scheme.{0}) (q : ℕ) : Prop :=
  ∃ y : ∀ (T : CochainComplex (SShv B q) ℤ) (U : B.Etale) (n : ℤ) (s : Sc (T.X n) U), dS T n (n + 1) U s = 0 →
      ((OU B q).obj U ⟶ (CategoryTheory.shiftFunctor _ n).obj (DerivedCategory.Q.obj T)),
    (∀ T U n s hs s' hs', (∃ b, dS T (n - 1) n U b = s - s') → y T U n s hs = y T U n s' hs') ∧
    (∀ T, T.IsKInjective → ∀ U n, (∀ s hs s' hs', y T U n s hs = y T U n s' hs' → ∃ b, dS T (n - 1) n U b = s - s') ∧
      ∀ x, ∃ s hs, y T U n s hs = x) ∧
    (∀ T (U U' : B.Etale) (a : U' ⟶ U) n s hs hs',
      y T U' n (((T.X n).obj.map a.op).hom s) hs' = (OU B q).map a ≫ y T U n s hs) ∧
    ∀ T T' (φ : T ⟶ T') U n s hs hs',
      y T' U n (((φ.f n).hom.app (op U)).hom s) hs' = y T U n s hs ≫ (CategoryTheory.shiftFunctor _ n).map (DerivedCategory.Q.map φ)

end UpperTheory.Et.Loc

end
