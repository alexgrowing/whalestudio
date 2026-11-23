import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Pb

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

namespace Frame

variable {d : ℕ} (E : Frame Φ d)

theorem τ_self (i : Fin d) {T : C} (σ : E.D ⟶ T) : E.τ i σ σ = 0 := by
  have h := E.add i σ σ σ
  linear_combination -h

theorem τ_swap (i : Fin d) {T : C} (σ σ' : E.D ⟶ T) : E.τ i σ' σ = -E.τ i σ σ' := by
  have h := E.add i σ σ' σ
  rw [E.τ_self] at h
  linear_combination -h

theorem ext' {T : C} {σ σ' : E.D ⟶ T} (h : ∀ i, E.τ i σ σ' = 0) : σ = σ' :=
  (E.bij σ (fun _ => 0) (fun _ => (Φ.J.S T).zero_mem)).unique (fun i => E.τ_self i σ) h

end Frame

def Frame.initial (E : Frame Φ 0) : Limits.IsInitial E.D :=
  Limits.IsInitial.ofUniqueHom (fun T => Classical.choice (E.ne T)) fun _ _ => E.ext' fun i => i.elim0

namespace Poly

variable (Q : Poly Φ)

def lift {T T' : C} (φ : T ⟶ T') (x : Φ.A.obj T') (hx : x ∈ Φ.J.S T') : Q.P T ⟶ T' :=
  Classical.choose (Q.univ φ x hx).exists

theorem lift_j {T T' : C} (φ : T ⟶ T') (x : Φ.A.obj T') (hx : x ∈ Φ.J.S T') : Q.j T ≫ Q.lift φ x hx = φ :=
  (Classical.choose_spec (Q.univ φ x hx).exists).1

theorem lift_X {T T' : C} (φ : T ⟶ T') (x : Φ.A.obj T') (hx : x ∈ Φ.J.S T') : (Φ.A.map (Q.lift φ x hx)).hom (Q.X T) = x :=
  (Classical.choose_spec (Q.univ φ x hx).exists).2

theorem hom_ext {T T' : C} {ψ ψ' : Q.P T ⟶ T'} (hj : Q.j T ≫ ψ = Q.j T ≫ ψ')
    (hX : (Φ.A.map ψ).hom (Q.X T) = (Φ.A.map ψ').hom (Q.X T)) : ψ = ψ' :=
  (Q.univ (Q.j T ≫ ψ) _ (Φ.J.map_mem ψ (Q.X_mem T))).unique ⟨rfl, rfl⟩ ⟨hj.symm, hX.symm⟩

end Poly

variable {d : ℕ}

structure Pt (E : Frame Φ d) : Type 1 where
  T : C
  s : E.D ⟶ T

instance (E : Frame Φ d) : Category.{0} (Pt E) where
  Hom X Y := X.T ⟶ Y.T
  id X := 𝟙 X.T
  comp f g := f ≫ g
  id_comp f := Category.id_comp (obj := C) f
  comp_id f := Category.comp_id (obj := C) f
  assoc f g h := Category.assoc (obj := C) f g h

namespace Pt

variable (E : Frame Φ d)

def U : Pt E ⥤ C where
  obj X := X.T
  map f := f

def S : C ⥤ Pt E where
  obj T := ⟨T, Classical.choice (E.ne T)⟩
  map f := f

def adj : U E ⊣ S E :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => Equiv.refl _
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun _ _ => rfl }

end Pt

structure Cut (E : Frame Φ (d + 1)) : Type 1 where
  T : C
  s : E.D ⟶ T

instance (E : Frame Φ (d + 1)) : Category.{0} (Cut E) where
  Hom X Y := {φ : X.T ⟶ Y.T // E.τ 0 (X.s ≫ φ) Y.s = 0}
  id X := ⟨𝟙 X.T, by rw [Category.comp_id]; exact E.τ_self 0 X.s⟩
  comp {X Y Z} f g := ⟨f.1 ≫ g.1, by
    rw [E.add 0 _ (Y.s ≫ g.1) _, ← Category.assoc, E.nat, f.2, map_zero, zero_add]
    exact g.2⟩
  id_comp f := Subtype.ext (Category.id_comp (obj := C) f.1)
  comp_id f := Subtype.ext (Category.comp_id (obj := C) f.1)
  assoc f g h := Subtype.ext (Category.assoc (obj := C) f.1 g.1 h.1)

namespace Cut

variable {E : Frame Φ (d + 1)}

theorem hom_ext {X Y : Cut E} {f g : X ⟶ Y} (h : f.1 = g.1) : f = g := Subtype.ext h

@[simp] theorem comp_val {X Y Z : Cut E} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).1 = f.1 ≫ g.1 := rfl

@[simp] theorem id_val (X : Cut E) : (𝟙 X : X ⟶ X).1 = 𝟙 X.T := rfl

variable (E)

def U : Cut E ⥤ C where
  obj X := X.T
  map f := f.1

def inc : Cut E ⥤ Pt E where
  obj X := ⟨X.T, X.s⟩
  map f := f.1

variable {E} (Q : Poly Φ)

def sec (X : Pt E) : E.D ⟶ Q.P X.T :=
  Classical.choose (E.bij (X.s ≫ Q.j X.T) (fun i => if i = 0 then Q.X X.T else 0) (fun i => by
    split_ifs
    · exact Q.X_mem _
    · exact (Φ.J.S _).zero_mem)).exists

theorem sec_spec (X : Pt E) (i : Fin (d + 1)) :
    E.τ i (X.s ≫ Q.j X.T) (sec Q X) = if i = 0 then Q.X X.T else 0 :=
  Classical.choose_spec (E.bij (X.s ≫ Q.j X.T) (fun i => if i = 0 then Q.X X.T else 0) (fun i => by
    split_ifs
    · exact Q.X_mem _
    · exact (Φ.J.S _).zero_mem)).exists i

theorem τ_sec (X : Pt E) {T' : C} (s' : E.D ⟶ T') (ψ : Q.P X.T ⟶ T') (i : Fin (d + 1)) :
    E.τ i (sec Q X ≫ ψ) s' = -(if i = 0 then (Φ.A.map ψ).hom (Q.X X.T) else 0) + E.τ i (X.s ≫ Q.j X.T ≫ ψ) s' := by
  rw [E.add i _ (X.s ≫ Q.j X.T ≫ ψ) _, ← Category.assoc X.s, E.nat, E.τ_swap, sec_spec, map_neg]
  split_ifs <;> simp

def val (X : Pt E) (Y : Pt E) (φ : X.T ⟶ Y.T) : Φ.A.obj (Q.P Y.T) :=
  Q.X Y.T + (Φ.A.map (Q.j Y.T)).hom (E.τ 0 (X.s ≫ φ) Y.s)

theorem val_mem (X Y : Pt E) (φ : X.T ⟶ Y.T) : val Q X Y φ ∈ Φ.J.S _ :=
  Ideal.add_mem _ (Q.X_mem _) (Φ.J.map_mem _ (E.mem 0 _ _))

def Pmap {X Y : Pt E} (φ : X.T ⟶ Y.T) : Q.P X.T ⟶ Q.P Y.T := Q.lift (φ ≫ Q.j Y.T) (val Q X Y φ) (val_mem Q X Y φ)

theorem mapA_comp {T T' T'' : C} (f : T ⟶ T') (g : T' ⟶ T'') (x : Φ.A.obj T) :
    (Φ.A.map (f ≫ g)).hom x = (Φ.A.map g).hom ((Φ.A.map f).hom x) := by
  rw [Φ.A.map_comp]; rfl

theorem Pmap_j {X Y : Pt E} (φ : X.T ⟶ Y.T) : Q.j X.T ≫ Pmap Q φ = φ ≫ Q.j Y.T := Q.lift_j _ _ _

theorem Pmap_X {X Y : Pt E} (φ : X.T ⟶ Y.T) : (Φ.A.map (Pmap Q φ)).hom (Q.X X.T) = val Q X Y φ := Q.lift_X _ _ _

theorem τ_comp (i : Fin (d + 1)) {T₁ T₂ T₃ : C} (s₁ : E.D ⟶ T₁) (s₂ : E.D ⟶ T₂) (s₃ : E.D ⟶ T₃) (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    E.τ i (s₁ ≫ f ≫ g) s₃ = (Φ.A.map g).hom (E.τ i (s₁ ≫ f) s₂) + E.τ i (s₂ ≫ g) s₃ := by
  rw [E.add i _ (s₂ ≫ g), ← Category.assoc, E.nat]

theorem val_comp {X Y Z : Pt E} (f : X.T ⟶ Y.T) (g : Y.T ⟶ Z.T) :
    val Q X Z (f ≫ g) = (Φ.A.map (Pmap Q g)).hom (val Q X Y f) := by
  have h1 : (Φ.A.map (Pmap Q g)).hom ((Φ.A.map (Q.j Y.T)).hom (E.τ 0 (X.s ≫ f) Y.s)) =
      (Φ.A.map (Q.j Z.T)).hom ((Φ.A.map g).hom (E.τ 0 (X.s ≫ f) Y.s)) := by
    rw [← mapA_comp, ← mapA_comp, Pmap_j]
  simp only [val, map_add, Pmap_X, h1]
  rw [τ_comp 0 X.s Y.s Z.s f g, map_add]
  abel

theorem Pmap_cut {X Y : Pt E} (φ : X.T ⟶ Y.T) : E.τ 0 (sec Q X ≫ Pmap Q φ) (sec Q Y) = 0 := by
  rw [τ_sec, if_pos rfl, Pmap, Q.lift_X, Q.lift_j, E.add 0 _ (Y.s ≫ Q.j Y.T), ← Category.assoc,
    E.nat, sec_spec, if_pos rfl, val]
  ring

def P0 : Pt E ⥤ Cut E where
  obj X := ⟨Q.P X.T, sec Q X⟩
  map {X Y} φ := ⟨Pmap Q φ, Pmap_cut Q φ⟩
  map_id X := by
    refine hom_ext (Q.hom_ext ?_ ?_)
    · change Q.j X.T ≫ Pmap Q (𝟙 X.T) = Q.j X.T ≫ 𝟙 _
      exact (Pmap_j Q (𝟙 X.T)).trans ((Category.id_comp (obj := C) _).trans (Category.comp_id (obj := C) _).symm)
    · change (Φ.A.map (Pmap Q (𝟙 X.T))).hom _ = (Φ.A.map (𝟙 _)).hom _
      rw [Pmap_X, val, Category.comp_id, E.τ_self, map_zero, add_zero, Φ.A.map_id]
      rfl
  map_comp {X Y Z} f g := by
    refine hom_ext (Q.hom_ext ?_ ?_)
    · change Q.j X.T ≫ Pmap Q (CategoryStruct.comp (obj := C) f g) = Q.j X.T ≫ Pmap Q f ≫ Pmap Q g
      rw [Pmap_j, ← Category.assoc (Q.j X.T), Pmap_j, Category.assoc (obj := C) f (Q.j Y.T), Pmap_j, Category.assoc]
    · change (Φ.A.map (Pmap Q (f ≫ g))).hom _ = (Φ.A.map (Pmap Q f ≫ Pmap Q g)).hom _
      rw [mapA_comp, Pmap_X, Pmap_X]
      exact val_comp Q f g

theorem truncation_hom_ext {X : Pt E} {Y : Cut E} {ψ ψ' : (P0 Q).obj X ⟶ Y} (h : Q.j X.T ≫ ψ.1 = Q.j X.T ≫ ψ'.1) : ψ = ψ' := by
  have e : ∀ ψ : (P0 Q).obj X ⟶ Y, (Φ.A.map ψ.1).hom (Q.X X.T) = E.τ 0 (X.s ≫ Q.j X.T ≫ ψ.1) Y.s := by
    intro ψ
    have := ψ.2
    change E.τ 0 (sec Q X ≫ ψ.1) Y.s = 0 at this
    rw [τ_sec, if_pos rfl] at this
    linear_combination -this
  exact hom_ext (Q.hom_ext h ((e ψ).trans ((congrArg (fun t => E.τ 0 (X.s ≫ t) Y.s) h).trans (e ψ').symm)))

def adjInv (X : Pt E) (Y : Cut E) (φ : X.T ⟶ Y.T) : (P0 Q).obj X ⟶ Y :=
  ⟨Q.lift φ (E.τ 0 (X.s ≫ φ) Y.s) (E.mem 0 (X.s ≫ φ) Y.s), by
    change E.τ 0 (sec Q X ≫ _) Y.s = 0
    rw [τ_sec, if_pos rfl, Q.lift_X, Q.lift_j]
    ring⟩

theorem adjInv_j (X : Pt E) (Y : Cut E) (φ : X.T ⟶ Y.T) : Q.j X.T ≫ (adjInv Q X Y φ).1 = φ :=
  Q.lift_j φ _ (E.mem 0 (X.s ≫ φ) Y.s)

def adj : P0 Q ⊣ inc E :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun ψ => (Q.j X.T ≫ ψ.1 : X.T ⟶ Y.T)
          invFun := fun φ => adjInv Q X Y φ
          left_inv := fun ψ => truncation_hom_ext Q (adjInv_j Q X Y _)
          right_inv := fun φ => adjInv_j Q X Y φ }
      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        refine truncation_hom_ext Q ?_
        change Q.j X'.T ≫ (adjInv Q X' Y (f ≫ g)).1 = Q.j X'.T ≫ Pmap Q f ≫ (adjInv Q X Y g).1
        rw [adjInv_j, Pmap, ← Category.assoc, Q.lift_j, Category.assoc, adjInv_j]
      homEquiv_naturality_right := fun {X Y Y'} f g => by
        change Q.j X.T ≫ f.1 ≫ g.1 = (Q.j X.T ≫ f.1) ≫ g.1
        rw [Category.assoc] }

def jNat : Pt.U E ⟶ P0 Q ⋙ U E where
  app X := Q.j X.T
  naturality {X Y} φ := (Pmap_j Q φ).symm

end Cut

end CrystallineSemistableComparison.Pb
