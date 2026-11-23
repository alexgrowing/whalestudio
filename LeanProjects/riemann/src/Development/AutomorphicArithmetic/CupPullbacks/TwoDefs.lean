import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

noncomputable section
namespace UpperTheory.P2

def TU (N : ℕ) (A : Type) [CommRing A] : Type := Um N A

instance (N : ℕ) (A : Type) [CommRing A] : SmallCategory (TU N A) where
  Hom v w := {u : Aˣ // v.1 = (u : A) • w.1}
  id v := ⟨1, by simp⟩
  comp f g := ⟨g.1 * f.1, by rw [Units.val_mul, mul_comm, ← smul_smul, ← g.2, ← f.2]⟩
  id_comp f := Subtype.ext (mul_one _)
  comp_id f := Subtype.ext (one_mul _)
  assoc f g h := Subtype.ext (mul_assoc _ _ _).symm

theorem TU.hom_subsingleton {N : ℕ} {A : Type} [CommRing A] (v w : TU N A) : Subsingleton (v ⟶ w) := by
  refine ⟨fun f g => Subtype.ext (Units.ext ?_)⟩
  have hf := f.2
  have hg := g.2
  have h0 : ∀ i, (((f.1 : Aˣ) : A) - ((g.1 : Aˣ) : A)) * w.1 i = 0 := by
    intro i
    have := congrFun (hf.symm.trans hg) i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [sub_mul, this, sub_self]
  have h1 : (1 : A) ∈ Ideal.span (Set.range w.1) := by rw [w.2]; trivial
  have h2 : ∀ x ∈ Ideal.span (Set.range w.1), (((f.1 : Aˣ) : A) - ((g.1 : Aˣ) : A)) * x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; exact h0 i
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  have := h2 1 h1
  rw [mul_one] at this
  exact sub_eq_zero.1 this

instance {N : ℕ} {A : Type} [CommRing A] (v w : TU N A) : Subsingleton (v ⟶ w) := TU.hom_subsingleton v w

def TU.map (N : ℕ) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : TU N A ⥤ TU N B where
  obj v := (Um.map N f).obj v
  map {v w} p := ⟨Units.map (f : A →* B) p.1, by
    funext i
    have h := congrArg f (congrFun p.2 i)
    change f (v.1 i) = f p.1 * f (w.1 i)
    simpa using h⟩
  map_id v := (TU.hom_subsingleton _ _).elim _ _
  map_comp p q := (TU.hom_subsingleton _ _).elim _ _

def tuCat (N : ℕ) : CommRingCat.{0} ⥤ Cat.{0,0} where
  obj A := Cat.of (TU N A)
  map f := (TU.map N f.hom).toCatHom
  map_id A := rfl
  map_comp f g := rfl

def TU.toUm (N : ℕ) (A : Type) [CommRing A] : TU N A ⥤ Um N A where
  obj v := v
  map {v w} p := ⟨(1, p.1), by simpa using p.2⟩
  map_id v := Subtype.ext (Prod.ext rfl rfl)
  map_comp p q := Subtype.ext (Prod.ext (one_mul _).symm rfl)

def tuι (N : ℕ) : tuCat N ⟶ pglCat N where
  app A := (TU.toUm N A).toCatHom
  naturality A B f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => heq_of_eq ?_)
    exact Subtype.ext (Prod.ext (map_one (Matrix.GeneralLinearGroup.map f.hom)).symm rfl)

def Dv (N : ℕ) : Spc := ofCat (tuCat N)

def Dv.toPGL (N : ℕ) : Dv N ⟶ PGL N := ofCatMap (tuι N)

def Dv.line (N : ℕ) : Dv N ⟶ ofCat (glCat 1) := Dv.toPGL N ≫ PGL.line N

def vx {N p : ℕ} {T : Scheme.{0}} (x : Sx (Dv N) p T) (k : Fin (p + 1)) : Um N Γ(T, ⊤) :=
  (show ComposableArrows (TU N Γ(T, ⊤)) p from x).obj k

theorem vx_ext {N p : ℕ} {T : Scheme.{0}} {x y : Sx (Dv N) p T} (h : ∀ k, vx x k = vx y k) : x = y :=
  CategoryTheory.Functor.ext (F := (show ComposableArrows (TU N Γ(T, ⊤)) p from x))
    (G := (show ComposableArrows (TU N Γ(T, ⊤)) p from y)) h (fun _ _ _ => (TU.hom_subsingleton _ _).elim _ _)

def Dv.mk {N p : ℕ} {T : Scheme.{0}} (v : Fin (p + 1) → Um N Γ(T, ⊤))
    (h : ∀ i j, ∃ u : Γ(T, ⊤)ˣ, (v i).1 = (u : Γ(T, ⊤)) • (v j).1) : Sx (Dv N) p T :=
  (show ComposableArrows (TU N Γ(T, ⊤)) p from
    { obj := v
      map := fun {i j} _ => (⟨(h i j).choose, (h i j).choose_spec⟩ : (show TU N Γ(T, ⊤) from v i) ⟶ (show TU N Γ(T, ⊤) from v j))
      map_id := fun _ => (TU.hom_subsingleton _ _).elim _ _
      map_comp := fun _ _ => (TU.hom_subsingleton _ _).elim _ _ })

theorem vx_prop {N p : ℕ} {T : Scheme.{0}} (x : Sx (Dv N) p T) {i j : Fin (p + 1)} (hij : i ≤ j) :
    ∃ u : Γ(T, ⊤)ˣ, (vx x i).1 = (u : Γ(T, ⊤)) • (vx x j).1 :=
  let c : ComposableArrows (TU N Γ(T, ⊤)) p := x
  ⟨(c.map (homOfLE hij)).1, (c.map (homOfLE hij)).2⟩

section Api
variable {E E' : Spc} {p r : ℕ} {T V : Scheme.{0}}

theorem vx_res {N : ℕ} (g : V ⟶ T) (x : Sx (Dv N) p T) (k) :
    vx (x.res g) k = (Um.map N g.appTop.hom).obj (vx x k) := rfl

theorem vx_along {N : ℕ} (x : Sx (Dv N) r T) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk r) (k) :
    vx (x.along θ) k = vx x (θ.toOrderHom k) := rfl

theorem along_along {s : ℕ} (x : Sx E r T) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk s)
    (η : SimplexCategory.mk s ⟶ SimplexCategory.mk r) : (x.along η).along θ = x.along (θ ≫ η) := by
  simp only [Sx.along, op_comp, Functor.map_comp]
  rfl

theorem along_res (g : V ⟶ T) (x : Sx E r T) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk r) :
    (x.res g).along θ = (x.along θ).res g :=
  (ConcreteCategory.congr_hom ((E.map θ.op).naturality g.op) x)

theorem map_along (f : E ⟶ E') (x : Sx E r T) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk r) :
    (x.along θ).map f = (x.map f).along θ :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality θ.op) (op T)) x)

theorem map_res (f : E ⟶ E') (g : V ⟶ T) (x : Sx E p T) : (x.res g).map f = (x.map f).res g :=
  (ConcreteCategory.congr_hom ((f.app _).naturality g.op) x)

theorem map_comp {E'' : Spc} (f : E ⟶ E') (f' : E' ⟶ E'') (x : Sx E p T) : x.map (f ≫ f') = (x.map f).map f' := rfl

def vtx (y : Sx E p T) (k : Fin (p + 1)) : Sx E 0 T := y.along (SimplexCategory.const _ _ k)

theorem vtx_along (y : Sx E r T) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk r) (k : Fin (p + 1)) :
    vtx (y.along θ) k = vtx y (θ.toOrderHom k) := by
  unfold vtx
  rw [along_along, SimplexCategory.const_comp]

theorem vtx_res (g : V ⟶ T) (y : Sx E p T) (k) : vtx (y.res g) k = (vtx y k).res g := along_res g y _

theorem face_along {N : ℕ} (y : Sx E (N + 1) T) (i) : y.face i = y.along (SimplexCategory.δ i) := rfl

end Api

theorem d1mk {p : ℕ} (i j : Fin (p + 1)) (h : i ≤ j) :
    SimplexCategory.δ (n := 0) 1 ≫ SimplexCategory.mkOfLe i j h = SimplexCategory.const _ _ i := by
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun k => ?_))
  obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
  rfl

theorem d0mk {p : ℕ} (i j : Fin (p + 1)) (h : i ≤ j) :
    SimplexCategory.δ (n := 0) 0 ≫ SimplexCategory.mkOfLe i j h = SimplexCategory.const _ _ j := by
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun k => ?_))
  obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
  rfl

theorem prop_of_edges {Y : Spc} {M : ℕ} (φ : ∀ T : Scheme.{0}, Sx Y 0 T → Um M Γ(T, ⊤))
    (hrel : ∀ (T : Scheme.{0}) (y : Sx Y 1 T), ∃ u : Γ(T, ⊤)ˣ, (φ T (y.face 1)).1 = (u : Γ(T, ⊤)) • (φ T (y.face 0)).1)
    {p : ℕ} {T : Scheme.{0}} (y : Sx Y p T) (i j : Fin (p + 1)) :
    ∃ u : Γ(T, ⊤)ˣ, (φ T (vtx y i)).1 = (u : Γ(T, ⊤)) • (φ T (vtx y j)).1 := by
  have key : ∀ i j : Fin (p + 1), i ≤ j → ∃ u : Γ(T, ⊤)ˣ, (φ T (vtx y i)).1 = (u : Γ(T, ⊤)) • (φ T (vtx y j)).1 := by
    intro i j h
    obtain ⟨u, hu⟩ := hrel T (y.along (SimplexCategory.mkOfLe i j h))
    rw [face_along, face_along, along_along, along_along, d1mk, d0mk] at hu
    exact ⟨u, hu⟩
  rcases le_total i j with h | h
  · exact key i j h
  · obtain ⟨u, hu⟩ := key j i h
    refine ⟨u⁻¹, ?_⟩
    rw [hu, smul_smul, Units.inv_mul, one_smul]

def Dv.lift {Y : Spc} {M : ℕ} (φ : ∀ T : Scheme.{0}, Sx Y 0 T → Um M Γ(T, ⊤))
    (hnat : ∀ {V T : Scheme.{0}} (g : V ⟶ T) (y : Sx Y 0 T), φ V (y.res g) = (Um.map M g.appTop.hom).obj (φ T y))
    (hrel : ∀ (T : Scheme.{0}) (y : Sx Y 1 T), ∃ u : Γ(T, ⊤)ˣ, (φ T (y.face 1)).1 = (u : Γ(T, ⊤)) • (φ T (y.face 0)).1) :
    Y ⟶ Dv M where
  app n :=
    { app := fun T => TypeCat.ofHom fun y =>
        Dv.mk (p := n.unop.len) (T := T.unop) (fun k => φ T.unop (vtx (p := n.unop.len) (T := T.unop) y k)) (prop_of_edges φ hrel y)
      naturality := fun T T' f => by
        ext y
        refine vx_ext (p := n.unop.len) (T := T'.unop) fun k => ?_
        exact ((congrArg (φ T'.unop) (vtx_res (p := n.unop.len) f.unop y k)).trans (hnat f.unop _)) }
  naturality n m f := by
    ext T y
    refine vx_ext (p := m.unop.len) (T := T.unop) fun k => ?_
    exact congrArg (φ T.unop) (vtx_along (p := m.unop.len) (r := n.unop.len) (T := T.unop) y f.unop k)

section Limits

theorem isPullback_of_sx {P A B C : Spc} {a : P ⟶ A} {b : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C} (w : a ≫ f = b ≫ g)
    (hinj : ∀ (p : ℕ) (T : Scheme.{0}) (x y : Sx P p T), x.map a = y.map a → x.map b = y.map b → x = y)
    (hex : ∀ (p : ℕ) (T : Scheme.{0}) (s : Sx A p T) (t : Sx B p T), s.map f = t.map g →
      ∃ x : Sx P p T, x.map a = s ∧ x.map b = t) : IsPullback a b f g := by
  refine IsPullback.of_forall_isPullback_app fun n => IsPullback.of_forall_isPullback_app fun T => ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact NatTrans.congr_app (NatTrans.congr_app w n) T
  · rintro x y ⟨h1, h2⟩
    exact hinj n.unop.len T.unop x y h1 h2
  · intro s t h
    exact hex n.unop.len T.unop s t h

theorem prod_sx_ext {A B : Spc} {p : ℕ} {T : Scheme.{0}} {x y : Sx (A ⨯ B) p T}
    (h1 : x.map prod.fst = y.map prod.fst) (h2 : x.map prod.snd = y.map prod.snd) : x = y := by
  let G : Spc ⥤ Type := (evaluation _ _).obj (op (SimplexCategory.mk p)) ⋙ (evaluation _ _).obj (op T)
  have l := mapIsLimitOfPreservesOfIsLimit G _ _ (prodIsProd A B)
  have := BinaryFan.IsLimit.hom_ext l (W := PUnit) (f := TypeCat.ofHom fun _ => x) (g := TypeCat.ofHom fun _ => y)
    (by ext; exact h1) (by ext; exact h2)
  exact ConcreteCategory.congr_hom this PUnit.unit

theorem prod_sx_mk {A B : Spc} {p : ℕ} {T : Scheme.{0}} (a : Sx A p T) (b : Sx B p T) :
    ∃ x : Sx (A ⨯ B) p T, x.map prod.fst = a ∧ x.map prod.snd = b := by
  let G : Spc ⥤ Type := (evaluation _ _).obj (op (SimplexCategory.mk p)) ⋙ (evaluation _ _).obj (op T)
  have l := mapIsLimitOfPreservesOfIsLimit G _ _ (prodIsProd A B)
  obtain ⟨m, h1, h2⟩ := BinaryFan.IsLimit.lift' l (W := PUnit) (TypeCat.ofHom fun _ => a) (TypeCat.ofHom fun _ => b)
  exact ⟨m PUnit.unit, ConcreteCategory.congr_hom h1 PUnit.unit, ConcreteCategory.congr_hom h2 PUnit.unit⟩

theorem spc_mono {A B : Spc} (f : A ⟶ B)
    (h : ∀ (p : ℕ) (T : Scheme.{0}) (x y : Sx A p T), x.map f = y.map f → x = y) : Mono f := by
  have : ∀ n, Mono (f.app n) := fun n => by
    have : ∀ T, Mono ((f.app n).app T) := fun T => by
      rw [mono_iff_injective]
      intro x y e
      exact h n.unop.len T.unop x y e
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

end Limits

section Triv
variable {N p : ℕ} {T : Scheme.{0}}

theorem spc_hom_ext {A B : Spc} {f g : A ⟶ B} (h : ∀ (p : ℕ) (T : Scheme.{0}) (x : Sx A p T), x.map f = x.map g) : f = g := by
  ext n T x
  exact h n.unop.len T.unop x

def vxP (x : Sx (PGL N) p T) (k : Fin (p + 1)) : Um N Γ(T, ⊤) := (show ComposableArrows (Um N Γ(T, ⊤)) p from x).obj k

theorem triv_arrow {E : Spc} (s : Sx E p T) (t : Sx (PGL N) p T) (h : s.map (triv E N) = t.map (PGL.pr N))
    {i j : Fin (p + 1)} (f : i ⟶ j) : ((show ComposableArrows (Um N Γ(T, ⊤)) p from t).map f).1.1 = 1 := by
  have := CategoryTheory.Functor.congr_hom (F := (Functor.const _).obj (SingleObj.star (GL (Fin N) Γ(T, ⊤))))
    (G := (show ComposableArrows (Um N Γ(T, ⊤)) p from t) ⋙ Um.toGL N _) h f
  have h2 := this.symm
  simp at h2
  exact h2

theorem um_arrow_eq {A : Type} [CommRing A] {X Y X' Y' : Um N A} (hx : X = X') (hy : Y = Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    (h : a.1.1 = 1) (h' : a'.1.1 = 1) : a = eqToHom hx ≫ a' ≫ eqToHom hy.symm := by
  subst hx hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Subtype.ext (Prod.ext (h.trans h'.symm) ?_)
  have e1 := a.2
  have e2 := a'.2
  rw [h] at e1
  rw [h'] at e2
  have := (TU.hom_subsingleton (N := N) (A := A) X Y).elim ⟨a.1.2, by simpa using e1⟩ ⟨a'.1.2, by simpa using e2⟩
  exact congrArg Subtype.val this

theorem single_ext {G J : Type} [Monoid G] [Category J] (F F' : J ⥤ SingleObj G)
    (h : ∀ (i j : J) (f : i ⟶ j), F.map f = F'.map f) : F = F' := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j f => ?_)
  rw [h]
  simp

theorem tri_w (E : Spc) (N : ℕ) : (prod.fst : E ⨯ Dv N ⟶ E) ≫ triv E N = (prod.snd ≫ Dv.toPGL N) ≫ PGL.pr N := by
  refine spc_hom_ext fun p T x => ?_
  refine single_ext _ _ (fun i j f => ?_)
  rfl

theorem tri_pullback (E : Spc) (N : ℕ) :
    IsPullback (prod.fst : E ⨯ Dv N ⟶ E) (prod.snd ≫ Dv.toPGL N) (triv E N) (PGL.pr N) := by
  refine isPullback_of_sx (tri_w E N) ?_ ?_
  · intro p T x y h1 h2
    refine prod_sx_ext h1 (vx_ext fun k => ?_)
    exact congrArg (fun z => vxP z k) h2
  · intro p T s t h
    have hp : ∀ i j : Fin (p + 1), ∃ u : Γ(T, ⊤)ˣ, (vxP t i).1 = (u : Γ(T, ⊤)) • (vxP t j).1 := by
      have key : ∀ i j : Fin (p + 1), i ≤ j → ∃ u : Γ(T, ⊤)ˣ, (vxP t i).1 = (u : Γ(T, ⊤)) • (vxP t j).1 := by
        intro i j hij
        let a := (show ComposableArrows (Um N Γ(T, ⊤)) p from t).map (homOfLE hij)
        refine ⟨a.1.2, ?_⟩
        have := a.2
        rw [triv_arrow s t h (homOfLE hij)] at this
        have h3 : ((show ComposableArrows (Um N Γ(T, ⊤)) p from t).obj i).1 = ((a.1.2 : Γ(T, ⊤)ˣ) : Γ(T, ⊤)) • ((show ComposableArrows (Um N Γ(T, ⊤)) p from t).obj j).1 := by simpa using this
        exact h3
      intro i j
      rcases le_total i j with hij | hij
      · exact key i j hij
      · obtain ⟨u, hu⟩ := key j i hij
        refine ⟨u⁻¹, ?_⟩
        rw [hu, smul_smul, Units.inv_mul, one_smul]
    obtain ⟨x, h1, h2⟩ := prod_sx_mk s (Dv.mk (vxP t) hp)
    refine ⟨x, h1, ?_⟩
    rw [map_comp, h2]
    refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j f => ?_)
    exact um_arrow_eq rfl rfl _ _ rfl (triv_arrow s t h f)

end Triv

end UpperTheory.P2
end
