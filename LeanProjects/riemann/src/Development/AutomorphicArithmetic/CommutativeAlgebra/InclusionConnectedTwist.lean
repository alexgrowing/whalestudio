import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

noncomputable section

namespace UpperTheory.SimplicialRelationHom

variable (D : Type) [CommRing D]

private def Rg : RF where
  obj A _ := D →+* A
  map f x := f.comp x
  map_id _ := rfl
  map_comp _ _ _ := rfl
  rel x y := x = y
  map_rel _ _ _ h := by rw [h]

private def forget (N : ℕ) : (Vec D N).Hom (Rg D) where
  app _ _ x := x.1.1
  nat _ _ := rfl

private theorem forget_rel (N : ℕ) : (forget D N).Rel := fun h => h.1

variable {D}

private theorem rel_iff {N : ℕ} {A : Type} [CommRing A] {x y : (Vec D N).obj A} :
    (Vec D N).rel x y ↔ x.1.1 = y.1.1 ∧ ∃ u : Aˣ, x.1.2 = fun j => (u : A) * y.1.2 j := Iff.rfl

private theorem unit_unique {A : Type} [CommRing A] {N : ℕ} {w : Fin N → A} (hw : Ideal.span (Set.range w) = ⊤)
    {u u' : A} (h : ∀ j, u * w j = u' * w j) : u = u' := by
  have key : ∀ a ∈ Ideal.span (Set.range w), u * a = u' * a := by
    intro a ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨j, rfl⟩
      exact h j
    · simp
    · intro a b _ _ h1 h2
      rw [mul_add, mul_add, h1, h2]
    · intro c a _ h1
      simp only [smul_eq_mul]
      rw [mul_left_comm, h1, mul_left_comm]
  simpa using key 1 (by rw [hw]; trivial)

private theorem um_hom_ext {A : Type} [CommRing A] {N : ℕ} {v w : Um N A} (p q : v ⟶ w) (h : p.1.1 = q.1.1) : p = q := by
  refine Subtype.ext (Prod.ext h (Units.ext ?_))
  refine unit_unique w.2 fun j => ?_
  have h1 := congrFun p.2 j
  have h2 := congrFun q.2 j
  rw [h] at h1
  simpa using h1.symm.trans h2

private def toUm {N : ℕ} {A : Type} [CommRing A] (x : (Vec D N).obj A) : Um N A := ⟨x.1.2, x.2⟩

private def relHom {N : ℕ} {A : Type} [CommRing A] {x y : (Vec D N).obj A} (h : (Vec D N).rel x y) :
    toUm x ⟶ toUm y :=
  ⟨(1, (rel_iff.1 h).2.choose), by
    have := (rel_iff.1 h).2.choose_spec
    funext j
    simpa [toUm] using congrFun this j⟩

private def tFun {n N : ℕ} {A : Type} [CommRing A] (x : Fin (n + 1) → (Vec D N).obj A)
    (hx : ∀ i j, (Vec D N).rel (x i) (x j)) : Fin (n + 1) ⥤ Um N A where
  obj i := toUm (x i)
  map {i j} _ := relHom (hx i j)
  map_id i := um_hom_ext _ _ rfl
  map_comp _ _ := um_hom_ext _ _ (mul_one _).symm

private theorem tFun_base {n N : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (x : Fin (n + 1) → (Vec D N).obj A) (hx : ∀ i j, (Vec D N).rel (x i) (x j)) :
    tFun (fun i => (Vec D N).map f (x i)) (fun i j => (Vec D N).map_rel f (hx i j)) = tFun x hx ⋙ Um.map N f :=
  CategoryTheory.Functor.hext (fun _ => rfl) fun i j p => heq_of_eq (um_hom_ext _ _ (map_one (Matrix.GeneralLinearGroup.map f)).symm)

private theorem tFun_pre {m n N : ℕ} {A : Type} [CommRing A] (g : Fin (m + 1) →o Fin (n + 1))
    (x : Fin (n + 1) → (Vec D N).obj A) (hx : ∀ i j, (Vec D N).rel (x i) (x j)) :
    tFun (fun i => x (g i)) (fun i j => hx _ _) = g.monotone.functor ⋙ tFun x hx :=
  CategoryTheory.Functor.hext (fun _ => rfl) fun i j p => heq_of_eq (um_hom_ext _ _ rfl)

private def tMap (D : Type) [CommRing D] (N : ℕ) : CN (Vec D N) ⟶ PGL N where
  app n :=
    { app := fun U => TypeCat.ofHom fun x =>
        (show Fin (n.unop.len + 1) ⥤ Um N Γ(U.unop, ⊤) from tFun x.1 x.2)
      naturality := fun U V f => by
        ext x
        exact tFun_base f.unop.appTop.hom x.1 x.2 }
  naturality n m θ := by
    ext U x
    exact tFun_pre θ.unop.toOrderHom x.1 x.2

private def trivF (n N : ℕ) (A : Type) [CommRing A] : Fin (n + 1) ⥤ SingleObj (GL (Fin N) A) :=
  (Functor.const _).obj (SingleObj.star _)

private def triv (E : Spc) (N : ℕ) : E ⟶ ofCat (glCat N) where
  app n :=
    { app := fun U => TypeCat.ofHom fun _ =>
        (show Fin (n.unop.len + 1) ⥤ SingleObj (GL (Fin N) Γ(U.unop, ⊤)) from trivF _ N _)
      naturality := fun U V f => by
        ext x
        refine CategoryTheory.Functor.hext (fun _ => rfl) fun i j p => heq_of_eq ?_
        exact (map_one (Matrix.GeneralLinearGroup.map f.unop.appTop.hom)).symm }
  naturality n m θ := by
    ext U x
    rfl

private theorem singleObj_map_eq {C : Type} [Category C] {M : Type} [Monoid M] {F G : C ⥤ SingleObj M} (h : F = G)
    {i j : C} (p : i ⟶ j) : (show M from F.map p) = (show M from G.map p) := by
  subst h
  rfl

variable (D) in

private theorem sq (N : ℕ) :
    IsPullback (CN.map (forget D N) (forget_rel D N)) (tMap D N) (triv (CN (Rg D)) N) (PGL.pr N) := by
  refine IsPullback.of_forall_isPullback_app fun n => IsPullback.of_forall_isPullback_app fun U =>
    (Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩
  · ext x
    refine (CategoryTheory.Functor.hext (fun _ => rfl) fun i j p => heq_of_eq rfl :
      (trivF _ N _ : Fin (n.unop.len + 1) ⥤ SingleObj (GL (Fin N) Γ(U.unop, ⊤))) = tFun x.1 x.2 ⋙ Um.toGL N _)
  · rintro x y ⟨h1, h2⟩
    refine Subtype.ext (funext fun i => Subtype.ext (Prod.ext ?_ ?_))
    · exact congrFun (congrArg Subtype.val h1) i
    · have h3 : tFun x.1 x.2 = tFun y.1 y.2 := h2
      exact congrArg Subtype.val (congrArg (fun F => F.obj i) h3)
  · intro r F h
    have h' : (trivF _ N _ : Fin (n.unop.len + 1) ⥤ SingleObj (GL (Fin N) Γ(U.unop, ⊤))) =
      (show Fin (n.unop.len + 1) ⥤ Um N Γ(U.unop, ⊤) from F) ⋙ Um.toGL N _ := h
    obtain ⟨F', rfl⟩ : ∃ F' : Fin (n.unop.len + 1) ⥤ Um N Γ(U.unop, ⊤), F' = F := ⟨F, rfl⟩
    have ha : ∀ {i j : Fin (n.unop.len + 1)} (p : i ⟶ j), (F'.map p).1.1 = 1 := fun p =>
      (singleObj_map_eq h' p).symm
    have hle : ∀ {i j : Fin (n.unop.len + 1)}, i ≤ j → ∃ u : Γ(U.unop, ⊤)ˣ, (F'.obj i).1 = fun k => (u : Γ(U.unop, ⊤)) * (F'.obj j).1 k := by
      intro i j hij
      refine ⟨(F'.map (homOfLE hij)).1.2, funext fun k => ?_⟩
      have h2 := congrFun (F'.map (homOfLE hij)).2 k
      rw [ha] at h2
      simpa using h2
    let x : Fin (n.unop.len + 1) → (Vec D N).obj Γ(U.unop, ⊤) := fun i => ⟨((r.1 i : D →+* Γ(U.unop, ⊤)), (F'.obj i).1), (F'.obj i).2⟩
    have hx : ∀ i j, (Vec D N).rel (x i) (x j) := by
      intro i j
      refine rel_iff.2 ⟨r.2 i j, ?_⟩
      rcases le_total i j with hij | hij
      · exact hle hij
      · obtain ⟨u, hu⟩ := hle hij
        refine ⟨u⁻¹, funext fun k => ?_⟩
        change (F'.obj i).1 k = ((u⁻¹ : Γ(U.unop, ⊤)ˣ) : Γ(U.unop, ⊤)) * (F'.obj j).1 k
        rw [hu]
        simp
    refine ⟨⟨x, hx⟩, rfl, ?_⟩
    exact CategoryTheory.Functor.hext (fun _ => rfl) fun i j p => heq_of_eq (um_hom_ext _ _ (ha p).symm)

private theorem pr_incl (d : ℕ) : CN.map (incl D d) (incl_rel D d) ≫ CN.map (forget D (d + 1)) (forget_rel D (d + 1)) =
    CN.map (forget D d) (forget_rel D d) := rfl

private theorem eqv_iso {R : Type} [CommRing R] (F : Shv R) {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F :=
  eqv_section F e.hom e.inv e.hom_inv_id fun n => by
    refine (Function.bijective_iff_has_inverse).2 ⟨pull R e.hom F n, fun x => ?_, fun x => ?_⟩
    · rw [← pull_comp, e.hom_inv_id, pull_id]
    · rw [← pull_comp, e.inv_hom_id, pull_id]

private theorem invertible_nerve (q : ℕ) (hq : IsUnit (q : D)) : Inv q (CN (Rg D)) := by
  rintro U ⟨x⟩
  have h1 := hq.map (show D →+* Γ(U, ⊤) from x.1 0)
  rwa [map_natCast] at h1

private theorem line_incl (d : ℕ) : CN.map (incl D d) (incl_rel D d) ≫ tMap D (d + 1) ≫ PGL.line (d + 1) =
    tMap D d ≫ PGL.line d := by
  ext n U x
  refine (CategoryTheory.Functor.hext (fun _ => rfl) fun i j p => heq_of_eq ?_ :
    (tFun (fun i => (incl D d).app _ (x.1 i)) (fun i j => incl_rel D d (x.2 i j)) ⋙ Um.toLine (d + 1) _ :
      Fin (n.unop.len + 1) ⥤ SingleObj (GL (Fin 1) Γ(U.unop, ⊤))) = tFun x.1 x.2 ⋙ Um.toLine d _)
  refine congrArg (Matrix.GeneralLinearGroup.scalar (Fin 1)) (Units.ext (unit_unique (x.1 j).2 fun k => ?_))
  have h1 := congrFun (rel_iff.1 (incl_rel D d (x.2 i j))).2.choose_spec k.castSucc
  have h2 := congrFun (rel_iff.1 (x.2 i j)).2.choose_spec k
  have e : ∀ y : (Vec D d).obj Γ(U.unop, ⊤), ((incl D d).app _ y).1.2 k.castSucc = y.1.2 k := fun y => by
    change Fin.snoc (α := fun _ => Γ(U.unop, ⊤)) y.1.2 0 k.castSucc = _
    simp
  simp only [e] at h1
  exact h1.symm.trans h2

end UpperTheory.SimplicialRelationHom

open UpperTheory.SimplicialRelationHom in
theorem UpperTheory.inclusion_connected_twist :
    LeafProj → A1 → A5 → A7 → A9 → A10 → D1 → ∀ (q : ℕ) [NeZero q] (i : ℤ) (d : ℕ) (D : Type) [CommRing D], IsUnit (q : D) → Conn _ (tw q i) (2 * d) (CN.map (incl D d) (incl_rel D d)) := by
  intro hP a1 a5 a7 a9 a10 d1 q _ i d D _ hq
  let e0 := (sq D d).isoPullback
  let e1 := (sq D (d + 1)).isoPullback
  have hs := hP a1 a5 a7 a9 a10 d1 q i (E := CN (Rg D)) (N := d) (triv _ d) (triv _ (d + 1)) (invertible_nerve q hq)
    (e0.inv ≫ CN.map (incl D d) (incl_rel D d) ≫ e1.hom) ?_ ?_
  · refine (conn_sq _ _ _ _ e0.hom e1.hom ?_ (eqv_iso _ e0) (eqv_iso _ e1)).2 hs
    simp
  · simp only [Category.assoc]
    rw [(sq D (d + 1)).isoPullback_hom_fst, pr_incl]
    exact (sq D d).isoPullback_inv_fst
  · simp only [Category.assoc]
    rw [IsPullback.isoPullback_hom_snd_assoc, line_incl]
    rw [← Category.assoc, (sq D d).isoPullback_inv_snd]

end
