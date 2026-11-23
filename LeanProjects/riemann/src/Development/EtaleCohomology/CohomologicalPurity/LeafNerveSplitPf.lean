import Development.EtaleCohomology.CohomologicalPurity.LeafTailNervePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def Vec.smul' {N k : ℕ} {U : Scheme.{0}} (c : (Γ(U, ⊤))ˣ) (v : Vec N k U) : Vec N k U :=
  ⟨fun i => (c : Γ(U, ⊤)) * v.1 i, fun p => by
    obtain ⟨i, hi, hp⟩ := v.2 p
    refine ⟨i, hi, ?_⟩
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit (X := U) c.isUnit]
    exact ⟨trivial, hp⟩⟩

def tprod {R : Type} [CommRing R] {m : ℕ} (u : Fin m → Rˣ) (i : Fin (m + 1)) : Rˣ :=
  ∏ j : Fin m, if i.val ≤ j.val then u j else 1

theorem tprod_castSucc {R : Type} [CommRing R] {m : ℕ} (u : Fin m → Rˣ) (i : Fin m) :
    tprod u i.castSucc = u i * tprod u i.succ := by
  unfold tprod
  have h : ∀ j : Fin m, (if i.castSucc.val ≤ j.val then u j else 1) =
      (if j = i then u i else 1) * (if i.succ.val ≤ j.val then u j else 1) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · have : j.val ≠ i.val := fun h => hj (Fin.ext h)
      simp only [Fin.val_castSucc, Fin.val_succ, hj, if_false, one_mul]
      by_cases h1 : i.val ≤ j.val
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
  rw [Finset.prod_congr rfl (fun j _ => h j), Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

theorem tprod_last {R : Type} [CommRing R] {m : ℕ} (u : Fin m → Rˣ) : tprod u (Fin.last m) = 1 := by
  unfold tprod
  apply Finset.prod_eq_one
  intro j _
  simp

def vert (N k : ℕ) (n : SimplexCategoryᵒᵖ) : (Pj N k).obj n ⟶ (Pj N k).obj (op (SimplexCategory.mk 0)) :=
  (Pj N k).map (SimplexCategory.const (SimplexCategory.mk 0) n.unop (Fin.last _)).op

def utsT (N k : ℕ) (n : SimplexCategoryᵒᵖ) : (Pj N k).obj n ⟶ Uts n.unop.len where
  app U := TypeCat.ofHom fun x i =>
    ((x : ComposableArrows (Vec N k U.unop) n.unop.len).map' i.val (i.val + 1)).1
  naturality U V f := rfl

def phi (N k : ℕ) (n : SimplexCategoryᵒᵖ) :
    (Pj N k).obj n ⟶ FunctorToTypes.prod ((Pj N k).obj (op (SimplexCategory.mk 0))) (Uts n.unop.len) :=
  FunctorToTypes.prod.lift (vert N k n) (utsT N k n)

theorem chain_ext {N k : ℕ} {U : Scheme.{0}} {m : ℕ} (x y : ComposableArrows (Vec N k U) m)
    (h0 : x.obj (Fin.last m) = y.obj (Fin.last m))
    (hu : ∀ i : Fin m, (x.map' i.val (i.val + 1)).1 = (y.map' i.val (i.val + 1)).1) : x = y := by
  have hobj : ∀ t : ℕ, ∀ i : Fin (m + 1), i.val + t = m → x.obj i = y.obj i := by
    intro t
    induction t with
    | zero =>
      intro i hi
      have : i = Fin.last m := Fin.ext (by simp; omega)
      subst this; exact h0
    | succ t ih =>
      intro i hi
      have hlt : i.val < m := by omega
      have e := ih ⟨i.val + 1, by omega⟩ (by simp; omega)
      apply Subtype.ext; funext j
      have hx := (x.map' i.val (i.val + 1)).2 j
      have hy := (y.map' i.val (i.val + 1)).2 j
      have hu' := hu ⟨i.val, hlt⟩
      change (x.obj i).1 j = (y.obj i).1 j
      erw [hx, hy, hu', e]
  exact ComposableArrows.ext (fun i => hobj (m - i.val) i (by omega))
    (fun i hi => (Vec.hom_subsingleton N k U _ _).elim _ _)

theorem smul'_one {N k : ℕ} {U : Scheme.{0}} (v : Vec N k U) : Vec.smul' 1 v = v := by
  apply Subtype.ext; funext i; simp [Vec.smul']

theorem phi_bij (N k : ℕ) (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) :
    Function.Bijective ((phi N k n).app U) := by
  constructor
  · intro x y hxy
    have h1 := congrArg Prod.fst hxy
    have h2 := congrArg Prod.snd hxy
    apply chain_ext (U := U.unop) x y
    · exact congrArg (fun z : ComposableArrows (Vec N k U.unop) 0 => z.obj 0) h1
    · intro i; exact congrFun h2 i
  · rintro ⟨w, u0⟩
    let u : Fin n.unop.len → (Γ(U.unop, ⊤))ˣ := u0
    let obj : Fin (n.unop.len + 1) → Vec N k U.unop := fun i => Vec.smul' (tprod u i) (w.obj 0)
    let ms : ∀ i : Fin n.unop.len, obj i.castSucc ⟶ obj i.succ := fun i => ⟨u i, fun j => by
      dsimp only [obj, Vec.smul']
      rw [show tprod u i.castSucc = u i * tprod u i.succ from tprod_castSucc u i, Units.val_mul, mul_assoc]⟩
    refine ⟨ComposableArrows.mkOfObjOfMapSucc obj ms, ?_⟩
    apply Prod.ext
    · apply ComposableArrows.ext₀
      change obj (Fin.last _) = w.obj 0
      exact (congrArg (fun c => Vec.smul' c (w.obj 0)) (tprod_last u)).trans (smul'_one _)
    · funext i
      exact congrArg Subtype.val (ComposableArrows.mkOfObjOfMapSucc_map_succ obj ms i.val i.isLt)

instance isIso_phi (N k : ℕ) (n : SimplexCategoryᵒᵖ) : IsIso (phi N k n) := by
  have : ∀ U, IsIso ((phi N k n).app U) := fun U => (isIso_iff_bijective _).2 (phi_bij N k n U)
  exact NatIso.isIso_of_isIso_app _

theorem LeafNerveSplit_of : LeafNerveSplit := by
  intro d n
  refine ⟨asIso (phi (d + 1) 1 n) ≪≫ (FunctorToTypes.binaryProductIso _ _).symm,
    asIso (phi d 0 n) ≪≫ (FunctorToTypes.binaryProductIso _ _).symm, ?_⟩
  apply prod.hom_ext
  · simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc, prod.map_fst,
      reassoc_of% FunctorToTypes.binaryProductIso_inv_comp_fst, FunctorToTypes.binaryProductIso_inv_comp_fst]
    simp only [phi, reassoc_of% FunctorToTypes.prod.lift_fst, FunctorToTypes.prod.lift_fst]
    exact ((Pj.tail d).naturality _).symm
  · simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc, prod.map_snd, Category.comp_id, FunctorToTypes.binaryProductIso_inv_comp_snd]
    simp only [phi, FunctorToTypes.prod.lift_snd]
    rfl

end LateralTheory.CohomologicalPurity.Thom
