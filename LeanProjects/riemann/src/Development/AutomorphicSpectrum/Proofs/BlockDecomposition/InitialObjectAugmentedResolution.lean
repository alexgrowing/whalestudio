import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

noncomputable section

namespace GlobalTheory.CompanionTheory.InitialCoh

open GlobalTheory.CatH (face toLast)

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T₀ : C}

def pre (h : Limits.IsInitial T₀) {n : ℕ} (s : ComposableArrows C n) : ComposableArrows C (n + 1) :=
  s.precomp (h.to s.left)

theorem pre_map (h : Limits.IsInitial T₀) {n : ℕ} (s : ComposableArrows C n) (a b : Fin (n + 1)) (hab : a ≤ b) :
    (pre h s).map (homOfLE (Fin.succ_le_succ_iff.2 hab)) = s.map (homOfLE hab) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  rfl

theorem map_homOfLE_source_eq {m : ℕ} (s : ComposableArrows C m) {a a' b : Fin (m + 1)} (hab : a ≤ b) (hab' : a' ≤ b) (e : a = a') :
    s.map (homOfLE hab) = eqToHom (congrArg s.obj e) ≫ s.map (homOfLE hab') := by
  subst e
  simp

theorem val_congr (F : C ⥤ ModuleCat.{w} R) {m : ℕ} (y : Cn F m) {a b : ComposableArrows C m} (e : a = b) {X : C}
    (φ : a.obj (Fin.last m) ⟶ X) (ψ : b.obj (Fin.last m) ⟶ X)
    (hφ : φ = eqToHom (congrArg (fun c : ComposableArrows C m => c.obj (Fin.last m)) e) ≫ ψ) :
    (F.map φ).hom (y a) = (F.map ψ).hom (y b) := by
  subst e
  simp only [eqToHom_refl, Category.id_comp] at hφ
  rw [hφ]

theorem hom_from_initial (h : Limits.IsInitial T₀) {X Y : C} (e : X = T₀) (a b : X ⟶ Y) : a = b := by
  subst e
  exact h.hom_ext a b

theorem whisker_congr {k l : ℕ} (a b : Fin (k + 1) ⥤ Fin (l + 1)) (e : ∀ i, a.obj i = b.obj i) (P : ComposableArrows C l) :
    a ⋙ P = b ⋙ P := by
  have : a = b := CategoryTheory.Functor.ext e (fun _ _ _ => Subsingleton.elim _ _)
  rw [this]

theorem face_zero_pre (h : Limits.IsInitial T₀) {n : ℕ} (s : ComposableArrows C n) : face 0 (pre h s) = s :=
  whisker_congr _ (Fin.succFunctor _) (fun i => by simp) (pre h s)

theorem face_face {m : ℕ} (P : ComposableArrows C (m + 2)) (a a' : Fin (m + 2)) (b b' : Fin (m + 3))
    (e : ∀ x, b.succAbove (a.succAbove x) = b'.succAbove (a'.succAbove x)) : face a (face b P) = face a' (face b' P) :=
  whisker_congr ((Fin.succAboveOrderEmb a).monotone.functor ⋙ (Fin.succAboveOrderEmb b).monotone.functor)
    ((Fin.succAboveOrderEmb a').monotone.functor ⋙ (Fin.succAboveOrderEmb b').monotone.functor) e P

theorem eq_of_face_zero (h : Limits.IsInitial T₀) {n : ℕ} {P Q : ComposableArrows C (n + 1)} (h0 : P.obj 0 = T₀) (h1 : Q.obj 0 = T₀)
    (e : face 0 P = face 0 Q) : P = Q := by
  refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
  · refine Fin.cases (h0.trans h1.symm) (fun j => ?_) i
    have := Functor.congr_obj e j
    simpa [face] using this
  · cases i with
    | zero => exact hom_from_initial h h0 _ _
    | succ i =>
      exact Functor.congr_hom e (homOfLE (Nat.le_succ i) : (⟨i, by omega⟩ : Fin (n + 1)) ⟶ ⟨i + 1, by omega⟩)

theorem face_succ_pre (h : Limits.IsInitial T₀) {n : ℕ} (s : ComposableArrows C (n + 1)) (i : Fin (n + 2)) :
    face i.succ (pre h s) = pre h (face i s) := by
  refine eq_of_face_zero h ?_ rfl ?_
  · change (pre h s).obj (i.succ.succAbove 0) = T₀
    rw [Fin.succ_succAbove_zero]
    rfl
  · rw [face_zero_pre, face_face (pre h s) 0 i i.succ 0 (fun x => by simp [Fin.succ_succAbove_succ]), face_zero_pre]

theorem val_zero (F : C ⥤ ModuleCat.{w} R) (h : Limits.IsInitial T₀) {n : ℕ} (y : Cn F n) (s : ComposableArrows C n) :
    (F.map (toLast 0 (pre h s))).hom (y (face 0 (pre h s))) = y s := by
  have e : (0 : Fin (n + 2)).succAbove (Fin.last n) = Fin.last (n + 1) := by simp
  have := val_congr F y (face_zero_pre h s) (toLast 0 (pre h s)) (𝟙 _)
    ((map_homOfLE_source_eq (pre h s) _ le_rfl e).trans
      (congrArg (fun g => eqToHom _ ≫ g) ((pre h s).map_id (Fin.last (n + 1)))))
  refine this.trans ?_
  rw [F.map_id]
  rfl

theorem val_succ (F : C ⥤ ModuleCat.{w} R) (h : Limits.IsInitial T₀) {n : ℕ} (y : Cn F (n + 1))
    (s : ComposableArrows C (n + 1)) (i : Fin (n + 2)) :
    (F.map (toLast i.succ (pre h s))).hom (y (face i.succ (pre h s))) =
      (F.map (toLast i s)).hom (y (pre h (face i s))) := by
  have e : i.succ.succAbove (Fin.last (n + 1)) = (i.succAbove (Fin.last n)).succ := by
    rw [← Fin.succ_last, Fin.succ_succAbove_succ]
  exact val_congr F y (face_succ_pre h s i) (toLast i.succ (pre h s)) (toLast i s)
    ((map_homOfLE_source_eq (pre h s) _ (Fin.succ_le_succ_iff.2 (Fin.le_last _)) e).trans
      (congrArg (fun g => eqToHom _ ≫ g) (pre_map h s _ _ (Fin.le_last _))))

def con (F : C ⥤ ModuleCat.{w} R) (h : Limits.IsInitial T₀) (n : ℕ) (y : Cn F (n + 1)) : Cn F n := fun s => y (pre h s)

theorem d_con (F : C ⥤ ModuleCat.{w} R) (h : Limits.IsInitial T₀) (n : ℕ) (y : Cn F (n + 1)) (hy : d F (n + 1) y = 0) :
    d F n (con F h n y) = y := by
  funext s
  have key : ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i (pre h s))).hom (y (face i (pre h s))) = 0 :=
    congrFun hy (pre h s)
  rw [Fin.sum_univ_succ] at key
  simp only [val_succ, Fin.val_succ, Fin.val_zero, pow_zero, one_smul, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib] at key
  rw [val_zero] at key
  exact (add_neg_eq_zero.1 key).symm

theorem resUpTo_one (F : C ⥤ ModuleCat.{w} R) (T₀ : C) (h : Limits.IsInitial T₀) :
    (cx F).ResUpTo 1 (aug F fun T => (F.map (h.to T)).hom) := by
  have hid : h.to T₀ = 𝟙 T₀ := h.hom_ext _ _
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun n y hy => ⟨con F h n y, ?_⟩⟩
  · funext s
    change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom ((F.map (h.to ((face i s).obj (Fin.last 0)))).hom x) = 0
    have e : ∀ i : Fin 2, (F.map (toLast i s)).hom ((F.map (h.to ((face i s).obj (Fin.last 0)))).hom x) =
        (F.map (h.to (s.obj (Fin.last 1)))).hom x := fun i => by
      rw [← ModuleCat.comp_apply, ← F.map_comp, h.hom_ext (h.to _ ≫ toLast i s) (h.to _)]
    simp only [e]
    simp [Fin.sum_univ_two]
  · have : (F.map (h.to T₀)).hom x = 0 := congrFun hx (ComposableArrows.mk₀ T₀)
    rw [hid] at this
    simpa using this
  · refine ⟨y (ComposableArrows.mk₀ T₀), funext fun s => ?_⟩
    have key : ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i (pre h s))).hom (y (face i (pre h s))) = 0 :=
      congrFun hy (pre h s)
    have e1 : face 1 (pre h s) = ComposableArrows.mk₀ T₀ := ComposableArrows.ext₀ rfl
    have t1 : (F.map (toLast 1 (pre h s))).hom (y (face 1 (pre h s))) =
        (F.map (h.to (s.obj (Fin.last 0)))).hom (y (ComposableArrows.mk₀ T₀)) :=
      val_congr F y e1 _ _ (hom_from_initial h rfl _ _)
    rw [Fin.sum_univ_two, t1] at key
    have t0 := val_zero F h y s
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul] at key
    rw [t0] at key
    rw [one_smul]
    exact (add_neg_eq_zero.1 key).symm
  · rw [one_smul]
    exact d_con F h n y hy

end GlobalTheory.CompanionTheory.InitialCoh
