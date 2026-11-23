import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OfNatTrans

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory
open GlobalTheory.CatH (face toLast)

namespace UpperTheory.Ru.crystallineComparison.Th

section Snoc

variable {E : Type*} [Category E] {m : ℕ} (s : ComposableArrows E m) {X : E} (a : s.obj (Fin.last m) ⟶ X)

def snObj (X : E) (i : Fin (m + 2)) : E := if h : (i : ℕ) < m + 1 then s.obj ⟨i, h⟩ else X

theorem snObj_lt (X : E) {i : Fin (m + 2)} (h : (i : ℕ) < m + 1) : snObj s X i = s.obj ⟨i, h⟩ := dif_pos h

theorem snObj_ge (X : E) {i : Fin (m + 2)} (h : ¬ (i : ℕ) < m + 1) : snObj s X i = X := dif_neg h

def snMap (i j : Fin (m + 2)) (hij : i ≤ j) : snObj s X i ⟶ snObj s X j :=
  if hj : (j : ℕ) < m + 1 then
    eqToHom (snObj_lt s X (lt_of_le_of_lt (Fin.le_def.1 hij) hj)) ≫
      s.map (homOfLE (show (⟨i, lt_of_le_of_lt (Fin.le_def.1 hij) hj⟩ : Fin (m + 1)) ≤ ⟨j, hj⟩ from Fin.le_def.2 (Fin.le_def.1 hij))) ≫
        eqToHom (snObj_lt s X hj).symm
  else if hi : (i : ℕ) < m + 1 then
    eqToHom (snObj_lt s X hi) ≫ s.map (homOfLE (Fin.le_last _)) ≫ a ≫ eqToHom (snObj_ge s X hj).symm
  else eqToHom ((snObj_ge s X hi).trans (snObj_ge s X hj).symm)

theorem snMap_lt {i j : Fin (m + 2)} (hij : i ≤ j) (hj : (j : ℕ) < m + 1) :
    snMap s a i j hij = eqToHom (snObj_lt s X (lt_of_le_of_lt (Fin.le_def.1 hij) hj)) ≫
      s.map (homOfLE (show (⟨i, lt_of_le_of_lt (Fin.le_def.1 hij) hj⟩ : Fin (m + 1)) ≤ ⟨j, hj⟩ from Fin.le_def.2 (Fin.le_def.1 hij))) ≫
        eqToHom (snObj_lt s X hj).symm := dif_pos hj

theorem snMap_mid {i j : Fin (m + 2)} (hij : i ≤ j) (hj : ¬ (j : ℕ) < m + 1) (hi : (i : ℕ) < m + 1) :
    snMap s a i j hij = eqToHom (snObj_lt s X hi) ≫ s.map (homOfLE (Fin.le_last _)) ≫ a ≫ eqToHom (snObj_ge s X hj).symm := by
  rw [snMap, dif_neg hj, dif_pos hi]

theorem snMap_top {i j : Fin (m + 2)} (hij : i ≤ j) (hj : ¬ (j : ℕ) < m + 1) (hi : ¬ (i : ℕ) < m + 1) :
    snMap s a i j hij = eqToHom ((snObj_ge s X hi).trans (snObj_ge s X hj).symm) := by
  rw [snMap, dif_neg hj, dif_neg hi]

def snoc : ComposableArrows E (m + 1) where
  obj := snObj s X
  map {i j} f := snMap s a i j (leOfHom f)
  map_id i := by
    by_cases hi : (i : ℕ) < m + 1
    · rw [snMap_lt s a _ hi]
      simp [homOfLE_refl]
    · rw [snMap_top s a _ hi hi]
      simp
  map_comp {i j k} f g := by
    have hij := leOfHom f
    have hjk := leOfHom g
    by_cases hk : (k : ℕ) < m + 1
    · have hj : (j : ℕ) < m + 1 := lt_of_le_of_lt (Fin.le_def.1 hjk) hk
      rw [snMap_lt s a _ hk, snMap_lt s a _ hk, snMap_lt s a _ hj]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Functor.map_comp_assoc]
      rfl
    · by_cases hj : (j : ℕ) < m + 1
      · have hi : (i : ℕ) < m + 1 := lt_of_le_of_lt (Fin.le_def.1 hij) hj
        rw [snMap_mid s a _ hk hi, snMap_mid s a _ hk hj, snMap_lt s a _ hj]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [← Functor.map_comp_assoc]
        rfl
      · by_cases hi : (i : ℕ) < m + 1
        · rw [snMap_mid s a _ hk hi, snMap_mid s a _ hj hi, snMap_top s a _ hk hj]
          simp
        · rw [snMap_top s a _ hk hi, snMap_top s a _ hj hi, snMap_top s a _ hk hj]
          simp

theorem snoc_last : (snoc s a).obj (Fin.last (m + 1)) = X := snObj_ge s X (by simp)

end Snoc
section Chains

variable {E : Type*} [Category E]

theorem chain_ext {n : ℕ} {T T' : ComposableArrows E n} (ho : ∀ i, T.obj i = T'.obj i)
    (hm : ∀ i j (h : i ≤ j), T.map (homOfLE h) = eqToHom (ho i) ≫ T'.map (homOfLE h) ≫ eqToHom (ho j).symm) : T = T' :=
  CategoryTheory.Functor.ext ho fun i j f => hm i j (leOfHom f)

theorem sigma_chain_eq {n : ℕ} {X : E} {s s' : ComposableArrows E n} {b : s.obj (Fin.last n) ⟶ X}
    {b' : s'.obj (Fin.last n) ⟶ X} (h : s = s') (w : b = eqToHom (by rw [h]) ≫ b') :
    (⟨s, b⟩ : Σ t : ComposableArrows E n, t.obj (Fin.last n) ⟶ X) = ⟨s', b'⟩ := by
  subst h
  simp only [eqToHom_refl, Category.id_comp] at w
  rw [w]

variable {m : ℕ} (s : ComposableArrows E m) {X : E} (a : s.obj (Fin.last m) ⟶ X)

theorem snObj_val {p : Fin (m + 2)} {q : Fin (m + 1)} (h : (p : ℕ) = q) : snObj s X p = s.obj q :=
  (snObj_lt s X (h ▸ q.2)).trans (congrArg s.obj (Fin.ext h))

theorem snMap_val {p p' : Fin (m + 2)} {q q' : Fin (m + 1)} (h : (p : ℕ) = q) (h' : (p' : ℕ) = q') (hp : p ≤ p') (hq : q ≤ q') :
    snMap s a p p' hp = eqToHom (snObj_val s h) ≫ s.map (homOfLE hq) ≫ eqToHom (snObj_val s h').symm := by
  obtain ⟨q, hq0⟩ := q
  obtain ⟨q', hq1⟩ := q'
  obtain rfl : (p : ℕ) = q := h
  obtain rfl : (p' : ℕ) = q' := h'
  exact snMap_lt s a hp hq1

theorem snMap_val_top {p p' : Fin (m + 2)} {q : Fin (m + 1)} (h : (p : ℕ) = q) (h' : ¬ (p' : ℕ) < m + 1) (hp : p ≤ p') :
    snMap s a p p' hp = eqToHom (snObj_val s h) ≫ s.map (homOfLE (Fin.le_last q)) ≫ a ≫ eqToHom (snObj_ge s X h').symm := by
  obtain ⟨q, hq0⟩ := q
  obtain rfl : (p : ℕ) = q := h
  exact snMap_mid s a hp h' hq0

def snε : (snoc s a).obj (Fin.last (m + 1)) ⟶ X := eqToHom (snoc_last s a)

theorem face_snoc_last : face (Fin.last (m + 1)) (snoc s a) = s := by
  have hv : ∀ i : Fin (m + 1), (((Fin.last (m + 1)).succAbove i : Fin (m + 2)) : ℕ) = i := fun i => by simp
  refine chain_ext (fun i => snObj_val s (hv i)) fun i j h => ?_
  exact snMap_val s a (hv i) (hv j) ((Fin.strictMono_succAbove _).monotone h) h

theorem gen_snoc_last :
    (⟨face (Fin.last (m + 1)) (snoc s a), toLast (Fin.last (m + 1)) (snoc s a) ≫ snε s a⟩ :
      Σ t : ComposableArrows E m, t.obj (Fin.last m) ⟶ X) = ⟨s, a⟩ := by
  refine sigma_chain_eq (face_snoc_last s a) ?_
  have hv : (((Fin.last (m + 1)).succAbove (Fin.last m) : Fin (m + 2)) : ℕ) = (Fin.last m : Fin (m + 1)) := by simp
  have e : toLast (Fin.last (m + 1)) (snoc s a) = eqToHom (snObj_val s hv) ≫ s.map (homOfLE (Fin.le_last _)) ≫ a ≫
      eqToHom (snObj_ge s X (by simp)).symm := snMap_val_top s a hv (by simp) (Fin.le_last _)
  rw [e]
  simp [snε, homOfLE_refl]

theorem snoc_reindex {n : ℕ} (f : Fin (n + 1) → Fin (m + 1)) (hf : Monotone f) (g : Fin (n + 2) → Fin (m + 2)) (hg : Monotone g)
    (h1 : ∀ (p : Fin (n + 2)) (hp : (p : ℕ) < n + 1), (g p : ℕ) = f ⟨p, hp⟩)
    (h2 : ∀ p : Fin (n + 2), ¬ (p : ℕ) < n + 1 → ¬ (g p : ℕ) < m + 1) :
    hg.functor ⋙ snoc s a = snoc (hf.functor ⋙ s) (s.map (homOfLE (Fin.le_last (f (Fin.last n)))) ≫ a) := by
  have ho : ∀ p, (hg.functor ⋙ snoc s a).obj p = (snoc (hf.functor ⋙ s) (s.map (homOfLE (Fin.le_last (f (Fin.last n)))) ≫ a)).obj p := by
    intro p
    by_cases hp : (p : ℕ) < n + 1
    · exact (snObj_val s (h1 p hp)).trans (snObj_lt (hf.functor ⋙ s) X hp).symm
    · exact (snObj_ge s X (h2 p hp)).trans (snObj_ge (hf.functor ⋙ s) X hp).symm
  refine chain_ext ho fun p p' h => ?_
  have e1 : (hg.functor ⋙ snoc s a).map (homOfLE h) = snMap s a (g p) (g p') (hg h) := rfl
  have e2 : (snoc (hf.functor ⋙ s) (s.map (homOfLE (Fin.le_last (f (Fin.last n)))) ≫ a)).map (homOfLE h) =
    snMap (hf.functor ⋙ s) (s.map (homOfLE (Fin.le_last (f (Fin.last n)))) ≫ a) p p' h := rfl
  rw [e1, e2]
  by_cases hp' : (p' : ℕ) < n + 1
  · have hp : (p : ℕ) < n + 1 := lt_of_le_of_lt (Fin.le_def.1 h) hp'
    rw [snMap_val s a (h1 p hp) (h1 p' hp') (hg h) (hf (Fin.le_def.2 (Fin.le_def.1 h))), snMap_lt _ _ h hp']
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    rfl
  · by_cases hp : (p : ℕ) < n + 1
    · rw [snMap_val_top s a (h1 p hp) (h2 p' hp') (hg h), snMap_mid _ _ h hp' hp]
      simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
      have e3 : s.map (homOfLE (Fin.le_last (f ⟨p, hp⟩))) =
          (hf.functor ⋙ s).map (homOfLE (Fin.le_last (⟨p, hp⟩ : Fin (n + 1)))) ≫ s.map (homOfLE (Fin.le_last (f (Fin.last n)))) := by
        change _ = s.map _ ≫ s.map _
        rw [← Functor.map_comp]
        rfl
      rw [e3]
      simp only [Category.assoc]
    · rw [snMap_top s a (hg h) (h2 p' hp') (h2 p hp), snMap_top _ _ h hp' hp]
      simp

end Chains

section Face

variable {E : Type*} [Category E] {m : ℕ} (s : ComposableArrows E (m + 1)) {X : E} (a : s.obj (Fin.last (m + 1)) ⟶ X)

private theorem sa_lt (i : Fin (m + 2)) (p : Fin (m + 2)) (hp : (p : ℕ) < m + 1) :
    ((i.castSucc.succAbove p : Fin (m + 3)) : ℕ) = (i.succAbove ⟨p, hp⟩ : Fin (m + 2)) := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

private theorem sa_ge (i : Fin (m + 2)) (p : Fin (m + 2)) (hp : ¬ (p : ℕ) < m + 1) :
    ¬ ((i.castSucc.succAbove p : Fin (m + 3)) : ℕ) < m + 2 := by
  have h1 : (p : ℕ) = m + 1 := by omega
  have h2 := i.2
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp <;> omega

theorem face_snoc_castSucc (i : Fin (m + 2)) : face i.castSucc (snoc s a) = snoc (face i s) (toLast i s ≫ a) :=
  snoc_reindex s a (Fin.succAboveOrderEmb i) (Fin.succAboveOrderEmb i).monotone (Fin.succAboveOrderEmb i.castSucc)
    (Fin.succAboveOrderEmb i.castSucc).monotone (sa_lt i) (sa_ge i)

theorem gen_snoc_castSucc (i : Fin (m + 2)) :
    (⟨face i.castSucc (snoc s a), toLast i.castSucc (snoc s a) ≫ snε s a⟩ :
      Σ t : ComposableArrows E (m + 1), t.obj (Fin.last (m + 1)) ⟶ X) =
      ⟨snoc (face i s) (toLast i s ≫ a), snε _ _⟩ := by
  refine sigma_chain_eq (face_snoc_castSucc s a i) ?_
  have h0 : ¬ ((i.castSucc.succAbove (Fin.last (m + 1)) : Fin (m + 3)) : ℕ) < m + 2 := sa_ge i _ (by simp)
  have e : toLast i.castSucc (snoc s a) = eqToHom ((snObj_ge s X h0).trans (snObj_ge s X (by simp)).symm) :=
    snMap_top s a (Fin.le_last _) (by simp) h0
  rw [e]
  simp [snε]

end Face

end UpperTheory.Ru.crystallineComparison.Th
