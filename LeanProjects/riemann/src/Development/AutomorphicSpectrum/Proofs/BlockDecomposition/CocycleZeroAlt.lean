import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Onto

universe u v w

noncomputable section

namespace GlobalTheory.CompanionTheory.CovDescent

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {C : Type u} [Category.{v} C]
  (F : C ⥤ ModuleCat.{w} R) (U : ι → ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q)

theorem cosieve_capU (hU : ∀ α, Cosieve (U α)) (S : Finset ι) : Cosieve (capU U S) := fun _ _ φ h =>
  ⟨h.1.imp fun a ha => hU a φ ha, fun α hα => hU α φ (h.2 α hα)⟩

variable {U} in
theorem capU_mono {S T : Finset ι} (h : S ⊆ T) {X : C} (hX : capU U T X) : capU U S X :=
  ⟨hX.1, fun α hα => hX.2 α (h hα)⟩

variable {U} in
theorem capU_cons {n : ℕ} {a : ι} {i : Fin n → ι} {T : C} (ha : U a T) (hi : capU U (ent i) T) :
    capU U (ent (Fin.cons (α := fun _ => ι) a i)) T := by
  refine ⟨⟨a, ha⟩, fun α hα => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hα
  refine Fin.cases ?_ (fun k => ?_) k
  · exact ha
  · exact hi.2 _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))

def liftC (hU : ∀ α, Cosieve (U α)) {n : ℕ} (S : Finset ι) (s : ComposableArrows C n)
    (h : capU U S (s.obj 0)) : ComposableArrows (capU U S).FullSubcategory n :=
  (capU U S).lift s fun k => cosieve_capU U hU S (s.map (homOfLE (Fin.zero_le k))) h

abbrev Tm (n : ℕ) : PM.{max u v w} R ι := (covSy F U hQ).term n

def evL (hU : ∀ α, Cosieve (U α)) {n : ℕ} (S : Finset ι) (s : ComposableArrows C n)
    (h : capU U S (s.obj 0)) : (Tm F U hQ n).M S →ₗ[R] F.obj (s.obj (Fin.last n)) :=
  (LinearMap.proj (R := R) (φ := fun t : ComposableArrows (capU U S).FullSubcategory n =>
    ((capU U S).ι ⋙ F).obj (t.obj (Fin.last n))) (liftC U hU S s h)) ∘ₗ
    (relS ((capU U S).ι ⋙ F) (fun T => Q T.obj) n).subtype

variable {F U hQ}

theorem evL_congr (hU : ∀ α, Cosieve (U α)) {n p : ℕ} (f : ∀ i : Fin p → ι, (Tm F U hQ n).M (ent i))
    {i i' : Fin p → ι} (e : i = i') (s : ComposableArrows C n) (h : capU U (ent i) (s.obj 0))
    (h' : capU U (ent i') (s.obj 0)) : evL F U hQ hU _ s h (f i) = evL F U hQ hU _ s h' (f i') := by
  subst e; rfl

theorem evL_d (hU : ∀ α, Cosieve (U α)) {p n : ℕ} (y : (Tm F U hQ n).cech.X p)
    (i : Fin (p + 2) → ι) (s : ComposableArrows C n) (h : capU U (ent i) (s.obj 0)) :
    evL F U hQ hU _ s h ((Tm F U hQ n).cech.d p y i) =
      ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
        evL F U hQ hU _ s (capU_mono (ent_comp i k.succAbove) h) (y (i ∘ k.succAbove)) := by
  have e := congrArg ((evL F U hQ hU _ s h) ∘ₗ
    (LinearMap.proj (R := R) (φ := fun i : Fin (p + 2) → ι => (Tm F U hQ n).M (ent i)) i))
    (Cos.d_apply (Tm F U hQ n).cech p y)
  rw [map_sum] at e
  simp only [map_zsmul] at e
  exact e

theorem capU_const {b : ι} {T : C} (hb : U b T) : capU U (ent fun _ : Fin 1 => b) T := by
  refine ⟨⟨b, hb⟩, fun α hα => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hα
  exact hb

theorem cons_zero {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons (α := fun _ => ι) a i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by
  funext k
  simp [Function.comp]

theorem cons_succ {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    (Fin.cons (α := fun _ => ι) a i : Fin (n + 2) → ι) ∘ j.succ.succAbove =
      Fin.cons (α := fun _ => ι) a (i ∘ j.succAbove) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Function.comp]
  · simp [Function.comp]

theorem M_ext (hU : ∀ α, Cosieve (U α)) {n : ℕ} {S : Finset ι} {x y : (Tm F U hQ n).M S}
    (h : ∀ t : ComposableArrows (capU U S).FullSubcategory n,
      evL F U hQ hU S (t ⋙ (capU U S).ι) (t.obj 0).property x =
        evL F U hQ hU S (t ⋙ (capU U S).ι) (t.obj 0).property y) : x = y :=
  Subtype.ext (funext h)

def mkM {n : ℕ} (S : Finset ι) (f : CH.Cn ((capU U S).ι ⋙ F) n)
    (hf : ∀ t : ComposableArrows (capU U S).FullSubcategory n, Q (t.obj 0).obj → f t = 0) :
    (Tm F U hQ n).M S :=
  (⟨f, hf⟩ : relS ((capU U S).ι ⋙ F) (fun T => Q T.obj) n)

theorem evL_zero (hU : ∀ α, Cosieve (U α)) {n : ℕ} (S : Finset ι) (x : (Tm F U hQ n).M S)
    (s : ComposableArrows C n) (h : capU U S (s.obj 0)) (hs : Q (s.obj 0)) :
    evL F U hQ hU S s h x = 0 :=
  x.2 (liftC U hU S s h) hs

theorem cocycle_eq (hU : ∀ α, Cosieve (U α)) {p n : ℕ} (y : (Tm F U hQ n).cech.X (p + 1))
    (hy : (Tm F U hQ n).cech.d (p + 1) y = 0) (i : Fin (p + 2) → ι) (s : ComposableArrows C n)
    (h : capU U (ent i) (s.obj 0)) (b : ι) (hb : U b (s.obj 0)) :
    evL F U hQ hU _ s h (y i) = ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      evL F U hQ hU _ s (capU_cons hb (capU_mono (ent_comp i j.succAbove) h))
        (y (Fin.cons (α := fun _ => ι) b (i ∘ j.succAbove))) := by
  have h' := capU_cons hb h
  have e := evL_d hU y _ s h'
  have z : evL F U hQ hU _ s h' ((Tm F U hQ n).cech.d (p + 1) y (Fin.cons (α := fun _ => ι) b i)) = 0 := by
    rw [hy]; exact map_zero _
  rw [z, Fin.sum_univ_succ] at e
  have e0 := evL_congr hU y (cons_zero b i) s (capU_mono (ent_comp _ _) h') h
  have e1 : ∀ j : Fin (p + 2),
      evL F U hQ hU _ s (capU_mono (ent_comp _ j.succ.succAbove) h')
        (y ((Fin.cons (α := fun _ => ι) b i : Fin (p + 3) → ι) ∘ j.succ.succAbove)) =
      evL F U hQ hU _ s (capU_cons hb (capU_mono (ent_comp i j.succAbove) h))
        (y (Fin.cons (α := fun _ => ι) b (i ∘ j.succAbove))) :=
    fun j => evL_congr hU y (cons_succ _ i j) s _ _
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, e0, e1] at e
  exact add_neg_eq_zero.1 e.symm

theorem cocycle_zero (hU : ∀ α, Cosieve (U α)) {n : ℕ} (y : (Tm F U hQ n).cech.X 0)
    (hy : (Tm F U hQ n).cech.d 0 y = 0) (i : Fin 1 → ι) (s : ComposableArrows C n)
    (h : capU U (ent i) (s.obj 0)) (b : ι) (hb : U b (s.obj 0)) :
    evL F U hQ hU _ s h (y i) = evL F U hQ hU _ s (capU_const hb) (y fun _ => b) := by
  have h' := capU_cons hb h
  have e := evL_d hU y _ s h'
  have z : evL F U hQ hU _ s h' ((Tm F U hQ n).cech.d 0 y (Fin.cons (α := fun _ => ι) b i)) = 0 := by
    rw [hy]; exact map_zero _
  rw [z, Fin.sum_univ_two] at e
  have e0 := evL_congr hU y (cons_zero b i) s (capU_mono (ent_comp _ _) h') h
  have e1 := evL_congr hU y (i := (Fin.cons (α := fun _ => ι) b i : Fin 2 → ι) ∘ (1 : Fin 2).succAbove)
    (i' := fun _ => b) (funext fun k => by
      obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
      rfl) s (capU_mono (ent_comp _ _) h') (capU_const hb)
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, e0, e1] at e
  exact add_neg_eq_zero.1 e.symm

def hh (hU : ∀ α, Cosieve (U α)) (a : ∀ T, (∃ b, U b T) → ι) (ha : ∀ T h, U (a T h) T) {p n : ℕ}
    (y : (Tm F U hQ n).cech.X (p + 1)) : (Tm F U hQ n).cech.X p := fun i =>
  mkM (ent i) (fun t => evL F U hQ hU _ (t ⋙ (capU U (ent i)).ι)
      (capU_cons (ha _ (t.obj 0).property.1) (t.obj 0).property)
      (y (Fin.cons (α := fun _ => ι) (a _ (t.obj 0).property.1) i)))
    fun t ht => evL_zero hU _ _ _ _ ht

theorem desc (hU : ∀ α, Cosieve (U α)) (n : ℕ) : (Tm F U hQ n).Ex := by
  have hc : ∀ T : C, ∀ h : ∃ b, U b T, ∃ b, U b T := fun _ h => h
  choose a ha using hc
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun m y hy => ?_⟩
  · funext i
    refine M_ext hU fun t => ?_
    refine (evL_d hU _ i _ _).trans ?_
    refine Eq.trans ?_ (map_zero (evL F U hQ hU _ _ _)).symm
    rw [Fin.sum_univ_two]
    change (-1 : ℤ) ^ 0 • evL F U hQ hU ∅ _ (capU_mono (Finset.empty_subset _) (t.obj 0).property) x +
      (-1 : ℤ) ^ 1 • evL F U hQ hU ∅ _ (capU_mono (Finset.empty_subset _) (t.obj 0).property) x = 0
    simp
  · rw [one_smul]
    refine M_ext hU fun t => ?_
    have hb := ha _ (t.obj 0).property.1
    have h1 := congrArg (evL F U hQ hU _ (t ⋙ (capU U ∅).ι) (capU_const hb))
      (congrFun hx fun _ => a _ (t.obj 0).property.1)
    exact (h1.trans (map_zero _)).trans (map_zero _).symm
  · refine ⟨mkM ∅ (fun t => evL F U hQ hU _ (t ⋙ (capU U ∅).ι) (capU_const (ha _ (t.obj 0).property.1))
      (y fun _ => a _ (t.obj 0).property.1)) fun t ht => evL_zero hU _ _ _ _ ht, ?_⟩
    rw [one_smul]
    funext i
    refine M_ext hU fun t => ?_
    exact (cocycle_zero hU y hy i (t ⋙ (capU U (ent i)).ι) (t.obj 0).property _
      (ha _ (t.obj 0).property.1)).symm
  · refine ⟨hh hU a ha y, ?_⟩
    rw [one_smul]
    funext i
    refine M_ext hU fun t => ?_
    refine (evL_d hU (hh hU a ha y) i (t ⋙ (capU U (ent i)).ι) (t.obj 0).property).trans ?_
    refine Eq.trans ?_ (cocycle_eq hU y hy i (t ⋙ (capU U (ent i)).ι) (t.obj 0).property _
      (ha _ (t.obj 0).property.1)).symm
    rfl

theorem covDesc : CovDesc := fun _ _ _ _ _ _ _ _ _ _ hU n => desc hU n

end GlobalTheory.CompanionTheory.CovDescent
