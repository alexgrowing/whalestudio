import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.DcColSurj
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace CrystallineSemistableComparison.ExtensionDiagram
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

def mk {Y : C ⥤ Type t} {q : ℕ} (c : ComposableArrows C q) (y : ∀ k, Y.obj (c.obj k))
    (h : ∀ {a b : Fin (q + 1)} (φ : a ⟶ b), Y.map (c.map φ) (y a) = y b) : ComposableArrows Y.Elements q where
  obj k := ⟨c.obj k, y k⟩
  map φ := ⟨c.map φ, h φ⟩
  map_id k := Subtype.ext (c.map_id k)
  map_comp φ ψ := Subtype.ext (c.map_comp φ ψ)

theorem mk_congr {Y : C ⥤ Type t} (F : C ⥤ ModuleCat.{w} R) {q : ℕ} (f : Cn (elF Y F) q) (c : ComposableArrows C q)
    {y y' : ∀ k, Y.obj (c.obj k)} h h' (e : y = y') :
    @Eq (F.obj (c.obj (Fin.last q))) (f (mk c y h)) (f (mk c y' h')) := by
  subst e; rfl

variable {E' E : C ⥤ Type t} (p : E' ⟶ E) (hp : ∀ T, Function.Surjective (p.app T))

noncomputable def lft {q : ℕ} (c : ComposableArrows C q) (e : E.obj (c.obj 0)) (k : Fin (q + 1)) : E'.obj (c.obj k) :=
  E'.map (c.map (homOfLE (Fin.zero_le k))) (hp _ e).choose

theorem lft_map {q : ℕ} (c : ComposableArrows C q) (e : E.obj (c.obj 0)) {a b : Fin (q + 1)} (φ : a ⟶ b) :
    E'.map (c.map φ) (lft p hp c e a) = lft p hp c e b := by
  unfold lft
  rw [← Functor.map_comp_apply, ← c.map_comp]; rfl

theorem p_lft {q : ℕ} (c : ComposableArrows C q) (e : E.obj (c.obj 0)) (k : Fin (q + 1)) :
    p.app _ (lft p hp c e k) = E.map (c.map (homOfLE (Fin.zero_le k))) e := by
  unfold lft
  rw [NatTrans.naturality_apply, (hp _ e).choose_spec]

theorem p_el {q n : ℕ} (s : ComposableArrows (cech p n).Elements q) (k : Fin (q + 1)) (i : Fin (n + 1)) :
    E.map (s.map (homOfLE (Fin.zero_le k))).1 (p.app _ ((s.obj 0).2.1 0)) = p.app _ ((s.obj k).2.1 i) := by
  rw [← NatTrans.naturality_apply, ← (s.obj k).2.2 0 i]
  exact congrArg (fun z => p.app _ (z.1 0)) (s.map (homOfLE (Fin.zero_le k))).2

noncomputable def extY {q n : ℕ} (s : ComposableArrows (cech p n).Elements q) (k : Fin (q + 1)) :
    (cech p (n + 1)).obj (s.obj k).1 :=
  ⟨Fin.cons (lft p hp (s ⋙ CategoryOfElements.π _) (p.app _ ((s.obj 0).2.1 0)) k) (s.obj k).2.1, by
    have h : ∀ i : Fin (n + 2), p.app _ ((Fin.cons (lft p hp (s ⋙ CategoryOfElements.π _) (p.app _ ((s.obj 0).2.1 0)) k)
        (s.obj k).2.1 : Fin (n + 2) → E'.obj (s.obj k).1) i) = p.app _ ((s.obj k).2.1 0) := by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact (p_lft p hp (s ⋙ CategoryOfElements.π _) _ k).trans (p_el p s k 0)
      · exact (s.obj k).2.2 i 0
    intro i j
    rw [h i, h j]⟩

theorem extY_map {q n : ℕ} (s : ComposableArrows (cech p n).Elements q) {a b : Fin (q + 1)} (φ : a ⟶ b) :
    (cech p (n + 1)).map (s.map φ).1 (extY p hp s a) = extY p hp s b := by
  refine Subtype.ext (funext fun i => ?_)
  refine Fin.cases ?_ (fun i => ?_) i
  · exact lft_map p hp (s ⋙ CategoryOfElements.π _) _ φ
  · exact congrArg (fun z => z.1 i) (s.map φ).2

noncomputable def ext {q n : ℕ} (s : ComposableArrows (cech p n).Elements q) : ComposableArrows (cech p (n + 1)).Elements q :=
  mk (s ⋙ CategoryOfElements.π _) (extY p hp s) (extY_map p hp s)

variable (F : C ⥤ ModuleCat.{w} R)

theorem dh_apply {q n : ℕ} (f : Cn (elF (cech p n) F) q) (s : ComposableArrows (cech p (n + 1)).Elements q) :
    @Eq (F.obj (s.obj (Fin.last q)).1) ((cechCos p F).dcx.dh n q f s)
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • f (s ⋙ CategoryOfElements.map (cechMap p i.succAbove))) := by
  have := congrFun (Cos.d_apply ((cechCos p F).cos q) n f) s
  rw [Finset.sum_apply] at this
  exact this

theorem ext_zero {q n : ℕ} (f : Cn (elF (cech p n) F) q) (s : ComposableArrows (cech p n).Elements q) :
    @Eq (F.obj (s.obj (Fin.last q)).1) (f (ext p hp s ⋙ CategoryOfElements.map (cechMap p (0 : Fin (n + 2)).succAbove))) (f s) :=
  rfl

theorem ext_succ {q n : ℕ} (f : Cn (elF (cech p (n + 1)) F) q) (s : ComposableArrows (cech p (n + 1)).Elements q) (i : Fin (n + 2)) :
    @Eq (F.obj (s.obj (Fin.last q)).1) (f (ext p hp s ⋙ CategoryOfElements.map (cechMap p i.succ.succAbove)))
      (f (ext p hp (s ⋙ CategoryOfElements.map (cechMap p i.succAbove)))) := by
  refine mk_congr F f (s ⋙ CategoryOfElements.π _)
    (y := fun k => (cechMap p i.succ.succAbove).app _ (extY p hp s k))
    (y' := fun k => extY p hp (s ⋙ CategoryOfElements.map (cechMap p i.succAbove)) k) _ _ (funext fun k => Subtype.ext (funext fun j => ?_))
  refine Fin.cases ?_ (fun j => ?_) j
  · change (extY p hp s k).1 (i.succ.succAbove 0) = _
    rw [Fin.succ_succAbove_zero]
    exact congrArg (fun e => lft p hp (s ⋙ CategoryOfElements.π _) e k) ((s.obj 0).2.2 _ _)
  · change (extY p hp s k).1 (i.succ.succAbove j.succ) = _
    rw [Fin.succ_succAbove_succ]
    rfl

noncomputable def ext0 {q : ℕ} (s : ComposableArrows E.Elements q) : ComposableArrows (cech p 0).Elements q :=
  mk (s ⋙ CategoryOfElements.π _) (fun k => ⟨fun _ => lft p hp (s ⋙ CategoryOfElements.π _) (s.obj 0).2 k, fun _ _ => rfl⟩)
    fun φ => Subtype.ext (funext fun _ => lft_map p hp (s ⋙ CategoryOfElements.π _) _ φ)

end CrystallineSemistableComparison.ExtensionDiagram

open CrystallineSemistableComparison.ExtensionDiagram in
theorem CrystallineSemistableComparison.P.cech_row : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R), (∀ T, Function.Surjective (p.app T)) → ∀ q, ((cechCos p F).dcx.row q).ResUpTo 1 ((cechAugRow p F).ε q) := by
  intro R _ C _ E' E p F hp q
  refine ⟨(cechAugRow p F).hε q, fun g hg => ?_, fun f hf => ?_, fun n f hf => ?_⟩
  · rw [one_smul]
    funext s
    have h1 := congrFun hg (ext0 p hp s)
    refine Eq.trans ?_ h1
    refine mk_congr F g (s ⋙ CategoryOfElements.π _) (y := fun k => (s.obj k).2)
      (y' := fun k => p.app _ (lft p hp (s ⋙ CategoryOfElements.π _) (s.obj 0).2 k)) (fun φ => (s.map φ).2) _ (funext fun k => ?_)
    rw [p_lft]
    exact (s.map (homOfLE (Fin.zero_le k))).2.symm
  · refine ⟨fun s => f (ext0 p hp s), ?_⟩
    rw [one_smul]
    funext s
    have h1 := (dh_apply p F f (ext p hp s)).symm.trans (congrFun hf (ext p hp s))
    rw [Fin.sum_univ_two] at h1
    have h2 : @Eq (F.obj (s.obj (Fin.last q)).1) (f (ext p hp s ⋙ CategoryOfElements.map (cechMap p (1 : Fin 2).succAbove)))
        (f (ext0 p hp (s ⋙ CategoryOfElements.map (cechAug p 0)))) := by
      refine mk_congr F f (s ⋙ CategoryOfElements.π _)
        (y := fun k => (cechMap p (1 : Fin 2).succAbove).app _ (extY p hp s k)) _ _ (funext fun k => Subtype.ext (funext fun j => ?_))
      obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) _ _
      rfl
    erw [ext_zero p hp F f s, h2] at h1
    change f (ext0 p hp (s ⋙ CategoryOfElements.map (cechAug p 0))) = f s
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul] at h1
    exact (add_neg_eq_zero.1 h1).symm
  · refine ⟨fun s => f (ext p hp s), ?_⟩
    rw [one_smul]
    funext s
    have h1 := (dh_apply p F f (ext p hp s)).symm.trans (congrFun hf (ext p hp s))
    rw [Fin.sum_univ_succ] at h1
    erw [ext_zero p hp F f s] at h1
    refine (dh_apply p F _ s).trans ?_
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib] at h1
    refine Eq.trans ?_ (add_neg_eq_zero.1 h1).symm
    exact Finset.sum_congr rfl fun i _ => congrArg _ (ext_succ p hp F f s i).symm

theorem CrystallineSemistableComparison.P.cech_desc : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R), (∀ T, Function.Surjective (p.app T)) → ∀ n, Function.Bijective ((cechAugRow p F).edge.mapH n) := by
  intro R _ C _ E' E p F hp n
  have := CrystallineSemistableComparison.P.dc_row (cechAugRow p F) 1 (CrystallineSemistableComparison.P.cech_row p F hp) n
  rw [one_pow] at this
  exact (CrystallineSemistableComparison.P.upTo_alg _ (LinearMap.id (R := R)) 1 1).2.2.2.2.1 this
