import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite
open GlobalTheory.LB (resG_resG resG_self fun_ext_of_cover exists_fun_of_cover)

namespace GlobalTheory.MatrixCocycle

variable {X : Scheme.{0}} {r : ℕ} {ι : Type} {U : ι → X.Opens}
  (A : ∀ i j, Matrix (Fin r) (Fin r) Γ(X, U i ⊓ U j)) {V W : X.Opens}

variable (V) in

def secGroup : AddSubgroup (∀ p : {p : ι × X.Opens // p.2 ≤ V ∧ p.2 ≤ U p.1}, Fin r → Γ(X, p.1.2)) where
  carrier := {s | (∀ (i : ι) (T T' : X.Opens) (h : T ≤ V) (hi : T ≤ U i) (h' : T' ≤ T) (b : Fin r),
      s ⟨(i, T'), h'.trans h, h'.trans hi⟩ b = resG X h' (s ⟨(i, T), h, hi⟩ b)) ∧
    ∀ (i j : ι) (T : X.Opens) (h : T ≤ V) (hi : T ≤ U i) (hj : T ≤ U j) (b : Fin r),
      s ⟨(i, T), h, hi⟩ b = ∑ c, resG X (le_inf hi hj) (A i j b c) * s ⟨(j, T), h, hj⟩ c}
  add_mem' := fun {s t} hs ht => ⟨fun i T T' h hi h' b => by
      simp only [Pi.add_apply, map_add, hs.1 i T T' h hi h', ht.1 i T T' h hi h'],
    fun i j T h hi hj b => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ← hs.2 i j T h hi hj, ← ht.2 i j T h hi hj]⟩
  zero_mem' := ⟨fun i T T' h hi h' b => by simp only [Pi.zero_apply, map_zero],
    fun i j T h hi hj b => by simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]⟩
  neg_mem' := fun {s} hs => ⟨fun i T T' h hi h' b => by
      simp only [Pi.neg_apply, map_neg, hs.1 i T T' h hi h'],
    fun i j T h hi hj b => by
      simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, ← hs.2 i j T h hi hj]⟩

theorem sec_ext {s t : secGroup A V}
    (e : ∀ i T h hi b, s.1 ⟨(i, T), h, hi⟩ b = t.1 ⟨(i, T), h, hi⟩ b) : s = t :=
  Subtype.ext (funext fun p => funext fun b => e p.1.1 p.1.2 p.2.1 p.2.2 b)

instance secModule : Module Γ(X, V) (secGroup A V) where
  smul a s := ⟨fun p b => resG X p.2.1 a * s.1 p b, fun i T T' h hi h' b => by
      dsimp only
      rw [s.2.1 i T T' h hi h', map_mul, resG_resG],
    fun i j T h hi hj b => by
      dsimp only
      rw [s.2.2 i j T h hi hj, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => mul_left_comm _ _ _⟩
  one_smul s := sec_ext A fun i T h hi b => by
    change resG X h 1 * _ = _
    rw [map_one, one_mul]
  mul_smul a a' s := sec_ext A fun i T h hi b => by
    change resG X h (a * a') * _ = resG X h a * (resG X h a' * _)
    rw [map_mul, mul_assoc]
  smul_zero a := sec_ext A fun i T h hi b => mul_zero (resG X h a)
  smul_add a s t := sec_ext A fun i T h hi b => mul_add (resG X h a) _ _
  add_smul a a' s := sec_ext A fun i T h hi b => by
    change resG X h (a + a') * _ = resG X h a * _ + resG X h a' * _
    rw [map_add, add_mul]
  zero_smul s := sec_ext A fun i T h hi b => by
    change resG X h 0 * _ = 0
    rw [map_zero, zero_mul]

def secRes (h : W ≤ V) : secGroup A V →+ secGroup A W where
  toFun s := ⟨fun p => s.1 ⟨p.1, p.2.1.trans h, p.2.2⟩,
    fun i T T' hT hi h' b => s.2.1 i T T' (hT.trans h) hi h' b,
    fun i j T hT hi hj b => s.2.2 i j T (hT.trans h) hi hj b⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def presheaf : TopCat.Presheaf Ab.{0} X where
  obj V := AddCommGrpCat.of (secGroup A V.unop)
  map f := AddCommGrpCat.ofHom (secRes A (leOfHom f.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

theorem isSheaf_presheaf : (presheaf A).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  have hc {T : X.Opens} (h : T ≤ iSup W) : T ≤ ⨆ k, T ⊓ W k := by
    rw [← inf_iSup_eq]; exact le_inf le_rfl h
  have hsf' (k l : κ) (i : ι) (T : X.Opens) (hk : T ≤ W k) (hl : T ≤ W l) (hi : T ≤ U i) :
      (sf k).1 ⟨(i, T), hk, hi⟩ = (sf l).1 ⟨(i, T), hl, hi⟩ :=
    congrFun (congrArg Subtype.val (hsf k l)) ⟨(i, T), le_inf hk hl, hi⟩
  have H (i : ι) (T : X.Opens) (h : T ≤ iSup W) (hi : T ≤ U i) (b : Fin r) : ∃ t : Γ(X, T), ∀ k,
      resG X inf_le_left t = (sf k).1 ⟨(i, T ⊓ W k), inf_le_right, inf_le_left.trans hi⟩ b := by
    refine exists_fun_of_cover (fun k => T ⊓ W k) (fun _ => inf_le_left) (hc h) _ fun k l => ?_
    exact ((sf k).2.1 i _ _ inf_le_right (inf_le_left.trans hi) inf_le_left b).symm.trans
      ((congrFun (hsf' k l i _ (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
        (inf_le_left.trans (inf_le_left.trans hi))) b).trans
        ((sf l).2.1 i _ _ inf_le_right (inf_le_left.trans hi) inf_le_right b))
  choose t ht using H
  have ht' (i : ι) (T : X.Opens) (h : T ≤ iSup W) (hi : T ≤ U i) (b : Fin r) (k : κ) (T' : X.Opens)
      (h₁ : T' ≤ T) (h₂ : T' ≤ W k) : resG X h₁ (t i T h hi b) = (sf k).1 ⟨(i, T'), h₂, h₁.trans hi⟩ b := by
    have := congrArg (resG X (le_inf h₁ h₂)) (ht i T h hi b k)
    rwa [← (sf k).2.1 i _ _ inf_le_right (inf_le_left.trans hi), resG_resG] at this
  have ext {T : X.Opens} (h : T ≤ iSup W) {a b : Γ(X, T)}
      (e : ∀ k, resG X (inf_le_left : T ⊓ W k ≤ T) a = resG X inf_le_left b) : a = b :=
    fun_ext_of_cover (fun k => T ⊓ W k) (fun _ => inf_le_left) (hc h) e
  refine ⟨⟨fun p => t p.1.1 p.1.2 p.2.1 p.2.2, fun i T T' h hi h' b => ?_, fun i j T h hi hj b => ?_⟩,
    fun k => sec_ext A fun i T h hi b => ?_,
    fun u hu => sec_ext A fun i T h hi b => ext h fun k => ?_⟩
  · refine ext (h'.trans h) fun k => ?_
    dsimp only
    rw [ht, resG_resG, ht' i T h hi b k _ _ inf_le_right]
  · refine ext h fun k => ?_
    dsimp only
    rw [ht, (sf k).2.2 i j _ inf_le_right (inf_le_left.trans hi) (inf_le_left.trans hj), map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, resG_resG, ht]
  · have := ht' i T (h.trans (le_iSup W k)) hi b k T le_rfl h
    rwa [resG_self] at this
  · change _ = resG X _ (t i T h hi b)
    rw [ht, ← u.2.1 i T _ h hi, ← hu k]
    rfl

def mod : X.Modules :=
  letI : ∀ V, Module (X.ringCatSheaf.obj.obj V) ((presheaf A).obj V) :=
    fun V => secModule A (V := V.unop)
  { val := PresheafOfModules.ofPresheaf (presheaf A) fun _ _ f a s =>
      sec_ext A fun i T h hi b =>
        congrArg (· * s.1 ⟨(i, T), h.trans (leOfHom f.unop), hi⟩ b) (resG_resG (leOfHom f.unop) h a).symm
    isSheaf := isSheaf_presheaf A }

def comp (s : Γ(mod A, V)) (i : ι) {T : X.Opens} (h : T ≤ V) (hi : T ≤ U i) (b : Fin r) : Γ(X, T) :=
  (show secGroup A V from s).1 ⟨(i, T), h, hi⟩ b

variable (hA : ∀ (i j k : ι) (V : X.Opens) (hij : V ≤ U i ⊓ U j) (hjk : V ≤ U j ⊓ U k) (hik : V ≤ U i ⊓ U k),
    (A i j).map (resG X hij) * (A j k).map (resG X hjk) = (A i k).map (resG X hik))

def frame (j : ι) (a : Fin r) : Γ(mod A, U j) :=
  (⟨fun p b => resG X (le_inf p.2.2 p.2.1) (A p.1.1 j b a), fun i T T' h hi h' b => (resG_resG _ _ _).symm,
    fun i k T h hi hk b => (congrFun (congrFun (hA i k j T (le_inf hi hk) (le_inf hk h) (le_inf hi h)) b) a).symm⟩ :
    secGroup A (U j))

theorem comp_linearCombination (j : ι) (hV : V ≤ U j) (x : Fin r → Γ(X, V)) (i : ι) {T : X.Opens} (h : T ≤ V)
    (hi : T ≤ U i) (b : Fin r) :
    comp A (Fintype.linearCombination Γ(X, V) (fun a => Twist.resM (mod A) hV (frame A hA j a)) x) i h hi b =
      ∑ a, resG X (le_inf hi (h.trans hV)) (A i j b a) * resG X h (x a) := by
  rw [Fintype.linearCombination_apply]
  refine (map_sum (AddMonoidHom.mk' (fun s : Γ(mod A, V) => comp A s i h hi b) fun _ _ => rfl) _ _).trans ?_
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem comp_linearCombination_self (h1 : ∀ i, A i i = 1) (j : ι) (hV : V ≤ U j) (x : Fin r → Γ(X, V)) (b : Fin r) :
    comp A (Fintype.linearCombination Γ(X, V) (fun a => Twist.resM (mod A) hV (frame A hA j a)) x) j le_rfl hV b =
      x b := by
  rw [comp_linearCombination, h1]
  simp [Matrix.one_apply, resG_self, apply_ite (resG X _)]

theorem isFrame_frame (h1 : ∀ i, A i i = 1) (j : ι) : VB.IsFrame (frame A hA j) := fun V hV => by
  refine ⟨fun x y hxy => funext fun b => ?_, fun s => ⟨fun b => comp A s j le_rfl hV b, ?_⟩⟩
  · rw [← comp_linearCombination_self A hA h1 j hV x, hxy, comp_linearCombination_self A hA h1]
  · refine sec_ext A fun i T h hi b => (comp_linearCombination A hA j hV _ i h hi b).trans ?_
    refine Eq.trans ?_ ((show secGroup A V from s).2.2 i j T h hi (h.trans hV) b).symm
    exact Finset.sum_congr rfl fun c _ =>
      congrArg _ ((show secGroup A V from s).2.1 j V T le_rfl hV h c).symm

theorem repr_frame (h1 : ∀ i, A i i = 1) (j : ι) (hV : V ≤ U j) (s : Γ(mod A, V)) (b : Fin r) :
    ((isFrame_frame A hA h1 j).basis hV).repr s b = comp A s j le_rfl hV b := by
  conv_rhs => rw [← ((isFrame_frame A hA h1 j).basis hV).sum_repr s, VB.IsFrame.coe_basis]
  exact (comp_linearCombination_self A hA h1 j hV _ b).symm

theorem exists_frames : ∀ (X : Scheme.{0}) (r : ℕ) (ι : Type) (U : ι → X.Opens) (A : ∀ i j, Matrix (Fin r) (Fin r) Γ(X, U i ⊓ U j)), (∀ x : X, ∃ i, x ∈ U i) → (∀ i, A i i = 1) → (∀ (i j k : ι) (V : X.Opens) (hij : V ≤ U i ⊓ U j) (hjk : V ≤ U j ⊓ U k) (hik : V ≤ U i ⊓ U k), (A i j).map (resG X hij) * (A j k).map (resG X hjk) = (A i k).map (resG X hik)) → ∃ (M : X.Modules) (f : ∀ i, Fin r → Γ(M, U i)) (hf : ∀ i, VB.IsFrame (f i)), ∀ i j b a, trCo (hf i) (f j) b a = A i j b a := by
  intro X r ι U A _ h1 hA
  refine ⟨mod A, frame A hA, isFrame_frame A hA h1, fun i j b a => ?_⟩
  rw [trCo, repr_frame A hA h1]
  exact resG_self _ _

end GlobalTheory.MatrixCocycle

end
