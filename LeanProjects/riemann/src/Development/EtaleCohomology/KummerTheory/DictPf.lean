import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def EvLin : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
  (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x,
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (-α) p s h U x = -ev α p s h U x) ∧
  (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
    Sec.res g (ev α p s h U x) = ev α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x)) ∧
  ∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U),
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x =
      ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x)

def DictExist : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) (X : Scheme.{0}) (n : ℤ) (a : Sec (I.X n) X),
  Sec.map (I.d n (n + 1)) a = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n,
    ev α.1 0 n (by simp) X (𝟙 X) = a ∧
    ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U), ev α.1 (p + 1) s h U y = 0

def DictNormal : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) (X : Scheme.{0}) (n : ℤ)
  (α : Cocycle ((chains R).obj (sch.obj X)) I n), ∃ α' : Cocycle ((chains R).obj (sch.obj X)) I n,
    CohomologyClass.mk α' = CohomologyClass.mk α ∧
    ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U), ev α'.1 (p + 1) s h U y = 0

def DictZero : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) (X : Scheme.{0}) (n : ℤ)
  (α : Cocycle ((chains R).obj (sch.obj X)) I n),
  (∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U), ev α.1 (p + 1) s h U y = 0) →
  Sec.map (I.d n (n + 1)) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 ∧
    (CohomologyClass.mk α = 0 ↔ ∃ b : Sec (I.X (n - 1)) X, Sec.map (I.d (n - 1) n) b = ev α.1 0 n (by simp) X (𝟙 X))

theorem Dict_of (hL : EvLin) (hE : DictExist) (hN : DictNormal) (hZ : DictZero) : Dict := by
  intro R _ I X n
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨α, h0, h1⟩ := hE R I X n a ha
    exact ⟨_, α, rfl, h0, h1⟩
  · intro x
    obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨α', e, h1⟩ := hN R I X n α
    exact ⟨_, α', e, rfl, h1⟩
  · rintro x a ⟨α, rfl, h0, h1⟩
    subst h0
    exact hZ R I X n α h1
  · rintro x x' a a' ⟨α, rfl, h0, h1⟩ ⟨α', rfl, h0', h1'⟩
    refine ⟨⟨α + α', CohomologyClass.mk_add _ _ |>.symm, ?_, ?_⟩, ⟨-α, ?_, ?_, ?_⟩⟩
    · rw [← h0, ← h0']; exact ((hL R).1 α.1 α'.1 0 n _ X (𝟙 X)).1
    · intro p s h U y
      rw [show ((α + α' : Cocycle _ _ n) : Cochain _ _ n) = α.1 + α'.1 from rfl, ((hL R).1 _ _ _ _ _ _ _).1, h1, h1', add_zero]
    · rw [← CohomologyClass.mk_neg]
    · rw [← h0]; exact ((hL R).1 α.1 α.1 0 n _ X (𝟙 X)).2
    · intro p s h U y
      rw [show ((-α : Cocycle _ _ n) : Cochain _ _ n) = -α.1 from rfl, ((hL R).1 α.1 α.1 _ _ _ _ _).2, h1, neg_zero]
  · rintro Y f x a ⟨α, rfl, h0, h1⟩
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n), rfl, ?_, ?_⟩
    · change ev ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add n)) 0 n _ Y (𝟙 Y) = _
      refine ((hL R).2.2 (sch.map f) α.1 0 n _ Y (𝟙 Y)).trans ?_
      rw [← h0]
      exact (((hL R).2.1 α.1 0 n _ Y X f (𝟙 X)).trans rfl).symm
    · intro p s h U y
      change ev ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add n)) (p + 1) s h U y = 0
      exact ((hL R).2.2 (sch.map f) α.1 _ _ _ _ _).trans (h1 _ _ _ _ _)

end LateralTheory.KummerTheory
