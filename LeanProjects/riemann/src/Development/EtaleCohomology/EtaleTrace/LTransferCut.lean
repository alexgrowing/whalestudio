import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleTrace.Tr

def Splits {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)) : Prop :=
  ∃ hs : ∀ j, s j ≫ a = x, IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 W) (by rw [hs j, Category.id_comp])) :
      ∐ (fun _ : Fin m => W) ⟶ pullback a x)

section
variable (R : Type) [CommRing R]

abbrev fr (X : Scheme.{0}) : Shv R := (free R).obj (yoneda.obj X)

abbrev frMap {Y X : Scheme.{0}} (f : Y ⟶ X) : fr R Y ⟶ fr R X := (free R).map (yoneda.map f)

abbrev gen {U X : Scheme.{0}} (x : U ⟶ X) : Sec (fr R X) U := freeGen R (yoneda.obj X) U x

def IsTr {Y X : Scheme.{0}} (a : Y ⟶ X) (τ : fr R X ⟶ fr R Y) : Prop :=
  ∀ (W : Scheme.{0}) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s →
    Sec.map τ (gen R x) = ∑ j, gen R (s j)

variable {R}

def simp0 {X Y : Scheme.{0}} (τ : fr R X ⟶ fr R Y) :
    ((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj X) ⟶
      ((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj Y) where
  app _ := τ
  naturality _ _ _ := by
    change (free R).map (𝟙 _) ≫ τ = τ ≫ (free R).map (𝟙 _)
    simp

def chMap {X Y : Scheme.{0}} (τ : fr R X ⟶ fr R Y) : (chains R).obj (sch.obj X) ⟶ (chains R).obj (sch.obj Y) :=
  (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map
    ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (simp0 τ))

def trH {X Y : Scheme.{0}} (τ : fr R X ⟶ fr R Y) (F : Shv R) (n : ℤ) : H R (sch.obj Y) F n →+ H R (sch.obj X) F n :=
  HK.pull R (chMap τ) F n

theorem trH_smul {X Y : Scheme.{0}} (τ : fr R X ⟶ fr R Y) (F : Shv R) (n : ℤ) (r : R) (z : H R (sch.obj Y) F n) :
    trH τ F n (r • z) = r • trH τ F n z := by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_smul _ _ _ (zero_add n)))

theorem trH_add {X Y : Scheme.{0}} (σ τ : fr R X ⟶ fr R Y) (F : Shv R) (n : ℤ)
    (z : H R (sch.obj Y) F n) : trH (σ + τ) F n z = trH σ F n z + trH τ F n z := by
  have h : chMap (σ + τ) = chMap σ + chMap τ := by
    have : (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (simp0 (σ + τ)) =
      (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (simp0 σ) +
      (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (simp0 τ) := by
      ext n : 1
      rfl
    exact (congrArg (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map this).trans (Functor.map_add _)
  obtain ⟨z, rfl⟩ := z.mk_surjective
  unfold trH
  rw [h]
  refine Eq.trans ?_ (CohomologyClass.mk_add _ _)
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_add]

def trA {X Y : Scheme.{0}} (F : Shv R) (n : ℤ) (z : H R (sch.obj Y) F n) : (fr R X ⟶ fr R Y) →+ H R (sch.obj X) F n :=
  AddMonoidHom.mk' (fun τ => trH τ F n z) (fun σ τ => trH_add σ τ F n z)

end

def LSpl : Prop := ∀ {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s →
  (∀ (U : Scheme.{0}) (w : U ⟶ W), Splits a (w ≫ x) m (fun j => w ≫ s j)) ∧
  (∀ y : W ⟶ Y, y ≫ a = x → ∀ t : W, ∃ (O : W.Opens) (j : Fin m), t ∈ O ∧ O.ι ≫ y = O.ι ≫ s j) ∧
  (Nonempty W → Function.Injective s)

def LRank : Prop := ∀ {Y X W : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a →
  ∀ (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s → ∀ w : W, a.finrank (x w) = m

def LPeel : Prop := ∀ {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a → ∀ σ : X ⟶ Y, σ ≫ a = 𝟙 X →
  ∃ (O : Scheme.{0}) (i : O ⟶ Y), IsFinite (i ≫ a) ∧ Etale (i ≫ a) ∧ (∀ t, a.finrank t = (i ≫ a).finrank t + 1) ∧
    ∀ (W : Scheme.{0}) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ O)), Splits (i ≫ a) x m s →
      Splits a x (m + 1) (Fin.cons (x ≫ σ) fun j => s j ≫ i)

def LMul : Prop := ∀ {Z Y X : Scheme.{0}} (g : Z ⟶ Y) (a : Y ⟶ X), IsFinite g → Etale g → IsFinite a → Etale a →
  ∀ N : ℕ, (∀ y, g.finrank y = N) → ∀ t, (g ≫ a).finrank t = N * a.finrank t

def LFrame : Prop := ∀ (m : ℕ) {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a → (∀ t, a.finrank t = m) →
  ∃ (W : Scheme.{0}) (f : W ⟶ X) (N : ℕ) (s : Fin m → (W ⟶ Y)), IsFinite f ∧ Etale f ∧ 0 < N ∧ (∀ t, f.finrank t = N) ∧
    Splits a f m s

def LPiece : Prop := ∀ (m : ℕ) {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a →
  ∃ (W : Scheme.{0}) (f : W ⟶ X) (N : ℕ) (s : Fin m → (W ⟶ Y)), IsFinite f ∧ Etale f ∧ 0 < N ∧
    (∀ t, f.finrank t = if a.finrank t = m then N else 0) ∧ Splits a f m s

def LLoc : Prop := ∀ {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a → ∀ (W : Scheme.{0}) (x : W ⟶ X) (t : W),
  ∃ (U : Scheme.{0}) (g : U ⟶ W) (m : ℕ) (s : Fin m → (U ⟶ Y)), Etale g ∧ t ∈ Set.range g ∧ Splits a (g ≫ x) m s

def LSum : Prop := ∀ (R : Type) [CommRing R] {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m m' : ℕ) (s : Fin m → (W ⟶ Y))
  (s' : Fin m' → (W ⟶ Y)), Splits a x m s → Splits a x m' s' → ∑ j, gen R (s j) = ∑ j, gen R (s' j)

def LTau : Prop := ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a →
  ∃ τ : fr R X ⟶ fr R Y, IsTr R a τ

def LSplit : Prop := ∀ (R : Type) [CommRing R] {Y X W : Scheme.{0}} (a : Y ⟶ X) (τ : fr R X ⟶ fr R Y), IsTr R a τ →
  ∀ (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s → frMap R x ≫ τ = ∑ j, frMap R (s j)

def LDeg : Prop := ∀ (R : Type) [CommRing R] {X : Scheme.{0}} {ι : Type} [Fintype ι] (W : ι → Scheme.{0}) (f : ∀ i, W i ⟶ X)
  (τ : ∀ i, fr R X ⟶ fr R (W i)) (c : ι → ℕ) (N : ℕ), (∀ i, IsFinite (f i) ∧ Etale (f i) ∧ IsTr R (f i) (τ i)) →
  (∀ t, ∑ i, c i * (f i).finrank t = N) → ∑ i, c i • (τ i ≫ frMap R (f i)) = N • 𝟙 (fr R X)

def LImg : Prop := ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (E : Spc) (n : ℤ)
  (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n,
    ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev β.1 p s h U x = ρ.app U s (ev α.1 p s h U x)

def LRed : Prop := ∀ (S R : Type) [CommRing S] [CommRing R] (F : Shv S) (G : Shv R) (ρ : SemiMap (res S F) (res R G))
  {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a → ∀ (σ : fr S X ⟶ fr S Y) (τ : fr R X ⟶ fr R Y),
  IsTr S a σ → IsTr R a τ → ∀ (n : ℤ) (z : H S (sch.obj Y) F n),
  ρ.op.app (sch.obj X) n (trH σ F n z) = trH τ G n (ρ.op.app (sch.obj Y) n z)

section Glue
variable (l : ℕ) [Fact l.Prime]

def trL (hR : LRed) {Y X : Scheme.{0}} (a : Y ⟶ X) (h1 : IsFinite a) (h2 : Etale a)
    (τ : ∀ j, fr (ZMod (l ^ j)) X ⟶ fr (ZMod (l ^ j)) Y) (hτ : ∀ j, IsTr _ a (τ j)) (n : ℤ) :
    Hl l (sch.obj Y) n 0 →ₗ[ℤ_[l]] Hl l (sch.obj X) n 0 where
  toFun z := ⟨fun j => trH (τ j) _ n (z.1 j), fun j =>
    (hR _ _ _ _ (redMap (l ^ (j + 1)) (l ^ j) 0) a h1 h2 _ _ (hτ (j + 1)) (hτ j) n _).trans (congrArg _ (z.2 j))⟩
  map_add' x y := Subtype.ext (funext fun j => map_add (trH (τ j) _ n) (x.1 j) (y.1 j))
  map_smul' r x := Subtype.ext (funext fun j => trH_smul (τ j) _ n (PadicInt.toZModPow j r) (x.1 j))

def lev (E : Spc) (n : ℤ) (j : ℕ) : Hl l E n 0 →+ Ht (l ^ j) E n 0 where
  toFun z := z.1 j
  map_zero' := rfl
  map_add' _ _ := rfl

end Glue

end LateralTheory.EtaleTrace.Tr

end
