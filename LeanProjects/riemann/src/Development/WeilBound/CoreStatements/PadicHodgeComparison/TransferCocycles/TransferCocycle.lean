import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace PositivityTheory.AutomorphicGaloisHodgeTate.Tr

section Transfer
variable (R : Type) [CommRing R]

def IsTransferC {Z X : Scheme.{0}} (f : Z ⟶ X) (t : (free R).obj (yoneda.obj X) ⟶ (free R).obj (yoneda.obj Z)) : Prop :=
  ∀ (S : Scheme.{0}) (x : S ⟶ X) (m : ℕ) (s : Fin m → (S ⟶ Z)) (hs : ∀ j, s j ≫ f = x),
    IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 S) (by rw [hs j, Category.id_comp])) :
      ∐ (fun _ : Fin m => S) ⟶ pullback f x) →
    (free R).map (yoneda.map x) ≫ t = ∑ j, (free R).map (yoneda.map (s j))

def transferSimp {Z X : Scheme.{0}} (t : (free R).obj (yoneda.obj X) ⟶ (free R).obj (yoneda.obj Z)) :
    ((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj X) ⟶
      ((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj Z) where
  app _ := t
  naturality _ _ _ := by
    simp [sch]
    exact (Category.id_comp t).trans (Category.comp_id t).symm

def transferHom {Z X : Scheme.{0}} (t : (free R).obj (yoneda.obj X) ⟶ (free R).obj (yoneda.obj Z)) :
    (chains R).obj (sch.obj X) ⟶ (chains R).obj (sch.obj Z) :=
  (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map
    ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (transferSimp R t))

def transferCocycle {Z X : Scheme.{0}} (t : (free R).obj (yoneda.obj X) ⟶ (free R).obj (yoneda.obj Z)) :
    Cocycle ((chains R).obj (sch.obj X)) ((chains R).obj (sch.obj Z)) 0 :=
  Cocycle.ofHom (transferHom R t)

def pushH {Z X : Scheme.{0}} (t : (free R).obj (yoneda.obj X) ⟶ (free R).obj (yoneda.obj Z)) (F : Shv R) (n : ℤ) :
    H R (sch.obj Z) F n →+ H R (sch.obj X) F n :=
  HK.pre R (transferCocycle R t) F n n (by simp)

def trC {Z X : Scheme.{0}} (f : Z ⟶ X) : (free R).obj (yoneda.obj X) ⟶ (free R).obj (yoneda.obj Z) :=
  pick (IsTransferC R f)

end Transfer

def pushHt (q : ℕ) {Z X : Scheme.{0}} (f : Z ⟶ X) (n i : ℤ) : Ht q (sch.obj Z) n i →+ Ht q (sch.obj X) n i :=
  pushH (ZMod q) (trC (ZMod q) f) (tw q i) n

section Adic
variable (l : ℕ) [Fact l.Prime]

def pushFam {Z X : Scheme.{0}} (f : Z ⟶ X) (n i : ℤ) (a : Hl l (sch.obj Z) n i) : ∀ k, HtL l k (sch.obj X) n i :=
  fun k => (pushHt (l ^ k) f n i (a.1 k) : HtL l k (sch.obj X) n i)

def pushHQ {Z X : Scheme.{0}} (f : Z ⟶ X) (n i : ℤ) : HQ l (sch.obj Z) n i →ₗ[ℚ_[l]] HQ l (sch.obj X) n i :=
  pick fun L => ∀ (a : Hl l (sch.obj Z) n i) (h : pushFam l f n i a ∈ HlSub l (sch.obj X) n i),
    L ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] a) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] (⟨pushFam l f n i a, h⟩ : Hl l (sch.obj X) n i)

section Geom
variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {Z X : Scheme.{0}}
  {p : X ⟶ Spec (CommRingCat.of k)} {p' : Z ⟶ Spec (CommRingCat.of k)}

def pushGeom (f : Z ⟶ X) (hf : f ≫ p = p') (n i : ℤ) :
    HQ l (sch.obj (GlobalTheory.Et.geom Ω p')) n i →ₗ[ℚ_[l]] HQ l (sch.obj (GlobalTheory.Et.geom Ω p)) n i :=
  pushHQ l (GlobalTheory.Et.geomMap Ω p' f hf) n i

def pullGeom (f : Z ⟶ X) (hf : f ≫ p = p') (n i : ℤ) :
    HQ l (sch.obj (GlobalTheory.Et.geom Ω p)) n i →ₗ[ℚ_[l]] HQ l (sch.obj (GlobalTheory.Et.geom Ω p')) n i :=
  pullHQ l (sch.map (GlobalTheory.Et.geomMap Ω p' f hf)) n i

end Geom

end Adic

end PositivityTheory.AutomorphicGaloisHodgeTate.Tr

end
