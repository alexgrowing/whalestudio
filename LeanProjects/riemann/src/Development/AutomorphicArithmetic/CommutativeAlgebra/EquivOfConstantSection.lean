import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

namespace UpperTheory.SimplicialRelations
open SimplicialObject Simplicial

private theorem qi_of_ed (R : Type) [CommRing R] (A : SimplicialObject.Augmented PSh)
    (ed : Augmented.ExtraDegeneracy A) :
    QuasiIso ((chainsN R).map (X := A.left) (Y := disc.obj A.right) A.hom) := by
  let W := (Augmented.whiskering PSh (Shv R)).obj (free R)
  let φ : A ⟶ Augmented.const.obj A.right :=
    { left := A.hom, right := 𝟙 _, w := by
        change A.hom ≫ 𝟙 _ = A.hom ≫ (SimplicialObject.const PSh).map (𝟙 _)
        rw [CategoryTheory.Functor.map_id] }
  have h1 := (ed.map (free R)).homotopyEquiv.quasiIso_hom
  have h2 := ((Augmented.ExtraDegeneracy.const A.right).map (free R)).homotopyEquiv.quasiIso_hom
  have nat := (AlgebraicTopology.AlternatingFaceMapComplex.ε (C := Shv R)).naturality (W.map φ)
  have hp : (Augmented.point ⋙ ChainComplex.single₀ _).map (W.map φ) = 𝟙 _ := by
    change (ChainComplex.single₀ _).map ((free R).map (𝟙 A.right)) = 𝟙 _
    rw [(free R).map_id, CategoryTheory.Functor.map_id]
  rw [hp] at nat
  have nat' := nat.trans (Category.comp_id (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (W.obj A)))
  haveI : QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (W.obj (Augmented.const.obj A.right))) := h2
  have key : QuasiIso ((Augmented.drop ⋙ AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (W.map φ) ≫
      AlgebraicTopology.AlternatingFaceMapComplex.ε.app (W.obj (Augmented.const.obj A.right))) := by
    rw [nat']; exact h1
  exact (quasiIso_iff_comp_right _ (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (W.obj (Augmented.const.obj A.right)))).1 key

variable {X M : RF} (ρ : X.Hom M) (hc : ρ.Const)
  (hr : ∀ {A : Type} [CommRing A] {x y : X.obj A}, ρ.app A x = ρ.app A y → X.rel x y)
  (γ : M.Hom X) (hγ : ∀ {A : Type} [CommRing A] (m : M.obj A), ρ.app A (γ.app A m) = m)

include hc in
private theorem ρ_eq {A : Type} [CommRing A] {n : ℕ} {x : Fin n → X.obj A} (hx : ∀ i j, X.rel (x i) (x j)) (i j : Fin n) :
    ρ.app A (x i) = ρ.app A (x j) := hc (hx i j)

private def sv {A : Type} [CommRing A] {n : ℕ} (x : Fin (n + 1) → X.obj A) : Fin (n + 2) → X.obj A :=
  Fin.cons (γ.app A (ρ.app A (x 0))) x

include hc hr hγ in
private theorem sv_rel {A : Type} [CommRing A] {n : ℕ} {x : Fin (n + 1) → X.obj A} (hx : ∀ i j, X.rel (x i) (x j))
    (i j : Fin (n + 2)) : X.rel (sv ρ γ x i) (sv ρ γ x j) := by
  have key : ∀ k, ρ.app A (sv ρ γ x k) = ρ.app A (x 0) := by
    intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [sv, hγ]
    · simpa [sv] using ρ_eq ρ hc hx k 0
  exact hr ((key i).trans (key j).symm)

private theorem sv_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ} (x : Fin (n + 1) → X.obj A) :
    sv ρ γ (fun i => X.map f (x i)) = fun i => X.map f (sv ρ γ x i) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [sv, ρ.nat, γ.nat]
  · simp [sv]

include hc in
private theorem sv_δ {A : Type} [CommRing A] {n : ℕ} {x : Fin (n + 2) → X.obj A} (hx : ∀ i j, X.rel (x i) (x j))
    (i j : Fin (n + 2)) : sv ρ γ x (i.succ.succAbove j) = sv ρ γ (fun k => x (i.succAbove k)) j := by
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [Fin.succ_succAbove_zero]
    simp only [sv, Fin.cons_zero]
    rw [ρ_eq ρ hc hx 0 (i.succAbove 0)]
  · rw [Fin.succ_succAbove_succ]
    simp [sv]

include hc in
private theorem sv_σ {A : Type} [CommRing A] {n : ℕ} (x : Fin (n + 1) → X.obj A) (i : Fin (n + 1)) (j : Fin (n + 3)) :
    sv ρ γ x (Fin.predAbove i.succ j) = sv ρ γ (fun k => x (Fin.predAbove i k)) j := by
  refine Fin.cases ?_ (fun k => ?_) j
  · have h0 : Fin.predAbove i.succ (0 : Fin (n + 3)) = 0 := by
      simp [Fin.predAbove]
    have h1 : Fin.predAbove i (0 : Fin (n + 2)) = 0 := by
      simp [Fin.predAbove]
    rw [h0]
    simp [sv, h1]
  · rw [Fin.succ_predAbove_succ]
    simp [sv]

private def augOf : SimplicialObject.Augmented PSh :=
  { left := CN X, right := M.psh, hom := CN.proj ρ hc }

private def sZ (hr' : ∀ {A : Type} [CommRing A] (x : X.obj A), X.rel x x) : M.psh ⟶ (CN X).obj (op (SimplexCategory.mk 0)) where
  app U := TypeCat.ofHom fun (m : M.obj Γ(U.unop, ⊤)) => ⟨fun _ => γ.app _ m, fun _ _ => hr' _⟩
  naturality U V f := by
    refine ConcreteCategory.hom_ext _ _ fun m => Subtype.ext (funext fun _ => ?_)
    exact γ.nat f.unop.appTop.hom m

include hc hr hγ in
private def sN (n : ℕ) : (CN X).obj (op (SimplexCategory.mk n)) ⟶ (CN X).obj (op (SimplexCategory.mk (n + 1))) where
  app U := TypeCat.ofHom fun (x : {x : Fin (n + 1) → X.obj Γ(U.unop, ⊤) // ∀ i j, X.rel (x i) (x j)}) =>
    ⟨sv ρ γ x.1, sv_rel ρ hc hr γ hγ x.2⟩
  naturality U V f := by
    refine ConcreteCategory.hom_ext _ _ fun x => Subtype.ext ?_
    exact sv_map ρ γ f.unop.appTop.hom x.1

include hr hγ in
private def edOf : Augmented.ExtraDegeneracy (augOf ρ hc) where
  s' := sZ γ (fun _ => hr rfl)
  s n := sN ρ hc hr γ hγ n
  s'_comp_ε := by
    ext U m
    exact hγ m
  s₀_comp_δ₁ := by
    ext U x
    refine Subtype.ext (funext fun (i : Fin 1) => ?_)
    have : i = 0 := Subsingleton.elim _ _
    subst this
    rfl
  s_comp_δ₀ n := by
    ext U x
    refine Subtype.ext (funext fun i => ?_)
    change sv ρ γ x.1 (Fin.succAbove 0 i) = x.1 i
    simp [sv]
  s_comp_δ n i := by
    ext U x
    refine Subtype.ext (funext fun j => ?_)
    exact sv_δ ρ hc γ x.2 i j
  s_comp_σ n i := by
    ext U x
    refine Subtype.ext (funext fun j => ?_)
    exact sv_σ ρ hc γ x.1 i j

end UpperTheory.SimplicialRelations

theorem UpperTheory.equiv_of_constant_section :
    A1 → ∀ (R : Type) [CommRing R] (F : Shv R) {X M : RF} (ρ : X.Hom M) (hc : ρ.Const), (∀ {A : Type} [CommRing A] {x y : X.obj A}, ρ.app A x = ρ.app A y → X.rel x y) → ∀ γ : M.Hom X, (∀ {A : Type} [CommRing A] (m : M.obj A), ρ.app A (γ.app A m) = m) → Eqv R (CN.proj ρ hc) F := by
  intro hA R _ F X M ρ hc hr γ hγ n
  have q : QuasiIso ((chainsN R).map (CN.proj ρ hc)) :=
    UpperTheory.SimplicialRelations.qi_of_ed R (UpperTheory.SimplicialRelations.augOf ρ hc) (UpperTheory.SimplicialRelations.edOf ρ hc hr γ hγ)
  have q2 : QuasiIso ((chains R).map (CN.proj ρ hc)) := by
    change QuasiIso (HomologicalComplex.extendMap ((chainsN R).map (CN.proj ρ hc)) ComplexShape.embeddingDownNat)
    infer_instance
  exact hA R ((chains R).map (CN.proj ρ hc)) F n
