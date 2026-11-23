import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

namespace BcIso

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {X : Over (Sp R)} {X' : Over (Sp R')}
  {q : X'.left ⟶ X.left}

def ringOf {E : Type} [CommRing E] (g : Sp E ⟶ X'.left) : R' →+* E :=
  (Spec.preimage (R := CommRingCat.of R') (S := CommRingCat.of E) (g ≫ X'.hom)).hom

theorem spMap_ringOf {E : Type} [CommRing E] (g : Sp E ⟶ X'.left) : spMap (ringOf g) = g ≫ X'.hom := by
  unfold ringOf
  exact Spec.map_preimage _

theorem ringOf_eq_of_spMap {E : Type} [CommRing E] (g : Sp E ⟶ X'.left) (τ : R' →+* E)
    (h : spMap τ = g ≫ X'.hom) : ringOf g = τ := by
  have h1 : spMap (ringOf g) = spMap τ := by rw [spMap_ringOf, h]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

def ptBack [IsIso q] {E : Type} [CommRing E] (g : Sp E ⟶ X.left) :
    @Pt R' _ X' E _ (ringOf (X' := X') (g ≫ inv q)).toAlgebra :=
  @Over.homMk _ _ _ (@SpAlg R' E _ _ (ringOf (X' := X') (g ≫ inv q)).toAlgebra) X' (g ≫ inv q)
    (spMap_ringOf (X' := X') (g ≫ inv q)).symm

theorem ringOf_comp (w : q ≫ X.hom = X'.hom ≫ spMap σ) [IsIso q] {E : Type} [CommRing E] [Algebra R E]
    (z : Pt X E) : (ringOf (X' := X') (z.left ≫ inv q)).comp σ = algebraMap R E := by
  have h1 : spMap ((ringOf (X' := X') (z.left ≫ inv q)).comp σ) = spMap (algebraMap R E) := by
    rw [spMap_comp, spMap_ringOf]
    simp only [Category.assoc, ← w, IsIso.inv_hom_id_assoc]
    exact Over.w z
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

theorem bcPull_transport (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X) (E E' : Type) [CommRing E] [CommRing E']
    (A : Algebra R' E) (A' : Algebra R' E') (i : Algebra R E) (i' : Algebra R E') (h : i = algVia σ E)
    (h' : i' = algVia σ E') (φ : @AlgHom R E E' _ _ _ i i') (z : @Pt R _ X E _ i) (ψ : E →ₐ[R'] E')
    (y : Pt X' E) (hψ : ∀ e, ψ e = φ e) (hy : y.left ≫ q = z.left) :
    @u E _ i E' _ i' φ z = bcPull w u E E' ψ y := by
  subst h h'
  letI := algVia σ E
  letI := algVia σ E'
  have e1 : homVia σ ψ = φ := AlgHom.ext hψ
  have e2 : ptVia w y = z := by
    apply Over.OverMorphism.ext
    exact hy
  rw [← e1, ← e2]
  rfl

end BcIso

open BcIso

theorem isCob_of_bcPull_isIso : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R))
    (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ), IsIso q → ∀ u : Fn1 X,
    IsCoc (whole X) u → (∃ k, IsCob (whole X') (bcPull w u) k) → ∃ k, IsCob (whole X) u k := by
  intro R R' _ _ σ X X' q w hq u _ hk
  obtain ⟨k', hk'⟩ := hk
  refine ⟨fun E _ _ z ↦ @k' E _ (ringOf (X' := X') (z.left ≫ inv q)).toAlgebra (ptBack z.left), ?_⟩
  intro E _ i E' _ i' φ z _
  let τ := ringOf (X' := X') (z.left ≫ inv q)
  let τ' := ringOf (X' := X') ((spOver φ ≫ z).left ≫ inv q)
  letI A : Algebra R' E := τ.toAlgebra
  letI A' : Algebra R' E' := τ'.toAlgebra
  have hτ : τ' = (φ : E →+* E').comp τ := by
    apply ringOf_eq_of_spMap
    rw [spMap_comp, spMap_ringOf]
    simp only [Over.comp_left, Category.assoc]
    rfl
  have hc : ∀ r, φ (τ r) = τ' r := fun r ↦ by rw [hτ]; rfl
  let ψ : E →ₐ[R'] E' := { (φ : E →+* E') with commutes' := hc }
  have h : i = algVia σ E := Algebra.algebra_ext _ _ fun r ↦ (congrArg (fun f ↦ f r) (ringOf_comp w z)).symm
  have h' : i' = algVia σ E' :=
    Algebra.algebra_ext _ _ fun r ↦ (congrArg (fun f ↦ f r) (ringOf_comp w (spOver φ ≫ z))).symm
  have e1 := bcPull_transport w u E E' A A' i i' h h' φ z ψ (ptBack z.left) (fun _ ↦ rfl)
    (by simp [ptBack])
  have e2 := hk' E E' ψ (ptBack z.left) (sm_whole _)
  have e3 : spOver ψ ≫ ptBack (X' := X') z.left = ptBack (spOver φ ≫ z).left :=
    Over.OverMorphism.ext (by simp [ptBack]; rfl)
  rw [e1, e2, e3]
  rfl

end GlobalTheory.PtExt
