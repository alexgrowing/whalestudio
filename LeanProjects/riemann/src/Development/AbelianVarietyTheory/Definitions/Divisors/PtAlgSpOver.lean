import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

def Fn1.pull {X Y : Over (Sp R)} (q : Y ⟶ X) (u : Fn1 X) : Fn1 Y := fun D _ _ D' _ _ φ y ↦ u D D' φ (y ≫ q)

section Alg

variable {D E E' : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E']

def ptAlg (z : Pt (SpAlg R D) E) : D →ₐ[R] E :=
  { (Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left).hom with
    commutes' := fun r ↦ by
      have h : CommRingCat.ofHom (algebraMap R D) ≫
          Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left =
          CommRingCat.ofHom (algebraMap R E) := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage]
        exact Over.w z
      exact congrArg (fun f ↦ CommRingCat.Hom.hom f r) h }

theorem spOver_ptAlg (z : Pt (SpAlg R D) E) : spOver (ptAlg z) = z :=
  Over.OverMorphism.ext (Spec.map_preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left)

theorem ptAlg_spOver (α : D →ₐ[R] E) : ptAlg (spOver α) = α := by
  refine AlgHom.ext fun r ↦ ?_
  exact congrArg (fun f ↦ CommRingCat.Hom.hom f r) (Spec.preimage_map (CommRingCat.ofHom (α : D →+* E)))

theorem ptAlg_comp (ψ : E →ₐ[R] E') (z : Pt (SpAlg R D) E) : ptAlg (spOver ψ ≫ z) = ψ.comp (ptAlg z) := by
  conv_lhs => rw [← spOver_ptAlg z, spOver_comp]
  exact ptAlg_spOver _

def epsEv (e : Pt (epsR R) E) : DualNumber E →ₐ[R] E :=
  DualNumber.lift ⟨(AlgHom.id R E, ptAlg (D := DualNumber R) e DualNumber.eps), by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero], fun _ ↦ Commute.all _ _⟩

end Alg

section Param

variable {A B : Over (Sp R)} {J : Type} [Fintype J] {D : Type} [CommRing D] [Algebra R D]

def sumMul (d : J → D) (b : J → Fn1 B) : Fn1 (SpAlg R D ⊗ B) := fun E _ _ E' _ _ ψ z ↦
  ∑ i, ψ (ptAlg (z ≫ fst _ _) (d i)) * b i E E' ψ (z ≫ snd _ _)

def IsCupCob {K : Type} (W : K → (A ⊗ B).left.Opens) (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)) : Prop :=
  ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E'']
    [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt (A ⊗ B) E), Sm W z →
    ψ (n E E' φ z) - n E E'' (ψ.comp φ) z + n E' E'' ψ (spOver φ ≫ z) =
      ∑ i, ψ (a i E E' φ (z ≫ fst _ _)) * b i E' E'' ψ (spOver φ ≫ z ≫ snd _ _)

def parCoc (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)) (x : Pt A D) : Fn1 (SpAlg R D ⊗ B) :=
  fun E _ _ E' _ _ ψ z ↦ n E E' ψ (z ≫ x ▷ B) -
    ∑ i, ψ (a i D E (ptAlg (z ≫ fst _ _)) x) * b i E E' ψ (z ≫ snd _ _)

def parCov {K : Type} (W : K → (A ⊗ B).left.Opens) (x : Pt A D) : K → (SpAlg R D ⊗ B).left.Opens :=
  fun i ↦ (x ▷ B).left ⁻¹ᵁ W i

end Param

section Change

variable {R' : Type} [CommRing R'] (σ : R →+* R')

@[reducible] def algVia (E : Type) [CommRing E] [Algebra R' E] : Algebra R E :=
  ((algebraMap R' E).comp σ).toAlgebra

def homVia {E E' : Type} [CommRing E] [Algebra R' E] [CommRing E'] [Algebra R' E'] (ψ : E →ₐ[R'] E') :
    @AlgHom R E E' _ _ _ (algVia σ E) (algVia σ E') :=
  @AlgHom.mk R E E' _ _ _ (algVia σ E) (algVia σ E') (ψ : E →+* E') fun r ↦ ψ.commutes (σ r)

variable {σ} {X : Over (Sp R)} {X' : Over (Sp R')} {q : X'.left ⟶ X.left}

def ptVia (w : q ≫ X.hom = X'.hom ≫ spMap σ) {E : Type} [CommRing E] [Algebra R' E] (y : Pt X' E) :
    @Pt R _ X E _ (algVia σ E) :=
  Over.homMk (y.left ≫ q) (by
    have h : y.left ≫ X'.hom = spMap (algebraMap R' E) := Over.w y
    change (y.left ≫ q) ≫ X.hom = spMap ((algebraMap R' E).comp σ)
    rw [Category.assoc, w, ← Category.assoc, h, Cris.spMap_comp])

def bcPull (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X) : Fn1 X' := fun E _ _ E' _ _ ψ y ↦
  @u E _ (algVia σ E) E' _ (algVia σ E') (homVia σ ψ) (ptVia w y)

end Change

section Gen

variable {X Y : Over (Sp R)}

def IsPtGen (L : LB X.left) (q : Y ⟶ X)
    (t : ∀ (E : Type) [CommRing E] [Algebra R E], Pt Y E → L.ι → E) : Prop :=
  (∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E) (i : L.ι), ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U i → IsUnit (t E z i)) ∧
  (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E') (z : Pt Y E)
    (i : L.ι), ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U i → t E' (spOver ψ ≫ z) i = ψ (t E z i)) ∧
  ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E) (i j : L.ι), ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U i →
    ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U j → t E z i = evU (z ≫ q).left (L.U i ⊓ L.U j) (L.g i j).val * t E z j

variable {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

def IsEpsGen (P : LB (A ⊗ B).left) (v : epsR R ⟶ B)
    (T : ∀ (E : Type) [CommRing E] [Algebra R E], Pt A E → P.ι → DualNumber E) : Prop :=
  (∀ (E : Type) [CommRing E] [Algebra R E] (x : Pt A E) (i : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i → IsUnit (T E x i)) ∧
  (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E') (x : Pt A E)
    (i : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i → T E' (spOver ψ ≫ x) i = epsHom ψ (T E x i)) ∧
  ∀ (E : Type) [CommRing E] [Algebra R E] (x : Pt A E) (i j : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i →
    ⊤ ≤ x.left ⁻¹ᵁ chartsA P j → T E x i = evU (ptV v x).left (P.U i ⊓ P.U j) (P.g i j).val * T E x j

end Gen

end GlobalTheory.PtExt
