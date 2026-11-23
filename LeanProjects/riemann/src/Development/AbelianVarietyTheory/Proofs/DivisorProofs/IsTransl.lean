import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

open GlobalTheory.DeRham

variable {K : Type} [Field K]

def IsTransl {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (v : epsR K ⟶ A) (w : Sp (DualNumber B) ⟶ A.left) : Prop :=
  ∃ x' v' : Over.mk (spMap ((algebraMap B (DualNumber B)).comp φ)) ⟶ A,
    x'.left = spMap (algebraMap B (DualNumber B)) ≫ x ∧ v'.left = spMap (dualMap φ) ≫ v.left ∧ (x' * v').left = w

def IsCechKS (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) (i : A.left ⟶ A'.left) (L : LB A.left)
    {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ (J : Type) (W : J → A.left.Opens) (c : J → L.ι)
    (lam : ∀ (_ : J) (B : Type) [CommRing B] [Algebra (DualNumber K) B], (Sp B ⟶ A.left) → (Sp B ⟶ A'.left)),
    ⨆ k, W k = ⊤ ∧ (∀ k, W k ≤ L.U (c k)) ∧
    (∀ k (B : Type) [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left),
      x ≫ A.hom = spMap ((algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))) → ⊤ ≤ x ⁻¹ᵁ W k →
      lam k B x ≫ A'.hom = spMap (algebraMap (DualNumber K) B) ∧
      spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ lam k B x =
        spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ x ≫ i ∧
      ∀ (B' : Type) [CommRing B'] [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B'),
        spMap (ρ : B →+* B') ≫ lam k B x = lam k B' (spMap (ρ : B →+* B') ≫ x)) ∧
    ∀ (k k' : J) (B : Type) [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left)
      (O : A'.left.Opens) (f : Γ(A'.left, O)) (w : Fin n → (Sp (DualNumber B) ⟶ A.left)),
      x ≫ A.hom = spMap ((algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))) →
      ⊤ ≤ x ⁻¹ᵁ (W k ⊓ W k') → ⊤ ≤ x ⁻¹ᵁ (i ⁻¹ᵁ O) →
      (∀ a, IsTransl ((algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))) x (u a) (w a)) →
      valR (lam k B x) O f - valR (lam k' B x) O f =
        algebraMap (DualNumber K) B DualNumber.eps *
          ∑ a, ∑ b, (algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K)) (θ a b) *
            ((valR (w b) _ (L.g (c k) (c k')).val).snd * valR x _ (L.g (c k) (c k'))⁻¹.val) *
            (valR (w a) (i ⁻¹ᵁ O) ((i.app O).hom f)).snd

end GlobalTheory.CechKS
