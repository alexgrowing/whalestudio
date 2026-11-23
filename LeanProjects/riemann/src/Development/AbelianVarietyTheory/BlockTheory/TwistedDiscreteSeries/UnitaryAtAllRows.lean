import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAtAllPlaces

def IsUnitaryRep {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Representation ℂ G H) : Prop :=
  ∀ (g : G) (x y : H), inner ℂ (ρ g x) (ρ g y) = inner ℂ x y

section ClassSum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ)

def pairAt (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (σ (S.bV.repr x i)) * σ (S.gramV i j) * σ (S.bV.repr y j)

def csumAt (f f' : S.Cl → S.V) : ℂ := ∑ c, ((S.wt c : ℂ))⁻¹ * pairAt S σ (f c) (f' c)

def IsUnitaryAtAll {G : Type} [Group G] (r : Representation K G S.Forms) : Prop :=
  ∀ (σ : K →+* ℂ) (g : G) (f f' : S.Forms),
    csumAt S σ (r g f : S.Cl → S.V) (r g f' : S.Cl → S.V) = csumAt S σ (f : S.Cl → S.V) (f' : S.Cl → S.V)

theorem pairAt_smul (a b : K) (x y : S.V) :
    pairAt S σ (a • x) (b • y) = starRingEnd ℂ (σ a) * σ b * pairAt S σ x y := by
  simp only [pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem csumAt_smul (a b : K) (f f' : S.Cl → S.V) :
    csumAt S σ (a • f) (b • f') = starRingEnd ℂ (σ a) * σ b * csumAt S σ f f' := by
  simp only [csumAt, Pi.smul_apply, pairAt_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => by ring

theorem pairAt_eq (h : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) (x y : S.V) : pairAt S σ x y = σ (S.pair x y) := by
  conv_rhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
  simp only [pairAt, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul,
    CSD.gramV, Matrix.of_apply, RingHom.id_apply, starRingEnd_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h, starRingEnd_apply]
  ring

end ClassSum

section Statement

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowsUnitary (R : RealDat D A Ks) : Prop := IsUnitaryRep R.gE

def LiftsUnitary (R : RealDat D A Ks) : Prop := ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), IsUnitaryRep (R.gW i σ)

variable (A) in

def DefiniteUnitary : Prop :=
  (∀ t : T, IsUnitaryAtAll (A.MtildeCSD t) (A.leftGroupActionRight t)) ∧
    ∀ (i : Fin D.R.m) (t : T), IsUnitaryAtAll (A.MtCSD i t) (A.leftGroupActionLift i t)

def GroupUnitary (R : RealDat D A Ks) : Prop := RowsUnitary R ∧ LiftsUnitary R ∧ DefiniteUnitary A

end Statement

def FiniteGroupActsUnitarily : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → GroupUnitary R

example : ¬ IsUnitaryRep (G := ℂˣ) (H := ℂ) (Representation.ofDistribMulAction ℂ ℂˣ ℂ) := by
  intro h
  have := h (Units.mk0 2 two_ne_zero) 1 1
  simp [Units.smul_def] at this
  norm_num [map_ofNat] at this

example {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Representation ℂ G H)
    (h : IsUnitaryRep ρ) (g : G) (x : H) : ‖ρ g x‖ = ‖x‖ := by
  have := h g x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
  have h2 : ‖ρ g x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast this
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAtAllPlaces
