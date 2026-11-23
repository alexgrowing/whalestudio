import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
open scoped InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiniteUnitaryAction

def IsUnitaryRep {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Representation ℂ G H) : Prop :=
  ∀ (g : G) (x y : H), inner ℂ (ρ g x) (ρ g y) = inner ℂ x y

section ClassSum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ)

def pairAt (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (σ (S.bV.repr x i)) * σ (S.gramV i j) * σ (S.bV.repr y j)

def classSumAt (f f' : S.Forms) : ℂ :=
  ∑ c, ((S.wt c : ℂ))⁻¹ * pairAt S σ ((f : S.Cl → S.V) c) ((f' : S.Cl → S.V) c)

def IsUnitaryAt {G : Type} [Group G] (r : Representation K G S.Forms) : Prop :=
  ∀ (g : G) (f f' : S.Forms), classSumAt S σ (r g f) (r g f') = classSumAt S σ f f'

theorem wt_ne_zero (c : S.Cl) : (S.wt c : ℂ) ≠ 0 := by
  have : 0 < S.wt c := Fintype.card_pos
  exact_mod_cast this.ne'

theorem pairAt_smul_left (a : K) (x y : S.V) : pairAt S σ (a • x) y = starRingEnd ℂ (σ a) * pairAt S σ x y := by
  simp only [pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem pairAt_smul_right (a : K) (x y : S.V) : pairAt S σ x (a • y) = σ a * pairAt S σ x y := by
  simp only [pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pairAt_eq (h : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) (x y : S.V) : pairAt S σ x y = σ (S.pair x y) := by
  have e : S.pair x y = ∑ i, ∑ j, star (S.bV.repr x i) * S.gramV i j * S.bV.repr y j := by
    conv_lhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      starRingEnd_apply, CSD.gramV, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  simp only [pairAt, map_sum, map_mul, h]

theorem classSumAt_eq (h : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) (f f' : S.Forms) :
    classSumAt S σ f f' = σ (S.csum f f') := by
  simp only [classSumAt, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast, pairAt_eq S σ h]

theorem isUnitaryAt_iff (h : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {G : Type} [Group G] (r : Representation K G S.Forms) :
    IsUnitaryAt S σ r ↔ ∀ (g : G) (f f' : S.Forms),
      S.csum (r g f : S.Cl → S.V) (r g f' : S.Cl → S.V) = S.csum (f : S.Cl → S.V) (f' : S.Cl → S.V) := by
  simp only [IsUnitaryAt, classSumAt_eq S σ h, σ.injective.eq_iff]

end ClassSum

section Statement

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}

structure DefiniteUnitary (A : FamIn D.what₂.LL G Pl0 T D.R.m) : Prop where

  what₂ : ∀ (t : T) (σ : D.what₂.LL →+* ℂ), IsUnitaryAt (A.MtildeCSD t) σ (A.leftGroupActionRight t)

  lifts : ∀ (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ), IsUnitaryAt (A.MtCSD i t) σ (A.leftGroupActionLift i t)

variable {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure ActsUnitarily (R : RealDat D A Ks) : Prop where

  what₂ : IsUnitaryRep R.gE

  formsW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), IsUnitaryRep (R.gW i σ)

  definite : DefiniteUnitary A

def UnitaryOfChar (R : RealDat D A Ks) (F : Face D A) : Prop := R.Char F → ActsUnitarily R

end Statement

def UnitaryAction : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), UnitaryOfChar R F

section Basic₂

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem IsUnitaryRep.tw {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ρ : Representation ℂ G H}
    (h : IsUnitaryRep ρ) (s : Bool) : IsUnitaryRep (Tw.rep s ρ) := fun g x y =>
  congrArg (cj s) (h g (Tw.out x) (Tw.out y))

theorem DefiniteUnitary.csum (h : DefiniteUnitary A) :
    (∀ t g (f f' : (A.MtildeCSD t).Forms), (A.MtildeCSD t).csum (A.leftGroupActionRight t g f : _ → _) (A.leftGroupActionRight t g f' : _ → _) =
      (A.MtildeCSD t).csum (f : _ → _) (f' : _ → _)) ∧
    ∀ i t g (f f' : (A.MtCSD i t).Forms), (A.MtCSD i t).csum (A.leftGroupActionLift i t g f : _ → _) (A.leftGroupActionLift i t g f' : _ → _) =
      (A.MtCSD i t).csum (f : _ → _) (f' : _ → _) :=
  ⟨fun t => (isUnitaryAt_iff _ _ D.starLL_cx _).1 (h.what₂ t _), fun i t => (isUnitaryAt_iff _ _ D.starLL_cx _).1 (h.lifts i t _)⟩

theorem rows_iff (R : RealDat D A Ks) (F : Face D A) (h : R.Char F) :
    IsUnitaryRep R.gE ↔ ∀ (g : G), ∀ x ∈ R.EEat R.triv, ∀ y ∈ R.EEat R.triv,
      Formalism.IndefR.Mult.ipM (R.MY 0) R.ν0 R.fd0
                (Formalism.IndefR.Mult.postOn _ (actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)) x)
                (Formalism.IndefR.Mult.postOn _ (actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)) y) =
        Formalism.IndefR.Mult.ipM (R.MY 0) R.ν0 R.fd0 x y := by
  obtain ⟨-, hr, hip⟩ := h.models.HE
  constructor
  · intro hu g x hx y hy
    rw [← hr] at hx hy
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    rw [← h.models.gE, ← h.models.gE, ← hip, ← hip, hu]
  · intro hu g x y
    rw [hip, hip, h.models.gE, h.models.gE]
    exact hu g _ (hr ▸ LinearMap.mem_range_self _ x) _ (hr ▸ LinearMap.mem_range_self _ y)

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.DefiniteUnitaryAction

end
