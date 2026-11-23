import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd

noncomputable section

namespace UpperTheory.V.Loc

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV IsLocalRing

def wtDer {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] (𝒜 : X → Submodule O R) (x : R →ₐ[O] O)
    (E : Type) [Field E] [Algebra O E] (j : X) : Submodule E (R →ₗ[O] E) where
  carrier := {D | D ∈ PtDer ((Algebra.ofId O E).comp x) E ∧ HasWt 𝒜 j D}
  zero_mem' := ⟨zero_mem _, fun _ _ _ _ => rfl⟩
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun i hi f hf => by
    rw [LinearMap.add_apply, ha.2 i hi f hf, hb.2 i hi f hf, add_zero]⟩
  smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun i hi f hf => by
    rw [LinearMap.smul_apply, ha.2 i hi f hf, smul_zero]⟩

def dimsL (w : ℤ × ℤ) : ℕ :=
  if w = wAl ∨ w = wBe ∨ w = wPs ∨ w = wTh ∨ w = 0 then 2 else if w ∈ wts then 1 else 0

def dimsP (w : ℤ × ℤ) : ℕ := if w = 0 then 2 else if w ∈ wts then 1 else 0

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
  {B : Type} [CommRing B] [Algebra c.O B]

def EqL (r : D.Gp l →* M4 B) : Prop :=
  (∀ g : D.Gp l, IsGSp (algebraMap c.O B (D.th g)) (r g)) ∧
    Ord ((D.Ip l).subgroupOf (D.Gp l)) (fun i g => algebraMap c.O B (D.ps i g)) D.s0 r

def EqP (p : ℕ) (r : D.Gp p →* M4 B) : Prop :=
  (∀ g : D.Gp p, IsGSp (algebraMap c.O B (D.th g)) (r g)) ∧
    ∀ g : D.Gp p, (g : G ℚ Ω) ∈ D.Ip p ⊓ D.ψ.ker → r g = 1

structure IsContinuousLiftOfRZero [Algebra ℚ_[l] B] {E : Type} [CommRing E] [Algebra c.O E] (π : B →+* E) (v : ℕ)
    (r : D.Gp v →* M4 B) : Prop where
  red : mapRep π r = mapRep (algebraMap c.O E) (D.r0At v)
  cont : ∀ a b, QCont l fun g => r g a b

def IsFirstOrderDeformationOfRZero {E : Type} [CommRing E] [Algebra c.O E] (v : ℕ) (γ : D.Gp v → M4 E) (r' : D.Gp v →* M4 (DualNumber E)) :
    Prop :=
  ∀ g a b, r' g a b = ⟨algebraMap c.O E (D.r0At v g a b), (γ g * (D.r0At v g).map (algebraMap c.O E)) a b⟩

def FlagIn {H K : Type} [Group H] [CommRing K] (r : H →* M4 K) (h : (M4 K)ˣ) (κ : Fin 4 → H →* Kˣ) : Prop :=
  ∀ g, (∀ i j, j < i → ((h⁻¹ : (M4 K)ˣ) * r g * h : M4 K) i j = 0) ∧
    ∀ i, ((h⁻¹ : (M4 K)ˣ) * r g * h : M4 K) i i = (κ i g : K)

def PtOn {v : ℕ} (P : Cond c.O (D.rbarAt v)) {K : Type} [CommRing K] [Algebra c.O K] (r : D.Gp v →* M4 K) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.O R) (_ : IsCO c.O R) (ρ : Lift c.O (D.rbarAt v) R) (y : R →ₐ[c.O] K),
    OnComp P (D.r0At v) ρ ∧ r = mapRep (y : R →+* K) ρ.hom

end UpperTheory.V.Loc
