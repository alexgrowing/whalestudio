import Formalism.WeaklyAdmissibleFiltrations.Statement

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module TensorProduct

structure PotCrysData (G : Type) [Group G] (Qp K₀ K K₀' K' : Type) [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR] where
  H : Subgroup G
  normal : H.Normal
  finiteIndex : H.FiniteIndex
  PD : PeriodData G Qp K₀ K B BdR
  PD' : PeriodData H Qp K₀' K' B BdR
  actB_eq : ∀ (h : H) (b : B), PD'.actB h b = PD.actB (h : G) b
  actdR_eq : ∀ (h : H) (b : BdR), PD'.actdR h b = PD.actdR (h : G) b
  φ_eq : ∀ b : B, PD'.φ b = PD.φ b
  ι_eq : ∀ b : B, PD'.ι b = PD.ι b
  Fil_eq : ∀ a, (PD'.Fil a : Set BdR) = PD.Fil a
  p_eq : PD'.p = PD.p
  t_eq : PD'.t = PD.t
  χ_eq : ∀ h : H, PD'.χ h = PD.χ (h : G)
  stableK₀' : ∀ (g : G) (c : K₀'), ∃ c' : K₀', PD.actB g (algebraMap K₀' B c) = algebraMap K₀' B c'

namespace PotCrysData

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

def resH : Representation LL PC.H V := ρ.comp PC.H.subtype

def Dpcris : Submodule LL (V ⊗[Qp] B) := Dcris PC.PD' (PC.resH ρ)

def IsPotCrys : Prop := IsCrys PC.PD' (PC.resH ρ)

def Iner : Subgroup G where
  carrier := {g | ∀ c : K₀', PC.PD.actB g (algebraMap K₀' B c) = algebraMap K₀' B c}
  one_mem' := fun c => by simp
  mul_mem' := by
    intro a b ha hb c
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, AlgEquiv.mul_apply, hb c, ha c]
  inv_mem' := by
    intro a ha c
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha c]
    rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]

def Eig (I : Subgroup G) (a : I →* LLˣ) : Submodule LL (V ⊗[Qp] B) :=
  PC.Dpcris ρ ⊓ ⨅ g : I, LinearMap.ker (actVB PC.PD ρ (g : G) - ((a g : LLˣ) : LL) • LinearMap.id)

def InertiaThrough (Sig : Finset (PC.Iner →* LLˣ)) : Prop :=
  (∀ a ∈ Sig, ∀ g : PC.Iner, (g : G) ∈ PC.H → a g = 1) ∧
    (∀ a ∈ Sig, Nat.Coprime (orderOf a) PC.PD.p) ∧ PC.Dpcris ρ = ⨆ a ∈ Sig, PC.Eig ρ PC.Iner a

def IsFrob (F : G) : Prop :=
  ∀ c : K₀', PC.PD.actB F (algebraMap K₀' B c) = algebraMap K₀' B (PC.PD'.σ c)

end PotCrysData

def FrobStable {G : Type} [Group G] {LL : Type} [Field LL] (I : Subgroup G) (F : G)
    (Sig : Finset (I →* LLˣ)) : Prop :=
  ∀ a ∈ Sig, ∃ b ∈ Sig, ∀ g : I, ∀ h : I, (h : G) = F⁻¹ * g * F → b g = a h

end Formalism.WeaklyAdmissibleFiltrations
