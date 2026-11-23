import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWsp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPo

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

section Generic

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

def eqvM (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) : Submodule ℂ (G → V) where
  carrier := {φ | (∀ h x, φ (ι h * x) = ρ h (φ x)) ∧ ∀ k ∈ K, ∀ x, φ (x * k) = φ x}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun h x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.add_apply, ha.1 h x, hb.1 h x, map_add]
    · simp only [Pi.add_apply, ha.2 k hk x, hb.2 k hk x]
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun h x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.smul_apply, ha.1 h x, map_smul]
    · simp only [Pi.smul_apply, ha.2 k hk x]

def stabCard (ι : H →* G) (K : Subgroup G) (x : G) : ℕ :=
  Nat.card (ι.range ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G)

def secM (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) (x : G) : V →ₗ[ℂ] (G → V) where
  toFun v y := ((stabCard ι K x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K then ρ h else 0) v
  map_add' a b := by
    funext y
    simp only [map_add, smul_add, Pi.add_apply]
  map_smul' c a := by
    funext y
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_comm c]

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPtHom : UE E n →* finU E n where
  toFun := finPt
  map_one' := by
    apply Subtype.ext
    rw [FinPtLoc.finPt_eq]
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, FinPtLoc.finPt_eq, FinPtLoc.finPt_eq, FinPtLoc.finPt_eq]
    apply Subtype.ext
    exact (congrArg (finGL E n) (map_mul (ratF E n) a.1 b.1)).trans (map_mul _ _ _)

theorem finPtHom_apply (γ : UE E n) : finPtHom γ = finPt γ := rfl

theorem wAt_mul (lam : InfinitePlace E → DomWeight n) (a b : UE E n) :
    GlobalTheory.BCT.TrKer.wAt lam (a * b) = GlobalTheory.BCT.TrKer.wAt lam a ∘ₗ GlobalTheory.BCT.TrKer.wAt lam b := by
  unfold GlobalTheory.BCT.TrKer.wAt
  rw [← PiTensorProduct.map_comp]
  refine congrArg PiTensorProduct.map (funext fun v => ?_)
  change GlobalTheory.Branching.sqRep ℂ n (lam v) (GeneralLinearGroup.map v.embedding (a.1 * b.1)) = _
  rw [map_mul, map_mul, Module.End.mul_eq_comp]

theorem wAt_one (lam : InfinitePlace E → DomWeight n) : GlobalTheory.BCT.TrKer.wAt lam 1 = LinearMap.id := by
  unfold GlobalTheory.BCT.TrKer.wAt
  simp only [OneMemClass.coe_one, map_one]
  exact PiTensorProduct.map_id

def wDual (lam : InfinitePlace E → DomWeight n) : Representation ℂ (UE E n) (Module.Dual ℂ (GlobalTheory.BCT.TrKer.Wsp lam)) where
  toFun γ := (GlobalTheory.BCT.TrKer.wAt lam γ⁻¹).dualMap
  map_one' := by
    rw [inv_one, wAt_one]
    rfl
  map_mul' a b := by
    rw [_root_.mul_inv_rev, wAt_mul, ← LinearMap.dualMap_comp_dualMap]
    rfl

end GlobalTheory.BCT.TraceBlocks
