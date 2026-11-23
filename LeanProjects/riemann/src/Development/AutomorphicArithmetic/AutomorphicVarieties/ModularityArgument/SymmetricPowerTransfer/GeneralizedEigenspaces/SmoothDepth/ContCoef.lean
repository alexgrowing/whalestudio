import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Al

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

variable (n) in

def away (w : Plc L) : Subgroup (UA L n) :=
  ⨅ (u : Plc L) (_ : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))), (cLoc u).ker

def InSpan (w : Plc L) (φ φ' : UA L n → V) : Prop :=
  φ' ∈ Submodule.span ℂ {ψ | ∃ x ∈ locU n w, ψ = fun g => φ (g * x)}

def repOn {π : Submodule ℂ (UA L n → ℂ)} (hπ : IsAutRepU π) : Representation ℂ (UA L n) π where
  toFun x := (RU L n x).restrict fun φ h => hπ.stable x φ h
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

def AF (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (U : Subgroup (UA L n)) : Submodule ℂ (UA L n → V) where
  carrier := {φ | IsAF R U φ}
  add_mem' ha hb := ⟨fun γ h g => by simp [ha.left γ h, hb.left γ h], fun x h g => by simp [ha.inf x h, hb.inf x h],
    fun u h g => by simp [ha.level u h, hb.level u h]⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => by simp, fun _ _ _ => rfl⟩
  smul_mem' c a ha := ⟨fun γ h g => by simp [ha.left γ h], fun x h g => by simp [ha.inf x h], fun u h g => by simp [ha.level u h]⟩

abbrev op (w : Plc L) (W : Sig.Lev (Kw w)) (d : Fin n → (Kw w)ˣ) : Module.End ℂ (UA L n → V) :=
  Hi.dc ((rightReg ℂ (UA L n) V).comp (secW n w)) (W.J n) (W.J n) (Sig.dg d)

def ContCoef {H : Type} [Group H] [TopologicalSpace H] (R : Representation ℂ H V) : Prop :=
  ∀ (x : V) (f : V →ₗ[ℂ] ℂ), Continuous fun g => f (R g x)

end UpperTheory.V.Z.Sym.Al

end
