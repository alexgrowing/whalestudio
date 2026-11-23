import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.openLev :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π → ∀ φ : UA L n → V, CoefIn φ π →
        ∃ U : Subgroup (UA L n), IsOpen {x : finU L n | (x : UA L n) ∈ U} ∧ ∀ u ∈ U, ∀ g, φ (g * u) = φ g := by
  intro L _ _ _ n V _ _ _ π hπ φ hc
  let U : Subgroup (UA L n) :=
    { carrier := {u | ∀ g, φ (g * u) = φ g}
      one_mem' := fun g => by rw [mul_one]
      mul_mem' := fun {a b} ha hb g => by rw [← mul_assoc, hb, ha]
      inv_mem' := fun {a} ha g => by rw [← ha, inv_mul_cancel_right] }
  refine ⟨U, ?_, fun u hu => hu⟩
  let b := Module.finBasis ℂ V
  have e : {x : finU L n | (x : UA L n) ∈ U} = ⋂ i, {k : finU L n | RU L n k (b.coord i ∘ φ) = b.coord i ∘ φ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine ⟨fun h i => funext fun g => congrArg (b.coord i) (h g), fun h g => b.ext_elem fun i => congrFun (h i) g⟩
  rw [e]
  exact isOpen_iInter_of_finite fun i => (hπ.aut _ (hc _)).level
