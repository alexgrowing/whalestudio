import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem mem_adicCompletionIntegers_iff_valuation_le_one (F : Type) [Field F] [NumberField F] (v : Pl F) (x : Kv v) :
    x ∈ v.adicCompletionIntegers F ↔ valuation (Kv v) x ≤ 1 := by
  rw [← (valuation (Kv v)).vle_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  change _ ↔ Valued.v x ≤ Valued.v (1 : Kv v)
  rw [map_one]

theorem UpperTheory.V.Z.Sym.Dict.Br.intsOv :
    ∀ (F : Type) [Field F] [NumberField F] (v : Pl F), Sig.IsInts (Kv v) (Ov v) ∧ ∀ x : Kv v, x ∈ v.adicCompletionIntegers F ↔ valuation (Kv v) x ≤ 1 := by
  intro F _ _ v
  refine ⟨⟨Subtype.val_injective, fun x => ?_⟩, mem_adicCompletionIntegers_iff_valuation_le_one F v⟩
  rw [← mem_adicCompletionIntegers_iff_valuation_le_one F v x]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
