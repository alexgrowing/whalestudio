import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnrSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Ga

variable {k : Type} [Field k]

abbrev tr {n : ℕ} (g : GL (Fin n) k) : k := (g : Matrix (Fin n) (Fin n) k).trace

def uf (g : GL (Fin 2) k) : k := tr g ^ 2 / (g : Matrix (Fin 2) (Fin 2) k).det - 2

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] {l : ℕ} [Fact l.Prime]

abbrev ep (l : ℕ) [Fact l.Prime] (g : G L Ω) : Qbar l := (cycBar L Ω l g : Qbar l)

def Bad (r : G L Ω →* GL (Fin 2) (Qbar l)) : Set (G L Ω) :=
  {g | ∃ m : ℤ, |m| ≤ 2 ∧ uf (r g) ^ 2 - 2 = ep l g ^ m + ep l g ^ (-m)}

def FrobAt (w : Plc L) (s : G L Ω) : Prop := ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ IsFrob A (normV w) s

variable [IsCMField L] [IsAlgClosure L Ω]

structure GalOf {n : ℕ} (ι : Qbar l ≃+* ℂ) (σ : Submodule ℂ (UA L n → ℂ)) (r : G L Ω →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous r
  comp : ∀ w, IsSplitAt w → ∃ τ, Comp σ w τ
  loc : ∀ w, IsSplitAt w → ∀ τ, Comp σ w τ → LocGlob ι r w τ
  pair : ∀ c : G (maximalRealSubfield L) Ω, IsConjEl c → ∃ P, IsPairing c r (cycBar L Ω l ^ (1 - (n : ℤ))) P

structure GoodSet (ι : Qbar l ≃+* ℂ) (M : ℕ) (r : G L Ω →* GL (Fin 2) (Qbar l)) (σ : Submodule ℂ (UA L 2 → ℂ)) (P : Set (Plc L))
    (ψ : ∀ w : Plc L, Fin 2 → (Kw w)ˣ →* ℂˣ) : Prop where
  mem : ∀ w ∈ P, IsSplitAt w ∧ ((l : ℕ) : 𝓞 L) ∉ w.asIdeal ∧ CompEq σ w (ψ w)
  meets : ∀ w, IsSplitAt w → (M : 𝓞 L) ∉ w.asIdeal → (∃ s, FrobAt w s ∧ s ∉ Bad r) →
    ∃ w' ∈ P, w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))

end UpperTheory.V.Z.Sym.Ga

end
