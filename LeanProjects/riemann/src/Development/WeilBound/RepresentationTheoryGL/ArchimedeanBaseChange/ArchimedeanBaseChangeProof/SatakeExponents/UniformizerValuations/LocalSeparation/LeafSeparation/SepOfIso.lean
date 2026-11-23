import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS.Leaf

def LeafIso : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)) (w : Pl E)
  (σ : SmIrr (GLw N w)), IsDiscrete V → IsLocCompGL V w σ →
  V ≤ ⨆ f : {f : σ.V →ₗ[ℂ] Sm E N // (∀ v, f v ∈ V) ∧ ∀ g v, f (σ.ρ g v) = finRep E N (locGL E N w g) (f v)},
    LinearMap.range f.1

def SepOfIso : Prop := ∀ (G V : Type) [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (S : Submodule ℂ V) (σ : SmIrr G), (∀ g, ∀ x ∈ S, ρ g x ∈ S) →
  S ≤ ⨆ f : {f : σ.V →ₗ[ℂ] V // (∀ v, f v ∈ S) ∧ ∀ g v, f (σ.ρ g v) = ρ g (f v)}, LinearMap.range f.1 → Sep ρ S σ.ρ

end PositivityTheory.Rg.BcB.F.RS.Leaf
