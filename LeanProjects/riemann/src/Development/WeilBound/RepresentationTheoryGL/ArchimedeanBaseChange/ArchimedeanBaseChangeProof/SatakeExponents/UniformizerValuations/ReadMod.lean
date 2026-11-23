import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadSplit

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

abbrev lp (P : Pre E n) (w : Pl E) := locProd P.h w (P.σ · w)

def SmVec {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V) : Prop :=
  ∃ U : Subgroup G, IsOpen (U : Set G) ∧ x ∈ fixed ρ U

def Sep {G V X : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G V) (S : Submodule ℂ V) (τ : Representation ℂ G X) : Prop :=
  (∀ g, ∀ x ∈ S, ρ g x ∈ S) ∧ ∃ (J : Type) (L : J → V →ₗ[ℂ] X),
    (∀ j g, ∀ x ∈ S, SmVec ρ x → L j (ρ g x) = τ g (L j x)) ∧ ∀ x ∈ S, SmVec ρ x → (∀ j, L j x = 0) → x = 0

def LeafMod : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)) (w : Pl E)
  (σ : SmIrr (GLw N w)), IsDiscrete V → IsLocCompGL V w σ → Sep ((finRep E N).comp (locGL E N w)) V σ.ρ

def NodeMod : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ) (t₁ : Tr E r) (t₂ : Tr E s) (w : Pl E)
  (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ₁ : Representation ℂ (GLw r w) X)
  (τ₂ : Representation ℂ (GLw s w) Y), Sep ((finRep E r).comp (locGL E r w)) t₁.space τ₁ →
  Sep ((finRep E s).comp (locGL E s w)) t₂.space τ₂ →
  Sep ((finRep E (r + s)).comp (locGL E (r + s) w)) (Tr.node t₁ t₂).space
    (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.extTensor τ₁ τ₂))

def JoinMod : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (χ₁ χ₂ : HChar E)
  (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n) (w : Pl E), IsJoin χ₁ χ₂ Pa Pb D →
  Nonempty ((lp D w).Equiv (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h)
    (GlobalTheory.SmGL.extTensor (twRep (lp Pa w) ((χ₁.loc w).comp GeneralLinearGroup.det))
      (twRep (lp Pb w) ((χ₂.loc w).comp GeneralLinearGroup.det)))))

def TreeMod : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (P : Pre E N) (w : Pl E),
  t.Good → t.Untw → TreeParts t P → Sep ((finRep E N).comp (locGL E N w)) t.space (lp P w)

def ReadMod : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (s₁ : Tr E a) (s₂ : Tr E b)
  (Pa : Pre E a) (Pb : Pre E b) (w : Pl E), s₁.Good → s₂.Good → s₁.Untw → s₂.Untw → TreeParts s₁ Pa → TreeParts s₂ Pb →
  Sep (pairRt a b w) (pairSpace s₁.space s₂.space) (GlobalTheory.SmGL.extTensor (lp Pa w) (lp Pb w))

def TreeModOf : Prop := LeafMod → NodeMod → JoinMod → TreeMod

def ReadModOf : Prop := TreeMod → ReadMod

def TreeSatOf : Prop := TreeMod → TreeSat

end PositivityTheory.Rg.BcB.F.RS

end
