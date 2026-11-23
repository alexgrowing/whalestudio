import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.CandSt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LemDCand

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def SIso (x y : Σ M : ℕ, Submodule ℂ (Sm E M)) : Prop := ∃ h : x.1 = y.1, IsoV (h ▸ x.2) y.2

def Strict {n : ℕ} (P P' : Pre E n) : Prop :=
  List.Forall₂ SIso (parts P) (parts P') ∧ ∃ h : P.c = P'.c, ∀ i, P.m i = P'.m (Fin.cast h i)

def FinStrict : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ)
  (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))),
  Levels E Θ → KTypes E Ω → ∀ m₀ : (E →+* ℂ) → Multiset ℂ,
  ∃ (k : ℕ) (Pl : Fin k → Pre E a), ∀ P : Pre E a,
    (∀ j, ∃ K' ∈ Θ (P.N j), ∃ W' ∈ Ω (P.N j), HasType K' W' (P.V j)) → (∀ τ, ∑ j, P.m j τ = m₀ τ) →
      ∃ i, Strict P (Pl i)

def StrictEqv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P P' P'' : Pre E n),
  (Strict P P' → Strict P' P) ∧ (Strict P P' → Strict P' P'' → Strict P P'')

def StrictPre : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P P' : Pre E n),
  Strict P P' → PreEquiv P P'

def StrictProd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P P' : Pre E n),
  Strict P P' → ∀ w : Pl E, Nonempty ((prodAt P w).Equiv (prodAt P' w))

def StrictJoin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (χ₁ χ₂ : HChar E)
  (Pa Pa' : Pre E a) (Pb Pb' : Pre E b) (D D' : Pre E n), IsJoin χ₁ χ₂ Pa Pb D → IsJoin χ₁ χ₂ Pa' Pb' D' →
    Strict Pa Pa' → Strict Pb Pb' → Strict D D'

def CandParts : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
  (π : Submodule ℂ (UA E n → ℂ)) (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (d : LocData E n) i s₁ s₂ Pa Pb D,
  F₀.Cand d i s₁ s₂ Pa Pb D →
    (∀ j, ∃ K' ∈ rlΘ₁ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (lev₁ F₀.Sec d (F₀.C.a i)) (lev₂ F₀.Sec d (F₀.C.a i)) (Pa.N j),
      ∃ W' ∈ rlΩ₁ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (Pa.N j), HasType K' W' (Pa.V j)) ∧
    (∀ j, ∃ K' ∈ rlΘ₂ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (lev₁ F₀.Sec d (F₀.C.a i)) (lev₂ F₀.Sec d (F₀.C.a i)) (Pb.N j),
      ∃ W' ∈ rlΩ₂ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (Pb.N j), HasType K' W' (Pb.V j))

def LevOpen : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
  (π : Submodule ℂ (UA E n → ℂ)) (S : Finset (Pl E)) (F₀ : Frame0 hR π S) (T' : Finset (Pl E)) c e b (a : ℕ), a ≤ n →
  IsOpen (lev₁ F₀.Sec (F₀.loc T' c e b) a : Set (GL (Fin a) (Af E))) ∧
    IsOpen (lev₂ F₀.Sec (F₀.loc T' c e b) a : Set (GL (Fin (n - a)) (Af E)))

def IsoInv : Prop := ∀ (G V V' : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V'), Nonempty (ρ.Equiv ρ') → ∀ K : Subgroup G,
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ G W),
      GlobalTheory.SmGL.IsSubquotient τ ρ ↔ GlobalTheory.SmGL.IsSubquotient τ ρ') ∧
    Module.finrank ℂ (fixed ρ K) = Module.finrank ℂ (fixed ρ' K) ∧
    (FiniteDimensional ℂ (fixed ρ K) ↔ FiniteDimensional ℂ (fixed ρ' K))

def AdmProd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Pre E n) (w : Pl E)
  (K : Subgroup (GLw n w)), IsOpen (K : Set (GLw n w)) → K ≤ GlobalTheory.LFun.KGL w n → FiniteDimensional ℂ (fixed (prodAt P w) K)

def CandFinOf : Prop :=
  JEigFin → FinStrict → StrictEqv → StrictPre → StrictProd → StrictJoin → CandParts → LevOpen → IsoInv → AdmProd → FX.CandFin

end PositivityTheory.Rg.BcB.F.FX.Bo

end
