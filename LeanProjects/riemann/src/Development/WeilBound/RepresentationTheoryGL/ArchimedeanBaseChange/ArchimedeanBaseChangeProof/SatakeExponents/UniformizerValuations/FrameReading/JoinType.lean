import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEx
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExtremeSph

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b N : ℕ}

abbrev prodAt (P : Pre E n) (w : Pl E) := lp P w

abbrev pairAt (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) := GlobalTheory.SmGL.extTensor (prodAt Pa w) (prodAt Pb w)

structure Ctx (μ : HChar E) (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n) : Prop where
  g₁ : s₁.Good
  g₂ : s₂.Good
  u₁ : s₁.Untw
  u₂ : s₂.Untw
  t₁ : TreeParts s₁ Pa
  t₂ : TreeParts s₂ Pb
  join : IsJoin (μ ^ b) (μ ^ a) Pa Pb D

def JoinType : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (μ : HChar E)
  (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))), KTypes E Ω →
  ∃ W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ), (∀ N, FiniteDimensional ℂ (W N)) ∧
    ∀ (a b : ℕ), a + b = n → ∀ (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
      s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ Ω M, HasType K' W' V) →
      s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ Ω M, HasType K' W' V) → ∀ i, HasKType (W (D.N i)) (D.V i)

def ReadLev : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (μ : HChar E)
  (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
  ∀ (w : Pl E) (K : Subgroup (GLw n w)) (L : Subgroup (GLw a w × GLw b w)) (G : H E a b → ℂ),
  IsOpen (K : Set (GLw n w)) → IsCompact (K : Set (GLw n w)) → IsOpen (L : Set (GLw a w × GLw b w)) →
  (∀ m X, blk h w m X ∈ K → m ∈ L ∧ μ.loc w (GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) = 1) →
  G ∈ pairSpace s₁.space s₂.space → G ≠ 0 → G ∈ fixed (pairRt a b w) L → GlobalTheory.LGrp.IsSpherical (prodAt D w) K

def actP (w : Pl E) (u : GLw a w × GLw b w → ℂ) (G : H E a b → ℂ) : H E a b → ℂ :=
  fun z => hint (K2 a b w) fun m => u m * pairRt a b w m G z

def phiMu (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : GLw n w → ℂ) (x y : GLw n w)
    (m : GLw a w × GLw b w) : ℂ :=
  (μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) * phi3 h w f x y m

def matS (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : GLw n w → ℂ) (X : Finset (GLw n w))
    (G : X → H E a b → ℂ) : X → H E a b → ℂ := fun x => ∑ y : X, actP w (phiMu h w μ f x y) (G y)

def ReadS : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (μ : HChar E)
  (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
  ∀ (w : Pl E) (K' : Subgroup (GLw n w)) (X : Finset (GLw n w)) (L : Subgroup (GLw a w × GLw b w)) (e : GLw n w → ℂ)
    (P : SmIrr (GLw n w)) (m : ℕ) (G : X → H E a b → ℂ), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n →
    (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) →
    (∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K') → IsOpen (L : Set (GLw a w × GLw b w)) → IsHk K' e →
    (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) → IsEmpty (τ.ρ.Equiv P.ρ) →
      ∀ v ∈ fixed τ.ρ K', hk τ.ρ K' e v = 0) →
    Module.finrank ℂ (fixed (prodAt D w) K') < m →
    (∀ x, G x ∈ pairSpace s₁.space s₂.space ∧ G x ∈ fixed (pairRt a b w) L) → (matS h w (μ.loc w) e X)^[m] G ≠ 0 →
    GlobalTheory.SmGL.IsSubquotient P.ρ (prodAt D w)

def hkG {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) (v : V) : V :=
  ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v

def dl (w : Pl E) (x : Fin N → ℤ) : ℂ := qh w ^ (∑ i : Fin N, ((N : ℤ) - 1 - 2 * (i : ℕ)) * x i)

def Gap (x : Fin N → ℤ) : Prop := ∀ i j, i < j → x j + 1 ≤ x i

abbrev I2 (a b : ℕ) (w : Pl E) : Subgroup (GLw a w × GLw b w) := (iwGL a w).prod (iwGL b w)

def dc2 (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (x : Fin a → ℤ) (y : Fin b → ℤ) (m : GLw a w × GLw b w) : ℂ :=
  dcos a w (tdiag ϖ x) m.1 * dcos b w (tdiag ϖ y) m.2

def ev2 (w : Pl E) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) (x : Fin a → ℤ) (y : Fin b → ℤ) : ℂ :=
  dl w x * pw ξa x * (dl w y * pw ξb y)

def JEig (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) : Prop :=
  ∃ v ∈ fixed (pairAt Pa Pb w) (I2 a b w), v ≠ 0 ∧
    ∀ x y, Gap x → Gap y → hkG (pairAt Pa Pb w) (I2 a b w) (dc2 w ϖ x y) v = ev2 w ξa ξb x y • v

def ReadT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (μ : HChar E)
  (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
  ∀ (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (J : Type) [Fintype J] (c : J → ℂ) (x : J → Fin a → ℤ) (y : J → Fin b → ℤ) (m : ℕ)
    (G : H E a b → ℂ), ordL (ϖ : w.adicCompletion E) = 1 → (∀ j, Gap (x j) ∧ Gap (y j)) →
    Module.finrank ℂ (fixed (pairAt Pa Pb w) (I2 a b w)) ≤ m →
    G ∈ pairSpace s₁.space s₂.space → G ∈ fixed (pairRt a b w) (I2 a b w) →
    (actP w fun g => ∑ j, c j * dc2 w ϖ (x j) (y j) g)^[m] G ≠ 0 →
    ∃ ξa ξb, JEig Pa Pb w ϖ ξa ξb ∧ ∑ j, c j * ev2 w ξa ξb (x j) (y j) ≠ 0

def JEigFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Pa : Pre E a) (Pb : Pre E b) (w : Pl E)
  (ϖ : (w.adicCompletion E)ˣ), ordL (ϖ : w.adicCompletion E) = 1 →
  ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧ ∀ (Pa' : Pre E a) (Pb' : Pre E b), PreEquiv Pa Pa' → PreEquiv Pb Pb' →
    Module.finrank ℂ (fixed (pairAt Pa' Pb' w) (I2 a b w)) ≤ m ∧ ∀ ξa ξb, JEig Pa' Pb' w ϖ ξa ξb → (ξa, ξb) ∈ Z

def ExpRead : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Pa : Pre E a) (Pb : Pre E b) (w : Pl E)
  (ϖ : (w.adicCompletion E)ˣ) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ), ordL (ϖ : w.adicCompletion E) = 1 →
  N3.Mono ξa → N3.Mono ξb → JEig Pa Pb w ϖ ξa ξb →
    Pa.Sat w (Finset.univ.val.map ξa) ∧ Pb.Sat w (Finset.univ.val.map ξb)

def RReadLev : Prop := RS.ReadMod → JoinMod → ReadLev
def RReadS : Prop := RS.ReadMod → JoinMod → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], LocOpUniformizer E) → ReadS
def RReadT : Prop := RS.ReadMod → ReadT
def RExpRead : Prop := N3.N3 → ExpRead

theorem tout_of {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {K : ∀ w : Pl E, Subgroup (GLw n w)}
    {W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)} {D : Pre E n}
    (wt : ∀ τ lam, HasWeightAt π τ lam → ∑ i, D.m i τ = infOfWeight lam)
    (good : ∀ᶠ w : Pl E in cofinite, IsSplitAt w → D.SplitAt π w)
    (atS : ∀ w ∈ S, IsSplitAt w → ∃ P : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient P.ρ (prodAt D w) ∧
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ)
    (atT : ∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → InertAt π D w)
    (lev : ∀ w, GlobalTheory.LGrp.IsSpherical (prodAt D w) (K w)) (kt : ∀ i, HasKType (W (D.N i)) (D.V i)) : TOut π S T K W D :=
  ⟨⟨wt, Set.Finite.subset (eventually_cofinite.1 good) fun _ hw hx => hw.2 (hx hw.1)⟩, atS, atT, lev, kt⟩

end PositivityTheory.Rg.BcB.F.Tail

end
