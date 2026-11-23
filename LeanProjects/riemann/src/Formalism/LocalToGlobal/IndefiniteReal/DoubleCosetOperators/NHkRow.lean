import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.HkCore
import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie

noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

namespace Formalism.IndefR.NX

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure NExpHeckeRow (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw)
    (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y) : Prop where
  tie : ∀ (i : Fin D.R.m) (k : ℕ) (P : PlE D.host), Formalism.BasicNotions.IsSplitPl D.host P →
    Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → (∃ i', P ∉ D.ntw.S0 i') → ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → k ≤ D.R.r →
    ∀ (α : GA D (Wc D i)) (R : Finset (GA D (Wc D i))), IsHeckeAt (Wc D i) P k α →
      Bridge.IsDC (levG (Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α R →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ x : S.WL ((i : ℕ) + 1),
        (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (H.hL ((i : ℕ) + 1) k P x))) =
          c • heckeOn (Rl.MW i (sg0 D A3.A)) R ((Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e x)))

def goodProjW {tw : NTw D.R D.host D.what₂ D.LL0 D.nd} (S : RatDat tw) (j : ℕ) (eC : G0g D.nd → ↥D.LL0) :
    Module.End D.what₂.LL (S.WL j) :=
  ∑ᶠ g : G0g D.nd, (((eC g : ↥D.LL0) : D.what₂.LL) *
    ((((S.A j).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹) • (S.A j).ρ (S.eG.symm g)

structure NExpHeckeRowX (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw)
    (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y) (eW : ∀ j, Module.End D.what₂.LL (S.WL j)) : Prop where
  tie : ∀ (i : Fin D.R.m) (k : ℕ) (P : PlE D.host), Formalism.BasicNotions.IsSplitPl D.host P →
    Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → (∃ i', P ∉ D.ntw.S0 i') → ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → k ≤ D.R.r →
    ∀ (α : GA D (Wc D i)) (R : Finset (GA D (Wc D i))), IsHeckeAt (Wc D i) P k α →
      Bridge.IsDC (levG (Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α R → ∀ x : S.WL ((i : ℕ) + 1),
        eW ((i : ℕ) + 1) x = x →
        (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (H.hL ((i : ℕ) + 1) k P x))) =
          ((((Rl.C.mu0 i).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
            heckeOn (Rl.MW i (sg0 D A3.A)) R ((Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e x)))

def HeckePreservesGoodPart (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw)
    (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y) : Prop :=
  (∀ i j b k P (x : D.nexp.Fm i j b), 1 ≤ j → j ≤ D.R.m → P ∉ D.ntw.S0 i → (∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∉ D.ntw.S0 i) →
    Formalism.BasicNotions.IsSplitPl D.host P → 1 ≤ k → k ≤ D.R.r →
    x ∈ D.nexp.Bsup i j b ⊓ (Formalism.MainNotions.IntegralHeckeForms.Fm0 D.nexp i j b ⊓ Formalism.MainNotions.IntegralHeckeForms.V0 D.nexp i j b).restrictScalars (D.ntw.O i) →
      D.nexp.hkF i j b k P x ∈
        D.nexp.Bsup i j b ⊓ (Formalism.MainNotions.IntegralHeckeForms.Fm0 D.nexp i j b ⊓ Formalism.MainNotions.IntegralHeckeForms.V0 D.nexp i j b).restrictScalars (D.ntw.O i)) ∧
  ∀ i b P, ∃ u : (D.ntw.O i)ˣ, H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u

def HeckeRationalOverBase (C : Core.RatCore) {Pl : Type} (σ0 : C.L0 →+* ℂ)
    (hC : ∀ j, ℕ → Pl → Module.End ℂ (C.W j σ0)) (Js : Set ℕ) (Ix : ℕ → Pl → Prop) : Prop :=
  ∃ hL : ∀ j, ℕ → Pl → Module.End C.L0 (C.WL j),
    ∀ j ∈ Js, ∀ k P, Ix k P →
      (∀ x : C.WL j, x ∈ (C.A j).WK → hL j k P x ∈ (C.A j).WK) ∧
        ∀ x : C.WL j, (C.A j).j σ0 (hL j k P x) = hC j k P ((C.A j).j σ0 x)

end Formalism.IndefR.NX
