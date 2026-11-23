import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBDefs

noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Classical ValuativeRel

section Cut

variable {D : Formalism.BasicNotions.D7}

def LocOrbSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (p : PlF D) (τ : Option ((M p).Cls D.R.rS)),
    HasSum (fL M δ (D.mem u).A.T (D.mem u').A.T p w τ) (BBtop M δ (D.mem u).A.T (D.mem u').A.T p w τ) ∧
    Summable (fun O => ‖fL M δ (D.mem u).A.T (D.mem u').A.T p w τ O‖) ∧
    (τ ≠ none → HasSum (gL M δ (D.mem u).A.T (D.mem u').A.T p w τ)
      (BBtop M δ (D.mem u).A.T (D.mem u').A.T p w τ / Pf.autP M p τ) ∧
    Summable (fun O => ‖gL M δ (D.mem u).A.T (D.mem u').A.T p w τ O‖))

def LocUnram (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (θ0 : ∀ p, Option ((M p).Cls D.R.rS)) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∃ S : Finset (PlF D), ∀ p ∉ S, Pf.autP M p (θ0 p) = 1 ∧
    ∀ (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)),
      fL M δ (D.mem u).A.T (D.mem u').A.T p w τ O =
          (if O = x0L M δ (D.mem u).A.T (D.mem u').A.T p w ∧ τ = θ0 p then 1 else 0) ∧
      gL M δ (D.mem u).A.T (D.mem u').A.T p w τ O =
          (if O = x0L M δ (D.mem u).A.T (D.mem u').A.T p w ∧ τ = θ0 p then 1 else 0)

def ThRestricted (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (θ0 : ∀ p, Option ((M p).Cls D.R.rS)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → Pf.Restricted θ0 (thT M δ γ)

def ThSome (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → ∀ p, thT M δ γ p ≠ none

def ScalKind (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ γ' : TermDef.Term D u u' F0 what₂) (w w' : Point D.host.E (D.R.rS + 1)), EligAt γ w → EligAt γ' w' →
    Corank.TermScal D γ γ' → kind w = kind w'

def EligFinite (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), {γ : TermDef.Term D u u' F0 what₂ | EligAt γ w}.Finite

def AtPtG (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), γ.atPt w →
    Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0

def PartnerTupleSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
    (∀ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' → EligAt γ' w' →
      {p | locT M δ γ' p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w'}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w'),
      HasSum (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
          (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = x.1} =>
          PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ'.1 w')
        (∏ᶠ p, fL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p))

def FiberTupleSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (L : CntLocal.LocSp D M) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc →
  ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (γ₀ : TermDef.Term D u u' F0 what₂) (w₀ : Point D.host.E (D.R.rS + 1)), EligAt γ₀ w₀ → kind w = kind w₀ →
    (∀ γ : TermDef.Term D u u' F0 what₂, EligAt γ w →
      {p | locT M δ γ p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w),
      HasSum (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
          (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} =>
          (PairVal.massTerm γ.1 : ℂ) * PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ.1 w)
        ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
          ∏ᶠ p, gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p))

def CoefProd (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ w =
      (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (locT M δ γ p)) *
        ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ)

def PartnerCount (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
    (∀ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' → EligAt γ' w' →
      {p | locT M δ γ' p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w'}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w'),
      HasSum (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
          (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = x.1} =>
          ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ))
        (∏ᶠ p, kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p))

def FiberCount (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (L : CntLocal.LocSp D M) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc →
  ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ (γ₀ : TermDef.Term D u u' F0 what₂) (w₀ : Point D.host.E (D.R.rS + 1)), EligAt γ₀ w₀ → kind w = kind w₀ →
    (∀ γ : TermDef.Term D u u' F0 what₂, EligAt γ w →
      {p | locT M δ γ p ≠ x0L M δ (D.mem u).A.T (D.mem u').A.T p w}.Finite) ∧
    ∀ x : Rst (fun p => x0L M δ (D.mem u).A.T (D.mem u').A.T p w),
      HasSum (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
          (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} =>
          (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ))
        ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
          ∏ᶠ p, eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p))

def DnInDens (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    ∃ Λ ∈ what₂, (CntLocal.EZ (CntLocal.Tn u') F0 Λ (zT γ)).Nonempty

def NormRepElig (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2

def CutAt (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (L : CntLocal.LocSp D M) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Prop :=
  LocOrbSum M δ u u' ∧ ScalKind u u' F0 what₂ ∧
    CoefProd M δ u u' F0 what₂ ∧ PartnerCount M δ u u' F0 what₂ ∧ FiberCount M δ L u u' F0 what₂ ∧
    NormRepElig u u' F0 what₂ ∧ ThSome M δ u u' F0 what₂ ∧
    ∃ θ0 : ∀ p, Option ((M p).Cls D.R.rS), LocUnram M δ u u' θ0 ∧ ThRestricted M δ u u' F0 what₂ θ0

end Cut

end Formalism.L2.SG.LsDatumB
