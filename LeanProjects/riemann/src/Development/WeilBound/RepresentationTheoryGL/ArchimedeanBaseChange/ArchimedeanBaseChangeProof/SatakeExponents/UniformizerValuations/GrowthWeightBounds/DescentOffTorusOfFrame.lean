import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GrowthWeightBounds.InstIPSFB
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GrowthWeightBounds.TBound

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B

open PositivityTheory.Rg.BcB.Desc PositivityTheory.AutomorphicGaloisHodgeTate.D

namespace PositivityTheory.Rg.BcB.F.FrE

attribute [local instance] borelG borelF borelA borelH GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

section Frame

variable {hR : Rd.ReadLimit} {π : CuspSub E n} {Z T₀ : Finset (Pl E)} {F₀ : Frame0 hR π} (F : RunFrame F₀ Z T₀)

def pP : F.Γ → ℂ
  | .inl _ => 1
  | .inr (.inl x) => F.dval x
  | .inr (.inr x) => twTr (F₀.τ x.1.1).ρ (GlobalTheory.LFun.KGL x.1.1 n) (GlobalTheory.LFun.KGL x.1.1 n)
      (Tj ℂ n (Ov E x.1.1) (F.d.ϖ x.1.1 : x.1.1.adicCompletion E) x.2.1) LinearMap.id

def pL (p : F.Γ × Bool) : ℂ := if p.2 then starRingEnd ℂ (pP F p.1) else pP F p.1

abbrev JU : Type := {j : F.fam.ι // ∀ w ∈ F.d.B, locOp (F.fam.σ j w) (F.d.KU w) (F.d.gU F.m w) ≠ 0}

def VV (i : F₀.C.ι) : Submodule ℂ (F.B i).Hb :=
  if h : i = F₀.i₀ then (piG (F₀.A i).D ((h ▸ F₀.a₀ : F₀.C.a i = n).symm ▸ π) (F.B i).I)ᗮ else ⊤

def tup (x : F.Γ) : Tup (fun i => (F.B i).Hb) (JU F) := (fun i => (F.g x i).op, fun j => (F.ug x).p F.fam j.1, pP F x)

def XX (i : F₀.C.ι) : (F.B i).Hb →L[ℂ] (F.B i).Hb := (F.β i).op ^ F.m

def PiTermAt : Prop := (∀ i j, FinOnG (F₀.A F₀.i₀).D.μ F₀.π' ((F.t₁ F₀.i₀).Φ i j)) ∧ ∃ c : ℂ, c ≠ 0 ∧
  ∀ ws : List (List (F.Γ × Bool)), ws ≠ [] → ∃ t, TwTrG (F₀.A F₀.i₀).D.μ F₀.π' (trM (tw F F₀.i₀ ws).Φ (MM F F₀.i₀)) t ∧
    BGen.sc (ws.map (bw F F₀.i₀)).flatten * t = c * (ws.flatten.map (pL F)).prod

def Out : Prop := ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧
  (∀ φ : E →+* ℂ, ∃ lam, HasWeightAt σ φ lam ∧ π.HasInfChar φ (infOfWeight lam)) ∧
  (∀ w, IsSplitAt w → ∀ τ, π.IsLocComp w τ → Comp σ w τ) ∧ (∀ w, ¬ IsSplitAt w → w ∉ F.d.T → IsUnramU σ w) ∧
  ∀ w ∈ F.d.T, ∀ (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ), IsWitt n w b → IsUnifAt ϖ → ∃ β, IsExtOf2 π w β ∧ ExtExp σ w b ϖ β

end Frame

def Hyp (π : CuspSub E n) : Prop := (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.PolarizedPair π (GlobalTheory.GalOfCusp.quadChar E ^ n) ∧
  (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) ∧ InertBC π

def All (P : ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : CuspSub E n)
    (Z T₀ : Finset (Pl E)) (F₀ : Frame0 hR π), RunFrame F₀ Z T₀ → Prop) : Prop :=
  ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
    Hyp π → ∀ (Z T₀ : Finset (Pl E)) (F₀ : Frame0 hR π) (F : RunFrame F₀ Z T₀), P hR E n π Z T₀ F₀ F

def FrameEx0 : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : CuspSub E n, Hyp π → Nonempty (Frame0 hR π)

def FrameEx : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : CuspSub E n, Hyp π → ∀ (F₀ : Frame0 hR π) (Z T₀ : Finset (Pl E)), Disjoint T₀ Z → (∀ w ∈ T₀, ¬ IsSplitAt w) →
    Nonempty (RunFrame F₀ Z T₀)

def FrameOk : Prop := All fun _ _ _ _ _ _ _ _ _ _ F => F.Struct

def Identity : Prop := All fun _ _ _ _ _ _ _ _ _ _ F => F.Struct → WordIdAt F

def PiTerm : Prop := All fun _ _ _ _ _ _ _ _ _ _ F => F.Struct → PiTermAt F

def ClassProj : Prop := All fun _ _ _ _ _ _ _ _ _ F₀ F => ∀ i : F₀.C.ι, IsClosed (VV F i : Set (F.B i).Hb) ∧
  ∀ t : PT (F.B i), t.Ok → (∀ v ∈ VV F i, t.op v ∈ VV F i) ∧ ∀ v ∈ (VV F i)ᗮ, t.op v ∈ (VV F i)ᗮ

def Bound : Prop := All fun _ _ _ _ _ _ _ _ _ _ F => F.Struct → TBound (tup F) (VV F) (XX F)

def BoundOf : Prop := Identity → PiTerm → ClassProj → Bound

def ReadMid : Prop := All fun _ E _ _ _ n π _ _ F₀ F => F.Struct → ∀ i, i ≠ F₀.i₀ → TChar (tup F) (VV F) (XX F) i →
  ∃ D : Pre E n, DOut F₀ F.d D ∧ ¬ IsOne D π

def ReadCompl : Prop := All fun _ E _ _ _ n π _ _ F₀ F => F.Struct → TChar (tup F) (VV F) (XX F) F₀.i₀ →
  ∃ D : Pre E n, DOut F₀ F.d D ∧ ¬ IsOne D π

def URead : Prop := All fun _ _ _ _ _ _ _ _ _ _ F => ∀ j : JU F, (∀ x, (F.ug x).p F.fam j.1 = pP F x) → Out F

end PositivityTheory.Rg.BcB.F.FrE

end
