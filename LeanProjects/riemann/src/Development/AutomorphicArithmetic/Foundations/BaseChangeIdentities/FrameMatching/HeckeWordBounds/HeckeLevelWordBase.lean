import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.WordIdAt
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.ChainSc

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def heckeLevelWordBase : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → ∀ a (ha : a ≤ n) (p : LL d),
  (locL d a ha p).Ok d.P ∧ ((d.eL a).mul (locL d a ha p)).Eqv d.P (locL d a ha p) ∧ d.IsLetter a ha (locL d a ha p)

def ProdOk : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → ∀ (ls : List (LL d)), ∀ a ≤ n, (prodL d ls a).Ok d.P

def MatchOn : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ) (d : LocData E n), d.Ok → MLM.MOk d →
  (∀ w, IsLevel (MonoidHom.id _) (KL n w) (d.KU w)) → ∀ (ls : List (LL d)) (m k : ℕ), 1 ≤ m → 1 ≤ k →
  ls.countP Sum.isLeft = m * k → ∀ a ≤ n, ∀ w ∈ d.B,
    Match n a (n - a) w (d.μ w) (U.lpow (d.KU w) (d.gU m w) k) (seen ((prodL d ls a).tr d.P d.one) (prodL d ls a).t w)

def MatchOff : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ) (d : LocData E n), d.Ok →
  (∀ w u, ‖((d.μ w u : ℂˣ) : ℂ)‖ = 1) → ∀ (ls : List (LL d)) (N : ℕ), ls.countP Sum.isLeft = N + 1 →
    ∀ a ≤ n, ∀ w ∉ d.B, (IsSplitAt w → d.Good w) →
    Match n a (n - a) w (d.μ w) (MLM.wordUS d w (atPlace d w ls)) (seen ((prodL d ls a).tr d.P d.one) (prodL d ls a).t w)

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
  {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T)

def lt (p : F.Γ × Bool) : LL F.d :=
  match p.1 with
  | .inr (.inr x) => .inr (.inr (⟨x.1.1, x.1.2.2⟩, x.2.1, x.2.2, p.2))
  | _ => .inr (.inl ())

def lw (ws : List (List (F.Γ × Bool))) : List (LL F.d) :=
  (ws.map fun w => List.replicate F.m (Sum.inl ()) ++ w.map (lt F)).flatten

end Frame

def FrFacts : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T),
  (∀ w, F.d.μ w = F₀.μ.loc w) ∧ (∀ w u, ‖((F.d.μ w u : ℂˣ) : ℂ)‖ = 1) ∧
    (∀ w ∈ F₀.Sec, w ∉ F.d.B → IsSplitAt w → F.d.Good w) ∧ (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec

def PsiLet : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T) (i : F₀.C.ι) (p : F.Γ × Bool),
  (∃ c, gl F i p = Sum.inl c ∧ locL F.d (F₀.C.a i) (F₀.C.le i) (lt F p) = F.d.eL (F₀.C.a i)) ∨
    ∃ s, gl F i p = Sum.inr s ∧ s.ψ = F.ψ i (locL F.d (F₀.C.a i) (F₀.C.le i) (lt F p))

def PsiWord : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T) (i : F₀.C.ι) (ws : List (List (F.Γ × Bool))),
  (tw F i ws).ψ = rt (F₀.u₁ _) (F₀.u₂ _) (F.ψ i (prodL F.d (lw F ws) (F₀.C.a i)))

def USph : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T) (ws : List (List (F.Γ × Bool))),
  (lw F ws).countP Sum.isLeft = F.m * ws.length ∧
    ∀ w, U.UGen.sph (ws.flatten.map (ul F)) w = MLM.wordUS F.d w (atPlace F.d w (lw F ws))

def UOk : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T), GlobalTheory.BCT.Unr E → ∀ p : F.Γ × Bool, (ul F p).Ok F₀.Sec F.d.B ∧
  F.R.op (ul F p) = if p.2 then star (F.R.op (F.ug p.1)) else F.R.op (F.ug p.1)

def TwOk : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T), F.Struct → ∀ i : F₀.C.ι,
  (∀ p, (gl F i p).Ok ∧ (gl F i p).op = if p.2 then star (F.g p.1 i).op else (F.g p.1 i).op) ∧
    (∀ w, ∀ g ∈ bw F i w, g.Ok) ∧ ∀ ws, (tw F i ws).Ok

def ArchLet : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T), F.Struct → ∀ i : F₀.C.ι,
  (∀ p, Sum.elim id (fun s : PT (F.B i) => s.val (F₀.A i).χa (F₀.A i).χb) (gl F i p) = Sum.elim id (fun _ => 1) (ul F p)) ∧
    (F.β i).val (F₀.A i).χa (F₀.A i).χb = 1 ∧ (F.t₁ i).val (F₀.A i).χa (F₀.A i).χb = 1 ∧
    (F.t₂ i).val (F₀.A i).χa (F₀.A i).χb = 1

def ArchSc : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T), F.Struct → ∀ (i : F₀.C.ι) (ws : List (List (F.Γ × Bool))),
  BGen.sc (ws.map (bw F i)).flatten * (tw F i ws).val (F₀.A i).χa (F₀.A i).χb = U.UGen.sc (ws.flatten.map (ul F))

def AdelWord : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T), F.Struct → ∀ (i : F₀.C.ι) (ws : List (List (F.Γ × Bool))),
  trM (tw F i ws).Φ (MM F i) = (F.B i).vol⁻¹ • adel F₀.Sec (F₀.u₁ (F₀.C.a i)) (F₀.u₂ (F₀.C.a i))
      ((tw F i ws).arch (F₀.A i).Ta (F₀.A i).Tb) ((prodL F.d (lw F ws) (F₀.C.a i)).tr F.d.P F.d.one)
      (prodL F.d (lw F ws) (F₀.C.a i)).t ∧ (F.B i).vol ≠ 0 ∧
    ∀ v, LefAt (F₀.C.νC (F₀.C.a i)) (F₀.C.νC (n - F₀.C.a i)) (F₀.C.l₁ i v) (F₀.C.l₂ i v)
      ((tw F i ws).va v ((F₀.A i).χa v) * (tw F i ws).vb v ((F₀.A i).χb v)) ((tw F i ws).arch (F₀.A i).Ta (F₀.A i).Tb v)

def TestWord : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T), GlobalTheory.BCT.Unr E → F.Struct → ∀ i : F₀.C.ι, ∃ c₀ : ℝ, 0 ≤ c₀ ∧
  ∀ ws : List (List (F.Γ × Bool)), ws ≠ [] →
    D4.IsTest2J (trM (tw F i ws).Φ (MM F i)) (c₀ * (1 + (tw F i ws).T) + (tw F i ws).r)

def TraceWord : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T), GlobalTheory.BCT.Unr E → F.Struct → ∀ ws : List (List (F.Γ × Bool)), ws ≠ [] →
  LinearMap.trace ℂ _ ((F.R.u ^ ws.length * ((ws.flatten.map (ul F)).map F.R.op).prod :
      EuclideanSpace ℂ (Fin F.R.d) →L[ℂ] EuclideanSpace ℂ (Fin F.R.d)) :
      EuclideanSpace ℂ (Fin F.R.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin F.R.d)) =
    ∑ i, (F₀.C.c i * (F.B i).vol) * (BGen.sc (ws.map (bw F i)).flatten *
      ellSum2 (F₀.C.μG (F₀.C.a i)) (F₀.C.μG (n - F₀.C.a i)) (trM (tw F i ws).Φ (MM F i)))

end UpperTheory.BaseChangeIdentities.FrameWordIdentity

end
