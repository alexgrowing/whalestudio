import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GrowthWeightBounds.RFChoiceP

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

namespace RunFrame

variable {hR : Rd.ReadLimit} {π : CuspSub E n} {Z T₀ : Finset (Pl E)} {F₀ : Frame0 hR π} (F : RunFrame F₀ Z T₀)

abbrev κ : Type := ∀ w : F.d.P, F.d.kap w

abbrev B (i : F₀.C.ι) : Block E := (F₀.A i).blk F.κ

def ψ (i : F₀.C.ι) (L : LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) : Matrix F.κ F.κ (Hf E (F₀.C.a i) (n - F₀.C.a i) → ℂ) :=
  fm F₀.Sec F.d.P (F.B i) (Equiv.refl _) L

def ptL (i : F₀.C.ι) (L : LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) : PT (F.B i) :=
  (F₀.A i).pt (fun _ => []) (fun _ => []) (F.ψ i L) (sizeOf (F.ψ i L))

def t₀ (i : F₀.C.ι) : PT (F.B i) := F.ptL i (F.d.eL _)

def β (i : F₀.C.ι) : PT (F.B i) := F.ptL i (F.d.betaL _ (F₀.C.le i))

def t₁ (i : F₀.C.ι) : PT (F.B i) := F.ptL i (F.d.fixL _)

def t₂ (i : F₀.C.ι) : PT (F.B i) :=
  (F₀.A i).pt (fun _ => []) (fun _ => []) (rt (F₀.u₁ _) (F₀.u₂ _) (F.ψ i (F.d.eL _)))
    (sizeOf (rt (F₀.u₁ _) (F₀.u₂ _) (F.ψ i (F.d.eL _))))

abbrev Γ : Type := Unit ⊕ (F₀.C.ι × InfinitePlace E × Bool × ℕ × Bool) ⊕ ({w : Pl E // w ∈ F₀.Sec ∧ F.d.Good w} × ℕ × Bool)

def dval (_ : RunFrame F₀ Z T₀) (x : F₀.C.ι × InfinitePlace E × Bool × ℕ × Bool) : ℂ :=
  if x.2.2.2.2 then zVal [(x.2.2.1, x.2.2.2.1)] ((F₀.A x.1).χb x.2.1) else zVal [(x.2.2.1, x.2.2.2.1)] ((F₀.A x.1).χa x.2.1)

def tD (i : F₀.C.ι) (v : InfinitePlace E) (s : Bool) (m : ℕ) (side : Bool) : PT (F.B i) :=
  (F₀.A i).pt (fun v' => if v' = v ∧ side = false then [(s, m)] else []) (fun v' => if v' = v ∧ side = true then [(s, m)] else [])
    (F.ψ i (F.d.eL _)) (sizeOf (F.ψ i (F.d.eL _)))

def g : F.Γ → ∀ i, BGen (F.B i)
  | .inl _, i => .inr (F.t₀ i)
  | .inr (.inl x), i => if i = x.1 then .inr (F.tD i x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) else .inl (F.dval x)
  | .inr (.inr x), i => .inr (F.ptL i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2))

def ug : F.Γ → U.UGen E n
  | .inl _ => .inl 1
  | .inr (.inl x) => .inl (F.dval x)
  | .inr (.inr x) => .inr ⟨x.1.1, F.d.hU x.1.1 x.2.1⟩

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
instance instIPS_FB (i : F₀.C.ι) : InnerProductSpace ℂ (F.B i).Hb := inferInstance
instance instCS_FB (i : F₀.C.ι) : CompleteSpace (F.B i).Hb := inferInstance

structure Struct : Prop where
  ok : ∀ x i, (F.g x i).Ok
  βok : ∀ i, (F.β i).Ok
  tok : ∀ i, (F.t₁ i).Ok ∧ (F.t₂ i).Ok
  comm : ∀ x y i, Commute (F.g x i).op (F.g y i).op
  commStar : ∀ x y i, Commute (F.g x i).op (star (F.g y i).op)
  βcomm : ∀ i x, Commute (F.β i).op (F.g x i).op ∧ Commute (F.β i).op (star (F.g x i).op)

end RunFrame

section Frame

variable {hR : Rd.ReadLimit} {π : CuspSub E n} {Z T₀ : Finset (Pl E)} {F₀ : Frame0 hR π} (F : RunFrame F₀ Z T₀)

def gl (i : F₀.C.ι) (p : F.Γ × Bool) : BGen (F.B i) := if p.2 then (F.g p.1 i).adj else F.g p.1 i

def ul (p : F.Γ × Bool) : U.UGen E n := if p.2 then (F.ug p.1).adj else F.ug p.1

def bw (i : F₀.C.ι) (w : List (F.Γ × Bool)) : List (BGen (F.B i)) := List.replicate F.m (Sum.inr (F.β i)) ++ w.map (gl F i)

def MM (i : F₀.C.ι) : Matrix (F.B i).I (F.B i).I ℂ := opM (F₀.A i).Ta (F₀.A i).Tb (tenN F.d.P (F.B i) (Equiv.refl _) F.d.one)

def tw (i : F₀.C.ι) (ws : List (List (F.Γ × Bool))) : PT (F.B i) :=
  BGen.wd (Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten) (F.t₂ i)

def WordIdAt : Prop := ∃ (cc : F₀.C.ι → ℂ) (c₀ : F₀.C.ι → ℝ), (∀ i, 0 ≤ c₀ i) ∧ cc F₀.i₀ ≠ 0 ∧ ∀ ws : List (List (F.Γ × Bool)), ws ≠ [] →
  (∀ i, D4.IsTest2J (trM (tw F i ws).Φ (MM F i)) (c₀ i * (1 + (tw F i ws).T) + (tw F i ws).r)) ∧
  LinearMap.trace ℂ _ ((F.R.u ^ ws.length * ((ws.flatten.map (ul F)).map F.R.op).prod :
      EuclideanSpace ℂ (Fin F.R.d) →L[ℂ] EuclideanSpace ℂ (Fin F.R.d)) :
      EuclideanSpace ℂ (Fin F.R.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin F.R.d)) =
    ∑ i, cc i * (BGen.sc (ws.map (bw F i)).flatten *
      ellSum2 (F₀.C.μG (F₀.C.a i)) (F₀.C.μG (n - F₀.C.a i)) (trM (tw F i ws).Φ (MM F i)))

end Frame

end PositivityTheory.Rg.BcB.F.FrE

end
