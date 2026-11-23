import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ExistsEigv

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def idem {a b : ℕ} {w : Pl E} (L : Subgroup (GLw a w × GLw b w)) : LF a b w :=
  (L : Set (GLw a w × GLw b w)).indicator fun _ => ((L.relIndex (K2 a b w) : ℕ) : ℂ)

structure LocData (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) where

  T : Finset (Pl E)

  S₀ : Finset (Pl E)
  Bad : Finset (Pl E)
  μ : ∀ w : Pl E, (w.adicCompletion E)ˣ →* ℂˣ
  ϖ : ∀ w : Pl E, (w.adicCompletion E)ˣ

  c : Pl E → (Fin n → ℤ) →₀ ℂ

  K' : ∀ w : Pl E, Subgroup (GLw n w)
  X : ∀ w : Pl E, Finset (GLw n w)
  e : ∀ w : Pl E, GLw n w → ℂ

  L : ∀ (a : ℕ) (w : Pl E), Subgroup (GLw a w × GLw (n - a) w)
  fix : ∀ (a : ℕ) (w : Pl E), LF a (n - a) w

  b : ∀ w : Pl E, GLw n w
  KB : ∀ w : Pl E, Subgroup (UL n w)

namespace LocData

variable {n : ℕ} (d : LocData E n)

def P : Finset (Pl E) := d.T ∪ d.S₀

def idx (w : Pl E) : Finset (Finset (Fin (n / 2)) × GLw n w) :=
  if w ∈ d.T then Finset.univ ×ˢ {1} else if w ∈ d.S₀ then {∅} ×ˢ d.X w else {(∅, 1)}

abbrev kap (w : Pl E) : Type := d.idx w

def lev (a : ℕ) (w : Pl E) : Subgroup (GLw a w × GLw (n - a) w) :=
  if w ∈ d.T then I2 a (n - a) w else if w ∈ d.S₀ ∪ d.Bad then d.L a w else K2 a (n - a) w

def lev₂ (a : ℕ) (w : Pl E) : Subgroup (GLw a w × GLw (n - a) w) := if w ∈ d.S₀ ∪ d.Bad then d.L a w else K2 a (n - a) w

def sgn (a : ℕ) (w : Pl E) : ℂ := (d.μ w ((-1) ^ (a * (n - a))) : ℂˣ)

def admitted (n a : ℕ) (s : Finset (Fin (n / 2))) : Prop :=
  (s.card = a / 2 ∧ sᶜ.card = (n - a) / 2 ∧ a % 2 + (n - a) % 2 = n % 2) ∧ (symIdx n (a % 2 = 1) s).card = a ∧
    (symIdx n ((n - a) % 2 = 1) sᶜ).card = n - a

def qT (a : ℕ) (w : Pl E) (s : Finset (Fin (n / 2))) : LF a (n - a) w := fun y =>
  if h : admitted n a s then (d.c w).sum fun x t => t * (-qh w) ^ (-vRes n a (lOf x) s) *
    (((I2 a (n - a) w).relIndex (K2 a (n - a) w) : ℕ) : ℂ) * dc2 w (d.ϖ w) (restr x _ h.2.1) (restr x _ h.2.2) y else 0

def mac (a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ) (x y : GLw n w) : LF a (n - a) w := fun m =>
  (d.sgn a w * ((d.X w).card : ℂ))⁻¹ * phiMu (Nat.add_sub_of_le ha) w (d.μ w) f x y m

def diag {a : ℕ} {w : Pl E} (f : d.kap w → LF a (n - a) w) (x y : d.kap w) : LF a (n - a) w := if x = y then f x else 0

def eL (a : ℕ) : LM d.kap a (n - a) :=
  ⟨fun w => d.diag fun _ => idem (d.lev a w), fun w => idem (d.lev a w), fun w => idem (d.lev₂ a w)⟩

def betaL (a : ℕ) (ha : a ≤ n) : LM d.kap a (n - a) :=
  ⟨fun w x y => if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else d.mac a ha w (d.e w) x.1.2 y.1.2,
    (d.eL a).s, (d.eL a).t⟩

def hc (a : ℕ) (ha : a ≤ n) (w : Pl E) (k : ℕ) : LF a (n - a) w :=
  (d.sgn a w)⁻¹ • RS.ctT (Nat.add_sub_of_le ha) w (d.μ w) (d.ϖ w : w.adicCompletion E) k

def hL (a : ℕ) (ha : a ≤ n) (w : Pl E) (k : ℕ) (intersection_update_fsHerm_neg_one : Bool) : LM d.kap a (n - a) :=
  ⟨(d.eL a).m, if intersection_update_fsHerm_neg_one then (d.eL a).s else Function.update (d.eL a).s w (d.hc a ha w k),
    if intersection_update_fsHerm_neg_one then Function.update (d.eL a).t w (d.hc a ha w k) else (d.eL a).t⟩

def fixL (a : ℕ) : LM d.kap a (n - a) :=
  ⟨fun w => d.diag fun _ => if w ∈ d.T then idem (d.lev a w) else d.sgn a w • idem (d.lev a w),
    fun w => if w ∈ d.Bad then d.fix a w else idem (d.lev a w), (d.eL a).t⟩

def one (w : Pl E) (x y : d.kap w) : ℂ := if x = y then 1 else 0

def B : Finset (Pl E) := d.T ∪ d.S₀ ∪ d.Bad

def KU (w : Pl E) : Subgroup (UL n w) :=
  if w ∈ d.T then iwU n w (d.b w) else if w ∈ d.S₀ then (d.K' w).subgroupOf (UL n w) else if w ∈ d.Bad then d.KB w else KL n w

def g₀ (w : Pl E) : UL n w → ℂ :=
  if w ∈ d.T then fun y => (d.c w).sum fun x t =>
    t * (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) * fU n w (d.b w) (d.ϖ w) (lOf x) y
  else if w ∈ d.S₀ then fun y => d.e w y.1 else U.lone (d.KU w)

def gU (m : ℕ) (w : Pl E) : UL n w → ℂ := U.lpow (d.KU w) (d.g₀ w) m

def hU (w : Pl E) (k : ℕ) : UL n w → ℂ := fun u => Tj ℂ n (Ov E w) (d.ϖ w : w.adicCompletion E) k u.1

structure Ok : Prop where
  disj : Disjoint d.T d.S₀ ∧ Disjoint d.T d.Bad ∧ Disjoint d.S₀ d.Bad
  unif : ∀ w, ordL (d.ϖ w : w.adicCompletion E) = 1
  cone : ∀ w ∈ d.T, (↑(d.c w).support : Set (Fin n → ℤ)) ⊆ coneGL n 2
  K' : ∀ w ∈ d.S₀, IsOpen (d.K' w : Set (GLw n w)) ∧ d.K' w ≤ GlobalTheory.LFun.KGL w n ∧
    (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ d.K' w, k * k' * k⁻¹ ∈ d.K' w) ∧ (∀ x ∈ d.X w, x ∈ GlobalTheory.LFun.KGL w n) ∧
    (∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ d.X w, x⁻¹ * k ∈ d.K' w) ∧ IsHk (d.K' w) (d.e w)
  L : ∀ a ≤ n, ∀ w ∈ d.S₀ ∪ d.Bad, ∃ L₁ L₂, d.L a w = Subgroup.prod L₁ L₂ ∧ IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) L₁ ∧
    IsLevel (thL (n - a) w) (GlobalTheory.LFun.KGL w (n - a)) L₂
  LS : ∀ a (ha : a ≤ n), ∀ w ∈ d.S₀, ∀ m ∈ d.L a w, m ∈ leviOf (Nat.add_sub_of_le ha) w (d.K' w) ∧
    d.μ w (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1
  fix : ∀ a ≤ n, ∀ w ∈ d.Bad, IsHecke (d.L a w) (d.fix a w)

def Good (w : Pl E) : Prop :=
  IsSplitAt w ∧ w ∉ d.T ∧ w ∉ d.S₀ ∧ w ∉ d.Bad ∧ ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → d.μ w u = 1

def IsGen (a : ℕ) (ha : a ≤ n) (L : LM d.kap a (n - a)) : Prop := L = d.eL a ∨ ∃ w k intersection_update_fsHerm_neg_one, d.Good w ∧ L = d.hL a ha w k intersection_update_fsHerm_neg_one

end LocData

def LM.Eqv {κ : Pl E → Type} {a b : ℕ} (P : Finset (Pl E)) (L L' : LM κ a b) : Prop :=
  (∀ w ∈ P, L.m w = L'.m w) ∧ (∀ w ∉ P, L.s w = L'.s w) ∧ L.t = L'.t

def LocOk : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → ∀ a (ha : a ≤ n),
  (∀ w, Nonempty (d.kap w)) ∧ (d.betaL a ha).Ok d.P ∧ (d.fixL a).Ok d.P ∧ ∀ L, d.IsGen a ha L → L.Ok d.P

def LocComm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → ∀ a (ha : a ≤ n),
  ∀ L L', d.IsGen a ha L → d.IsGen a ha L' →
    (L.mul L').Eqv d.P (L'.mul L) ∧ (L.mul L'.adj).Eqv d.P (L'.adj.mul L) ∧
      ((d.betaL a ha).mul L).Eqv d.P (L.mul (d.betaL a ha)) ∧ ((d.betaL a ha).mul L.adj).Eqv d.P (L.adj.mul (d.betaL a ha))

def SphComm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (f f' : LF a b w),
  IsHecke (K2 a b w) f → IsHecke (K2 a b w) f' → mconv f f' = mconv f' f

def IdemAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
  (L : Subgroup (GLw a w × GLw b w)), IsOpen (L : Set (GLw a w × GLw b w)) → L ≤ K2 a b w →
  IsHecke L (idem L) ∧ lfStar (idem L) = idem L ∧ ∀ f : LF a b w, IsHecke L f →
    mconv (idem L) f = f ∧ mconv f (idem L) = f ∧ IsHecke L (lfStar f)

end PositivityTheory.Rg.BcB.F

end
