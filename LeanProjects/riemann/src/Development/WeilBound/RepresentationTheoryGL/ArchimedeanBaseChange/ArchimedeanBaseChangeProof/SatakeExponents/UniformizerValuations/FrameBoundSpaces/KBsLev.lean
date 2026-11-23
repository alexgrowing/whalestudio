import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdjKer0
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.DataExOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadLimit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM

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

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section RL
variable (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E]

def rlW₁ := (hR E).choose
def rlW₂ := (hR E).choose_spec.choose
def rlΩ₁ := (hR E).choose_spec.choose_spec.choose
def rlΩ₂ := (hR E).choose_spec.choose_spec.choose_spec.choose
def rlΘ₁ := (hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose
def rlΘ₂ := (hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
end RL

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure Frame0 (hR : Rd.ReadLimit) (π : Submodule ℂ (UA E n → ℂ)) (S : Finset (Pl E)) : Type 1 where
  lam : InfinitePlace E → DomWeight n
  hlam : ∀ v, HasWeightAt π v.embedding (lam v)
  μ : HChar E
  e : InfinitePlace E → ℤ
  hμ : IsMu μ e
  Sec : Set (Pl E)
  hSec : IsSection Sec
  d₀ : LocData E n
  ok₀ : d₀.Ok
  T₀ : d₀.T = ∅
  μloc : ∀ w, d₀.μ w = μ.loc w
  unif : ∀ w, IsUnifAt (d₀.ϖ w) ∧ IsUnifV E w (d₀.ϖ w : w.adicCompletion E)
  S₀ : ∀ w ∈ d₀.S₀, w ∈ Sec ∧ IsSplitAt w
  S_le : ∀ w ∈ S, IsSplitAt w → w ∈ d₀.S₀
  bad : ∀ w ∈ d₀.Bad, w ∈ Sec ∧ (¬ IsSplitAt w → ¬ IsUnramU π w)
  good : ∀ w ∈ Sec, w ∉ d₀.S₀ → w ∉ d₀.Bad → IsUnramU π w ∧ μ.UnrAt w
  kB : Pl E → ℕ
  kB_pos : ∀ w ∈ d₀.Bad, ¬ IsSplitAt w → 1 ≤ kB w
  KBs : ∀ w : Pl E, Subgroup (UL n w)
  KBs_lev : ∀ w ∈ d₀.Bad, IsSplitAt w → IsLevel (MonoidHom.id _) (KL n w) (KBs w)
  KB_def : ∀ w, d₀.KB w = if w ∈ d₀.Bad then (if IsSplitAt w then KBs w else
    Subgroup.closure {γ | γ.1 ∈ MB.congK n w (kB w)}) else KL n w
  fix_def : ∀ a (ha : a ≤ n), ∀ w, d₀.fix a w = if w ∈ d₀.Bad then (if IsSplitAt w then
    ctMu (Nat.add_sub_cancel' ha) w (d₀.μ w) (U.lone (d₀.KB w)) else
    fun y => (((d₀.KB w).relIndex (KL n w) : ℕ) : ℂ) * MB.pairIndicatorMatch n a (n - a) w (kB w) y) else 0
  K'_lev : ∀ w ∈ d₀.S₀, IsLevel (MonoidHom.id _) (KL n w) ((d₀.K' w).subgroupOf (UL n w))
  levFam : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) d₀.KU
  level : ∀ K' : ∀ w : Pl E, Subgroup (UL n w), (∀ w, K' w ≤ d₀.KU w) → HasLevel Sec π K'
  fix : ∀ a ≤ n, ∀ w ∈ d₀.Bad, Match n a (n - a) w (μ.loc w) (U.lone (d₀.KB w)) (d₀.fix a w)
  u₁ : ∀ a, GL (Fin a) E
  u₂ : ∀ a, GL (Fin (n - a)) E
  hu : ∀ a, IsTransl (u₁ a) ∧ IsTransl (u₂ a)
  C : Chain μ e lam
  A : ∀ i : C.ι, Arch E (C.a i) (n - C.a i) (C.l₁ i) (C.l₂ i) (C.μG (C.a i)) (C.μG (n - C.a i)) (C.νC (C.a i)) (C.νC (n - C.a i))
  K : ∀ w : Pl E, Subgroup (GLw n w)
  hK : F5.IsLevel K
  Kc : ∀ w, IsCompact (K w : Set (GLw n w))
  K_good : ∀ w : Pl E, (∀ u ∈ d₀.S₀ ∪ d₀.Bad, u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) →
    K w = GlobalTheory.LFun.KGL w n
  K_bad : ∀ a (ha : a ≤ n), ∀ w ∈ d₀.S₀ ∪ d₀.Bad, ∀ m X, blk (Nat.add_sub_of_le ha) w m X ∈ K w →
    m ∈ d₀.L a w ∧ μ.loc w (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1
  K_conj : ∀ a (ha : a ≤ n), ∀ w ∈ d₀.S₀ ∪ d₀.Bad, IsSplitAt w → ∀ u, ConjPl w u → ∀ m X, blk (Nat.add_sub_of_le ha) u m X ∈ K u →
    μ.loc u (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1 ∧
      ∃ m' ∈ d₀.L a w, embW a u m.1 = embT a w m'.1 ∧ embW (n - a) u m.2 = embT (n - a) w m'.2
  W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)
  hW : ∀ N, FiniteDimensional ℂ (W N)
  W_join : ∀ (i : C.ι) (s₁ : Tr E (C.a i)) (s₂ : Tr E (n - C.a i)) Pa Pb (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
    s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ rlΩ₁ hR E _ _ (A i).Ma (A i).Mb M, HasType K' W' V) →
    s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ rlΩ₂ hR E _ _ (A i).Ma (A i).Mb M, HasType K' W' V) →
    ∀ j, HasKType (W (D.N j)) (D.V j)

def levSet (Sec : Set (Pl E)) (d : LocData E n) (a : ℕ) : Set (Hf E a (n - a)) :=
  {h | ∀ w ∈ Sec, atW w h ∈ d.lev a w ∧ (IsSplitAt w → atW w (thP E a (n - a) h) ∈ d.lev₂ a w)}

def lev₁ (Sec : Set (Pl E)) (d : LocData E n) (a : ℕ) : Subgroup (GL (Fin a) (Af E)) :=
  Subgroup.closure {g | (g, 1) ∈ levSet Sec d a}

def lev₂ (Sec : Set (Pl E)) (d : LocData E n) (a : ℕ) : Subgroup (GL (Fin (n - a)) (Af E)) :=
  Subgroup.closure {g | (1, g) ∈ levSet Sec d a}

namespace Frame0

variable {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S : Finset (Pl E)} (F₀ : Frame0 hR π S)

abbrev loc (T' : Finset (Pl E)) (c : Pl E → (Fin n → ℤ) →₀ ℂ) (e : ∀ w : Pl E, GLw n w → ℂ) (b : ∀ w : Pl E, GLw n w) :
    LocData E n := { F₀.d₀ with T := T', c := c, e := e, b := b }

structure Cand (d : LocData E n) (i : F₀.C.ι) (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i))
    (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n) : Prop where
  ctx : Ctx F₀.μ s₁ s₂ Pa Pb D
  leaves₁ : s₁.AllLeaves fun M V => M = 0 ∨ ∃ K' ∈ rlΘ₁ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (lev₁ F₀.Sec d (F₀.C.a i)) (lev₂ F₀.Sec d (F₀.C.a i)) M,
    ∃ W' ∈ rlΩ₁ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb M, HasType K' W' V
  leaves₂ : s₂.AllLeaves fun M V => M = 0 ∨ ∃ K' ∈ rlΘ₂ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (lev₁ F₀.Sec d (F₀.C.a i)) (lev₂ F₀.Sec d (F₀.C.a i)) M,
    ∃ W' ∈ rlΩ₂ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb M, HasType K' W' V
  inf₁ : ∀ τ, HasInfCharGL s₁.space τ (mOf (F₀.A i).χa τ)
  inf₂ : ∀ τ, HasInfCharGL s₂.space τ (mOf (F₀.A i).χb τ)
  vec : ∃ G ∈ pairSpace s₁.space s₂.space, G ≠ 0 ∧ TypeH (lev₁ F₀.Sec d (F₀.C.a i)) (lev₂ F₀.Sec d (F₀.C.a i))
    (rlW₁ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb) (rlW₂ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb) G

end Frame0

end PositivityTheory.Rg.BcB.F

end
