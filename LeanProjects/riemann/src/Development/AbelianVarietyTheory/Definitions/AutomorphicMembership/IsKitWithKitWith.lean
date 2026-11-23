import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PadTrueNormDetConst
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotIsBettiZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulCardPsi

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam

variable {D : D7}

abbrev StFams (D : D7) : Type 1 := ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A), StFam S κ

section One

variable {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (F : StFam S κ) (s : FinalTheorems S κ) (L : CmList A) (jC : JC D)

abbrev PolOf {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag) : Type := PolDat s Φ (metsOf x Φ) (refMet x Φ)

abbrev padWith {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag) (cts : Ats S κ) {jC : JC D} (hj : jC.Pinned) (hA : AdmEx S κ) :
    PadPkg D N j s.Comp jC ngTrue :=
  padTrue s Φ (metsOf x Φ) jC hj hA (locStOf F cts) (globStOf F cts)

structure IsKitWith (k : KitT s L jC) (d : s.Comp → D.what₂.Tau → ℝ) (x : ToroidalCompactificationData s) (P : PolOf x k.Φ) (cts : Ats S κ)
    (hj : jC.Pinned) (hA : AdmEx S κ) : Prop where
  ats : cts.Over jC
  bd : IsBdOf x L k.B
  fl : k.fl = flBetti s k.Φ L
  mb : k.Mb = mbarOf P
  pad : k.pad = padWith F x k.Φ cts hj hA
  deg : d = degFlat s k.Φ (metsOf x k.Φ)

variable {s jC} in

def kitWith (Φ : s.Flag) (key : KeySec s.Xo κ.c) (x : ToroidalCompactificationData s) (B : s.Bd L) (P : PolOf x Φ) (cts : Ats S κ)
    (hj : jC.Pinned) (hA : AdmEx S κ) : KitT s L jC where
  Φ := Φ
  dim_eq := (CmDim.cm_dim D A).2.2 N j S κ s Φ
  key := key
  B := B
  fl := flBetti s Φ L
  Mb := mbarOf P
  pad := padWith F x Φ cts hj hA
  levIn _ := Iff.rfl

variable {s L jC} in

theorem isKitWith_kitWith (Φ : s.Flag) (key : KeySec s.Xo κ.c) {x : ToroidalCompactificationData s} {B : s.Bd L} (hB : IsBdOf x L B)
    (P : PolOf x Φ) {cts : Ats S κ} (hc : cts.Over jC) (hj : jC.Pinned) (hA : AdmEx S κ) :
    IsKitWith F s L jC (kitWith F L Φ key x B P cts hj hA) (degFlat s Φ (metsOf x Φ)) x P cts hj hA :=
  ⟨hc, hB, rfl, rfl, rfl, rfl⟩

namespace IsKitWith

variable {F s L jC} {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} {x : ToroidalCompactificationData s} {P : PolOf x k.Φ} {cts : Ats S κ}
  {hj : jC.Pinned} {hA : AdmEx S κ} (h : IsKitWith F s L jC k d x P cts hj hA)
include h

theorem pad_eq : k.pad = padAt s (locStOf F cts) (globStOf F cts) (admissible_representation_factorisation S κ jC hj hA) (flatSt s k.Φ (metsOf x k.Φ))
    (arIn s k.Φ (metsOf x k.Φ)) := h.pad

theorem isBetti {c : s.Comp} {τ : D.what₂.Tau} (hb : ∃ b, IsBetti s k.Φ L c τ (flatSec s k.Φ c τ) b) :
    IsBetti s k.Φ L c τ (flatSec s k.Φ c τ) (k.fl c τ) := h.fl ▸ isBetti_flBetti hb

open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain in

theorem r_eq (c : s.Comp) {z} (hz : z ∈ DomI D.what₂.Tau j (N - j)) :
    (k.B c).r z = x.r κ.σ₀ (s.toCpt L c z) := h.bd.r_eq c hz

theorem bd_ne_invariant (hb : (genBd s.T.Z : Set (gen s.T.Z : Scheme.{0})).Nonempty) :
    k.B ≠ GlobalTheory.TrueCx.invariantB _ _ (GlobalTheory.TrueCx.first_index_eq_of_unfolded _ s.isUnf S.p_eq) _ := fun e =>
  have ⟨c⟩ := s.compNe
  h.bd.m_ne_zero c hb (by rw [e]; rfl)

end IsKitWith

end One

def IsKitOf (st : StFams D) : KitClass D := fun A N j S κ s L jC k d =>
  ∃ x P cts hj hA, IsKitWith (st A N j S κ) s L jC k d x P cts hj hA

namespace IsKitOf

variable {st : StFams D} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} {L : CmList A} {jC : JC D}
  {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} (h : IsKitOf st A N j S κ s L jC k d)
include h

theorem fl_eq : k.fl = flBetti s k.Φ L := have ⟨_, _, _, _, _, h⟩ := h; h.fl

theorem bd_ne_invariant (hb : (genBd s.T.Z : Set (gen s.T.Z : Scheme.{0})).Nonempty) :
    k.B ≠ GlobalTheory.TrueCx.invariantB _ _ (GlobalTheory.TrueCx.first_index_eq_of_unfolded _ s.isUnf S.p_eq) _ :=
  have ⟨_, _, _, _, _, h⟩ := h; h.bd_ne_invariant hb

end IsKitOf

example {A : Amb D} {N j : ℕ} (S : Sig A N j) (L : CmList A) (τ : D.what₂.Tau) :
    expo S.Dw (detSym S.Dw (fun _ => false) none (DV.tauEmb D τ)) =
      fun z => -GlobalTheory.AllWt.exOf S.Dw (GlobalTheory.FlatLine.flatWt S.Dw (L.ψ τ)) 0 (some z) := detEx_eq S L τ

example {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {F : StFam S κ} {s : FinalTheorems S κ} {L : CmList A} {jC : JC D}
    {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} {x : ToroidalCompactificationData s} {P : PolOf x k.Φ} {cts : Ats S κ}
    {hj : jC.Pinned} {hA : AdmEx S κ} (h : IsKitWith F s L jC k d x P cts hj hA) (τ : D.what₂.Tau) :
    ¬ IsKitWith F s L jC k (d + 1) x P cts hj hA := fun h' =>
  have ⟨c⟩ := s.compNe
  by simpa using congrFun₂ (h'.deg.trans h.deg.symm) c τ

example {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {F : StFam S κ} {s : FinalTheorems S κ} {L : CmList A} {jC : JC D}
    {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} {x : ToroidalCompactificationData s} {P : PolOf x k.Φ} {cts : Ats S κ}
    {hj : jC.Pinned} {hA : AdmEx S κ} (h : IsKitWith F s L jC k d x P cts hj hA) (hq : S.Dw.q = 0) :
    d = degFrame s k.Φ (metsOf x k.Φ) := by
  funext c τ
  simp [h.deg, degFlat, hq]

end GlobalTheory.ShFam
