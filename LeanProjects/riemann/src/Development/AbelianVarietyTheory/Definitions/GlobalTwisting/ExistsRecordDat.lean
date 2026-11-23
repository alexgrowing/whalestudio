import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsAboveNe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PlacesOverConjPrimes

noncomputable section

namespace GlobalTheory.LvT.Built.Inh

open NumberField IsDedekindDomain Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2
open Formalism.MainNotions.product_first_zeroth_parts (Ow)

theorem val_tauAt {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) (hX : X.AbelianUnramifiedExtensionConditions) {w : HeightOneSpectrum (𝓞 X.K)}
    (hw : ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal) (P : Pr.vT u) (s : Bool) (hs : s = true ↔ seenC Pr u w) (x : X.E) :
    X.emb (tauAt hPr u w P) (if s then x else star x) ∈ GlobalTheory.LvT.Inh.valO w ↔ P.1.valuation X.E x ≤ 1 := by
  rw [GlobalTheory.LvT.Inh.mem_valO_of_below (X.emb (tauAt hPr u w P)) w (pullW (tauAt hPr u w P) w) (fun _ => Iff.rfl), GlobalTheory.LvT.Inh.mem_valO]
  by_cases h : s = true
  · rw [if_pos h, show pullW _ w = P.1 from seesP_tauAt hPr u hX (hs.1 h) P]
  · rw [if_neg h, show pullW _ w = conjPrime₂ P.1 from seesPbar_tauAt hPr u hX hw (mt hs.2 h) P,
      GlobalTheory.CharVal.valuation_conjP, star_star]

structure NonDeg {D : D7} {u : D.what₂.Word} (A : Dat D u) : Prop where
  sees : A.Sees
  T_eq : A.J.T = (D.mem u).A.T
  cl : ∀ i, Nonempty (A.I.S i).Cl
  split : ∀ i, Nonempty (Split (A.J.A i) A.J.T)
  forms : A.ch.fm.Fi 0 ≠ ⊥

local instance starHost (B : Base) : StarRing B.host.E := B.fields.starE

variable (B : Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W) (G : GJStage B C)
  (u : B.Word)

def ofOk (I : ChainIn B.fields.E B.fields.K B.fields.Tau B.R) (J : AtIn I) (Q : PerIn I)
    (Z : FmIn J (assemble B C W V S N G).what₂.places) (hI : I.Ok) (hJ : J.Ok) (hQ : Q.Ok) (hT : Q.Over J) :
    Dat (assemble B C W V S N G) u where
  E := B.fields.E
  sE := B.fields.starE
  emb := B.fields.emb
  fok := base_fOk B
  I := I
  J := J
  Q := Q
  Z := Z
  hI := hI
  hJ := hJ
  hQ := hQ
  l := (laws_all I J _ _ _ (base_fOk B) hI hJ Q hQ (assemble B C W V S N G).what₂.places).1
  lf := (laws_all I J _ _ _ (base_fOk B) hI hJ Q hQ (assemble B C W V S N G).what₂.places).2
  hT := hT

theorem sees_ofOk (X : PreX B.toPre) (I : ChainIn B.fields.E B.fields.K B.fields.Tau B.R) (J : AtIn I) (Q : PerIn I)
    (Z : FmIn J (assemble B C W V S N G).what₂.places) (hI : I.Ok) (hJ : J.Ok) (hQ : Q.Ok) (hT : Q.Over J)
    (eT : J.T = B.T u) (eS : ∀ P ∈ J.ST, P ∈ (B.primes X).vT u)
    (eZ : ∀ w (P : J.ST), Z.tauOf w P = tauAt (GlobalTheory.BasePrimes.primes_ok B X).1 u w ⟨P.1, eS P.1 P.2⟩)
    (eF : ∀ w, Z.seenP w = true ↔ seenC (B.primes X) u w) :
    (ofOk B C W V S N G u I J Q Z hI hJ hQ hT).Sees := by
  intro w hw P x
  have h1 := GlobalTheory.LvT.Inh.resChar_mem_plEq (assemble B C W V S N G) w
  rw [show (assemble B C W V S N G).what₂.places.resChar w = B.T u from hw.trans eT] at h1
  refine (GlobalTheory.LvT.Inh.mem_Ow_iff_valO (assemble B C W V S N G) w _).trans ?_
  have h2 := val_tauAt (GlobalTheory.BasePrimes.primes_ok B X).1 u (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1 h1 ⟨P.1, eS P.1 P.2⟩ _ (eF w) x
  exact (iff_of_eq (congrArg (fun τ => B.fields.emb τ (if Z.seenP w then x else star x) ∈ GlobalTheory.LvT.Inh.valO w) (eZ w P))).trans h2

end GlobalTheory.LvT.Built.Inh
