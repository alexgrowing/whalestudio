import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalRingCardinality.DataRows

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage

open Formalism.BasicNotions Formalism.MainNotions.N

def ThetaTMapsIntoEig {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
    x ∈ ZgoodN N A i → HasParamX N A i x Sig →
      ∀ f ∈ MjSig N A i Sig, what₂.thetaT (N.mu i) (N.j i) f ∈ eigC N A i x

def MjSigOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) (Sig : List (Part A.CG)) : Submodule ℂ (what₂.Mj (N.j i)) :=
  ⨆ σ ∈ {σ | ∀ w, SplitOut N i w → isoLoc N A Sig w = A.locW i σ w}, what₂.isot (N.j i) σ

def ThetaTMapsIntoEigOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
    x ∈ ZgoodN N A i → HasParamX N A i x Sig →
      ∀ f ∈ MjSigOut N A i Sig, what₂.thetaT (N.mu i) (N.j i) f ∈ eigC N A i x

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem mjSig_le_mjSigOut (i : N.Loc) (Sig : List (Part A.CG)) :
    MjSig N A i Sig ≤ MjSigOut N A i Sig := by
  unfold MjSig MjSigOut
  exact biSup_mono fun σ hσ w hw => hσ.2.2 w hw.1

theorem thetaTMapsIntoEig_of_out (h : ThetaTMapsIntoEigOut N A) : ThetaTMapsIntoEig N A :=
  fun i x Sig hx hp f hf => h i x Sig hx hp f (mjSig_le_mjSigOut N A i Sig hf)

theorem thetaTMapsIntoEig_iff_map_le : ThetaTMapsIntoEig N A ↔
    ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
      x ∈ ZgoodN N A i → HasParamX N A i x Sig →
        (MjSig N A i Sig).map (what₂.thetaT (N.mu i) (N.j i)) ≤ eigC N A i x := by
  unfold ThetaTMapsIntoEig
  simp only [Submodule.map_le_iff_le_comap]
  rfl

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage
