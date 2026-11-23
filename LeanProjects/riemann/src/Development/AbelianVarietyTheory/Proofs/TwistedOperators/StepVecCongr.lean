import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorGiven
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ChainCol

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Classical in

def extDat {m n : ℕ} (e e' : AE D) (Λ : AddSubgroup (Mx D m n)) (φ : Mx D m n → ℂ) : Mx D m n → ℂ :=
  fun x => if IsHalf e x ∧ x.map ((e - e') * ·) ∈ Λ then φ (x.map (e' * ·)) else 0

open Classical in

def stepDat (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (LS : LevDat D.host.E ℂ S.rank) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (e : AE D) :
    WO S T → ℂ :=
  fun x => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then
      omegaG LS χj (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q LS.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x))
    else 0

theorem r_le_colY {T : Type} (L : LevCh D T) (j : ℕ) : D.R.r ≤ (columnBlock L j).sp.rank := by
  rcases j with _ | j
  · exact r_le_Y 0
  · by_cases h : j + 1 < D.R.m
    · rw [colY_lt L h]; exact r_le_Y _
    · rw [show columnBlock L (j + 1) = ⟨D.sp.X', L.ΛX⟩ from if_neg h]; exact r_le_X

def colDat {T : Type} (L : LevCh D T) (t : T) (j : ℕ) : LevDat D.host.E ℂ (columnBlock L j).sp.rank :=
  Formalism.IndefR.Lev.datY _ D.R.r D.R.t j (r_le_colY L j) L.Pg (L.Q t) (LevelP.triv L.Pg D.R.r ℂ) L.chi (L.xiR t) Formalism.IndefR.Lev.Frm.B

theorem lsp_heq {X : LSp D} {S : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (h : X = ⟨S, Λ⟩) :
    X.sp = S ∧ HEq X.lat Λ := by
  subst h; exact ⟨rfl, HEq.rfl⟩

theorem datY_heq {n n' : ℕ} (h : n = n') (r t j : ℕ) (hr : r ≤ n) (hr' : r ≤ n') (Pg Q : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (fr : Formalism.IndefR.Lev.Frm) :
    HEq (Formalism.IndefR.Lev.datY n r t j hr Pg Q P χ ξ fr) (Formalism.IndefR.Lev.datY n' r t j hr' Pg Q P χ ξ fr) := by
  subst h; rfl

theorem stepVec_congr {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S S' T T' : HSp D} (hS : S = S') (hT : T = T')
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {sS' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ} {sT' : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)} {ΛT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}
    {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)} {βS' : GL (Fin S'.rank) (EAf D)} {βT' : GL (Fin T'.rank) (EAf D)}
    {LS : LevDat D.host.E ℂ S.rank} {LS' : LevDat D.host.E ℂ S'.rank} {χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {Q : Finset (Pl D.host.E)} {f₀ f : WO S T → ℂ} {f₀' f' : WO S' T' → ℂ}
    (h1 : HEq sS sS') (h2 : HEq sT sT') (h3 : HEq ΛS ΛS') (h4 : HEq ΛT ΛT') (h5 : HEq βS βS') (h6 : HEq βT βT')
    (h7 : HEq LS LS') (h8 : HEq f₀ f₀') (h9 : HEq f f')
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f) :
    IsStepVecOf ψ θ S' T' sS' sT' ΛS' ΛT' βS' βT' LS' χj Q ξ f₀' f' := by
  subst hS hT
  cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; cases h7; cases h8; cases h9
  exact h

end GlobalTheory.ChainCol
