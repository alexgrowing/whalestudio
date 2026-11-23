import Formalism.LocalToGlobal.Columns.Record
import Formalism.LocalToGlobal.Columns.GFamSEv

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

section Fam

variable {X : Fields} {R : Ranks}

abbrev FamStabS (F : GFamS X.K) (c : F.Cl) : Type := MulAction.stabilizer (F.G c.1) ((F.sec c.1).rep c.2)

def recChainFS (hc : X.Tau → HCParam R) (F : ℕ → GFamS X.K) (hF : ∀ j, (F j).Ok) (σ₀ : X.K →+* ℂ)
    (D : ℕ) (hD : 0 < D) (hdvd : ∀ j, j ≤ R.m → ∀ c : (F j).Cl, Nat.card (FamStabS (F j) c) ∣ D)
    (A : ChainArgF R (fun i => (F i).toGFam) σ₀) : ColumnChain R X.Tau hc where
  cls := fun i => (F i).Cl
  clsFin := fun i => (hF i).fintypeCl
  stab := fun i c => FamStabS (F i) c
  stabGrp := fun _ _ => inferInstance
  stabFin := fun i c => (hF i c.1).fin_stab _
  DGam := D
  DGam_pos := hD
  dvd_DGam := hdvd
  Y := fun i => FrS X σ₀ (R.N i)
  de := fun _ y τ => deFr y τ
  de_ne := fun _ y τ => (y.2 τ).ne_zero
  rhoDet := A.rhoDet
  rhoDet' := A.rhoDet'
  rho_norm := A.rho_norm
  rho'_norm := A.rho'_norm
  unf := A.unf
  sSharp := sSharpH hc
  sSharp_eq := fun i h τ => by
    obtain ⟨a, ha⟩ := (rec_sInt R (hc τ) ⟨i, h⟩).2
    have e : (RowPar.of (hc τ)).eAt i = (hc τ).e ⟨i, h⟩ := by
      unfold RowPar.eAt
      rw [dif_pos h]
      rfl
    unfold sSharpH
    rw [e]
    simp only at ha
    rw [ha, Int.floor_intCast]
  sDiv := sDivH hc
  sDiv_eq := fun i h τ => by
    obtain ⟨a, ha⟩ := (rec_sInt R (hc τ) ⟨i, h⟩).1
    have e : (RowPar.of (hc τ)).eAt i = (hc τ).e ⟨i, h⟩ := by
      unfold RowPar.eAt
      rw [dif_pos h]
      rfl
    unfold sDivH
    rw [e]
    simp only at ha
    rw [ha, Int.floor_intCast]

end Fam

end Formalism.L2.Col
