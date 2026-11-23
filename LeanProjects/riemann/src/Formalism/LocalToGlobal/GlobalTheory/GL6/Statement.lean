import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.LocalToGlobal.HermitianForms.FormsTied

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Classical NumberField

section Split

variable (D : D7) (u : D.what₂.Word)

def KernelOperatorLatticeInclusions (C : ℝ) : Prop :=
  ∀ w, OverT D u w →
    ∀ i, i < D.R.m →
      ((D.fm u).seenP w = false →
        Into D u w (fun φ => tpow D u (lossK D u C) • KT D u i φ) ((D.fm u).S i w) ((D.fm u).S (i + 1) w)) ∧
      ((D.fm u).seenP w = true → ∃ BV, IsBfam D u (i + 1) w BV ∧
        Into D u w (fun φ => tpow D u (lossK D u C) • KT D u i φ) ((D.fm u).S i w) (BV Finset.univ)) ∧
      (∃ e1 : ℕ, (e1 : ℝ) ≤ 4 * ∑ τ, (Wt D u τ : ℝ) + C * D.R.f * D.R.N D.R.m ∧
        Into D u w (fun φ => tpow D u e1 • Uprod D u (i + 1) w (KT D u i φ))
          ((D.fm u).S i w) ((D.fm u).S (i + 1) w))

def WeightLatticeInclusion : Prop :=
  ∀ w, OverT D u w →
    ∀ i, i ≤ D.R.m → (D.fm u).seenP w = true → ∀ v, (D.fm u).tauOf w v ∉ tops D →
      Into D u w (fun φ => tpow D u (2 * Wt D u ((D.fm u).tauOf w v) + D.R.t) • φ) ((D.fm u).Bw i w v) ((D.fm u).S i w)

def CongruenceLatticeLengthBound : Prop :=
  ∀ w, OverT D u w →
    Nlam D u w ≤ Sram D u w ∧
    (∃ n : ℕ, len D u w (Sram D u w) (Nlam D u w) = n ∧
      (n : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.R.m * D.duS u * ∑ v ∈ VV D u w,
        ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v) + D.R.k + (D.fm u).bTop ((D.fm u).tauOf w v))))

def CongruenceKernelClause (C : ℝ) : Prop :=
  ∀ w, OverT D u w →
    ∃ e : ℕ, (e : ℝ) ≤ D.R.m * (4 * ∑ τ, (Wt D u τ : ℝ) + C * D.R.f * D.R.N D.R.m) +
        ∑ v ∈ VV D u w, ((D.R.t : ℝ) + 1 + 2 * Wt D u ((D.fm u).tauOf w v) + C * D.R.N D.R.m) *
          ((D.R.m : ℝ) * (D.R.m + 1) / 2) ∧
      Into D u w (fun φ => tpow D u e • colT D u φ) (Nlam D u w) ((D.fm u).S D.R.m w)

def FrobeniusOperatorRelations : Prop :=
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ MramI D u i, FFop D u i v φ = Dop D u i v (Gs D u i v φ)) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i,
    Gs D u i v (GsD D u i v φ) = ((D.mem u).A.T : ℂ) • φ - Nm D u i v φ) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ MramI D u i, FFop D u i v φ ∈ MramI D u i) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ MramI D u i, ∀ ψ ∈ MramI D u i,
    (D.fm u).ipC i (FFop D u i v φ) (FFop D u i v ψ) = ((D.mem u).A.T : ℂ) ^ D.R.N i * (D.fm u).ipC i φ ψ) ∧
  (∀ i, i ≤ D.R.m → ∀ φ ∈ MramI D u i, ∀ ψ ∈ MramI D u i,
    (D.fm u).ipC i (FFall D u i φ) (FFall D u i ψ) = ((D.mem u).A.T : ℂ) ^ (D.R.f * D.R.N i) * (D.fm u).ipC i φ ψ)

def FrobeniusKernelClause : Prop :=
  ∀ i, i < D.R.m → ∀ v, ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ MramI D u i,
    FFop D u (i + 1) v (KT D u i φ) = c • KT D u i (FFop D u i v φ)

end Split

def ChiUnit {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) (x : (T.cls i hi).lev.U), ‖(((T.cls i hi).lev.chi x : ℂˣ) : ℂ)‖ = 1

def ChiFin {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.FormsTied D u) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ i (hi : i ≤ D.R.m) (x : (T.cls i hi).lev.U),
    (((T.cls i hi).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧
      ∃ r : D.what₂.LL, D.what₂.embLL r = (((T.cls i hi).lev.chi x : ℂˣ) : ℂ)

def FormsCompatible (D : D7) (u : D.what₂.Word) : Prop := ∃ T : Formalism.L2.Forms.FormsTied D u, ChiFin T

def LinkAdmT : Prop := ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → admT D u

def HeckeRelationsFamily : Prop := ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → HidaSetting D u → Conclusion1 D u

def RamifiedLatticeFamily : Prop :=
  ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → HidaSetting D u → admS D u → Conclusion2 D u

def WeightLatticeInclusionFamily : Prop := ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → HidaSetting D u → WeightLatticeInclusion D u

def CongruenceLatticeLengthBoundFamily : Prop :=
  ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → HidaSetting D u → admS D u → CongruenceLatticeLengthBound D u

def FrobeniusNoKernelFamily : Prop := ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → HidaSetting D u → FrobeniusOperatorRelations D u

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
