import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem GlobalTheory.LogPole.exists_basicOpen_cell_choose : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J), W ≤ toBase TF Z ⁻¹ᵁ U.1 → W ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k → Nonempty W → ∃ a : Γ(TF.Y.X, U.1), TF.Y.X.basicOpen a ≤ LogKS.interior TF.Y ⊓ barComp TF.Y Z ⊓ (TF.X.F.M k).U ∧ ∃ w : Y₀ TF.X Z, w ∈ W ∧ w ∈ U₀ TF.X Z ∧ toBase TF Z w ∈ TF.Y.X.basicOpen a := by
  intro E _ _ _ H Dw l Xo c TF Z U W k hWU hWk hW
  obtain ⟨⟨w₁, hw₁⟩⟩ := hW
  obtain ⟨w, hwW, hw0⟩ := (dense_U₀ TF.X Z).inter_open_nonempty (W : Set (Y₀ TF.X Z)) W.isOpen ⟨w₁, hw₁⟩
  have hcomp : toBase TF Z w = TF.X.π w.1 := Scheme.Hom.comp_apply _ _ _
  have hU : toBase TF Z w ∈ U.1 := hWU hwW
  have hI : toBase TF Z w ∈ LogKS.interior TF.Y := by
    rw [hcomp]; exact hw0
  have hB : toBase TF Z w ∈ barComp TF.Y Z := by
    rw [hcomp]; exact w.2
  have hM : toBase TF Z w ∈ (TF.X.F.M k).U := by
    rw [hcomp]; exact TF.X.F.le k (hWk hwW)
  obtain ⟨a, ha, hxa⟩ := U.2.exists_basicOpen_le
    (V := LogKS.interior TF.Y ⊓ barComp TF.Y Z ⊓ (TF.X.F.M k).U) ⟨toBase TF Z w, ⟨⟨hI, hB⟩, hM⟩⟩ hU
  exact ⟨a, ha, w, hwW, hw0, hxa⟩
