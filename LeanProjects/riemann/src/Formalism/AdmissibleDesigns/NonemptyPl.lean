import Formalism.SharpRestriction.LevelLetterCocycles.RingDataOfIdempotents
import Formalism.WachLatticeTwists.RealDisplaySplitting.GaloisTheoremThirdForms

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions Formalism.MainNotions.N

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem nonempty_pl : Nonempty (HeightOneSpectrum (𝓞 D.host.E)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM
    (NumberField.RingOfIntegers.not_isField _)⟩⟩

def plSet : Finset (HeightOneSpectrum (𝓞 D.host.E)) := dc.row ∪ dc.col ∪ D.nd.Q i

def idx (v : HeightOneSpectrum (𝓞 D.host.E)) : ℕ :=
  if h : v ∈ plSet i dc then ((plSet i dc).equivFin ⟨v, h⟩ : ℕ) else (plSet i dc).card

def plOf (n : ℕ) : HeightOneSpectrum (𝓞 D.host.E) :=
  if h : n < (plSet i dc).card then ((plSet i dc).equivFin.symm ⟨n, h⟩ : HeightOneSpectrum (𝓞 D.host.E))
  else Classical.choice nonempty_pl

theorem plOf_idx {v : HeightOneSpectrum (𝓞 D.host.E)} (h : v ∈ plSet i dc) : plOf i dc (idx i dc v) = v := by
  unfold plOf idx
  rw [dif_pos h, dif_pos ((plSet i dc).equivFin ⟨v, h⟩).isLt]
  simp

theorem idx_inj {v w : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∈ plSet i dc) (hw : w ∈ plSet i dc)
    (h : idx i dc v = idx i dc w) : v = w := by
  calc v = plOf i dc (idx i dc v) := (plOf_idx i dc hv).symm
    _ = plOf i dc (idx i dc w) := by rw [h]
    _ = w := plOf_idx i dc hw

def rowsN : Finset ℕ := dc.row.image (idx i dc)
def colsN : Finset ℕ := dc.col.image (idx i dc)
def qsN : Finset ℕ := (D.nd.Q i).image (idx i dc)

abbrev Col : Type := {u : HeightOneSpectrum (𝓞 D.host.E) // u ∈ dc.col}

def colIdx (l : Col i dc) : ℕ := idx i dc l.1

theorem colIdx_inj : Function.Injective (colIdx i dc) := by
  intro l₁ l₂ h
  apply Subtype.ext
  have m₁ : l₁.1 ∈ plSet i dc := by
    unfold plSet
    exact Finset.mem_union_left _ (Finset.mem_union_right _ l₁.2)
  have m₂ : l₂.1 ∈ plSet i dc := by
    unfold plSet
    exact Finset.mem_union_left _ (Finset.mem_union_right _ l₂.2)
  exact idx_inj i dc m₁ m₂ h

def Aw (n : ℕ) : ValuationSubring D.nd.Om := D.nd.plOm.1 (plOf i dc n)
def Av (v : HeightOneSpectrum (𝓞 D.host.E)) : ValuationSubring D.nd.Om := D.nd.plOm.1 v

end Formalism.MainNotions.N.K

end
