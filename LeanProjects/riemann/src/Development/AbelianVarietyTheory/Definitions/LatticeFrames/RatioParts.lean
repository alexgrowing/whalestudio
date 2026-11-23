import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

open GlobalTheory.Fam (UnitRatio)

variable {D : D7} {c : Comm D} (v : VCom c) {𝒯 : Type} (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)) (F : ∀ s, GlobalTheory.QPl.QFam v (t s))

structure RatioParts (S : 𝒯 → ℕ → Prop) (s₀ : 𝒯) : Prop where
  base : (F s₀).r = 0
  sc : ∀ s j, j < D.R.m → UnitRatio (S s) ((w s).sc j) ((w s₀).sc j)
  cT : ∀ s j ρ, j + 2 * ρ + 2 = D.R.m → UnitRatio (S s) ((w s).cT j) ((w s₀).cT j)
  cI : ∀ s j, j < D.R.m → (t s).cI j * ∏ i, (((F s).Q i).idx (j + 1) : ℂ) = (t s₀).cI j
  cK : ∀ s j, j < D.R.m → UnitRatio (S s) ((t s).cK j) ((t s₀).cK j)
  cP : ∀ s, UnitRatio (S s) (t s).cP (t s₀).cP

end GlobalTheory.SeeSaw

end
