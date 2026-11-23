import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HtOrth

open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped NNReal

variable {D : D7}

open Classical in

def vInf (w : InfinitePlace D.host.F) {n : ℕ} (x : Fin n → AE D) : ℝ≥0 :=
  Finset.univ.sup fun p : EmbOver D.host.E w × Fin n =>
    ‖infEmb p.1 (compInf D.host.F D.host.E w (x p.2))‖₊

def vFin (v : HeightOneSpectrum (𝓞 D.host.F)) {n : ℕ} (x : Fin n → AE D) : ℝ≥0 :=
  Finset.univ.sup fun i => absFin D.host.F v (compFin D.host.F D.host.E v (x i))

def vsize {n : ℕ} (x : Fin n → AE D) : ℝ :=
  (((∏ w, vInf w x) * ∏ᶠ v, vFin v x : ℝ≥0) : ℝ)

def seen (V : HSp D) (g : GA D V) (ξ : Fin V.rank → D.host.E) : Fin V.rank → AE D :=
  mt V g⁻¹ *ᵥ fun i => incA D (ξ i)

theorem vsize_nonneg {n : ℕ} (x : Fin n → AE D) : 0 ≤ vsize x := NNReal.coe_nonneg _

end GlobalTheory.HtOrth

end
