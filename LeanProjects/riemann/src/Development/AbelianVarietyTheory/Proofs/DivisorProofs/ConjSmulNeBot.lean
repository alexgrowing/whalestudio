import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BotPairSmall

def cvec (D : D7) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (o a d : ℕ) (e0 : VC D a d → ℂ) : VC D a d → ℂ :=
  ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d))
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)

theorem cosetVec_eq {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (𝔪 : Ideal (𝓞 D.host.E)) (o : ℕ) :
    cosetVec P 𝔪 o = cvec D δ 𝔪 o P.a P.d P.e0 := rfl

def blockSet (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : Set (GA D N) :=
  {h | h ∈ intG D N ∧ ∀ i j : Fin N, j.1 < a → a ≤ i.1 →
    ((h : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪}

def blockJ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : Subgroup (GA D N) := Subgroup.closure (blockSet D 𝔪 a N)

theorem blockJ_le (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : blockJ D 𝔪 a N ≤ intG D N :=
  (Subgroup.closure_le _).2 fun _ h => h.1

theorem conj_smul_ne_bot (D : D7) {𝔪 : Ideal (𝓞 D.host.E)} (h : 𝔪 ≠ ⊥) : D.host.conj • 𝔪 ≠ ⊥ := by
  intro e
  apply h
  have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) e
  simpa [smul_smul] using this

end GlobalTheory.BotPairSmall
