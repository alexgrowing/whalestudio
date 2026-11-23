import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormThetaMul

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open GroundTheory.Global PositivityTheory.Rg.Base1
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

variable {F : Type} [Field F] [NumberField F]

def phiA (G : Ainf F → ℝ) (a : (AF F)ˣ) : (Unit → Ainf F) → ℝ := fun y => G ((a : AF F).1 * y ())

def psiA (S : Finset (HeightOneSpectrum (𝓞 F))) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) : (Unit → Fv F v) → ℝ := fun y =>
  if v ∈ S then g v ((a : AF F).2 v * y ())
  else if (a : AF F).2 v * y () ∈ v.adicCompletionIntegers F then 1 else 0

theorem md_mul (a b : (AF F)ˣ) : md (a * b) = md a * md b := by
  simp [md, map_mul]

theorem md_pos (a : (AF F)ˣ) : 0 < md a := (IdeleGroup.ideleModule F a).2

theorem md_pr (t : Fˣ) : md (pr t) = 1 := by
  have h := IdeleGroup.ideleModule_diagonal (K := F) t
  have h2 : pr t = IdeleGroup.diagonal F t := rfl
  rw [md, h2, h]
  rfl

theorem th_pr (f : (AF F)ˣ → ℝ≥0∞) (k : Fˣ) (a : (AF F)ˣ) : th f (pr k * a) = th f a := by
  unfold th
  rw [← (Equiv.mulRight k).tsum_eq (fun t : Fˣ => f (pr t * a))]
  refine tsum_congr fun t => ?_
  have : pr (t * k) = pr t * pr k := by simp [pr, map_mul]
  simp only [Equiv.coe_mulRight, this, mul_assoc]

end GlobalTheory.CompanionTheory.BasePsi

end
