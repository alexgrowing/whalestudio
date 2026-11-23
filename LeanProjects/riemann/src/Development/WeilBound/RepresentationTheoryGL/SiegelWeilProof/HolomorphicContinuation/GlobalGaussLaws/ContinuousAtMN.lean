import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.EmbP

open Formalism.IndefR.Eqv (glueA splitInv psiT psiT_glueA finPart_glueA mat_ext psiT_sigR finPart_sigR psiT_inclR
  finPart_inclR continuous_glueA continuous_splitInv thetaC eq_thetaC)

variable (D : D7) {N : ℕ}

open Classical

def atMN (τ : D.what₂.Tau) (g : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) (AE D) :=
  Matrix.of fun i j => glueA D (splitInv D fun τ' => if τ' = τ then g i j else (1 : Matrix (Fin N) (Fin N) ℂ) i j)
    ((1 : Matrix (Fin N) (Fin N) (Af D.host.F ⊗[D.host.F] D.host.E)) i j)

theorem psi_atMN (τ τ' : D.what₂.Tau) (g : Matrix (Fin N) (Fin N) ℂ) :
    (atMN D τ g).map (psiT D τ') = if τ' = τ then g else 1 := by
  classical
  ext i j
  rw [Matrix.map_apply, atMN, Matrix.of_apply, psiT_glueA]
  split_ifs <;> rfl

theorem fin_atMN (τ : D.what₂.Tau) (g : Matrix (Fin N) (Fin N) ℂ) : (atMN D τ g).map (finPart D) = 1 := by
  ext i j
  rw [Matrix.map_apply, atMN, Matrix.of_apply, finPart_glueA]

theorem atMN_mul (τ : D.what₂.Tau) (g g' : Matrix (Fin N) (Fin N) ℂ) :
    atMN D τ (g * g') = atMN D τ g * atMN D τ g' := by
  apply mat_ext D
  · intro τ'
    rw [Matrix.map_mul, psi_atMN, psi_atMN, psi_atMN]
    split_ifs <;> simp
  · rw [Matrix.map_mul, fin_atMN, fin_atMN, fin_atMN, Matrix.one_mul]

theorem atMN_one (τ : D.what₂.Tau) : atMN D τ (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
  apply mat_ext D
  · intro τ'
    rw [psi_atMN, Matrix.map_one _ (map_zero _) (map_one _)]
    split_ifs <;> rfl
  · rw [fin_atMN, Matrix.map_one _ (map_zero _) (map_one _)]

theorem cT_map_psiT (τ : D.what₂.Tau) (M : Matrix (Fin N) (Fin N) (AE D)) :
    (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M).map (psiT D τ) = (M.map (psiT D τ))ᴴ := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply, psiT_sigR]

theorem cT_map_fin (M : Matrix (Fin N) (Fin N) (AE D)) :
    (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M).map (finPart D) =
      Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (M.map (finPart D)) := by
  ext i j; simp [Formalism.UG.cT, finPart_sigR]

theorem JR_map_psiT (τ : D.what₂.Tau) (J : Matrix (Fin N) (Fin N) D.host.E) :
    (JR (AF D.host.F) J).map (psiT D τ) = J.map (tauE D τ) := by
  ext i j; simp [JR, psiT_inclR]

theorem JR_map_fin (J : Matrix (Fin N) (Fin N) D.host.E) :
    (JR (AF D.host.F) J).map (finPart D) = JR (Af D.host.F) J := by
  ext i j; simp [JR, finPart_inclR]

theorem atMN_unitary (τ : D.what₂.Tau) (J : Matrix (Fin N) (Fin N) D.host.E) (g : Matrix (Fin N) (Fin N) ℂ)
    (hg : gᴴ * J.map (tauE D τ) * g = J.map (tauE D τ)) :
    Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (atMN D τ g) * JR (AF D.host.F) J * atMN D τ g = JR (AF D.host.F) J := by
  apply mat_ext D
  · intro τ'
    rw [Matrix.map_mul, Matrix.map_mul, cT_map_psiT, JR_map_psiT, psi_atMN]
    split_ifs with h
    · subst h; exact hg
    · simp
  · rw [Matrix.map_mul, Matrix.map_mul, cT_map_fin, JR_map_fin, fin_atMN, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem continuous_atMN (τ : D.what₂.Tau) : Continuous (atMN D (N := N) τ) := by
  classical
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_glueA D _).comp ((continuous_splitInv D).comp (continuous_pi fun τ' => ?_))
  by_cases h : τ' = τ
  · simp only [h, if_true]; exact (continuous_apply j).comp (continuous_apply i)
  · simp only [h, if_false]; exact continuous_const

end PositivityTheory.Rg.Sw.Glob.EmbP
