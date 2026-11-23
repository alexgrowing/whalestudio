import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLiftResiduesIdempotentSumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLift
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.HalfFrameLift

theorem exists_half_redM_frMapO : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP PP), ∃ u : WO S T, IsHalf e u ∧ IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) ∧ ∀ PP ∈ Q, redM PP (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) = y PP := by
  intro D S T βS βT Q e he ϖ hϖ y
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  subst hsum
  choose N hN hNe hNr using fun (i : Fin T.rank) (j : Fin S.rank) =>
    GlobalTheory.T.exists_integral_lift_residues_idempotentSum D Q es hes hc (fun PP => y PP i j)
  set e := ∑ PP ∈ Q, es PP with he_def
  let z : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.of N
  let A : Matrix (Fin T.rank) (Fin S.rank) (EAf D) :=
    ((βT.val : Matrix (Fin T.rank) (Fin T.rank) (EAf D)) * z : Matrix (Fin T.rank) (Fin S.rank) (EAf D)) *
      ((βS⁻¹).val : Matrix (Fin S.rank) (Fin S.rank) (EAf D))
  choose w hw using fun (i : Fin T.rank) (j : Fin S.rank) =>
    GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) (A i j)
  have hϖ' : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ
  have hinv : incA D (ϖ : D.host.E) * incA D (ϖ : D.host.E)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hϖ', map_one]
  let u : WO S T := Matrix.of fun i j => e * incA D (ϖ : D.host.E)⁻¹ * w i j
  have key : frMapO S T βS βT (u.map fun v => incA D (ϖ : D.host.E) * v) = z := by
    have hmap : (u.map fun v => incA D (ϖ : D.host.E) * v).map (toEAf D) = toEAf D e • A := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, u, Matrix.of_apply]
      rw [← hw i j, ← map_mul]
      congr 1
      linear_combination (e * w i j) * hinv
    unfold frMapO
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, z, Matrix.of_apply]
    exact hNe i j
  refine ⟨u, fun i j => ?_, ?_, fun PP hPP => ?_⟩
  · show e * (e * incA D (ϖ : D.host.E)⁻¹ * w i j) = e * incA D (ϖ : D.host.E)⁻¹ * w i j
    rw [← mul_assoc, ← mul_assoc, hee]
  · rw [key]; exact fun i j => hN i j
  · rw [key]
    funext i j
    exact (dif_pos (hN i j)).trans (hNr i j PP hPP)

end GlobalTheory.HalfFrameLift
