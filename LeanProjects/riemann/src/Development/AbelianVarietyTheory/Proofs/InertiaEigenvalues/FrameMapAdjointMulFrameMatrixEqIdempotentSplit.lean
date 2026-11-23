import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.LocDisj

theorem map_cA_smul_of_fix (D : D7) {m n : ℕ} (f : AE D) (hf : cA D f = f) (X : Matrix (Fin m) (Fin n) (AE D)) :
    (f • X).map (cA D) = f • X.map (cA D) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hf]

theorem map_toEAf_smul (D : D7) {m n : ℕ} (f : AE D) (Y : Matrix (Fin m) (Fin n) (AE D)) :
    (f • Y).map (toEAf D) = toEAf D f • Y.map (toEAf D) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem frMapAdj_smul_of_fix (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (hf : cA D f = f) (x : WO V W) :
    frMapAdj V W βV βW (f • x) = toEAf D f • frMapAdj V W βV βW x := by
  unfold frMapAdj
  have h3 : (HMul.hMul (HMul.hMul ((V.gram⁻¹).map (incA D)) ((f • (x : Matrix (Fin W.rank) (Fin V.rank) (AE D))).map (cA D)).transpose) (W.gram.map (incA D)) : Matrix (Fin V.rank) (Fin W.rank) (AE D))
      = f • (HMul.hMul (HMul.hMul ((V.gram⁻¹).map (incA D)) ((x : Matrix (Fin W.rank) (Fin V.rank) (AE D)).map (cA D)).transpose) (W.gram.map (incA D)) : Matrix (Fin V.rank) (Fin W.rank) (AE D)) := by
    rw [map_cA_smul_of_fix D f hf, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
  rw [h3, map_toEAf_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_smul_eq {n : ℕ} {R : Type} [CommRing R] (c : R) (β : GL (Fin n) R) (M : Matrix (Fin n) (Fin n) R)
    (h0 : ∀ i j, c * (M - 1) i j = 0) :
    c • (β⁻¹.val * M * β.val) = c • (1 : Matrix (Fin n) (Fin n) R) := by
  have hM : c • M = c • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← sub_eq_zero, ← smul_sub]
    ext i j
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] using h0 i j
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hM, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.inv_mul]

theorem split_mul {m n : ℕ} {R : Type} [CommRing R] (c : R) (A A' : Matrix (Fin m) (Fin n) R) (K : Matrix (Fin n) (Fin n) R)
    (hx : c • A = c • A') (hK : (1 - c) • K = (1 - c) • (1 : Matrix (Fin n) (Fin n) R)) :
    A' * K = c • (A * K) + (1 - c) • A' := by
  calc A' * K = (c + (1 - c)) • (A' * K) := by rw [add_sub_cancel, one_smul]
    _ = (c • A') * K + A' * ((1 - c) • K) := by rw [add_smul, Matrix.smul_mul, Matrix.mul_smul]
    _ = (c • A) * K + A' * ((1 - c) • (1 : Matrix (Fin n) (Fin n) R)) := by rw [hx, hK]
    _ = c • (A * K) + (1 - c) • A' := by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one]

theorem suppF_entry (D : D7) (W : HSp D) (f : AE D) (k : GA D W) (hk : SuppF W f k) (i j : Fin W.rank) :
    (1 - toEAf D f) * ((Formalism.L2.Theta.mt W k).map (toEAf D) - 1) i j = 0 := by
  have e : ((Formalism.L2.Theta.mt W k).map (toEAf D) - 1) i j = toEAf D ((Formalism.L2.Theta.mt W k - 1) i j) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e, ← map_one (toEAf D), ← map_sub, ← map_mul, sub_mul, one_mul, hk i j, sub_self, map_zero]

end GlobalTheory.LocDisj

namespace GlobalTheory.LocDisj

theorem frMapAdj_mul_frame_eq (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (hf : cA D f = f) (k : GA D W) (hk : SuppF W f k) (x x' : WO V W) (hxx : ∀ a b, f * x a b = f * x' a b) :
  (HMul.hMul (frMapAdj V W βV βW x') (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) = toEAf D f • (HMul.hMul (frMapAdj V W βV βW x) (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) + (1 - toEAf D f) • frMapAdj V W βV βW x' := by
  have hfx : f • x = f • x' := by
    ext a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hxx a b
  have hx : toEAf D f • frMapAdj V W βV βW x = toEAf D f • frMapAdj V W βV βW x' := by
    rw [← frMapAdj_smul_of_fix D V W βV βW f hf, ← frMapAdj_smul_of_fix D V W βV βW f hf, hfx]
  exact split_mul (toEAf D f) _ _ _ hx (conj_smul_eq _ βW _ (suppF_entry D W f k hk))

end GlobalTheory.LocDisj
