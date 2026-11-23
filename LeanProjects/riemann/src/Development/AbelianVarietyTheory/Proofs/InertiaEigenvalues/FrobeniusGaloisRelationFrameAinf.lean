import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.GalPhi

variable {l : ℕ} [Fact l.Prime]

theorem σA_frobenius (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) := by
  apply inclW_injective
  rw [← frobW_inclW, ← galW_inclW, ← galW_inclW, ← frobW_inclW]
  refine WittVector.ext fun n => ?_
  simp [galW, frobW, mapAlgEquivW, mapEquivW, WittVector.map_coeff, frobenius_def]

theorem frobenius_algebraMap (z : ℤ_[l]) :
    WittVector.frobenius (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (Ainf l) z := by
  change WittVector.frobenius (zlW l (OCb l) z) = zlW l (OCb l) z
  rw [WittVector.frobenius_eq_map_frobenius]
  simp only [zlW, RingHom.comp_apply]
  refine WittVector.ext fun n => ?_
  simp only [WittVector.map_coeff]
  exact congrArg (fun φ : ZMod l →+* OCb l => φ (((WittVector.equiv l).symm.toRingHom z).coeff n))
    (RingHom.ext_zmod ((frobenius (OCb l) l).comp (ZMod.castHom (dvd_refl l) (OCb l))) (ZMod.castHom (dvd_refl l) (OCb l)))

theorem gal_ainf {K : FinExt l} (bk : BK K) (τ : Ainf l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (hY : Y.map (inclW l) = inclW l τ ^ N • F.T)
    (g : ↥(GK K)) :
    τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l))) =
      Per.σA (g : GQ l) τ ^ N • (Y * F.ε g) := by
  have hz : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW (ρ g) := by
    refine Matrix.ext fun i j => ?_; exact (inclWA l).commutes _
  have hσ : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) := by
    refine Matrix.ext fun i j => ?_; exact (galW_inclW _ _).symm
  have hT : (Y.map (inclW l)).map (galW l (g : GQ l)) = inclW l (Per.σA (g : GQ l) τ) ^ N • F.T.map (galW l (g : GQ l)) := by
    rw [hY, ← galW_inclW, ← map_pow]
    refine Matrix.ext fun i j => ?_; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  refine Matrix.ext fun i j => ?_
  apply inclW_injective
  have key : (τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l)))).map (inclW l) =
      (Per.σA (g : GQ l) τ ^ N • (Y * F.ε g)).map (inclW l) := by
    rw [Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_mul, Matrix.map_mul,
      hz, hσ, hT, Matrix.mul_smul, F.gal, hY, Matrix.smul_mul, smul_smul, smul_smul, mul_comm]
    simp only [map_pow]
  exact congrFun (congrFun key i) j

end GlobalTheory.GalPhi

open GlobalTheory.GalPhi in

theorem GlobalTheory.GalPhi.galPhi : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ g : ↥(GK K), (bk.ev bk.E * τ) ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * (Y.map WittVector.frobenius).map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) (bk.ev bk.E * τ) ^ N • (Y.map WittVector.frobenius * (F.ε g).map WittVector.frobenius) := by
  intro l _ K bk τ hτ N d ρ F Y hY g
  have h := congrArg (fun M => M.map (WittVector.frobenius : Ainf l →+* Ainf l)) (gal_ainf bk τ N d ρ F Y hY g)
  rw [Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_mul, Matrix.map_mul,
    map_pow, map_pow, ← σA_frobenius, hτ.1] at h
  have h1 : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (WittVector.frobenius : Ainf l →+* Ainf l) =
      (ρ g).map (algebraMap ℤ_[l] (Ainf l)) := by
    refine Matrix.ext fun i j => ?_; exact frobenius_algebraMap _
  have h2 : (Y.map (Per.σA (g : GQ l))).map (WittVector.frobenius : Ainf l →+* Ainf l) =
      (Y.map WittVector.frobenius).map (Per.σA (g : GQ l)) := by
    refine Matrix.ext fun i j => ?_; exact (σA_frobenius _ _).symm
  rw [h1, h2] at h
  exact h

end
