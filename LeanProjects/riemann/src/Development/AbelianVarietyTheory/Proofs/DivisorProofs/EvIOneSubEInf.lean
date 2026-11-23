import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

noncomputable section

namespace GlobalTheory.ThK.ConeEuler.SuppOne

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem evI_eFin (v : Pl F) : evI F (eFin v) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
  exact map_zero _

theorem evFin_eInf (v : Pl F) : evFin F v (eInf F) = 0 := by
  show evalV F v 0 = 0
  exact map_zero _

theorem evFin_eFin_ne {v w : Pl F} (hwv : w ≠ v) : evFin F v (eFin w) = 0 := by
  have h := GlobalTheory.LatVac.at_liftV w 1 (GlobalTheory.LatVac.liftV v 1) (by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (GlobalTheory.AdelicU.singleFin v 1) = 0
    exact GlobalTheory.AdelicU.evalV_singleFin_ne hwv 1)
  have := congrArg (evFin F v) h
  rw [smul_eq_mul, map_mul, GlobalTheory.LatVac.evFin_liftV, one_mul, map_zero] at this
  exact this

theorem evI_one_sub_eInf : evI F (1 - eInf F) = 0 := by
  rw [GlobalTheory.ArchUniq.evI_eq_evIHom, map_sub, map_one, ← GlobalTheory.ArchUniq.evI_eq_evIHom, eInf, evI_realAd_one, sub_self]

theorem idemU_eq_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : AF F} (hε : ε * ε = ε) (g : UA σ J)
    (h : ε • (mat g - 1) = 0) : idemU σ J ε hε g = 1 := by
  apply Subtype.ext; apply Units.ext
  change ε • mat g + (1 - ε) • 1 = mat (1 : UA σ J)
  rw [GlobalTheory.StabHaar.mat_one]
  rw [smul_sub, sub_eq_zero] at h
  rw [h, ← add_smul, add_sub_cancel, one_smul]

theorem idemU_eq_self {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : AF F} (hε : ε * ε = ε) (g : UA σ J)
    (h : (1 - ε) • (mat g - 1) = 0) : idemU σ J ε hε g = g := by
  apply Subtype.ext; apply Units.ext
  change ε • mat g + (1 - ε) • 1 = mat g
  rw [smul_sub, sub_eq_zero] at h
  rw [← h, ← add_smul, add_sub_cancel, one_smul]

theorem comp_of_supp (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (X : Spc F E n) (g : UA σ X.J) :
    (∀ v : Pl F, g ∈ UAt σ X (evFin F v) → compAt σ X.J v g = g ∧ compArch σ X.J g = 1 ∧
      ∀ w : Pl F, w ≠ v → compAt σ X.J w g = 1) ∧
    (g ∈ UAt σ X (evI F) → compArch σ X.J g = g ∧ ∀ v : Pl F, compAt σ X.J v g = 1) := by
  refine ⟨fun v hg => ⟨?_, ?_, fun w hw => ?_⟩, fun hg => ⟨?_, fun v => ?_⟩⟩
  · exact idemU_eq_self _ g (hg _ (by rw [map_sub, map_one, eFin, GlobalTheory.LatVac.evFin_liftV, sub_self]))
  · exact idemU_eq_one _ g (hg _ (evFin_eInf v))
  · exact idemU_eq_one _ g (hg _ (evFin_eFin_ne hw))
  · exact idemU_eq_self _ g (hg _ evI_one_sub_eInf)
  · exact idemU_eq_one _ g (hg _ (evI_eFin v))

end GlobalTheory.ThK.ConeEuler.SuppOne
