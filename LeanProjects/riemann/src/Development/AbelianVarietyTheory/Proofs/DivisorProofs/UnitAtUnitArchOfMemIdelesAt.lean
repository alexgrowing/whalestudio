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

namespace GlobalTheory.ThK.ConeEuler

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem val_idemUnit_eq (ε : AF F) (hε : ε * ε = ε) (l : (AE F E)ˣ) :
    (idemUnit E ε hε l : AE F E) = 1 + ε • ((l : AE F E) - 1) := by
  rw [val_idemUnit, smul_sub, sub_smul, one_smul]; abel

theorem idemUnit_eq_one_of_at {R : Type} [Zero R] {ev : AF F → R} (ε : AF F) (hε : ε * ε = ε) {l : (AE F E)ˣ}
    (hl : l ∈ idelesAt E ev) (h0 : ev ε = 0) : idemUnit E ε hε l = 1 :=
  Units.ext (by rw [val_idemUnit_eq, hl ε h0, add_zero, Units.val_one])

theorem idemUnit_eq_self_of_at {R : Type} [Zero R] {ev : AF F → R} (ε : AF F) (hε : ε * ε = ε) {l : (AE F E)ˣ}
    (hl : l ∈ idelesAt E ev) (h1 : ev (1 - ε) = 0) : idemUnit E ε hε l = l := by
  have h := hl (1 - ε) h1
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact Units.ext (by rw [val_idemUnit_eq, ← h]; abel)

theorem unitAt_unitArch_of_mem_idelesAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (l : (AE F E)ˣ) :
    (∀ v : Pl F, l ∈ idelesAt E (evFin F v) → unitAt E v l = l ∧ unitArch F E l = 1 ∧ ∀ w : Pl F, w ≠ v → unitAt E w l = 1) ∧
    (l ∈ idelesAt E (evI F) → unitArch F E l = l ∧ ∀ v : Pl F, unitAt E v l = 1) := by
  refine ⟨fun v hl => ⟨?_, ?_, fun w hw => ?_⟩, fun hl => ⟨?_, fun v => ?_⟩⟩
  · exact idemUnit_eq_self_of_at _ _ hl (by rw [map_sub, map_one, eFin, GlobalTheory.LatVac.evFin_liftV, sub_self])
  · exact idemUnit_eq_one_of_at _ _ hl (map_zero (evalV F v))
  · exact idemUnit_eq_one_of_at _ _ hl (evalV_singleFin_ne (Ne.symm hw) 1)
  · exact idemUnit_eq_self_of_at _ _ hl (by
      rw [GlobalTheory.ArchUniq.evI_eq_evIHom, map_sub, map_one, ← GlobalTheory.ArchUniq.evI_eq_evIHom, eInf, evI_realAd_one, sub_self])
  · exact idemUnit_eq_one_of_at _ _ hl (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))

end GlobalTheory.ThK.ConeEuler
