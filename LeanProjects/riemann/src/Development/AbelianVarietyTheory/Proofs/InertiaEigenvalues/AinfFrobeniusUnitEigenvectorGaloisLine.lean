import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFixedEqPadicInt
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.UnitLine

theorem exists_fixed {R : Type} [CommRing R] (φ σ : R →+* R) (h : ∀ a, φ (σ a) = σ (φ a)) (w c : R)
    (hw : IsUnit w) (hc : IsUnit c) (hσ : σ c = c) (hφ : φ w = c * w) :
    ∃ a, φ a = a ∧ σ w = a * w := by
  obtain ⟨v, hv⟩ := hw.exists_right_inv
  have e : σ w = σ w * v * w := by linear_combination (-σ w) * hv
  refine ⟨σ w * v, ?_, e⟩
  have h1 := congrArg φ e
  rw [map_mul φ _ w, h, hφ, map_mul σ, hσ] at h1
  apply (hc.mul hw).mul_right_cancel
  rw [← h1]
  linear_combination (-c * σ w) * hv

theorem sigma_unit_eigen : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l) (u : ℤ_[l]ˣ), IsUnit w → Per.φA l w = Per.zA l u * w → ∀ g : GQ l, ∃ z : ℤ_[l], Per.σB g (Per.aB l w) = Per.zB l z * Per.aB l w := by
  intro l _ w u hw hφ g
  obtain ⟨-, -, -, -, -, h6, -, h8, -⟩ := ActLaws.act_laws l
  obtain ⟨a, ha, e⟩ := exists_fixed (Per.φA l) (Per.σA g) (ActLaws.φA_σA g) w (Per.zA l u) hw
    (u.isUnit.map _) (h8 g u) hφ
  obtain ⟨z, hz⟩ := phi_fixed_eq_padicInt l (algebraMap (Per.Ainf l) (Per.Acris l) a)
    ((PhiFix.phiA_alg l a).trans (congrArg _ ha))
  have hb : Per.aB l a = Per.zB l z := by
    rw [GlobalTheory.RingIface.zB_eq_aB_zA, GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.RingIface.aB_eq_alg, hz]
  exact ⟨z, by rw [h6, e, map_mul, hb]⟩

end GlobalTheory.UnitLine
