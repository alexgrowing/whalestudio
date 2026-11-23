import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDstOfIsSstStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAddFinrankLeFinrankInfComapSubIdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPairingDstDcrisFrobeniusFixedStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory

theorem finrank_dcris_phi_fixed_add_finrank_mon_le : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) + finrank ℚ_[l] ↥((Dst P ρ).map (monV P ℚ_[l] V)) ≤ finrank ℚ_[l] ↥(Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) := by
  intro l _ P AI T K V _ _ _ V' _ _ _ ρ ρ' m hD hS
  obtain ⟨B, h1, h2, h3⟩ := GlobalTheory.T.exists_pairing_Dst_Dcris_frobenius_fixed l P AI T K V V' ρ ρ' m hD hS
  haveI := GlobalTheory.T.finiteDimensional_Dst_of_isSst' l P K V ρ hS
  refine GlobalTheory.T.finrank_add_finrank_le_finrank_inf_comap_sub_id' ℚ_[l] _ _ (Dst P ρ) ((Dst P ρ).map (monV P ℚ_[l] V))
    ((l : ℚ_[l]) • phiV P ℚ_[l] V) B ?_ ?_ ?_ ?_ h3
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_Dst] at hx
    rw [mem_Dst]
    intro g
    rw [← Module.End.mul_apply, ← monV_stRep, Module.End.mul_apply, hx g]
  · intro x hx
    rw [mem_Dst] at hx ⊢
    intro g
    rw [LinearMap.smul_apply, map_smul, ← Module.End.mul_apply, ← phiV_stRep, Module.End.mul_apply,
      hx g]
  · rintro _ ⟨x, hx, rfl⟩ w
    exact h1 x hx w
  · intro x hx w
    exact h2 x hx w

end GlobalTheory
