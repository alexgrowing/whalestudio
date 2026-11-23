import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEisensteinPowSmulMonodromyMemBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealPowerMembershipDivisibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinModuleTensorBdRPlusEqLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyImageMemBdRplusLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.NgalENM

theorem EN_mem_Man : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ m ∈ P.M, P.EN m ∈ P.Man := by
  intro hB l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I jB Pl AI hS hC hH m hm
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_eisensteinPow_smul_monodromy_mem_breuilKisin _ _ l e a ι P
  have hv := hn m hm
  obtain ⟨jD, hjD⟩ := GlobalTheory.T.kisinModule_tensor_bdRPlus_eq_lattice l a e _ _ (thetaW a LL) ϖ ι P T I
  let w : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e := fun τ i =>
    toHat _ _ l e ⟨(E ↥LL.1 l e ^ n • P.EN m) τ i, mem_tot.1 hv τ i⟩
  have hw : ∀ τ i, algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e) (w τ i) =
      hat ↥(OL LL) l e ((E ↥LL.1 l e ^ n • P.EN m) τ i) := fun τ i => (hat_coe_Rpi l e _).symm
  clear_value w
  have h3 := GlobalTheory.T.monodromy_image_mem_BdRplus_lattice hB l a e ϖ LL hl ι P T I jB Pl AI hS hC hH jD hjD m hm n hv w hw
  choose y hy using fun i => GlobalTheory.T.ideal_power_membership_divisible l a e _ _ (thetaW a LL) ϖ n (fun τ => w τ i) (h3 i)
  have hE : P.EN m ∈ P.Mext (RpiE ↥(OL LL) ↥LL.1 l e) := P.mem_Mext_invE_of_mem_divE hv
  rw [← P.hatTot_mem_Mhat_iff hE, P.mem_Mhat]
  intro τ i
  refine ⟨y i τ, ?_⟩
  have h1 := congrFun (hy i) τ
  have h2 := hw τ i
  have h4 := hat_E_pow_mul (O := ↥(OL LL)) l e n (mem_tot.1 hE τ i)

  have h1' : w τ i = Ehat ↥(OL LL) ↥LL.1 l e ^ n * y i τ := by rw [h1]; rfl
  have h5 : (E ↥LL.1 l e ^ n • P.EN m) τ i = E ↥LL.1 l e ^ n * P.EN m τ i := rfl
  have h7 := ((congrArg (algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e)) h1').symm.trans h2).trans
    ((congrArg (hat ↥(OL LL) l e) h5).trans h4)
  have h8 := (map_mul (algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e)) _ _).symm.trans h7
  have hu : IsUnit (algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e ^ n)) := by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (Ehat ↥(OL LL) ↥LL.1 l e)).pow n
  exact hu.mul_left_cancel h8

end GlobalTheory.NgalENM
