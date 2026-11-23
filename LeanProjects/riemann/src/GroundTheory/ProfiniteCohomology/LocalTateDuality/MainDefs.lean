import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormationAlt
import GroundTheory.ProfiniteCohomology.LocalTateDuality.EqZeroOfForallCupPairingZmodMulEqZeroLeft
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing
import GroundTheory.ProfiniteCohomology.CartierDual
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IntermediateField GroundTheory.LocalField

universe u

attribute [local instance 2000] Rep.hV2

section Top

variable (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]

theorem brauerInv_eq_localInv_top (y : galoisBrauerGroup K Ω) :
    brauerInv K Ω y = localInv K Ω ⊤
      ((cohomologyRes (galUnits.{0} K Ω) ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) 2).hom
        y) := by
  rw [localInv_apply]
  have : IsSepClosure (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) Ω :=
    ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K _ Ω⟩
  have : IsGalois (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) Ω :=
    IsGalois.tower_top_of_isGalois K _ Ω
  have hres : (openCohomologyIso (⊤ : OpenSubgroup Gal(Ω/K)) 2).hom.hom
      ((cohomologyRes (galUnits.{0} K Ω) ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) 2).hom
        y) =
      (brauerRes K (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) Ω).hom y := by
    rw [openCohomologyIso_hom, cohomologyRes_eq, ← ModuleCat.comp_apply,
      ← cohomologyMapAlong_comp, brauerRes_eq]
    congr 1
  have hrank :
      Module.finrank K (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) = 1 := by
    rw [← index_openSubgroup]
    exact Subgroup.index_top
  rw [hres, brauerInv_brauerRes, hrank, one_smul]

end Top

section SepClosure

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

def brauerInvOfIsSepClosure : galoisBrauerGroup K Ksep →+ QZ :=
  letI := algebraicValuativeRel K Ksep
  letI := algebraicTopology K Ksep
  haveI := algebraicTopology_isValuativeTopology K Ksep
  haveI := algebraicValuativeRel_valuativeExtension K Ksep
  brauerInv K Ksep

theorem brauerInvOfIsSepClosure_bijective :
    Function.Bijective (brauerInvOfIsSepClosure K Ksep) :=
  letI := algebraicValuativeRel K Ksep
  letI := algebraicTopology K Ksep
  haveI := algebraicTopology_isValuativeTopology K Ksep
  haveI := algebraicValuativeRel_valuativeExtension K Ksep
  brauerInv_bijective K Ksep

def brauerInvEquivOfIsSepClosure : galoisBrauerGroup K Ksep ≃+ QZ :=
  AddEquiv.ofBijective (brauerInvOfIsSepClosure K Ksep) (brauerInvOfIsSepClosure_bijective K Ksep)

@[simp]
theorem brauerInvEquivOfIsSepClosure_apply (y : galoisBrauerGroup K Ksep) :
    brauerInvEquivOfIsSepClosure K Ksep y = brauerInvOfIsSepClosure K Ksep y :=
  rfl

theorem brauerInvOfIsSepClosure_eq_inv_top (y : galoisBrauerGroup K Ksep) :
    brauerInvOfIsSepClosure K Ksep y = (localClassFormationOfIsSepClosure K Ksep).inv ⊤
      ((cohomologyRes (galUnits.{0} K Ksep)
        ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) 2).hom y) :=
  letI := algebraicValuativeRel K Ksep
  letI := algebraicTopology K Ksep
  haveI := algebraicTopology_isValuativeTopology K Ksep
  haveI := algebraicValuativeRel_valuativeExtension K Ksep
  brauerInv_eq_localInv_top K Ksep y

variable {K Ksep} {n : ℕ}

def localDualityHypotheses (hn : (n : K) ≠ 0) :
    DualityHypotheses n (galRootsOfUnity.{0} K Ksep n) where
  nonempty_addEquiv := nonempty_addEquiv_galRootsOfUnity hn
  finite_cohomology := finite_cohomology_galois_le_two K Ksep hn
  subsingleton_cohomology_three := subsingleton_cohomology_three_galois K Ksep hn
  t := localInvRootsOfUnity hn
  t_cores := localInvRootsOfUnity_cores hn
  isPerfectPairing := isPerfectPairing_localInvRootsOfUnity hn

theorem localDualityHypotheses_alt (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    (localDualityHypotheses (Ksep := Ksep) hn).t U = localInvRootsOfUnity hn U :=
  rfl

end SepClosure

section Bridge

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

def dualRepRootsOfUnityIso (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) (n : ℕ)
    (hM : ∀ m : M, n • m = 0) :
    dualRep (galRootsOfUnity.{u} K L n) M ≅ cartierDual K L M :=
  cartierDualIsoHomRootsOfUnityOfNsmul K L M n hM

variable {K L}

@[simp]
theorem dualRepRootsOfUnityIso_hom_apply (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) (n : ℕ)
    (hM : ∀ m : M, n • m = 0) (f : M →ₗ[ULift.{u} ℤ] galRootsOfUnity.{u} K L n) (m : M) :
    ((dualRepRootsOfUnityIso K L M n hM).hom.hom f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) m =
      (rootsOfUnityToUnits K L n).hom (f m) :=
  rfl

end Bridge

section Pairing

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

def localDualityPairing (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M] [Finite M]
    {r s : ℕ} (h : r + s = 2) :
    cohomology M r →+ cohomology (cartierDual K Ksep M) s →+ QZ :=
  (AddMonoidHom.compHom (brauerInvOfIsSepClosure K Ksep)).comp
    (bilinAddHom (cupPairing (cartierPairing K Ksep M) h))

variable {K Ksep}

theorem localDualityPairing_apply (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M] [Finite M]
    {r s : ℕ} (h : r + s = 2) (x : cohomology M r) (y : cohomology (cartierDual K Ksep M) s) :
    localDualityPairing K Ksep M h x y =
      brauerInvOfIsSepClosure K Ksep (cupPairing (cartierPairing K Ksep M) h x y) :=
  rfl

end Pairing

end GroundTheory.ProfCoh
