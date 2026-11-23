import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelope
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffGaloisTilt
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.Per

export GlobalTheory.MemLoc (Core)

variable {l : ℕ} [Fact l.Prime]

def IsStd (P : LocPrime l) (AI : LocAinf l P) : Prop := Nonempty (LocTied l P AI)

theorem IsStd.of_tied {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) : IsStd P AI := ⟨T⟩

end GlobalTheory.Per

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem locAinf_actC {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (x : ℂ_[l]) :
    AI.actC g x = Per.σC g x := by
  have hc : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hc (GlobalTheory.RingIface.sigC_cont l g)
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem locAinf_actT {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (x : OCb l) :
    AI.actT g x = Per.σF g x := by
  refine Perfection.ext fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  obtain ⟨y₁, h₁, e₁⟩ := AI.actT_coeff g x n y hy.symm
  obtain ⟨y₂, h₂, e₂⟩ := coeff_galois_tilt l g x n y hy.symm
  have : y₁ = y₂ := Subtype.ext (by rw [h₁, h₂, locAinf_actC])
  exact e₁.trans (this ▸ e₂.symm)

theorem locAinf_actW {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (a : Ainf l) :
    AI.actW g a = Per.σA g a :=
  WittVector.ext fun n => (locAinf_actT AI g (a.coeff n)).trans (GlobalTheory.RingIface.sigA_coeff l g a n).symm

theorem locAinf_xi {P : LocPrime l} (AI : LocAinf l P) : AI.ξ = xi AI.ε := rfl

theorem locAinf_mu {P : LocPrime l} (AI : LocAinf l P) : AI.μ = mu AI.ε := rfl

variable (l)

theorem isUnit_l_BdRp : IsUnit ((l : ℕ) : Per.BdRp l) := by
  have h := (GlobalTheory.RingBasics.isUnit_l l).map (algebraMap (Per.AinfP l) (Per.BdRp l))
  rwa [map_natCast] at h

theorem isUnit_l_Bcris : IsUnit ((l : ℕ) : Per.Bcris l) := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hne : e ≠ 1 := by
    rintro rfl
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    simp [rootT]
  obtain ⟨w, hw, -⟩ := exists_mu_pow_div l e he
  have hw' : ((l : ℕ) : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) :=
    Subtype.ext (by simpa using hw)
  have hm : IsUnit (((algebraMap (Per.Acris l) (Per.Bcris l)).comp (algebraMap (Per.Acris0 l) (Per.Acris l)))
      (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e))) := by
    rw [RingHom.comp_apply, ← GlobalTheory.RingIface.tower]
    exact GlobalTheory.CrisLoc.unit_of_root l e he hne
  have h2 := congrArg
    ((algebraMap (Per.Acris l) (Per.Bcris l)).comp (algebraMap (Per.Acris0 l) (Per.Acris l))) hw'
  rw [map_mul, map_natCast, map_pow] at h2
  exact isUnit_of_mul_isUnit_left (h2 ▸ hm.pow (l - 1))

def BcrisP : Type := Localization.Away ((l : ℕ) : Per.Acris l)

instance : CommRing (BcrisP l) := inferInstanceAs (CommRing (Localization.Away ((l : ℕ) : Per.Acris l)))

instance : Algebra (Per.Acris l) (BcrisP l) :=
  inferInstanceAs (Algebra (Per.Acris l) (Localization.Away ((l : ℕ) : Per.Acris l)))

instance : IsLocalization.Away ((l : ℕ) : Per.Acris l) (BcrisP l) :=
  inferInstanceAs (IsLocalization.Away _ (Localization.Away ((l : ℕ) : Per.Acris l)))

variable {l} in

def plusLift {S : Type} [CommRing S] (f : Per.Acris l →+* S) (h : IsUnit ((l : ℕ) : S)) : BcrisP l →+* S :=
  IsLocalization.Away.lift ((l : ℕ) : Per.Acris l) (g := f) (by rwa [map_natCast])

variable {l} in

theorem plusLift_alg {S : Type} [CommRing S] (f : Per.Acris l →+* S) (h : IsUnit ((l : ℕ) : S))
    (x : Per.Acris l) : plusLift f h (algebraMap _ _ x) = f x :=
  IsLocalization.Away.lift_eq _ _ x

theorem isUnit_l_BcrisP : IsUnit ((l : ℕ) : BcrisP l) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := BcrisP l) ((l : ℕ) : Per.Acris l)
  rwa [map_natCast] at h

def plusToB : BcrisP l →+* Per.Bcris l :=
  plusLift (algebraMap (Per.Acris l) (Per.Bcris l)) (isUnit_l_Bcris l)

def phiP : BcrisP l →+* BcrisP l :=
  plusLift ((algebraMap (Per.Acris l) (BcrisP l)).comp (phiA l)) (isUnit_l_BcrisP l)

variable {l}

def sigP (g : Per.Gq l) : BcrisP l →+* BcrisP l :=
  plusLift ((algebraMap (Per.Acris l) (BcrisP l)).comp (sigA g)) (isUnit_l_BcrisP l)

theorem plusToB_alg (x : Per.Acris l) :
    plusToB l (algebraMap _ _ x) = algebraMap (Per.Acris l) (Per.Bcris l) x := plusLift_alg _ _ x

theorem phiP_alg (x : Per.Acris l) : phiP l (algebraMap _ _ x) = algebraMap _ _ (phiA l x) :=
  plusLift_alg _ _ x

theorem sigP_alg (g : Per.Gq l) (x : Per.Acris l) : sigP g (algebraMap _ _ x) = algebraMap _ _ (sigA g x) :=
  plusLift_alg _ _ x

theorem plus_ext {S : Type} [CommRing S] {f f' : BcrisP l →+* S}
    (h : ∀ x : Per.Acris l, f (algebraMap _ _ x) = f' (algebraMap _ _ x)) : f = f' :=
  IsLocalization.ringHom_ext (Submonoid.powers ((l : ℕ) : Per.Acris l)) (RingHom.ext h)

theorem plusToB_phi (x : BcrisP l) : plusToB l (phiP l x) = Per.φB l (plusToB l x) :=
  RingHom.congr_fun (plus_ext (f := (plusToB l).comp (phiP l)) (f' := (Per.φB l).comp (plusToB l)) fun y => by
    rw [RingHom.comp_apply, RingHom.comp_apply, phiP_alg, plusToB_alg, plusToB_alg]
    exact ((ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.2 y).symm) x

theorem plusToB_sig (g : Per.Gq l) (x : BcrisP l) : plusToB l (sigP g x) = Per.σB g (plusToB l x) :=
  RingHom.congr_fun (plus_ext (f := (plusToB l).comp (sigP g)) (f' := (Per.σB g).comp (plusToB l)) fun y => by
    rw [RingHom.comp_apply, RingHom.comp_apply, sigP_alg, plusToB_alg, plusToB_alg]
    exact ((ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1 g y).symm) x

namespace Core

variable (C : Core l)

def jP : BcrisP l →+* Per.BdRp l := plusLift C.j (isUnit_l_BdRp l)

theorem jP_alg (x : Per.Acris l) : C.jP (algebraMap _ _ x) = C.j x := plusLift_alg _ _ x

theorem ι_plusToB (x : BcrisP l) :
    C.ι (plusToB l x) = algebraMap (Per.BdRp l) (Per.BdR l) (C.jP x) :=
  RingHom.congr_fun (plus_ext (f := C.ι.comp (plusToB l))
    (f' := (algebraMap (Per.BdRp l) (Per.BdR l)).comp C.jP) fun y => by
      rw [RingHom.comp_apply, RingHom.comp_apply, plusToB_alg, jP_alg, C.ι_j]) x

def oD : Om l →+* Per.BdR l := (algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o

def qB : ℚ_[l] →+* Per.Bcris l := C.u.comp (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))

def tB : Per.Bcris l := algebraMap (Per.Acris l) (Per.Bcris l) C.t

theorem ker_theta : RingHom.ker (Per.θ l) = Ideal.span {xi C.ε} := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact theta_eq_zero_iff_xi_dvd l C.ε (core_isEps l C) a

end Core

variable (l) in

theorem acris_torsionFree_complete : (∀ x : Per.Acris l, ((l : ℕ) : Per.Acris l) * x = 0 → x = 0) ∧
    IsAdicComplete (Ideal.span {((l : ℕ) : Per.Acris l)}) (Per.Acris l) :=
  ⟨(acris_basic l).2.1, (acris_basic l).1⟩

variable (l) in

theorem thetaD_onto_ker : Function.Surjective (Per.θD l) ∧ RingHom.ker (Per.θD l) = Per.FilP l 1 :=
  ⟨(thetaD_props l).1, Ideal.ext fun y => (thetaD_props l).2.1 y⟩

namespace Core

variable (C : Core l)

def DVR : Prop :=
  ∃ _ : IsDomain (Per.BdRp l), ∃ _ : IsDiscreteValuationRing (Per.BdRp l),
    IsLocalRing.maximalIdeal (Per.BdRp l) = Ideal.span {C.j C.t} ∧
    IsLocalRing.maximalIdeal (Per.BdRp l) = RingHom.ker (Per.θD l) ∧
    IsAdicComplete (IsLocalRing.maximalIdeal (Per.BdRp l)) (Per.BdRp l) ∧
    (∀ n : ℕ, Per.FilP l n = Ideal.span {C.j C.t ^ n}) ∧
    IsFractionRing (Per.BdRp l) (Per.BdR l)

def AwayT : Prop := IsLocalization.Away C.t (Per.Bcris l)

def PlusAwayT : Prop :=
  letI := (plusToB l).toAlgebra
  IsLocalization.Away (algebraMap (Per.Acris l) (BcrisP l) C.t) (Per.Bcris l)

def PlusInj : Prop := Function.Injective C.jP

def InvdR : Prop := ∀ (K : FinExt l) (b : Per.BdR l), (∀ g ∈ GK K, Per.σD g b = b) → ∃ x ∈ K.1, C.oD x = b

def InvB : Prop := ∀ (K : FinExt l) (b : Per.Bcris l), (∀ g ∈ GK K, Per.σB g b = b) →
  ∃ x : ↥(MaximalUnramifiedExtension l), (x : Om l) ∈ K.1 ∧ C.u x = b

def PhiInj (_C : Core l) : Prop := Function.Injective (Per.φB l)

def IotaInj : Prop := Function.Injective C.ι

def TensorInj : Prop := ∀ (m : ℕ) (x : Fin m → Om l), LinearIndependent ↥(MaximalUnramifiedExtension l) x →
  ∀ b : Fin m → Per.Bcris l, ∑ i, C.oD (x i) * C.ι (b i) = 0 → ∀ i, b i = 0

def Fund : Prop := ∀ b : Per.Bcris l, Per.φB l b = b → C.ι b ∈ Per.FilD l 0 → ∃ x : ℚ_[l], C.qB x = b

def FundOnto : Prop := ∀ w : Per.BdR l, ∃ b : Per.Bcris l, Per.φB l b = b ∧ C.ι b - w ∈ Per.FilD l 0

def OneSubPhiOnto (_C : Core l) : Prop := ∀ y : Per.Bcris l, ∃ x : Per.Bcris l, x - Per.φB l x = y

def Regular : Prop := ∀ (K : FinExt l) (b : Per.Bcris l), b ≠ 0 →
  (∀ g ∈ GK K, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) → IsUnit b

end Core

structure Fits {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (C : Core l) : Prop where

  ζ : C.ζ = P.ζQ

  ε : C.ε = AI.ε

  o : ∀ x : Om l, T.eD (algebraMap (Om l) P.R.BdR x) = C.oD x

  ι : ∀ b : P.R.B, T.eD (P.ιB b) = C.ι (T.eB b)

  u : ∀ c : ↥(MaximalUnramifiedExtension l), T.eB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = C.u c

  t : T.eB P.tB = C.tB

  χ : ∀ g : GQ l, ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((C.χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])

  σ : ∀ (K : FinExt l) (x : ↥(K0 K)) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) = (x : Om l) →
    (((P.PD K).σ x : ↥(K0 K)) : Om l) = ((C.σ c : ↥(MaximalUnramifiedExtension l)) : Om l)

example (C : Core l) : Per.θ l (xi C.ε) = 0 :=
  (theta_eq_zero_iff_xi_dvd l C.ε (core_isEps l C) _).2 dvd_rfl

example (C : Core l) : Nontrivial (BcrisP l) := ((Per.θD l).comp C.jP).domain_nontrivial

example (C : Core l) (x : ℚ_[l]) : C.ι (C.qB x) = C.oD (algebraMap ℚ_[l] (Om l) x) := C.ι_u _

example (C : Core l) (x : ℚ_[l]) : C.ι (C.qB x) ∈ Per.FilD l 0 := by
  rw [show C.ι (C.qB x) = _ from C.ι_u _]
  exact GlobalTheory.RingIface.alg_mem_FilD_zero l _

end GlobalTheory.MemLoc
