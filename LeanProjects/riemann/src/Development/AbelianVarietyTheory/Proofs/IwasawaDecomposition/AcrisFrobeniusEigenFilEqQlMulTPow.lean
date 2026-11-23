import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TeichmullerTiltMinusOneDvdOfThetaFrobeniusZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFixedEqPadicIntStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelopeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusAcrisDecompositionMuPowerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFontaineTEqMulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariantStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.MemLoc.FixR

theorem step_abs {R A K : Type} [CommRing R] [CommRing A] [IsDomain A] [Field K]
    (i : R →+* A) (f : R →+* R) (φ : A →+* A) (Θ : A →+* K) (p : A) (hp : Θ p ≠ 0)
    (hφp : φ p = p) (hf : ∀ a, φ (i a) = i (f a))
    (μ : R) (hμ : ∀ n, Θ (i (f^[n] μ)) = 0)
    (hI : ∀ a : R, (∀ n, Θ (i (f^[n] a)) = 0) → μ ∣ a)
    (w : A) (m : ℕ) (hw : p * w = i μ ^ (m + 1))
    (himg : ∀ y, ∃ a z, φ y = i a + w * z)
    (t u : A) (hu : IsUnit u) (ht : t = i μ * u) (ht0 : t ≠ 0) (hφt : φ t = p * t)
    (r : ℕ) (x : A) (hx : φ x = p ^ (r + 1) * x) (hx0 : Θ x = 0) :
    ∃ x', p ^ (r + 2) * x = t * x' ∧ φ x' = p ^ r * x' := by
  have hit : ∀ n a, φ^[n] (i a) = i (f^[n] a) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro a; rw [Function.iterate_succ_apply, hf, ih, Function.iterate_succ_apply]
  have hpn : ∀ n, (φ ^ n) p = p := by
    intro n
    rw [RingHom.coe_pow]
    exact Function.iterate_fixed hφp n
  have hit' : ∀ n a, (φ ^ n) (i a) = i (f^[n] a) := by
    intro n a
    rw [RingHom.coe_pow]; exact hit n a
  have hxn : ∀ n, Θ ((φ ^ n) x) = 0 := by
    intro n
    induction n with
    | zero => simpa using hx0
    | succ n ih =>
      rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, hx]
      simp only [map_mul, ih, mul_zero]
  have hwn : ∀ n, Θ ((φ ^ n) w) = 0 := by
    intro n
    have := congrArg (fun y => Θ ((φ ^ n) y)) hw
    simp only [map_mul, map_pow, hpn, hit', hμ] at this
    simpa [hp] using this
  obtain ⟨a, z, haz⟩ := himg x
  obtain ⟨b, hb⟩ : μ ∣ a := by
    apply hI
    intro n
    have := congrArg (fun y => Θ ((φ ^ n) y)) (hx.symm.trans haz)
    simpa only [map_mul, map_add, hxn, hwn, hit', mul_zero, zero_mul, add_zero, eq_comm] using this
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hp0 : p ≠ 0 := fun h => hp (by rw [h, map_zero])
  have h1 : p ^ (r + 2) * x = t * (v * (p * i b + i μ ^ m * z)) := by
    have e := hx.symm.trans haz
    rw [hb, map_mul] at e
    rw [ht]
    linear_combination p * e + z * hw - (i μ * (p * i b + i μ ^ m * z)) * hv
  refine ⟨_, h1, ?_⟩
  set x' := v * (p * i b + i μ ^ m * z)
  have h2 := congrArg φ h1
  rw [map_mul, map_mul, map_pow, hφp, hx, hφt] at h2
  apply mul_left_cancel₀ (mul_ne_zero hp0 ht0)
  linear_combination p ^ (r + 1) * h1 - h2

variable {l : ℕ} [Fact l.Prime]

theorem alg_eq (a : Per.Ainf l) : algebraMap (Per.Ainf l) (Per.Acris l) a =
    algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
  GlobalTheory.RingIface.tower l a

theorem phi_nat (n : ℕ) : phiA l (n : Per.Acris l) = n := map_natCast _ _

theorem phi_alg (a : Per.Ainf l) : phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) =
    algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) := (GlobalTheory.CrisMaps.phiA_extends l).alg a

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem j_alg {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (a : Per.Ainf l) :
    j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [alg_eq, hj.on0]
  rfl

theorem theta_phi_mu (e : Per.Fl l) (he : e.untilt = 1) (n : ℕ) :
    Per.θ l ((Per.φA l)^[n] (mu e)) = 0 := by
  induction n generalizing e with
  | zero => simp [mu, he]
  | succ n ih =>
    have h : Per.φA l (mu e) = mu (e ^ l) := by
      simp only [mu, map_sub, map_one, GlobalTheory.RingIface.phiA_teich]
    rw [Function.iterate_succ_apply, h]
    exact ih _ (by rw [map_pow, he, one_pow])

theorem exists_w (e : Per.Fl l) (he : e.untilt = 1) : ∃ w : Per.Acris l,
    (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) := by
  obtain ⟨w, hw, -⟩ := GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope l e he
  have h : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) :=
    Subtype.ext (by simpa using hw)
  refine ⟨algebraMap (Per.Acris0 l) (Per.Acris l) w, ?_⟩
  rw [alg_eq, ← map_pow, ← h, map_mul, map_natCast]

theorem fil_div (C : Core l) (r : ℕ) (y : Per.BdRp l) (h : C.j C.t * y ∈ Per.FilP l (r + 1)) :
    y ∈ Per.FilP l r := by
  obtain ⟨hF, hreg, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l C.ε (GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C)
  obtain ⟨-, h1, h2, -⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  obtain ⟨-, hk, hun, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  rw [hF] at h h1 h2 ⊢
  obtain ⟨v, hv⟩ := h1
  have hvu : IsUnit v := by
    apply hun
    intro h0
    obtain ⟨c, hc⟩ := (hF _ _).1 ((hk v).1 h0)
    exact h2 ⟨c, by rw [hv, hc]; ring⟩
  obtain ⟨c, hc⟩ := h
  rw [← hvu.dvd_mul_left]
  refine ⟨c, sub_eq_zero.1 (hreg _ ?_)⟩
  rw [hv] at hc
  linear_combination hc

end GlobalTheory.MemLoc.FixR

namespace GlobalTheory.MemLoc
open FixR

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem fix_pow (l : ℕ) [Fact l.Prime] (C : Core l) (r : ℕ) (x : Per.Acris l)
    (hx : phiA l x = (l : Per.Acris l) ^ r * x) (hF : C.j x ∈ Per.FilP l r) :
    ∃ (z : ℤ_[l]) (k : ℕ), (l : Per.Acris l) ^ k * x =
      algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z) * C.t ^ r := by
  induction r generalizing x with
  | zero =>
    obtain ⟨z, hz⟩ := GlobalTheory.T.acris_frobenius_fixed_eq_padicInt l x (by simpa using hx)
    exact ⟨z, 0, by simpa using hz⟩
  | succ r ih =>
    have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
    haveI := (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).1
    haveI : IsDomain (Per.Acris l) := (GlobalTheory.T.acrisToBdRPlus_injective l C.j C.j_cris).isDomain C.j
    obtain ⟨hFil, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l C.ε he
    obtain ⟨-, hk, -, hth, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
    obtain ⟨w, hw⟩ := exists_w C.ε he.1
    obtain ⟨t, u, htl, hu, htu⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l C.ε he.1
    have htt : C.t = t := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l C.ε t he.1 htl).1 _ C.t_log
    have hΘ : ∀ a, ((Per.θD l).comp C.j) (algebraMap (Per.Ainf l) (Per.Acris l) a) =
        (Per.θ l a : ℂ_[l]) := fun a => by
      rw [RingHom.comp_apply, j_alg C.j_cris, hth]
    have hl2 : l - 1 = (l - 2) + 1 := by
      have := (Fact.out : l.Prime).two_le
      omega
    obtain ⟨x', h1, h2⟩ := step_abs (algebraMap (Per.Ainf l) (Per.Acris l)) (Per.φA l) (phiA l)
      ((Per.θD l).comp C.j) (l : Per.Acris l) (by rw [map_natCast]; exact GlobalTheory.RingBasics.p_ne_zero)
      (phi_nat l) (phi_alg (l := l)) (mu C.ε)
      (fun n => by rw [hΘ, theta_phi_mu _ he.1]; rfl)
      (fun a ha => GlobalTheory.T.teichmullerTiltMinusOne_dvd_of_theta_frobenius_zero l C.ε he a fun n => Subtype.ext ((hΘ _).symm.trans (ha n)))
      w (l - 2) (hl2 ▸ hw) (GlobalTheory.T.frobenius_acris_decomposition_mu_power l C.ε he w hw) C.t u hu (htt.trans htu)
      (fun h => (GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C).2.2.1 (by rw [h, map_zero]; exact zero_mem _))
      (GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul l C) r x hx
      ((hk _).2 ((hFil _ _).2 ((pow_dvd_pow _ (by omega)).trans ((hFil _ _).1 hF))))
    have h3 : C.j x' ∈ Per.FilP l r := by
      apply fil_div C
      rw [← map_mul, ← h1, map_mul]
      exact Ideal.mul_mem_left _ _ hF
    obtain ⟨z, k, hz⟩ := ih x' h2 h3
    exact ⟨z, k + (r + 2), by linear_combination (l : Per.Acris l) ^ k * h1 + C.t * hz⟩

end GlobalTheory.MemLoc
