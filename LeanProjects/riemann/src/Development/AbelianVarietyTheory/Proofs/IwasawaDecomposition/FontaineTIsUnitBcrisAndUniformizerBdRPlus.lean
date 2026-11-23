import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelopeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariantStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TFil

variable {l : ℕ} [Fact l.Prime]

theorem alg_factor (a : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) a =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
  GlobalTheory.RingIface.tower l a

theorem j_alg {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (a : Per.Ainf l) :
    j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [alg_factor, hj.on0]
  rfl

theorem mu_eq (e : Per.Fl l) :
    mu e = xi e * (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) - 1) := by
  rw [xi, geom_sum_mul, ← map_pow, mu]
  congr 2
  rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

theorem isUnit_mu {e : Per.Fl l} (he : IsEps e) :
    IsUnit (algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (mu e))) := by
  have h1 : e ≠ 1 := by
    rintro rfl
    exact he.2 (by rw [map_one, map_one])
  exact GlobalTheory.CrisLoc.unit_of_root l e he.1 h1

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem isUnit_l {e : Per.Fl l} (he : IsEps e) : IsUnit (l : Per.Bcris l) := by
  obtain ⟨w, hw, -⟩ := GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope l e he.1
  have h0 : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) := by
    apply Subtype.ext
    simpa using hw
  have h1 := congrArg (fun x => algebraMap (Per.Acris l) (Per.Bcris l)
    (algebraMap (Per.Acris0 l) (Per.Acris l) x)) h0
  simp only [map_mul, map_natCast, map_pow, ← alg_factor] at h1
  have h2 := (isUnit_mu he).pow (l - 1)
  rw [← h1] at h2
  exact isUnit_of_mul_isUnit_left h2

theorem isUnit_cofactor {e : Per.Fl l} (he : IsEps e) :
    IsUnit (aDp l (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) - 1)) := by
  obtain ⟨-, -, hu, hθ, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  apply hu
  rw [hθ, map_sub, map_one, WittVector.fontaineTheta_teichmuller]
  intro h
  apply he.2
  rw [← sub_eq_zero]
  exact Subtype.ext h

theorem fil_of_eq {e : Per.Fl l} (he : IsEps e) (y v : Per.BdRp l) (hv : IsUnit v)
    (hy : y = aDp l (xi e) * v) : y ∈ Per.FilP l 1 ∧ y ∉ Per.FilP l 2 := by
  obtain ⟨hF, hr, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  obtain ⟨-, hk, -, -, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  refine ⟨(hF 1 y).2 ⟨v, by rw [hy, pow_one]⟩, fun h => ?_⟩
  obtain ⟨c, hc⟩ := (hF 2 y).1 h
  have h1 : v - aDp l (xi e) * c = 0 := by
    apply hr
    rw [mul_sub, ← hy, hc]
    ring
  have h2 : v ∈ Per.FilP l 1 := (hF 1 v).2 ⟨c, by rw [pow_one]; exact sub_eq_zero.1 h1⟩
  exact (hv.map (Per.θD l)).ne_zero ((hk v).2 h2)

end GlobalTheory.MemLoc.TFil

namespace GlobalTheory.MemLoc
open TFil

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem core_t_unit_fil : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l,
    IsUnit (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ∧ C.j C.t ∈ Per.FilP l 1 ∧
      C.j C.t ∉ Per.FilP l 2 ∧ IsUnit (l : Per.Bcris l) := by
  intro l _ C
  have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
  obtain ⟨t, u, ht, hu, htu⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l C.ε he.1
  have h1 : t = C.t := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l C.ε C.t he.1 C.t_log).1 t ht
  rw [h1] at htu
  have h2 : C.j C.t = aDp l (xi C.ε) *
      (aDp l (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm C.ε) - 1) * C.j u) := by
    rw [htu, map_mul, j_alg C.j_cris, mu_eq, map_mul, mul_assoc]
  have h3 := fil_of_eq he _ _ ((isUnit_cofactor he).mul (hu.map C.j)) h2
  refine ⟨?_, h3.1, h3.2, isUnit_l he⟩
  rw [htu, map_mul]
  exact (isUnit_mu he).mul (hu.map _)

end GlobalTheory.MemLoc
