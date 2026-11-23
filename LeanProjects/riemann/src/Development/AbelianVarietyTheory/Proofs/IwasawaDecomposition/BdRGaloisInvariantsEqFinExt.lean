import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CLTateInvariantsFiniteExtensionMemStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApproxStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusSimpleRootsSectionUniqueEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariantStatement

namespace GlobalTheory.MemLoc.InvDR
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

section Abstract
variable {R F G : Type} [CommRing R] [IsDomain R] [Field F]

theorem inv_ker_eq_zero (θ : R →+* F) (σ : G → R →+* R) (τ : G → F →+* F) (c : G → R) (t : R) (ht : t ≠ 0)
    (hker : ∀ y, θ y = 0 → t ∣ y) (hsep : ∀ y, (∀ n : ℕ, t ^ n ∣ y) → y = 0)
    (hθ : ∀ g y, θ (σ g y) = τ g (θ y)) (hσt : ∀ g, σ g t = c g * t)
    (tate : ∀ (i : ℤ) (x : F), i ≠ 0 → (∀ g, τ g x * θ (c g) ^ i = x) → x = 0)
    (z : R) (hz : θ z = 0) (hinv : ∀ g, σ g z = z) : z = 0 := by
  have key : ∀ m : ℕ, t ^ (m + 1) ∣ z := by
    intro m
    induction m with
    | zero => simpa using hker z hz
    | succ m ih =>
      obtain ⟨w, hw⟩ := ih
      have h1 : ∀ g, σ g w * c g ^ (m + 1) = w := by
        intro g
        have h := hinv g
        rw [hw, map_mul, map_pow, hσt] at h
        apply mul_left_cancel₀ (pow_ne_zero (m + 1) ht)
        rw [← h]
        ring
      have h2 : θ w = 0 := by
        refine tate ((m + 1 : ℕ) : ℤ) _ (by omega) fun g => ?_
        rw [zpow_natCast, ← hθ, ← map_pow, ← map_mul, h1]
      obtain ⟨v, hv⟩ := hker w h2
      exact ⟨v, by rw [hw, hv]; ring⟩
  exact hsep z fun n => (pow_dvd_pow t (Nat.le_succ n)).trans (key n)

theorem eigen_eq (θ : R →+* F) (σ : G → R →+* R) (τ : G → F →+* F) (c : G → R) (t : R) (ht : t ≠ 0)
    (hker : ∀ y, θ y = 0 → t ∣ y) (hc : ∀ g, θ (c g) ≠ 0)
    (hθ : ∀ g y, θ (σ g y) = τ g (θ y)) (hσt : ∀ g, σ g t = c g * t)
    (tate : ∀ (i : ℤ) (x : F), i ≠ 0 → (∀ g, τ g x * θ (c g) ^ i = x) → x = 0)
    (n : ℕ) : ∀ y : R, (∀ g, σ g y = c g ^ n * y) → ∃ w, y = t ^ n * w ∧ ∀ g, σ g w = w := by
  induction n with
  | zero => intro y hy; exact ⟨y, by simp, fun g => by simpa using hy g⟩
  | succ n ih =>
    intro y hy
    have h2 : θ y = 0 := by
      refine tate (-((n + 1 : ℕ) : ℤ)) _ (by omega) fun g => ?_
      rw [zpow_neg, zpow_natCast, ← hθ, hy, map_mul, map_pow]
      have := pow_ne_zero (n + 1) (hc g)
      field_simp
    obtain ⟨v, hv⟩ := hker y h2
    obtain ⟨w, hw, hw'⟩ := ih v fun g => by
      have h := hy g
      rw [hv, map_mul, hσt] at h
      have hc0 : c g ≠ 0 := fun h0 => hc g (by rw [h0, map_zero])
      apply mul_left_cancel₀ (mul_ne_zero hc0 ht)
      rw [h]
      ring
    exact ⟨w, by rw [hv, hw]; ring, hw'⟩

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem j_alg (C : Core l) (a : Per.Ainf l) :
    C.j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [GlobalTheory.RingIface.tower, C.j_cris.on0, aDp, RingHom.comp_apply, SubalgebraClass.coe_algebraMap]

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem invariants_BdR (l : ℕ) [Fact l.Prime] (C : Core l) (K : FinExt l) (b : Per.BdR l)
    (hb : ∀ g ∈ GK K, Per.σD g b = b) :
    ∃ y ∈ K.1, algebraMap (Per.BdRp l) (Per.BdR l) (C.o y) = b := by
  have he := GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨hdom, hinj, -, hfrac⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨hfil, hreg, hcompl, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l C.ε he
  obtain ⟨-, hker, hunit, -, hθ⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  obtain ⟨-, ht1, ht2, -⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  obtain ⟨-, -, hoσ⟩ := GlobalTheory.T.bdRPlus_simple_roots_section_unique_equivariant l C.o C.o_sec
  obtain ⟨-, hjσ, -⟩ := GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris
  have hσD := (GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1
  have hact := GlobalTheory.T.acrisGaloisAction_fontaine_t_eq_cyclotomic l C
  have htate := GlobalTheory.T.eq_zero_of_tateTwist_invariant_finiteExtension l C K
  have hast := GlobalTheory.T.cLTate_invariants_finiteExtension_mem l K
  generalize hx : aDp l (xi C.ε) = x at *
  obtain ⟨n, y0, hy0⟩ := hfrac C.ε he b
  rw [hx] at hy0
  generalize htt : C.j C.t = t at *
  obtain ⟨u, hu⟩ := (hfil 1 t).1 ht1
  rw [pow_one] at hu
  have huu : IsUnit u := by
    refine hunit u fun h0 => ht2 ?_
    obtain ⟨v, hv⟩ := (hfil 1 u).1 ((hker u).1 h0)
    exact (hfil 2 t).2 ⟨v, by rw [hu, hv]; ring⟩
  have ht0 : t ≠ 0 := fun h0 => ht2 (h0 ▸ zero_mem _)
  have htx : t ∣ x := by rw [hu]; exact huu.mul_right_dvd.2 dvd_rfl
  have hxt : x ∣ t := ⟨u, hu⟩
  let c : ↥(GK K) → Per.BdRp l := fun g => C.o (algebraMap ℚ_[l] (Om l) ((C.χ g.1 : ℤ_[l]) : ℚ_[l]))
  have hθc : ∀ g, Per.θD l (c g) = algebraMap ℚ_[l] ℂ_[l] ((C.χ g.1 : ℤ_[l]) : ℚ_[l]) := fun g =>
    (C.o_sec.th _).trans rfl
  have hc : ∀ g, Per.θD l (c g) ≠ 0 := fun g => by
    rw [hθc, map_ne_zero]
    exact fun h => (C.χ g.1).ne_zero (PadicInt.coe_eq_zero.1 h)
  have hσt : ∀ g : ↥(GK K), Per.σDp g.1 t = c g * t := fun g => by
    rw [← htt, ← hjσ, hact, map_mul, j_alg, ← C.o_sec.z]
  have hker' : ∀ y, Per.θD l y = 0 → t ∣ y := fun y hy =>
    htx.trans (by simpa using (hfil 1 y).1 ((hker y).1 hy))
  have hsep : ∀ y : Per.BdRp l, (∀ n : ℕ, t ^ n ∣ y) → y = 0 := fun y hy => by
    refine hcompl.toIsHausdorff.haus y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (pow_dvd_pow_of_dvd hxt n).trans (hy n)
  have tate : ∀ (i : ℤ) (x : ℂ_[l]), i ≠ 0 →
      (∀ g : ↥(GK K), Per.σC g.1 x * Per.θD l (c g) ^ i = x) → x = 0 := fun i x hi h =>
    htate i x hi fun g hg => by simpa only [hθc] using h ⟨g, hg⟩
  have hy : b * algebraMap (Per.BdRp l) (Per.BdR l) t ^ n =
      algebraMap (Per.BdRp l) (Per.BdR l) (y0 * u ^ n) := by
    rw [hu, map_mul, map_mul, map_pow, ← hy0]
    ring
  generalize y0 * u ^ n = y at hy
  have hyσ : ∀ g : ↥(GK K), Per.σDp g.1 y = c g ^ n * y := fun g => by
    apply hinj
    rw [← hσD, ← hy, map_mul, map_pow, hσD, hσt, hb g.1 g.2, map_mul, map_mul, map_pow, ← hy]
    ring
  obtain ⟨w, hw, hw'⟩ := eigen_eq (Per.θD l) (fun g : ↥(GK K) => Per.σDp g.1) (fun g => Per.σC g.1) c t ht0
    hker' hc (fun g y => hθ g.1 y) hσt tate n y hyσ
  obtain ⟨k, hk, hkθ⟩ := hast (Per.θD l w) fun g hg => by rw [← hθ, hw' ⟨g, hg⟩]
  have hz : w - C.o k = 0 := by
    refine inv_ker_eq_zero (Per.θD l) (fun g : ↥(GK K) => Per.σDp g.1) (fun g => Per.σC g.1) c t ht0
      hker' hsep (fun g y => hθ g.1 y) hσt tate _ ?_ fun g => ?_
    · rw [map_sub, C.o_sec.th, hkθ, sub_self]
    · have hg : g.1 k = k := g.2 ⟨k, hk⟩
      rw [map_sub, hw' g, hoσ, hg]
  refine ⟨k, hk, ?_⟩
  rw [← sub_eq_zero.1 hz]
  haveI : IsDomain (Per.BdR l) := (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.2.1.isDomain
  have ht' : algebraMap (Per.BdRp l) (Per.BdR l) t ^ n ≠ 0 :=
    pow_ne_zero n ((map_ne_zero_iff _ hinj).2 ht0)
  apply mul_right_cancel₀ ht'
  rw [hy, hw, map_mul, map_pow, mul_comm]

end GlobalTheory.MemLoc.InvDR
