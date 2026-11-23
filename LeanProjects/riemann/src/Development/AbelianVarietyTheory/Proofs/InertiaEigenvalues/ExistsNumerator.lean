import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandard

set_option autoImplicit false

namespace GlobalTheory.ScalarUnit

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts
open scoped nonZeroDivisors

section Ideals

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem smul_eq_idlE_mul (J : Ideal (𝓞 E)) (M : Submodule (𝓞 E) E) : J • M = idlE J * M := by
  unfold idlE
  apply le_antisymm
  · refine Submodule.smul_le.mpr fun r hr m hm => ?_
    rw [Algebra.smul_def]
    exact Submodule.mul_mem_mul (Submodule.mem_map_of_mem hr) hm
  · refine Submodule.mul_le.mpr fun x hx m hm => ?_
    obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.mp hx
    rw [Algebra.linearMap_apply, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hr hm

omit [NumberField E] in
theorem idlE_mul (I J : Ideal (𝓞 E)) : idlE (I * J) = idlE I * idlE J := IsLocalization.coeSubmodule_mul E I J

theorem idlE_cancel {G : Ideal (𝓞 E)} (hG : G ≠ ⊥) {X Y : Submodule (𝓞 E) E} (h : idlE G * X = idlE G * Y) :
    X = Y := by
  have hG' : (G : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hG
  have e : idlE G = ((G : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := rfl
  have key : ∀ Z : Submodule (𝓞 E) E,
      (((G : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) *
        (idlE G * Z) = Z := by
    intro Z
    rw [e, ← mul_assoc, ← FractionalIdeal.coe_mul, inv_mul_cancel₀ hG', FractionalIdeal.coe_one, one_mul]
  rw [← key X, h, key Y]

theorem index_coprime {n p : ℕ} (hp : p.Prime) (Λ : GenLat E n) (h : Λ.TrivAt p)
    (h0 : (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ≠ 0) :
    Nat.Coprime (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index p := by
  obtain ⟨k, hk, hk1, -⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero h0
  let _ := Fintype.ofFinite (Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup)
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have hdvd' : p ∣ Fintype.card
      (Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup) := by
    rw [← Nat.card_eq_fintype_card]; exact hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hdvd'
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hmem : k • y ∈ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup := by
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]
    have hc : ((k • y : Λ.La.toAddSubgroup) : Fin n → E) = (k : 𝓞 E) • (y : Fin n → E) := by
      rw [Nat.cast_smul_eq_nsmul]
      rfl
    rw [hc]
    have h1 : (k : 𝓞 E) • (y : Fin n → E) ∈ Ideal.span {(k : 𝓞 E)} • Λ.La :=
      Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) y.2
    show (k : 𝓞 E) • (y : Fin n → E) ∈ Λ.La ⊓ stdLat E n
    exact Submodule.mem_inf.mpr ⟨Λ.La.smul_mem _ y.2, hk1 h1⟩
  have hz : k • (QuotientAddGroup.mk y :
      Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup) = 0 := by
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hmem
  have hpk : p ∣ k := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero hz
  exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hk.symm hpk)

theorem val_natCast {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {p a : ℕ}
    (hp : (p : 𝓞 K) ∈ la.asIdeal) (h : Nat.Coprime a p) : la.valuation K (a : K) = 1 := by
  have hnot : (a : 𝓞 K) ∉ la.asIdeal := by
    intro ha
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr h).map (Int.castRingHom (𝓞 K))
    have huv' : u * (a : 𝓞 K) + v * (p : 𝓞 K) = 1 := by simpa using huv
    apply la.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← huv']
    exact la.asIdeal.add_mem (la.asIdeal.mul_mem_left u ha) (la.asIdeal.mul_mem_left v hp)
  rw [← map_natCast (algebraMap (𝓞 K) K) a]
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (v := la) (K := K)).mpr hnot

variable [IsCMField E]

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem map_bar_bar (H : Host E) (J : Ideal (𝓞 E)) :
    (J.map (H.bar : 𝓞 E →+* 𝓞 E)).map (H.bar : 𝓞 E →+* 𝓞 E) = J := by
  rw [Ideal.map_map]
  have hid : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _ :=
    RingHom.ext fun a => bar_bar H a
  rw [hid, Ideal.map_id]

theorem conjI_eq (H : Host E) (J : Ideal (𝓞 E)) : GlobalTheory.SW.conjI J = J.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  unfold GlobalTheory.SW.conjI
  rw [Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, hab⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    exact (H.bar_eq b).trans hab.symm
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, H.bar_eq b⟩

theorem exists_numerator (H : Host E) {n : ℕ} (Λ : GenLat E n) (h : Λ.Unimod) :
    (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ≠ 0 ∧
    ∃ cc : Ideal (𝓞 E), cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧
      Submodule.span (𝓞 E) (detSet Λ.La) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc ∧
      (((Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℕ) : 𝓞 E) ∈ cc := by
  obtain ⟨J, hJ0, hJn, hJd, hJc, -⟩ := GlobalTheory.DetIdeal.detIdeal_selfDual E n Λ h
  refine ⟨?_, ?_⟩
  · rw [← hJn]
    exact fun h0 => hJ0 (Ideal.absNorm_eq_zero_iff.mp h0)
  have hrel : idlE J * Submodule.span (𝓞 E) (detSet Λ.La) = idlE (J.map (H.bar : 𝓞 E →+* 𝓞 E)) := by
    rw [← smul_eq_idlE_mul, ← hJd, hJc, conjI_eq H]
    rfl
  obtain ⟨A, hA⟩ : J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E) ∣ J := Ideal.dvd_iff_le.mpr le_sup_left
  have hG0 : J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := fun h0 => hJ0 (eq_bot_iff.mpr (h0 ▸ le_sup_left))
  have hGbar : (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)).map (H.bar : 𝓞 E →+* 𝓞 E) =
      J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [Ideal.map_sup, map_bar_bar, sup_comm]
  have hJbar : J.map (H.bar : 𝓞 E →+* 𝓞 E) =
      (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)) * A.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    conv_lhs => rw [hA]
    rw [Ideal.map_mul, hGbar]
  have hcop : A ⊔ A.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ := by
    have e : (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)) * (A ⊔ A.map (H.bar : 𝓞 E →+* 𝓞 E)) =
        (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)) * ⊤ := by
      rw [Ideal.mul_sup, ← hA, ← hJbar, Ideal.mul_top]
    exact mul_left_cancel₀ hG0 e
  have hJA : J ≤ A := by
    rw [hA]
    exact Ideal.mul_le_right
  refine ⟨A.map (H.bar : 𝓞 E →+* 𝓞 E), ?_, ?_, ?_⟩
  · rw [map_bar_bar, sup_comm]
    exact hcop
  · rw [map_bar_bar, mul_comm]
    apply idlE_cancel hG0
    rw [← mul_assoc, ← idlE_mul, ← hA, hrel]
    conv_lhs => rw [hJbar]
    rw [idlE_mul]
  · have hm : (((Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℕ) : 𝓞 E) ∈ J := by
      rw [← hJn]
      exact Ideal.absNorm_mem J
    have h2 := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hm
    rw [map_natCast] at h2
    exact Ideal.map_mono hJA h2

end Ideals

end GlobalTheory.ScalarUnit
