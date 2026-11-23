import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

noncomputable section

namespace GlobalTheory.CompanionTheory.RedInEx

section Abstract

variable {A : Type} [CommRing A] {I : Ideal A} {γ : DividedPowers I} {l s : ℕ}

theorem one_eq (γ : DividedPowers I) : pdP γ 1 = I := by
  refine le_antisymm (GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_one_le γ) fun x hx => ?_
  have h := GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP γ 1 hx
  rwa [γ.dpow_one hx] at h

theorem mem_of_pow_mul (hb : TFBase γ l s) (N : ℕ) (x : A) (h : (l : A) ^ N * x ∈ I) : x ∈ I := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih ?_
    have := hb.tf 1 ((l : A) ^ N * x) (by
      rw [one_eq]
      rwa [pow_succ', mul_assoc] at h)
    rwa [one_eq] at this

theorem eq_zero_of_pow_mul (hb : TFBase γ l s) (N : ℕ) (x : A) (h : (l : A) ^ N * x = 0) : x = 0 := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih ?_
    have := hb.tf s ((l : A) ^ N * x) (by
      rw [hb.nil]
      rw [pow_succ', mul_assoc] at h
      exact h)
    rw [hb.nil] at this
    exact this

theorem mem_of_fact_mul (hb : TFBase γ l s) (k : ℕ) (x : A) (h : (k.factorial : A) * x ∈ I) : x ∈ I := by
  obtain ⟨N, u, hu⟩ := hb.dv _ k.factorial_ne_zero
  refine mem_of_pow_mul hb N x ?_
  rw [← hu, mul_comm _ u, mul_assoc]
  exact Ideal.mul_mem_left _ _ h

theorem eq_of_fact_mul (hb : TFBase γ l s) (k : ℕ) {x y : A} (h : (k.factorial : A) * x = (k.factorial : A) * y) :
    x = y := by
  obtain ⟨N, u, hu⟩ := hb.dv _ k.factorial_ne_zero
  rw [← sub_eq_zero]
  refine eq_zero_of_pow_mul hb N _ ?_
  rw [← hu, mul_comm _ u, mul_assoc, mul_sub, h, sub_self, mul_zero]

theorem dpow_congr (hb : TFBase γ l s) {n : ℕ} {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (h : Ideal.Quotient.mk (Ideal.span {(l : A) ^ n}) x = Ideal.Quotient.mk _ y) (k : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(l : A) ^ n}) (γ.dpow k x) = Ideal.Quotient.mk _ (γ.dpow k y) := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  have haI : a ∈ I := mem_of_pow_mul hb n a (by rw [mul_comm, ha]; exact sub_mem hx hy)
  have hc : (l : A) ^ n * a ∈ I := Ideal.mul_mem_left _ _ haI
  have e : x = y + (l : A) ^ n * a := by rw [mul_comm, ha]; ring
  rw [e, γ.dpow_add hy hc, map_sum, Finset.sum_eq_single (k, 0)]
  · rw [γ.dpow_zero hc, mul_one]
  · rintro ⟨i, j⟩ hij hne
    have hj : j ≠ 0 := by
      rintro rfl
      have : i = k := by simpa using hij
      exact hne (by rw [this])
    change Ideal.Quotient.mk _ (γ.dpow i y * γ.dpow j ((l : A) ^ n * a)) = 0
    rw [γ.dpow_mul haI, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (by
      rw [pow_succ]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  · intro h0
    exact absurd (by simp) h0

end Abstract

section Concrete

open PAlg

variable {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A]

def e0 (l : ℕ) [Fact l.Prime] : Acris0 l ≃+* (base l).Acr0 :=
  RingEquiv.ofBijective (base l).cris0 (RL.base_acr (base l) isBase_base).1.1

def lam0 (lam : Acris l →+* A) : (base l).Acr0 →+* A :=
  (lam.comp (algebraMap (Acris0 l) (Acris l))).comp (e0 l).symm.toRingHom

theorem lam0_cris0_eq_lam_of (lam : Acris l →+* A) (y : Acris0 l) :
    lam0 lam ((base l).cris0 y) = lam (AdicCompletion.of _ _ y) := by
  have h : (e0 l).symm ((base l).cris0 y) = y := (e0 l).symm_apply_apply y
  change lam (algebraMap (Acris0 l) (Acris l) ((e0 l).symm ((base l).cris0 y))) = _
  rw [h]
  rfl

theorem lam0_algebraMap_sW_eq_lam_algebraMap (lam : Acris l →+* A) (w : Ainf l) :
    lam0 lam (algebraMap (base l).W (base l).Acr0 ((base l).sW w)) = lam (algebraMap (Ainf l) (Acris l) w) := by
  have h : algebraMap (base l).W (base l).Acr0 ((base l).sW w) = (base l).cris0 (algebraMap (Ainf l) (Acris0 l) w) :=
    Subtype.ext (awayW_algebraMap (base l).s w).symm
  rw [h, lam0_cris0_eq_lam_of, AdicCompletion.algebraMap_apply]

def rho (lam : Acris l →+* A) (n : ℕ) : (base l).Acr n →+* A ⧸ Ideal.span {(l : A) ^ n} :=
  ((base l).cris n).liftOfSurjective ((RL.base_acr (base l) isBase_base).2 n).1
    ⟨(Ideal.Quotient.mk _).comp lam, fun x hx => by
      rw [((RL.base_acr (base l) isBase_base).2 n).2] at hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      have hz : Ideal.Quotient.mk (Ideal.span {(l : A) ^ n}) ((l : A) ^ n) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      rw [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_mul, map_pow, map_natCast, hz, mul_zero]⟩

theorem rho_cris (lam : Acris l →+* A) (n : ℕ) (c : Acris l) :
    rho lam n ((base l).cris n c) = Ideal.Quotient.mk _ (lam c) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ c

theorem rho_mk (lam : Acris l →+* A) (n : ℕ) (y : (base l).Acr0) :
    rho lam n ((base l).mkAcr n y) = Ideal.Quotient.mk _ (lam0 lam y) := by
  obtain ⟨y, rfl⟩ := (e0 l).surjective y
  change rho lam n ((base l).mkAcr n ((base l).cris0 y)) = Ideal.Quotient.mk _ (lam0 lam ((base l).cris0 y))
  rw [← cris_of, rho_cris, lam0_cris0_eq_lam_of]

variable {I : Ideal A} {γ : DividedPowers I} {s : ℕ}

theorem lam0_mem_of_mem_fil0_one (hb : TFBase γ l s) (lam : Acris l →+* A)
    (hξ : lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I) {x : (base l).Acr0} (hx : x ∈ (base l).Fil0 1) :
    lam0 lam x ∈ I := by
  have : (base l).Fil0 1 ≤ I.comap (lam0 lam) := by
    rw [Fil0, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    refine mem_of_fact_mul hb k _ ?_
    rw [← map_natCast (lam0 lam), ← map_mul, (RL.filtration_multiplicative (base l)).2.2.1 k, map_pow]
    refine Ideal.pow_mem_of_mem _ ?_ _ hk
    rw [show (base l).xi = (base l).sW (xi0 l) from rfl, lam0_algebraMap_sW_eq_lam_algebraMap]
    exact hξ
  exact this hx

theorem lam0_dpow (hb : TFBase γ l s) (lam : Acris l →+* A)
    (hξ : lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I) {x z : (base l).Acr0} (hx : x ∈ (base l).Fil0 1) (k : ℕ)
    (hz : (k.factorial : (base l).Acr0) * z = x ^ k) : lam0 lam z = γ.dpow k (lam0 lam x) := by
  refine eq_of_fact_mul hb k ?_
  rw [γ.factorial_mul_dpow_eq_pow (lam0_mem_of_mem_fil0_one hb lam hξ hx), ← map_natCast (lam0 lam), ← map_mul, hz, map_pow]

theorem exists_unit_one_add_generator (x : (base l).Acr0) (hx : x ∈ (base l).Fil0 1) (k : ℕ) :
    ∃ z : (base l).Acr0, (k.factorial : (base l).Acr0) * z = x ^ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact ⟨1, by simp⟩
  · obtain ⟨z, -, hz⟩ := (RL.pdi (base l)).1 x hx k hk
    exact ⟨z, hz⟩

end Concrete

theorem redIn_ex : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {A : Type} [CommRing A] [Algebra (OK l K) A]
    {I : Ideal A} (γ : DividedPowers I) (s : ℕ) (lam : Acris l →+* A), TFBase γ l s →
    lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I →
    (∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a → algebraMap (OK l K) A a - lam (algebraMap (Ainf l) (Acris l) w) ∈ I) →
    ∀ n : ℕ, ∃ d : RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) γ l n,
      ∀ c, d.ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (lam c) := by
  intro l _ K A _ _ I γ s lam hb hξ hO n
  have hfil : ∀ x ∈ (PAlg.base l).Fil n 1, ∃ x₀ ∈ (PAlg.base l).Fil0 1, (PAlg.base l).mkAcr n x₀ = x := by
    intro x hx
    rw [((PAlg.base l).isPd_pdFil n).1] at hx
    exact (Ideal.mem_map_iff_of_surjective _ ((PAlg.base l).mkAcr_surjective n)).1 hx
  refine ⟨{ hl := (Fact.out : l.Prime).ne_zero, ρ := rho lam n, mem := ?_, dp := ?_, hκ := ?_ }, rho_cris lam n⟩
  · intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hfil x hx
    exact ⟨lam0 lam x₀, lam0_mem_of_mem_fil0_one hb lam hξ hx₀, rho_mk lam n x₀⟩
  · intro k x hx y hy e
    obtain ⟨x₀, hx₀, rfl⟩ := hfil x hx
    obtain ⟨z, hz⟩ := exists_unit_one_add_generator x₀ hx₀ k
    have e1 : (B.DD false (PAlg.base l) n).dpow k ((PAlg.base l).mkAcr n x₀) = (PAlg.base l).mkAcr n z :=
      ((PAlg.base l).isPd_pdFil n).2 k x₀ z hx₀ hz
    rw [e1, rho_mk, lam0_dpow hb lam hξ hx₀ k hz]
    rw [rho_mk] at e
    exact dpow_congr hb (lam0_mem_of_mem_fil0_one hb lam hξ hx₀) hy e k
  · intro a r h
    obtain ⟨w, hw⟩ := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l (okToOC l K a)
    have h1 : B.κb (okToOC l K) false n a = Ideal.Quotient.mk _ ((PAlg.base l).toAcr n ((PAlg.base l).sW w)) := by
      change B.uJ false (PAlg.base l) n ((PAlg.base l).oC (okToOC l K a)) = _
      rw [← hw, PAlg.oC_theta0, B.uJ_th]
    rw [h1] at h
    have h2 : r - (PAlg.base l).toAcr n ((PAlg.base l).sW w) ∈ (PAlg.base l).Fil n 1 :=
      Ideal.Quotient.eq.1 h.symm
    obtain ⟨x₀, hx₀, e⟩ := hfil _ h2
    have h3 : rho lam n r = Ideal.Quotient.mk _ (lam (algebraMap (Ainf l) (Acris l) w) + lam0 lam x₀) := by
      rw [map_add, ← rho_mk, e, ← PAlg.cris_algebraMap, ← rho_cris, PAlg.cris_algebraMap, map_sub, add_sub_cancel]
    refine ⟨lam0 lam x₀ - (algebraMap (OK l K) A a - lam (algebraMap (Ainf l) (Acris l) w)),
      sub_mem (lam0_mem_of_mem_fil0_one hb lam hξ hx₀) (hO a w hw), ?_⟩
    rw [h3]
    congr 1
    ring

end GlobalTheory.CompanionTheory.RedInEx
