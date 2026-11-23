import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.FrobRoots

open Ideal

section General

theorem root_step {A : Type} [CommRing A] (φ : A →+* A) (hφ : Function.Injective φ) (c : A) (hc : φ c = c) (q : ℕ)
    (ω : ℕ → A) (hω : ∀ n, φ (ω (n + 1)) = ω n) (h0 : φ (ω 0) = c * ω 0 + ω 0 ^ q) :
    ∀ n, c * ω (n + 1) + ω (n + 1) ^ q = ω n := by
  intro n
  induction n with
  | zero =>
    apply hφ
    rw [map_add, map_mul, map_pow, hc, hω, h0]
  | succ n ih =>
    apply hφ
    rw [map_add, map_mul, map_pow, hc, hω, hω, ih]

theorem pow_pow_eq {R : Type} [Monoid R] (q : ℕ) (r : ℕ → R) (h : ∀ n, r (n + 1) ^ q = r n) :
    ∀ n, r n ^ (q ^ n) = r 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, h, ih]

theorem coeff_pow_eq {O : Type} [CommRing O] {l : ℕ} [Fact l.Prime] [Fact (¬ IsUnit (l : O))]
    (z : PreTilt O l) (m : ℕ) : PreTilt.coeff m (z ^ (l ^ m)) = PreTilt.coeff 0 z := by
  rw [map_pow, GlobalTheory.LTTilt.coeff_eq_pow z 0 m, zero_add]

theorem sub_mem_of_three {O : Type} [CommRing O] (I : Ideal O) {u t y v : O} (h1 : u - t ∈ I) (h2 : t - y ∈ I)
    (h3 : y - v ∈ I) : u - v ∈ I := by
  have := I.add_mem (I.add_mem h1 h2) h3
  rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this

theorem sub_mem_pow {O : Type} [CommRing O] {l : ℕ} [Fact l.Prime] (I : Ideal O) (hlI : (l : O) ∈ I) {P : O}
    (hP : P ∈ I) {f : ℕ} (hf : 0 < f) {u v : ℕ → O} (hu : ∀ n, P * u (n + 1) + u (n + 1) ^ l ^ f = u n)
    (hv : ∀ n, P * v (n + 1) + v (n + 1) ^ l ^ f = v n) (h1 : ∀ n, u n - v n ∈ I) :
    ∀ k n, u n - v n ∈ I ^ (k + 1) := by
  intro k
  induction k with
  | zero => intro n; simpa using h1 n
  | succ k ih =>
    intro n
    have hq : u (n + 1) ^ l ^ f - v (n + 1) ^ l ^ f ∈ I ^ (k + 1 + 1) := by
      obtain ⟨g, hg⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [hg, show l ^ (g + 1) = l ^ g * l from pow_succ l g, pow_mul, pow_mul]
      exact GlobalTheory.LTTilt.pow_l_sub_mem I hlI (by omega) (GlobalTheory.LTTilt.pow_sub_mem _ (ih (n + 1)) _)
    have e : u n - v n = P * (u (n + 1) - v (n + 1)) + (u (n + 1) ^ l ^ f - v (n + 1) ^ l ^ f) := by
      rw [← hu n, ← hv n]; ring
    rw [e]
    refine Ideal.add_mem _ ?_ hq
    rw [pow_succ' I (k + 1)]
    exact Ideal.mul_mem_mul hP (ih (n + 1))

end General

section OC

open Formalism.BasicNotions

theorem eq_of_forall_mem_pow {l : ℕ} [Fact l.Prime] {P a b : OC l} (hP : ¬ IsUnit P)
    (h : ∀ k, a - b ∈ (Ideal.span {P}) ^ (k + 1)) : a = b := by
  have hP1 := GlobalTheory.LTTilt.norm_lt_one_of_not_isUnit P hP
  have hk : ∀ k, ‖((a - b : OC l) : ℂ_[l])‖ ≤ ‖(P : ℂ_[l])‖ ^ (k + 1) := by
    intro k
    have := h k
    rw [Ideal.span_singleton_pow, GlobalTheory.LTTilt.mem_span_iff_norm, SubmonoidClass.coe_pow, norm_pow] at this
    exact this
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hP1).comp (Filter.tendsto_add_atTop_nat 1)
  have h0 := ge_of_tendsto' hlim fun k => hk k
  have h2 : ((a - b : OC l) : ℂ_[l]) = 0 := norm_le_zero_iff.1 h0
  have h3 : a - b = 0 := Subtype.ext h2
  exact sub_eq_zero.1 h3

end OC

section Main

theorem sub_mem_of_root {l : ℕ} [Fact l.Prime] {P u a v : OC l} (hlP : ((l : ℕ) : OC l) ∈ span {P})
    {x y : OCb l} {m : ℕ} (hxy : y ^ (l ^ m) = x)
    (ha : PreTilt.coeff m x = Ideal.Quotient.mk (span {((l : ℕ) : OC l)}) a) (hav : a - v ∈ span {P})
    (hu : P ∣ u - y.untilt) : u - v ∈ span {P} := by
  refine sub_mem_of_three _ (Ideal.mem_span_singleton.2 hu) ?_ hav
  refine span_le.2 (Set.singleton_subset_iff.2 hlP) ?_
  rw [← hxy, coeff_pow_eq, ← PreTilt.mk_untilt_eq_coeff_zero] at ha
  exact Ideal.Quotient.eq.1 ha

theorem thetaK_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π → ∀ (v : ℕ → OC l) (ω : ℕ → AK K),
    (∀ n, intToOC K π * v (n + 1) + v (n + 1) ^ l ^ fK K = v n) →
    GlobalTheory.LTTilt.IsTiltOf (fK K) (intToOC K π) (red K (ω 0)) v → (∀ n, frobq K (ω (n + 1)) = ω n) →
    frobq K (ω 0) = inO K π * ω 0 + ω 0 ^ l ^ fK K → ∀ n, thetaK K (ω n) = v n := by
  intro l _ K π hπ v ω hv hx hω h0
  have hF : ∀ n, inO K π * ω (n + 1) + ω (n + 1) ^ l ^ fK K = ω n :=
    root_step (frobq K).toRingHom (frobq_bijective K).1 (inO K π) (frobq_inO K π) _ ω hω h0
  have hu : ∀ n, intToOC K π * thetaK K (ω (n + 1)) + thetaK K (ω (n + 1)) ^ l ^ fK K = thetaK K (ω n) := by
    intro n
    have := congrArg (thetaK K) (hF n)
    rwa [map_add, map_mul, map_pow, thetaK_inO] at this
  have hr : ∀ n, red K (ω n) ^ (l ^ (fK K * n)) = red K (ω 0) := by
    intro n
    rw [pow_mul]
    exact pow_pow_eq (l ^ fK K) (fun n => red K (ω n))
      (fun n => (red_frobq (ω (n + 1))).symm.trans (congrArg (red K) (hω n))) n
  have hlP := GlobalTheory.LTTilt.natCast_mem_span_intToOC K hπ
  have h1 : ∀ n, thetaK K (ω n) - v n ∈ span {intToOC K π} := fun n =>
    (hx n).elim fun a ha => sub_mem_of_root hlP (hr n) ha.1 ha.2 (dvd_thetaK_sub hπ (ω n))
  exact fun n => eq_of_forall_mem_pow (GlobalTheory.LTTilt.not_isUnit_intToOC K hπ) fun k =>
    sub_mem_pow _ hlP (Ideal.mem_span_singleton_self _) (Nat.pos_of_ne_zero (NeZero.ne (fK K)))
      (u := fun n => thetaK K (ω n)) hu hv h1 k n

end Main

end GlobalTheory.FrobRoots
