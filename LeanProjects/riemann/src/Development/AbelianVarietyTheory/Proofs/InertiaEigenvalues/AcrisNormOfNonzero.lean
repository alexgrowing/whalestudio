import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfKernelPowerClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.GaussDefinite

theorem add_pow_split {R : Type} [CommRing R] (x p : R) (j m : ℕ) :
    ∃ u v : R, (x + p) ^ j = x ^ m * u + p ^ (j - m) * v := by
  induction j generalizing m with
  | zero => exact ⟨0, 1, by simp⟩
  | succ j ih =>
    rcases m with _ | m
    · exact ⟨(x + p) ^ (j + 1), 0, by simp⟩
    obtain ⟨u, v, h⟩ := ih m
    obtain ⟨u', v', h'⟩ := ih (m + 1)
    obtain ⟨d, hd⟩ : ∃ d, j - (m + 1) + 1 = j - m + d := ⟨j - (m + 1) + 1 - (j - m), by omega⟩
    refine ⟨u + p * u', x * v + p ^ d * v', ?_⟩
    rw [show j + 1 - (m + 1) = j - m by omega]
    have e : p * p ^ (j - (m + 1)) = p ^ (j - m) * p ^ d := by rw [← pow_add, ← hd, pow_succ']
    calc (x + p) ^ (j + 1) = x * (x + p) ^ j + p * (x + p) ^ j := by ring
      _ = x * (x ^ m * u + p ^ (j - m) * v) + p * (x ^ (m + 1) * u' + p ^ (j - (m + 1)) * v') := by
        rw [← h, ← h']
      _ = _ := by linear_combination v' * e

variable (l : ℕ) [hl : Fact l.Prime]

theorem exists_flat : ∃ x : Per.Fl l, x.untilt = (l : Per.OC l) := by
  have hr : ∀ a : Per.OC l, ∃ b : Per.OC l, b ^ l = a := by
    intro a
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ_[l]) hl.out.pos
    have h1 : ‖b‖ ^ l ≤ 1 := by rw [← norm_pow, hb]; exact (GlobalTheory.RingBasics.mem_OC _).1 a.2
    exact ⟨⟨b, (GlobalTheory.RingBasics.mem_OC _).2 ((pow_le_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h1)⟩,
      Subtype.ext hb⟩
  choose r hr using hr
  obtain ⟨e, he⟩ := zeta_exists_tilt (p := l) (O := Per.OC l) (fun n => r^[n] (l : Per.OC l)) (fun n => by
    rw [Function.iterate_succ_apply', hr])
  exact ⟨e, he 0⟩

theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]
  simp

theorem norm_root (x : Per.Fl l) (i : ℕ) :
    ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) =
      ‖(((((frobeniusEquiv (Per.Fl l) l).symm ^ i) x).untilt : Per.OC l) : ℂ_[l])‖ := by
  have h := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x i
  have e : ((frobeniusEquiv (Per.Fl l) l).symm ^ i) x = ((frobeniusEquiv (Per.Fl l) l).symm)^[i] x := by
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', Function.iterate_succ_apply', ← ih (PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x i)]; rfl
  rw [← h, e]
  push_cast
  rw [norm_pow, one_div, ← Nat.cast_pow, Real.pow_rpow_inv_natCast (norm_nonneg _)
    (pow_ne_zero _ hl.out.ne_zero)]

theorem split_of_small (a : Per.Ainf l) (M m : ℕ)
    (h : ∀ i : ℕ, ‖(((a.coeff i).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) * ((l : ℝ)⁻¹) ^ i ≤
      ((l : ℝ)⁻¹) ^ M) :
    ∃ c : Per.Ainf l, a - (l : Per.Ainf l) ^ (M - m) * c ∈ RingHom.ker (Per.θ l) ^ m := by
  obtain ⟨w, hw⟩ := exists_flat l
  have hk : Per.tm w - (l : Per.Ainf l) ∈ RingHom.ker (Per.θ l) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, WittVector.fontaineTheta_teichmuller, hw, sub_self]
  have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hl.out.pos)
  have key : ∀ i ∈ Finset.Iic M, ∃ c : Per.Ainf l,
      Per.tm (((frobeniusEquiv (Per.Fl l) l).symm ^ i) (a.coeff i)) * (l : Per.Ainf l) ^ i -
        (l : Per.Ainf l) ^ (M - m) * c ∈ RingHom.ker (Per.θ l) ^ m := by
    intro i hi
    rw [Finset.mem_Iic] at hi
    have h1 := h i
    rw [norm_root] at h1
    set y := ((frobeniusEquiv (Per.Fl l) l).symm ^ i) (a.coeff i)
    have h2 : ‖((y.untilt : Per.OC l) : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ (M - i) := by
      rw [norm_l]
      refine le_of_mul_le_mul_right ?_ (pow_pos hl0 i)
      rwa [← pow_add, Nat.sub_add_cancel hi]
    rw [← GlobalTheory.RingBasics.mem_span_pow_OC, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← hw,
      ← map_pow] at h2
    obtain ⟨z, hz⟩ := GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd h2
    obtain ⟨u, v, huv⟩ := add_pow_split (Per.tm w - (l : Per.Ainf l)) (l : Per.Ainf l) (M - i) m
    obtain ⟨d, hd⟩ : ∃ d, M - i - m + i = M - m + d := ⟨M - i - m + i - (M - m), by omega⟩
    have e : (l : Per.Ainf l) ^ (M - i - m) * (l : Per.Ainf l) ^ i =
        (l : Per.Ainf l) ^ (M - m) * (l : Per.Ainf l) ^ d := by rw [← pow_add, hd, pow_add]
    refine ⟨(l : Per.Ainf l) ^ d * v * Per.tm z, ?_⟩
    have e2 : Per.tm y * (l : Per.Ainf l) ^ i - (l : Per.Ainf l) ^ (M - m) * ((l : Per.Ainf l) ^ d * v * Per.tm z)
        = (Per.tm w - (l : Per.Ainf l)) ^ m * (u * Per.tm z * (l : Per.Ainf l) ^ i) := by
      rw [sub_add_cancel] at huv
      rw [hz, Per.tm, map_mul, map_pow]
      change Per.tm w ^ (M - i) * Per.tm z * _ - _ = _
      rw [huv]
      linear_combination (v * Per.tm z) * e
    rw [e2]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hk m)
  choose! c hc using key
  obtain ⟨t, ht⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (p := l) a M
  obtain ⟨d, hd⟩ : ∃ d, M + 1 = M - m + d := ⟨M + 1 - (M - m), by omega⟩
  refine ⟨∑ i ∈ Finset.Iic M, c i + (l : Per.Ainf l) ^ d * t, ?_⟩
  have := Ideal.sum_mem _ hc
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
  rw [hd, pow_add] at ht
  convert this using 1
  linear_combination ht

theorem map_mem_kerP (a : Per.Ainf l) (m : ℕ) (h : a ∈ RingHom.ker (Per.θ l) ^ m) :
    algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ m := by
  have h1 : RingHom.ker (Per.θ l) ≤ (Per.kerP l).comap (algebraMap (Per.Ainf l) (Per.AinfP l)) := by
    intro x hx
    exact Ideal.mem_comap.2 (GlobalTheory.RingIface.alg_mem_kerP l (RingHom.mem_ker.1 hx))
  exact Ideal.le_comap_pow _ m (Ideal.pow_right_mono h1 m h)

theorem term_le_one (a : Per.Ainf l) (i : ℕ) :
    ‖(((a.coeff i).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) * ((l : ℝ)⁻¹) ^ i ≤ 1 := by
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_le
  rw [norm_root]
  exact mul_le_one₀ ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.property _)) (by positivity)
    (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h1))

theorem gauss_pow_le (k : ℕ) :
    ⨆ i : ℕ, ‖(((((l : Per.Ainf l) ^ k).coeff i).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) *
      ((l : ℝ)⁻¹) ^ i ≤ ((l : ℝ)⁻¹) ^ k := by
  refine ciSup_le fun i => ?_
  rw [norm_root]
  by_cases h : i = k
  · subst h
    exact mul_le_of_le_one_left (by positivity) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.property _))
  · have h0 : (0 : Per.Fl l).untilt = 0 := by
      rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]
    rw [WittVector.coeff_p_pow_eq_zero _ _ h, map_zero, h0]
    simp

theorem envelope_split (N : Per.Acris l → ℝ) (h0 : ∀ x, 0 ≤ N x) (hm : ∀ x y, N (x * y) = N x * N y)
    (hA : ∀ a : Per.Ainf l, N (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ((l : ℝ)⁻¹) ^ n)
    (s : Per.Acris0 l) (k m : ℕ) (hs : N (algebraMap (Per.Acris0 l) (Per.Acris l) s) ≤ ((l : ℝ)⁻¹) ^ (k + m)) :
    ∃ c : Per.Ainf l, (s : Per.AinfP l) - algebraMap (Per.Ainf l) (Per.AinfP l) ((l : Per.Ainf l) ^ k * c) ∈
      Per.kerP l ^ m := by
  obtain ⟨K, a, ha⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) (s : Per.AinfP l)
  have e0 : s * algebraMap (Per.Ainf l) (Per.Acris0 l) ((l : Per.Ainf l) ^ K) =
      algebraMap (Per.Ainf l) (Per.Acris0 l) a := Subtype.ext (by rw [← map_pow] at ha; exact ha)
  have hc : ∀ x, algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) =
      algebraMap (Per.Ainf l) (Per.Acris l) x := fun x => (GlobalTheory.RingIface.tower l x).symm
  have e1 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) e0
  rw [map_mul, hc, hc] at e1
  have hN : N (algebraMap (Per.Ainf l) (Per.Acris l) a) ≤ ((l : ℝ)⁻¹) ^ (k + m + K) := by
    rw [← e1, hm, pow_add]
    refine mul_le_mul hs ?_ (h0 _) (by positivity)
    rw [hA]
    exact gauss_pow_le l K
  rw [hA] at hN
  obtain ⟨c, hc⟩ := split_of_small l a (k + m + K) m fun i =>
    (le_ciSup (f := fun n : ℕ => ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) *
      ((l : ℝ)⁻¹) ^ n) ⟨1, by rintro _ ⟨i, rfl⟩; exact term_le_one l a i⟩ i).trans hN
  refine ⟨c, ?_⟩
  have h2 := map_mem_kerP l _ m hc
  rw [show k + m + K - m = k + K by omega, map_sub, ← ha, map_natCast] at h2
  rw [← Ideal.unit_mul_mem_iff_mem _ ((GlobalTheory.RingBasics.isUnit_l l).pow K)]
  convert h2 using 1
  simp only [map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.MemLoc.GaussDefinite

namespace GlobalTheory.MemLoc

theorem gauss_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (N : ℝ → Per.Acris l → ℝ), (∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N r x ∧ N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧ (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ ∀ a : Per.Ainf l, N r (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ b : Per.Acris l, b ≠ 0 → N (l : ℝ)⁻¹ b ≠ 0 := by
  intro l hl N hN b hb hb0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  obtain ⟨h01, hadd, hneg, hm, hA⟩ := hN _ le_rfl (inv_lt_one_of_one_lt₀ hl1)
  obtain ⟨j, hj⟩ := exists_isCrisP l
  refine hb (crisP_injective l j hj ?_)
  rw [map_zero]
  refine GlobalTheory.RingIface.ev_ext l _ _ fun m => ?_
  rw [map_zero]
  obtain ⟨N₀, hN₀⟩ := hj.bdd m
  obtain ⟨a, ha⟩ := hN₀ b
  have hu : IsUnit (Per.ev l m (((l : ℕ) : Per.BdRp l) ^ N₀)) := by
    have := ((GlobalTheory.RingBasics.isUnit_l l).pow N₀).map (Ideal.Quotient.mk (Per.kerP l ^ m))
    rw [map_pow, map_natCast] at this ⊢
    exact this
  rw [← hu.mul_right_eq_zero, ← map_mul, ha, Ideal.Quotient.eq_zero_iff_mem]
  refine image_kerP_pow_separated l m a fun k => ?_
  obtain ⟨s, z, hs⟩ := (acris_basic l).2.2.1 b (k + m)
  have hz : N (l : ℝ)⁻¹ (-((l : Per.Acris l) ^ (k + m) * z)) ≤ ((l : ℝ)⁻¹) ^ (k + m) := by
    rw [hneg, hm, ← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)), ← map_pow, hA]
    exact (mul_le_mul (GaussDefinite.gauss_pow_le l _) (h01 z).2 (h01 z).1 (by positivity)).trans
      (mul_one _).le
  have hs' : N (l : ℝ)⁻¹ (algebraMap (Per.Acris0 l) (Per.Acris l) s) ≤ ((l : ℝ)⁻¹) ^ (k + m) := by
    have e : algebraMap (Per.Acris0 l) (Per.Acris l) s = b + -((l : Per.Acris l) ^ (k + m) * z) := by
      rw [hs]; ring
    rw [e]
    refine (hadd _ _).trans (max_le ?_ hz)
    rw [hb0]
    positivity
  obtain ⟨c, hc⟩ := GaussDefinite.envelope_split l (N (l : ℝ)⁻¹) (fun x => (h01 x).1) hm hA s k m hs'
  obtain ⟨a', ha'⟩ := hN₀ z
  have hev : Per.ev l m (algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) =
      Ideal.Quotient.mk _ (s : Per.AinfP l) := GlobalTheory.RingIface.ev_alg l m _
  refine ⟨(l : Per.Ainf l) ^ N₀ * c + (l : Per.Ainf l) ^ m * a', ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hc ⊢
  rw [hs] at ha
  simp only [map_add, map_sub, map_mul, map_pow, map_natCast, hj.on0, hev] at ha ha' hc ⊢
  linear_combination -ha + (l : Per.AinfP l ⧸ Per.kerP l ^ m) ^ (k + m) * ha' +
    (l : Per.AinfP l ⧸ Per.kerP l ^ m) ^ N₀ * hc

end GlobalTheory.MemLoc
