import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnram

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.LiftS

section Ideals
variable {K : Type} [Field K] [NumberField K] [StarRing K]

omit [NumberField K] in
theorem star_one_mem {x : K} (hx : x ∈ (1 : Submodule (𝓞 K) K)) : star x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  refine Submodule.mem_one.2 ⟨⟨star (algebraMap (𝓞 K) K y), ?_⟩, rfl⟩
  exact (NumberField.RingOfIntegers.isIntegral_coe y).map (starRingEnd K).toIntAlgHom

private theorem star_mem_mul_of_star_mem {M N : Submodule (𝓞 K) K} (hM : ∀ x ∈ M, star x ∈ M)
    (hN : ∀ x ∈ N, star x ∈ N) : ∀ x ∈ M * N, star x ∈ M * N := by
  intro x hx
  refine Submodule.mul_induction_on hx (C := fun x => star x ∈ M * N) ?_ ?_
  · intro m hm n hn
    have hmn := Submodule.mul_mem_mul (hM m hm) (hN n hn)
    rw [star_mul, mul_comm (star n) (star m)]
    exact hmn
  · intro a b ha hb
    rw [star_add]
    exact Submodule.add_mem _ ha hb

theorem pow_star (𝔡 : Ideal (𝓞 K)) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℕ) :
    ∀ x ∈ (((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ n : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      star x ∈ (((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ n : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  rw [FractionalIdeal.coe_pow, FractionalIdeal.coe_coeIdeal]
  have base : ∀ x ∈ IsLocalization.coeSubmodule K 𝔡, star x ∈ IsLocalization.coeSubmodule K 𝔡 := by
    intro x hx
    rw [IsLocalization.mem_coeSubmodule] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, hz'⟩ := hs y hy
    exact ⟨z, hz, hz'⟩
  induction n with
  | zero => intro x hx; rw [pow_zero] at hx ⊢; exact star_one_mem hx
  | succ m ih => rw [pow_succ]; exact star_mem_mul_of_star_mem ih base

theorem ipow_star (𝔡 : Ideal (𝓞 K)) (h0 : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℤ)
    {x : K} (hx : x ∈ ipow 𝔡 n) : star x ∈ ipow 𝔡 n := by
  unfold ipow at hx ⊢
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast] at hx ⊢
    exact pow_star 𝔡 hs m x hx
  · have hne : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ m) ≠ 0 :=
      pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 h0)
    rw [zpow_neg, zpow_natCast] at hx ⊢
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff hne] at hx ⊢
    intro y hy
    have h1 := hx (star y) (pow_star 𝔡 hs m y hy)
    rw [FractionalIdeal.mem_one_iff] at h1 ⊢
    obtain ⟨w, hw⟩ := h1
    have h2 : star (algebraMap (𝓞 K) K w) ∈ (1 : Submodule (𝓞 K) K) :=
      star_one_mem (Submodule.mem_one.2 ⟨w, rfl⟩)
    obtain ⟨v, hv⟩ := Submodule.mem_one.1 h2
    refine ⟨v, ?_⟩
    rw [hv, hw, star_mul, star_star, mul_comm]

omit [StarRing K] in
theorem ipow_mul (𝔡 : Ideal (𝓞 K)) (h0 : 𝔡 ≠ ⊥) (n : ℤ) : ipow 𝔡 n * ipow 𝔡 (-n) = 1 := by
  have h : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h0
  unfold ipow
  rw [← FractionalIdeal.coe_mul, ← zpow_add₀ h, add_neg_cancel, zpow_zero, FractionalIdeal.coe_one]

end Ideals

section Abstract
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem symm0 (H : HermSpace K V) {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm x y, h, star_zero]

def levi (p q s : V →ₗ[K] V) : V →ₗ[K] V := s ∘ₗ p + (1 - p - q) ∘ₗ s ∘ₗ (1 - p - q) + q ∘ₗ s ∘ₗ q

omit [StarRing K] in
theorem levi_apply (p q s : V →ₗ[K] V) (x : V) : levi p q s x =
    s (p x) + (s (x - p x - q x) - p (s (x - p x - q x)) - q (s (x - p x - q x))) + q (s (q x)) := by
  simp only [levi, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply]

theorem levi_isom (H : HermSpace K V) (p q : V →ₗ[K] V) (s : V ≃ₗ[K] V)
    (adj : ∀ x y, H.B (p x) y = H.B x (q y)) (pp : ∀ x, p (p x) = p x) (qq : ∀ x, q (q x) = q x)
    (pq : ∀ x, p (q x) = 0) (qp : ∀ x, q (p x) = 0) (hs : ∀ x y, H.B (s x) (s y) = H.B x y)
    (h1 : ∀ x, p (s (p x)) = s (p x)) (h2 : ∀ x, p (s.symm (p x)) = s.symm (p x)) (x y : V) :
    H.B (levi p q s x) (levi p q s y) = H.B x y := by
  have hqa : ∀ v w, H.B (q v) w = H.B v (p w) := by
    intro v w
    rw [← H.herm w (q v), ← adj w v, H.herm]
  have hpp0 : ∀ v w, H.B (p v) (p w) = 0 := by
    intro v w
    rw [adj, qp, map_zero]
  have hqq0 : ∀ v w, H.B (q v) (q w) = 0 := by
    intro v w
    rw [hqa, pq, map_zero]
  have hsq : ∀ w, q w = 0 → q (s w) = 0 := by
    intro w hw
    apply H.nondeg
    intro t
    rw [hqa]
    have e : p t = s (p (s.symm (p t))) := by rw [h2 t, LinearEquiv.apply_symm_apply]
    rw [e, hs, ← hqa, hw, map_zero, LinearMap.zero_apply]
  have hpv : ∀ v w, p v = v → H.B v (q w) = H.B v w := by
    intro v w hv
    have e : H.B v (w - q w) = 0 := by
      rw [← hv, adj, map_sub, qq, sub_self, map_zero]
    rw [map_sub, sub_eq_zero] at e
    exact e.symm
  have hpv' : ∀ v w, p v = v → H.B (q w) v = H.B w v := by
    intro v w hv
    have e : H.B (w - q w) v = 0 := by
      rw [← hv, ← hqa, map_sub, qq, sub_self, map_zero, LinearMap.zero_apply]
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at e
    exact e.symm
  obtain ⟨u, hu⟩ : ∃ u, x - p x - q x = u := ⟨_, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u', y - p y - q y = u' := ⟨_, rfl⟩
  have pu : p u = 0 := by rw [← hu]; simp [pp, pq]
  have qu : q u = 0 := by rw [← hu]; simp [qp, qq]
  have pu' : p u' = 0 := by rw [← hu']; simp [pp, pq]
  have qu' : q u' = 0 := by rw [← hu']; simp [qp, qq]
  have hx : x = p x + u + q x := by rw [← hu]; abel
  have hy : y = p y + u' + q y := by rw [← hu']; abel
  have hxy : H.B x y = H.B (p x) (q y) + H.B u u' + H.B (q x) (p y) := by
    have f1 := hpp0 x y
    have f2 : H.B (p x) u' = 0 := by rw [adj, qu', map_zero]
    have f3 : H.B u (p y) = 0 := by rw [← hqa, qu, map_zero, LinearMap.zero_apply]
    have f4 : H.B u (q y) = 0 := by rw [← adj, pu, map_zero, LinearMap.zero_apply]
    have f5 : H.B (q x) u' = 0 := by rw [hqa, pu', map_zero]
    have f6 := hqq0 x y
    have hexp : H.B (p x + u + q x) (p y + u' + q y) = H.B (p x) (p y) + H.B (p x) u' + H.B (p x) (q y) +
        H.B u (p y) + H.B u u' + H.B u (q y) + H.B (q x) (p y) + H.B (q x) u' + H.B (q x) (q y) := by
      simp only [map_add, LinearMap.add_apply]
      ring
    calc H.B x y = H.B (p x + u + q x) (p y + u' + q y) := by rw [← hx, ← hy]
      _ = _ := by rw [hexp, f1, f2, f3, f4, f5, f6]; ring
  rw [levi_apply, levi_apply]
  simp only [LinearEquiv.coe_coe]
  rw [hu, hu', hsq u qu, hsq u' qu', sub_zero, sub_zero]
  have e1 : H.B (s (p x)) (s (p y)) = 0 := by rw [hs]; exact hpp0 x y
  have e2 : H.B (s (p x)) (s u') = 0 := by rw [hs, adj, qu', map_zero]
  have e3 : H.B (s (p x)) (p (s u')) = 0 := by rw [← h1 x]; exact hpp0 _ _
  have e4 : H.B (s (p x)) (q (s (q y))) = H.B (p x) (q y) := by rw [hpv _ _ (h1 x), hs]
  have e5 : H.B (s u) (s (p y)) = 0 := by rw [hs, ← hqa, qu, map_zero, LinearMap.zero_apply]
  have e6 : H.B (s u) (s u') = H.B u u' := hs u u'
  have e7 : H.B (s u) (p (s u')) = 0 := by rw [← hqa, hsq u qu, map_zero, LinearMap.zero_apply]
  have e8 : H.B (s u) (q (s (q y))) = H.B (p (s u)) (s (q y)) := (adj (s u) (s (q y))).symm
  have e9 : H.B (p (s u)) (s (p y)) = 0 := by rw [← h1 y]; exact hpp0 _ _
  have e10 : H.B (p (s u)) (s u') = 0 := by rw [adj, hsq u' qu', map_zero]
  have e11 : H.B (p (s u)) (p (s u')) = 0 := hpp0 _ _
  have e12 : H.B (p (s u)) (q (s (q y))) = H.B (p (s u)) (s (q y)) := by
    rw [adj (s u) (q (s (q y))), qq, ← adj (s u) (s (q y))]
  have e13 : H.B (q (s (q x))) (s (p y)) = H.B (q x) (p y) := by rw [hpv' _ _ (h1 y), hs]
  have e14 : H.B (q (s (q x))) (s u') = H.B (s (q x)) (p (s u')) := hqa _ _
  have e15 : H.B (q (s (q x))) (p (s u')) = H.B (s (q x)) (p (s u')) := by rw [hqa, pp]
  have e16 : H.B (q (s (q x))) (q (s (q y))) = 0 := hqq0 _ _
  have hexp : H.B (s (p x) + (s u - p (s u)) + q (s (q x))) (s (p y) + (s u' - p (s u')) + q (s (q y))) =
      H.B (s (p x)) (s (p y)) + H.B (s (p x)) (s u') - H.B (s (p x)) (p (s u')) + H.B (s (p x)) (q (s (q y))) +
      H.B (s u) (s (p y)) + H.B (s u) (s u') - H.B (s u) (p (s u')) + H.B (s u) (q (s (q y))) -
      H.B (p (s u)) (s (p y)) - H.B (p (s u)) (s u') + H.B (p (s u)) (p (s u')) - H.B (p (s u)) (q (s (q y))) +
      H.B (q (s (q x))) (s (p y)) + H.B (q (s (q x))) (s u') - H.B (q (s (q x))) (p (s u')) +
      H.B (q (s (q x))) (q (s (q y))) := by
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    ring
  linear_combination hexp + e1 + e2 - e3 + e4 + e5 + e6 - e7 + e8 - e9 - e10 + e11 - e12 + e13 + e14 - e15 + e16 - hxy

def trans (H : HermSpace K V) (h z : V) (T τ : K) : V →ₗ[K] V :=
  LinearMap.id - T⁻¹ • (H.B.flip z).smulRight h + T⁻¹ • (H.B.flip h).smulRight z
    + (τ * T⁻¹) • (H.B.flip h).smulRight h

theorem trans_apply (H : HermSpace K V) (h z : V) (T τ : K) (y : V) : trans H h z T τ y =
    y - (T⁻¹ * H.B y z) • h + (T⁻¹ * H.B y h) • z + (τ * (T⁻¹ * H.B y h)) • h := by
  simp only [trans, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.flip_apply, smul_smul, mul_assoc]

theorem trans_isom (H : HermSpace K V) (h z : V) (T τ : K) (hT : T ≠ 0) (hT' : star T = T)
    (hτ : τ + star τ = 1) (hh : H.B h h = 0) (hz : H.B h z = 0) (zz : H.B z z = -T) (x y : V) :
    H.B (trans H h z T τ x) (trans H h z T τ y) = H.B x y := by
  have hzh : H.B z h = 0 := by rw [← H.herm h z, hz, star_zero]
  have hTi : star T⁻¹ = T⁻¹ := by rw [star_inv₀, hT']
  have hTT : T * T⁻¹ = 1 := mul_inv_cancel₀ hT
  rw [trans_apply, trans_apply]
  simp only [map_add, map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_mul', hTi, hh, hz, hzh, zz]
  simp only [← H.herm y h, ← H.herm y z]
  linear_combination (T⁻¹ * H.B x h * star (H.B y h)) * hτ - (T⁻¹ * H.B x h * star (H.B y h)) * hTT

end Abstract

section Flag
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem Xa_le {F : FlagD H r} {a : ℕ} {M : Submodule K V} (h : ∀ b : Fin r, b.val < a → F.e b.castSucc ∈ M) :
    F.Xa a ≤ M := by
  unfold FlagD.Xa
  rw [Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  exact h b hb

theorem e_mem_Xa (F : FlagD H r) {a : ℕ} (b : Fin r) (h : b.val < a) : F.e b.castSucc ∈ F.Xa a := by
  unfold FlagD.Xa
  exact Submodule.subset_span ⟨b, h, rfl⟩

theorem Xa_mono (F : FlagD H r) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b := by
  exact GlobalTheory.DegCnt.LiftS.Xa_le (fun c hc => GlobalTheory.DegCnt.LiftS.e_mem_Xa F c (lt_of_lt_of_le hc h))

theorem Xa_le_X (F : FlagD H r) (a : ℕ) : F.Xa a ≤ F.X := by
  exact GlobalTheory.DegCnt.LiftS.Xa_le (fun b _ => GlobalTheory.DegCnt.LiftS.e_mem_Xa F b b.2)

theorem orth_of (F : FlagD H r) {a : ℕ} {x y : V} (hx : x ∈ F.Xa a)
    (h : ∀ b : Fin r, b.val < a → H.B (F.e b.castSucc) y = 0) : H.B x y = 0 := by
  have h2 : F.Xa a ≤ LinearMap.ker (H.B.flip y) :=
    GlobalTheory.DegCnt.LiftS.Xa_le (fun b hb => by rw [LinearMap.mem_ker, LinearMap.flip_apply]; exact h b hb)
  have h3 := h2 hx
  rwa [LinearMap.mem_ker, LinearMap.flip_apply] at h3

theorem orth_e (F : FlagD H r) {x : V} (hx : x ∈ F.X) (b : Fin r) : H.B x (F.e b.castSucc) = 0 := by
  exact GlobalTheory.DegCnt.LiftS.orth_of F (a := r) hx (fun c _ => F.iso c b)

theorem hermFlag_isotropicPart_orthogonal_anisotropicVector (F : FlagD H r) {x : V} (hx : x ∈ F.X) : H.B x F.z = 0 := by
  exact GlobalTheory.DegCnt.LiftS.orth_of F (a := r) hx (fun c _ => F.zperp c)

theorem orth_X (F : FlagD H r) {x y : V} (hx : x ∈ F.X) (hy : y ∈ F.X) : H.B x y = 0 := by
  exact GlobalTheory.DegCnt.LiftS.orth_of F (a := r) hx (fun b _ => by
    rw [← H.herm y (F.e b.castSucc), GlobalTheory.DegCnt.LiftS.orth_e F hy b, star_zero])

end Flag

section Conc
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)

def pI : V →ₗ[K] V := ∑ b ∈ Finset.univ.filter (fun b : Fin r => N.j ≤ b.val),
  (H.B.flip (N.ist b)).smulRight (N.F.e b.castSucc)

def qI : V →ₗ[K] V := ∑ b ∈ Finset.univ.filter (fun b : Fin r => N.j ≤ b.val),
  (H.B.flip (N.F.e b.castSucc)).smulRight (N.ist b)

theorem pI_apply (y : V) : pI N y = ∑ b ∈ Finset.univ.filter (fun b : Fin r => N.j ≤ b.val),
    H.B y (N.ist b) • N.F.e b.castSucc := by
  simp only [GlobalTheory.DegCnt.LiftS.pI, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]

theorem qI_apply (y : V) : qI N y = ∑ b ∈ Finset.univ.filter (fun b : Fin r => N.j ≤ b.val),
    H.B y (N.F.e b.castSucc) • N.ist b := by
  simp only [GlobalTheory.DegCnt.LiftS.qI, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]

theorem adj (x y : V) : H.B (pI N x) y = H.B x (qI N y) := by
  simp only [GlobalTheory.DegCnt.LiftS.pI_apply, GlobalTheory.DegCnt.LiftS.qI_apply, map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, LinearMap.map_smulₛₗ, starRingEnd_apply, H.herm, smul_eq_mul]
  exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)

theorem p_zero {y : V} (h : ∀ b : Fin r, N.j ≤ b.val → H.B y (N.ist b) = 0) : pI N y = 0 := by
  rw [GlobalTheory.DegCnt.LiftS.pI_apply]
  exact Finset.sum_eq_zero (fun b hb => by rw [h b (Finset.mem_filter.1 hb).2, zero_smul])

theorem q_zero {y : V} (h : ∀ b : Fin r, N.j ≤ b.val → H.B y (N.F.e b.castSucc) = 0) : qI N y = 0 := by
  rw [GlobalTheory.DegCnt.LiftS.qI_apply]
  exact Finset.sum_eq_zero (fun b hb => by rw [h b (Finset.mem_filter.1 hb).2, zero_smul])

theorem p_e (a : Fin r) (ha : N.j ≤ a.val) : pI N (N.F.e a.castSucc) = N.F.e a.castSucc := by
  rw [GlobalTheory.DegCnt.LiftS.pI_apply, Finset.sum_eq_single a]
  · rw [N.ist_e a a ha, if_pos rfl, one_smul]
  · intro b hb hba
    rw [N.ist_e a b (Finset.mem_filter.1 hb).2, if_neg (fun h => hba h.symm), zero_smul]
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ a, ha⟩) h

theorem i_e (a b : Fin r) (ha : N.j ≤ a.val) : H.B (N.ist a) (N.F.e b.castSucc) = if b = a then 1 else 0 := by
  rw [← H.herm (N.F.e b.castSucc) (N.ist a), N.ist_e b a ha]
  split_ifs <;> simp

theorem q_i (a : Fin r) (ha : N.j ≤ a.val) : qI N (N.ist a) = N.ist a := by
  rw [GlobalTheory.DegCnt.LiftS.qI_apply, Finset.sum_eq_single a]
  · rw [GlobalTheory.DegCnt.LiftS.i_e N a a ha, if_pos rfl, one_smul]
  · intro b _ hba
    rw [GlobalTheory.DegCnt.LiftS.i_e N a b ha, if_neg hba, zero_smul]
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ a, ha⟩) h

theorem p_i (a : Fin r) (ha : N.j ≤ a.val) : pI N (N.ist a) = 0 := by
  exact GlobalTheory.DegCnt.LiftS.p_zero N (fun b hb => N.ist_iso a b ha hb)

theorem q_X {y : V} (hy : y ∈ N.F.X) : qI N y = 0 := by
  exact GlobalTheory.DegCnt.LiftS.q_zero N (fun b _ => GlobalTheory.DegCnt.LiftS.orth_e N.F hy b)

theorem c_ne : N.c ≠ 0 := by
  intro h
  have h1 := N.c_norm
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem e'_eq (b : Fin r) (hb : N.j ≤ b.val) : N.F'.e b.castSucc = N.c • N.F.e b.castSucc := by
  exact N.same b.castSucc hb

theorem z'_eq : N.F'.z = N.c • N.F.z := by
  show N.F'.e (Fin.last r) = N.c • N.F.e (Fin.last r)
  exact N.same _ (by rw [Fin.val_last]; exact N.j_le)

theorem q_X' {y : V} (hy : y ∈ N.F'.X) : qI N y = 0 := by
  rw [qI_apply]
  refine Finset.sum_eq_zero (fun b hb => ?_)
  have hb' : N.j ≤ b.val := (Finset.mem_filter.1 hb).2
  have h1 : H.B y (N.F'.e b.castSucc) = 0 := orth_X N.F' hy (e_mem_Xa N.F' b b.2)
  rw [e'_eq N b hb', map_smulₛₗ] at h1
  have hc : starRingEnd K N.c ≠ 0 := by
    intro h
    have h2 := N.c_norm
    rw [← starRingEnd_apply, h, mul_zero] at h2
    exact zero_ne_one h2
  rw [smul_eq_mul] at h1
  rw [(mul_eq_zero.1 h1).resolve_left hc, zero_smul]

theorem hermForm_second_flag_X_z_eq_zero {y : V} (hy : y ∈ N.F'.X) : H.B y N.F.z = 0 := by
  have h1 : H.B y N.F'.z = 0 := hermFlag_isotropicPart_orthogonal_anisotropicVector N.F' hy
  rw [z'_eq N, map_smulₛₗ, smul_eq_mul] at h1
  have hc : starRingEnd K N.c ≠ 0 := by
    intro h
    have h2 := N.c_norm
    rw [← starRingEnd_apply, h, mul_zero] at h2
    exact zero_ne_one h2
  exact (mul_eq_zero.1 h1).resolve_left hc

theorem p_Xa {y : V} (hy : y ∈ N.F.Xa N.j) : pI N y = 0 := by
  refine p_zero N (fun b hb => orth_of N.F hy (fun a ha => ?_))
  rw [N.ist_e a b hb, if_neg]
  rintro rfl
  omega

theorem p_Xa' {y : V} (hy : y ∈ N.F'.Xa N.j) : pI N y = 0 :=
  p_zero N (fun b hb => orth_of N.F' hy (fun a ha => N.ist_e' a b ha hb))

theorem projectionOntoCommonIsotropicPart_anisotropicVector : pI N N.F.z = 0 :=
  p_zero N (fun b hb => N.normalForm_dual_orthogonal_last b hb)

theorem projectionOntoDualIsotropicSpan_anisotropicVector : qI N N.F.z = 0 :=
  q_zero N (fun b _ => symm0 H (N.F.zperp b))

theorem e_mem_II (b : Fin r) (hb : N.j ≤ b.val) : N.F.e b.castSucc ∈ II N.F N.F' := by
  have he : N.F.e b.castSucc = N.c⁻¹ • N.F'.e b.castSucc := by
    rw [e'_eq N b hb, smul_smul, inv_mul_cancel₀ (c_ne N), one_smul]
  refine Submodule.mem_inf.2 ⟨e_mem_Xa N.F b b.2, ?_⟩
  rw [he]
  exact Submodule.smul_mem _ _ (e_mem_Xa N.F' b b.2)

theorem p_mem (y : V) : pI N y ∈ II N.F N.F' := by
  rw [pI_apply]
  exact Submodule.sum_mem _ (fun b hb =>
    Submodule.smul_mem _ _ (e_mem_II N b (Finset.mem_filter.1 hb).2))

theorem p_II (h0 : II N.F N.F' ⊓ N.F.Xa N.j = ⊥) {y : V} (hy : y ∈ II N.F N.F') : pI N y = y := by
  have key : N.F.X ≤ (N.F.Xa N.j).comap (LinearMap.id - pI N) := by
    show Submodule.span K ((fun b : Fin r => N.F.e b.castSucc) '' {b | b.val < r}) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨b, -, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]
    by_cases hbj : N.j ≤ b.val
    · rw [p_e N b hbj, sub_self]
      exact Submodule.zero_mem _
    · have hb : N.F.e b.castSucc ∈ N.F.Xa N.j := e_mem_Xa N.F b (by omega)
      rw [p_Xa N hb, sub_zero]
      exact hb
  have hX : y ∈ N.F.X := (Submodule.mem_inf.1 hy).1
  have hm : y - pI N y ∈ II N.F N.F' ⊓ N.F.Xa N.j :=
    Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hy (p_mem N y), key hX⟩
  rw [h0, Submodule.mem_bot] at hm
  exact (sub_eq_zero.1 hm).symm

theorem qq (y : V) : qI N (qI N y) = qI N y := by
  rw [qI_apply N y, map_sum]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [map_smul, q_i N b (Finset.mem_filter.1 hb).2]

theorem pq (y : V) : pI N (qI N y) = 0 := by
  rw [qI_apply N y, map_sum]
  refine Finset.sum_eq_zero (fun b hb => ?_)
  rw [map_smul, p_i N b (Finset.mem_filter.1 hb).2, smul_zero]

theorem projectionOntoDualIsotropicSpan_orthogonal_anisotropic (y : V) : H.B (qI N y) N.F.z = 0 := by
  rw [qI_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero (fun b hb => ?_)
  rw [map_smul, LinearMap.smul_apply, symm0 H (N.normalForm_dual_orthogonal_last b (Finset.mem_filter.1 hb).2), smul_zero]

theorem II_le_uPerp {y : V} (hy : y ∈ II N.F N.F') : y ∈ uPerp N.F N.F' := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hy
  refine (mem_perp_iff H (N.F.X ⊔ N.F'.X) y).2 (fun x hx => ?_)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add, orth_X N.F h1 ha, orth_X N.F' h2 hb, add_zero]

theorem z_mem_uPerp : N.F.z ∈ uPerp N.F N.F' := by
  refine (mem_perp_iff H (N.F.X ⊔ N.F'.X) N.F.z).2 (fun x hx => ?_)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add, symm0 H (hermFlag_isotropicPart_orthogonal_anisotropicVector N.F ha), symm0 H (hermForm_second_flag_X_z_eq_zero N hb), add_zero]

theorem isotropicSpan_le_jointSpan_left : N.F.X ≤ V0 N.F N.F' :=
  le_sup_left.trans (le_sup_left : N.F.X ⊔ N.F'.X ≤ _)
theorem isotropicSpan_le_jointSpan_right : N.F'.X ≤ V0 N.F N.F' :=
  le_sup_right.trans (le_sup_left : N.F.X ⊔ N.F'.X ≤ _)
theorem lastVector_mem_jointSpan_left : N.F.z ∈ V0 N.F N.F' :=
  Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))

theorem hermFramePairNormalForm_frameSpan_le_of_generators {M : Submodule K V} (h1 : N.F.X ≤ M) (h2 : N.F'.X ≤ M) (h3 : N.F.z ∈ M) : V0 N.F N.F' ≤ M := by
  have h4 : N.F'.z ∈ M := by
    rw [z'_eq N]
    exact M.smul_mem _ h3
  exact sup_le (sup_le h1 h2)
    (Submodule.span_le.2 (Set.insert_subset_iff.2 ⟨h3, Set.singleton_subset_iff.2 h4⟩))

theorem hermFramePairNormalForm_complement_orthogonal_frameSpan {w y : V} (hw : w ∈ N.Wt) (hy : y ∈ V0 N.F N.F') : H.B w y = 0 :=
  (mem_perp_iff H (V0 N.F N.F' ⊔ N.Ist) w).1 hw y (Submodule.mem_sup_left hy)

theorem p_Wt {w : V} (hw : w ∈ N.Wt) : pI N w = 0 := by
  refine p_zero N (fun b hb => ?_)
  have hI : N.ist b ∈ N.Ist := Submodule.subset_span ⟨b, hb, rfl⟩
  exact (mem_perp_iff H (V0 N.F N.F' ⊔ N.Ist) w).1 hw _ (Submodule.mem_sup_right hI)

theorem q_Wt {w : V} (hw : w ∈ N.Wt) : qI N w = 0 :=
  q_zero N (fun b _ => hermFramePairNormalForm_complement_orthogonal_frameSpan N hw (isotropicSpan_le_jointSpan_left N (e_mem_Xa N.F b b.2)))

theorem projectionOntoDualIsotropicSpan_frameSpan_eq_zero {y : V} (hy : y ∈ V0 N.F N.F') : qI N y = 0 :=
  LinearMap.mem_ker.1 (hermFramePairNormalForm_frameSpan_le_of_generators N (M := LinearMap.ker (qI N)) (fun _ hx => LinearMap.mem_ker.2 (q_X N hx))
    (fun _ hx => LinearMap.mem_ker.2 (q_X' N hx)) (LinearMap.mem_ker.2 (projectionOntoDualIsotropicSpan_anisotropicVector N)) hy)

theorem q_Ist {y : V} (hy : y ∈ N.Ist) : qI N y = y := by
  have key : N.Ist ≤ LinearMap.eqLocus (qI N) LinearMap.id := by
    show Submodule.span K (N.ist '' {b | N.j ≤ b.val}) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    exact LinearMap.mem_eqLocus.2 (by rw [q_i N b hb, LinearMap.id_apply])
  exact LinearMap.mem_eqLocus.1 (key hy)

end Conc

section Lat
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)

omit [NumberField K] [StarRing K] in
theorem mem_line {A : Submodule (𝓞 K) K} (v : V) {t : K} (ht : t ∈ A) : t • v ∈ line A v := by
  unfold line
  exact Submodule.mem_map.2 ⟨t, ht, by simp⟩

omit [NumberField K] [StarRing K] in
theorem line_le {A : Submodule (𝓞 K) K} {v : V} {M : Submodule (𝓞 K) V} (h : ∀ t ∈ A, t • v ∈ M) :
    line A v ≤ M := by
  unfold line
  rintro _ ⟨t, ht, rfl⟩
  simpa using h t ht

noncomputable def Pst : Submodule (𝓞 K) V := ⨆ a : Fin r, ⨆ _ : N.j ≤ a.val, line (ipow N.𝔡 ((r : ℤ) - a.val)) (N.ist a)

theorem Pst_le : Pst N ≤ N.P0 := by
  unfold Pst NF.P0
  exact le_sup_right

theorem mem_Pst (a : Fin r) (ha : N.j ≤ a.val) {t : K} (ht : t ∈ ipow N.𝔡 ((r : ℤ) - a.val)) :
    t • N.ist a ∈ Pst N := by
  unfold Pst
  exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha (mem_line _ ht))

theorem hermFramePairNormalForm_smul_frame_mem_referenceLattice (a : Fin r) {t : K} (ht : t ∈ N.aa a) : t • N.F.e a.castSucc ∈ N.P0 := by
  have h : t • N.F.e a.castSucc ∈ ⨆ a : Fin r, line (N.aa a) (N.F.e a.castSucc) :=
    Submodule.mem_iSup_of_mem a (mem_line _ ht)
  unfold NF.P0
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left h))

theorem hermFramePairNormalForm_anisotropic_mem_referenceLattice : N.F.z ∈ N.P0 := by
  have h1 : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have h : (1 : K) • N.F.z ∈ line 1 N.F.z := mem_line _ h1
  rw [one_smul] at h
  unfold NF.P0
  exact Submodule.mem_sup_left (Submodule.mem_sup_right h)

theorem normalForm_baseLattice_le_dualSpan_sup_line {M : Submodule (𝓞 K) V} (h1 : ∀ a : Fin r, ∀ t ∈ N.aa a, t • N.F.e a.castSucc ∈ M)
    (h2 : ∀ a : Fin r, a.val < N.j → ∀ t ∈ N.aa a, t • N.F'.e a.castSucc ∈ M)
    (h3 : ∀ t ∈ (1 : Submodule (𝓞 K) K), t • N.F.z ∈ M)
    (h4 : ∀ a : Fin r, N.j ≤ a.val → ∀ t ∈ ipow N.𝔡 ((r : ℤ) - a.val), t • N.ist a ∈ M) : N.P0 ≤ M := by
  unfold NF.P0
  refine sup_le (sup_le (sup_le ?_ ?_) (line_le h3)) ?_
  · exact iSup_le fun a => line_le (h1 a)
  · exact iSup_le fun a => iSup_le fun ha => line_le (h2 a ha)
  · exact iSup_le fun a => iSup_le fun ha => line_le (h4 a ha)

private theorem B_smul_ist_mem_one_of_mem_ipow (a : Fin r) (ha : N.j ≤ a.val) {t : K} (ht : t ∈ ipow N.𝔡 ((r : ℤ) - a.val))
    {y : V} (hy : y ∈ N.P0) : H.B y (t • N.ist a) ∈ (1 : Submodule (𝓞 K) K) := by
  have hz : (0 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.zero_mem _
  have hle : N.P0 ≤ (1 : Submodule (𝓞 K) K).comap ((H.B.flip (t • N.ist a)).restrictScalars (𝓞 K)) := by
    apply normalForm_baseLattice_le_dualSpan_sup_line
    · intro b u hu
      simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.flip_apply, map_smul,
        LinearMap.smul_apply, LinearMap.map_smulₛₗ, N.ist_e b a ha, smul_eq_mul]
      split_ifs with hba
      · subst hba
        have hm := Submodule.mul_mem_mul (ipow_star N.𝔡 N.𝔡_ne N.𝔡_star _ ht) hu
        unfold NF.aa at hm
        rw [ipow_mul N.𝔡 N.𝔡_ne] at hm
        convert hm using 1
        simp only [starRingEnd_apply, mul_one]
        ring
      · simpa using hz
    · intro b hb u hu
      simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.flip_apply, map_smul,
        LinearMap.smul_apply, LinearMap.map_smulₛₗ, N.ist_e' b a hb ha, smul_eq_mul, mul_zero]
      exact hz
    · intro u hu
      simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.flip_apply, map_smul,
        LinearMap.smul_apply, LinearMap.map_smulₛₗ, N.normalForm_dual_orthogonal_last a ha, smul_eq_mul, mul_zero]
      exact hz
    · intro b hb u hu
      simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.flip_apply, map_smul,
        LinearMap.smul_apply, LinearMap.map_smulₛₗ, N.ist_iso b a hb ha, smul_eq_mul, mul_zero]
      exact hz
  simpa using hle hy

theorem pair_int {x y : V} (hx : x ∈ Pst N) (hy : y ∈ N.P0) : H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
  have hle : Pst N ≤ (1 : Submodule (𝓞 K) K).comap ((H.B.flip y).restrictScalars (𝓞 K)) := by
    unfold Pst
    refine iSup_le fun a => iSup_le fun ha => line_le fun t ht => ?_
    have h := star_one_mem (B_smul_ist_mem_one_of_mem_ipow N a ha ht hy)
    rw [H.herm] at h
    simpa using h
  simpa using hle hx

theorem pair_ideal (𝔫 : Ideal (𝓞 K)) (hn : ∀ x ∈ 𝔫, ∃ y ∈ 𝔫, (y : K) = star (x : K)) {x y : V}
    (hx : x ∈ Pst N) (hy : y ∈ 𝔫 • N.P0) : ∃ m ∈ 𝔫, (m : K) = H.B x y := by
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro c hc v hv
    obtain ⟨k, hk⟩ := Submodule.mem_one.1 (pair_int N hx hv)
    obtain ⟨c', hc', hc'e⟩ := hn c hc
    refine ⟨c' * k, Ideal.mul_mem_right _ _ hc', ?_⟩
    rw [← algebraMap_smul K c v, LinearMap.map_smulₛₗ, smul_eq_mul, ← hk, starRingEnd_apply]
    change algebraMap (𝓞 K) K (c' * k) = _
    rw [map_mul]
    congr 1
    all_goals exact hc'e
  · rintro a b ⟨m1, hm1, e1⟩ ⟨m2, hm2, e2⟩
    refine ⟨m1 + m2, Ideal.add_mem _ hm1 hm2, ?_⟩
    rw [map_add, ← e1, ← e2]
    simp

theorem coef_mem (𝔫 : Ideal (𝓞 K)) (b : Fin r) (hb : N.j ≤ b.val) (γ : K)
    (h : ∀ u ∈ N.aa b, ∃ m ∈ 𝔫, (m : K) = γ * u) : γ • N.ist b ∈ 𝔫 • Pst N := by
  have h1 : (1 : K) ∈ N.aa b * ipow N.𝔡 ((r : ℤ) - b.val) := by
    rw [Submodule.mul_comm]
    unfold NF.aa
    rw [ipow_mul N.𝔡 N.𝔡_ne]
    exact Submodule.mem_one.2 ⟨1, map_one _⟩
  have key : ∀ w ∈ N.aa b * ipow N.𝔡 ((r : ℤ) - b.val), (γ * w) • N.ist b ∈ 𝔫 • Pst N := by
    intro w hw
    refine Submodule.mul_induction_on hw (C := fun w => (γ * w) • N.ist b ∈ 𝔫 • Pst N) ?_ ?_
    · intro u hu v hv
      obtain ⟨m, hm, hme⟩ := h u hu
      have hv' := mem_Pst N b hb hv
      have e : (γ * (u * v)) • N.ist b = m • (v • N.ist b) := by
        rw [← algebraMap_smul K m, smul_smul, ← mul_assoc]
        congr 1
        rw [← hme]
      rw [e]
      exact Submodule.smul_mem_smul hm hv'
    · intro w1 w2 h1 h2
      rw [mul_add, add_smul]
      exact Submodule.add_mem _ h1 h2
  simpa using key 1 h1

omit [NumberField K] [StarRing K] [IsScalarTower (𝓞 K) K V] in
theorem symm_mem (s : V ≃ₗ[K] V) (n : ℕ) (hn : ((s : V →ₗ[K] V) - 1) ^ n = 0) (Q : Submodule (𝓞 K) V)
    (h : ∀ x ∈ Q, s x - x ∈ Q) {y : V} (hy : y ∈ Q) : s.symm y ∈ Q := by
  set M : V →ₗ[K] V := (s : V →ₗ[K] V) - 1 with hM
  have hneg : ∀ x ∈ Q, (-M) x ∈ Q := by
    intro x hx
    have := Q.neg_mem (h x hx)
    simpa [hM] using this
  have hpow : ∀ k : ℕ, ∀ x ∈ Q, ((-M) ^ k) x ∈ Q := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih => intro x hx; rw [pow_succ', Module.End.mul_apply]; exact hneg _ (ih x hx)
  have hg : (s : V →ₗ[K] V) * ∑ i ∈ Finset.range n, (-M) ^ i = 1 := by
    have := mul_neg_geom_sum (-M) n
    rw [neg_pow, hn, mul_zero, sub_zero, sub_neg_eq_add, hM, add_sub_cancel] at this
    exact this
  have e : s.symm y = (∑ i ∈ Finset.range n, (-M) ^ i) y := by
    apply s.injective
    rw [LinearEquiv.apply_symm_apply]
    have := congrArg (fun f : V →ₗ[K] V => f y) hg
    simpa [Module.End.mul_apply] using this.symm
  rw [e, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ => hpow i y hy

end Lat

section Main
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem s_Xa (G : FlagD H r) {s : V →ₗ[K] V} (hs : G.InN s) (a : ℕ) {y : V} (hy : y ∈ G.Xa a) :
    s y ∈ G.Xa a := by
  obtain ⟨-, -, he, -⟩ := hs
  have key : ∀ b : Fin r, b.val < a → s (G.e b.castSucc) ∈ G.Xa a := by
    intro b hb
    have h1 : s (G.e b.castSucc) - G.e b.castSucc ∈ G.Xa a := Xa_mono G hb.le (he b)
    have h2 : G.e b.castSucc ∈ G.Xa a := Submodule.subset_span ⟨b, hb, rfl⟩
    simpa using add_mem h1 h2
  have hle : G.Xa a ≤ (G.Xa a).comap s := Submodule.span_le.2 (by
    rintro _ ⟨b, hb, rfl⟩
    exact key b hb)
  exact hle hy

theorem exists_lift [FiniteDimensional K V] (N : NF H r) (h0 : II N.F N.F' ⊓ N.F.Xa N.j = ⊥)
    (htop : N.Wt ⊔ (V0 N.F N.F' ⊔ N.Ist) = ⊤) (τ : K) (hτ : τ + star τ = 1) (s : V ≃ₗ[K] V)
    (hF : N.F.InN (s : V →ₗ[K] V)) (hF' : N.F'.InN (s : V →ₗ[K] V))
    (hU : ∀ y ∈ uPerp N.F N.F', s y - y ∈ II N.F N.F')
    (hU' : ∀ y ∈ uPerp N.F N.F', s.symm y - y ∈ II N.F N.F') :
    ∃ s' ∈ N.Rs, (∀ y ∈ V0 N.F N.F', s' y = s y) ∧
      ∀ y ∈ N.Ist, s' y = trans H (s N.F.z - N.F.z) N.F.z N.T τ (qI N (s y)) := by
  obtain ⟨d, hd⟩ : ∃ d : V, d = s N.F.z - N.F.z := ⟨_, rfl⟩
  rw [← hd]
  have hIIX : ∀ y ∈ II N.F N.F', y ∈ N.F.X := fun y hy => (Submodule.mem_inf.1 hy).1
  have hIIX' : ∀ y ∈ II N.F N.F', y ∈ N.F'.X := fun y hy => (Submodule.mem_inf.1 hy).2
  have hIIV0 : ∀ y ∈ II N.F N.F', y ∈ V0 N.F N.F' := fun y hy => isotropicSpan_le_jointSpan_left N (hIIX y hy)
  have hsII : ∀ y ∈ II N.F N.F', s y ∈ II N.F N.F' := fun y hy => by
    simpa using add_mem (hU y (II_le_uPerp N hy)) hy
  have hsII' : ∀ y ∈ II N.F N.F', s.symm y ∈ II N.F N.F' := fun y hy => by
    simpa using add_mem (hU' y (II_le_uPerp N hy)) hy
  have hdII : d ∈ II N.F N.F' := by rw [hd]; exact hU _ (z_mem_uPerp N)
  have hT0 : (N.T : K) ≠ 0 := by rw [← N.hT]; exact N.F.hT
  have hzz : H.B N.F.z N.F.z = -(N.T : K) := by rw [← N.hT]; exact N.F.zz
  have hdz : H.B d N.F.z = 0 := hermFlag_isotropicPart_orthogonal_anisotropicVector N.F (hIIX d hdII)
  have hzd : H.B N.F.z d = 0 := symm0 H hdz
  have hdd : H.B d d = 0 := orth_X N.F (hIIX d hdII) (hIIX d hdII)
  have hisoS : ∀ x y, H.B (s x) (s y) = H.B x y := fun x y => hF.1 x y
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[K] V,
      f = (trans H d N.F.z (N.T : K) τ).comp (levi (pI N) (qI N) (s : V →ₗ[K] V)) := ⟨_, rfl⟩
  have hfa : ∀ y, f y = trans H d N.F.z (N.T : K) τ (levi (pI N) (qI N) (s : V →ₗ[K] V) y) :=
    fun y => by rw [hf]; rfl
  have hlev : ∀ x y, H.B (levi (pI N) (qI N) (s : V →ₗ[K] V) x)
      (levi (pI N) (qI N) (s : V →ₗ[K] V) y) = H.B x y :=
    levi_isom H (pI N) (qI N) s (adj N) (fun x => p_II N h0 (p_mem N x)) (qq N) (pq N)
      (fun x => q_X N (hIIX _ (p_mem N x))) hisoS
      (fun x => p_II N h0 (hsII _ (p_mem N x))) (fun x => p_II N h0 (hsII' _ (p_mem N x)))
  have hfiso : ∀ x y, H.B (f x) (f y) = H.B x y := fun x y => by
    rw [hfa, hfa, trans_isom H d N.F.z (N.T : K) τ hT0 (by simp) hτ hdd hdz hzz, hlev]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact H.nondeg x fun y => by rw [← hfiso x y, hx]; simp
  have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.1 hinj
  have htr : ∀ y, H.B y N.F.z = 0 → H.B y d = 0 → trans H d N.F.z (N.T : K) τ y = y := by
    intro y h1 h2
    rw [trans_apply, h1, h2]
    simp
  have hfII : ∀ u ∈ II N.F N.F', f u = s u := by
    intro u hu
    have hsu := hsII u hu
    rw [hfa, levi_apply, p_II N h0 hu, q_X N (hIIX u hu)]
    simp only [sub_self, sub_zero, map_zero, add_zero, LinearEquiv.coe_coe]
    exact htr _ (hermFlag_isotropicPart_orthogonal_anisotropicVector N.F (hIIX _ hsu)) (orth_X N.F (hIIX _ hsu) (hIIX d hdII))
  have hfXa : ∀ u ∈ N.F.Xa N.j, f u = s u := by
    intro u hu
    have hsu : s u ∈ N.F.Xa N.j := s_Xa N.F hF N.j hu
    have hsuX : s u ∈ N.F.X := Xa_le_X N.F N.j hsu
    rw [hfa, levi_apply, p_Xa N hu, q_X N (Xa_le_X N.F N.j hu)]
    simp only [sub_zero, map_zero, add_zero, zero_add, LinearEquiv.coe_coe]
    rw [p_Xa N hsu, q_X N hsuX, sub_zero, sub_zero]
    exact htr _ (hermFlag_isotropicPart_orthogonal_anisotropicVector N.F hsuX) (orth_X N.F hsuX (hIIX d hdII))
  have hfXa' : ∀ u ∈ N.F'.Xa N.j, f u = s u := by
    intro u hu
    have hsu : s u ∈ N.F'.Xa N.j := s_Xa N.F' hF' N.j hu
    have hsuX : s u ∈ N.F'.X := Xa_le_X N.F' N.j hsu
    rw [hfa, levi_apply, p_Xa' N hu, q_X' N (Xa_le_X N.F' N.j hu)]
    simp only [sub_zero, map_zero, add_zero, zero_add, LinearEquiv.coe_coe]
    rw [p_Xa' N hsu, q_X' N hsuX, sub_zero, sub_zero]
    exact htr _ (hermForm_second_flag_X_z_eq_zero N hsuX) (orth_X N.F' hsuX (hIIX' d hdII))
  have hfz : f N.F.z = s N.F.z := by
    have e : s N.F.z = d + N.F.z := by rw [hd, sub_add_cancel]
    have hps : pI N (s N.F.z) = d := by rw [e, map_add, p_II N h0 hdII, projectionOntoCommonIsotropicPart_anisotropicVector N, add_zero]
    have hqs : qI N (s N.F.z) = 0 := by rw [e, map_add, q_X N (hIIX d hdII), projectionOntoDualIsotropicSpan_anisotropicVector N, add_zero]
    rw [hfa, levi_apply, projectionOntoCommonIsotropicPart_anisotropicVector N, projectionOntoDualIsotropicSpan_anisotropicVector N]
    simp only [sub_zero, map_zero, add_zero, zero_add, LinearEquiv.coe_coe]
    rw [hps, hqs, sub_zero]
    have e2 : s N.F.z - d = N.F.z := by rw [hd, sub_sub_cancel]
    rw [e2, trans_apply, hzz, hzd, mul_neg, inv_mul_cancel₀ hT0, hd]
    simp
  have hfV0 : ∀ u ∈ V0 N.F N.F', f u = s u := by
    have hle : V0 N.F N.F' ≤ LinearMap.eqLocus f (s : V →ₗ[K] V) := by
      apply hermFramePairNormalForm_frameSpan_le_of_generators N
      · show N.F.Xa r ≤ _
        apply Xa_le
        intro b _
        rw [LinearMap.mem_eqLocus]
        by_cases hb : N.j ≤ b.val
        · exact hfII _ (e_mem_II N b hb)
        · exact hfXa _ (e_mem_Xa N.F b (not_le.1 hb))
      · show N.F'.Xa r ≤ _
        apply Xa_le
        intro b _
        rw [LinearMap.mem_eqLocus]
        by_cases hb : N.j ≤ b.val
        · rw [e'_eq N b hb]
          exact hfII _ (Submodule.smul_mem _ _ (e_mem_II N b hb))
        · exact hfXa' _ (e_mem_Xa N.F' b (not_le.1 hb))
      · exact LinearMap.mem_eqLocus.2 hfz
    exact fun u hu => LinearMap.mem_eqLocus.1 (hle hu)
  have hWtU : ∀ w ∈ N.Wt, w ∈ uPerp N.F N.F' := by
    intro w hw
    rw [uPerp, mem_perp_iff]
    intro x hx
    exact hermFramePairNormalForm_complement_orthogonal_frameSpan N hw ((sup_le (isotropicSpan_le_jointSpan_left N) (isotropicSpan_le_jointSpan_right N)) hx)
  have hfw : ∀ w ∈ N.Wt, f w = w := by
    intro w hw
    have hpw : pI N w = 0 := p_Wt N hw
    have hqw : qI N w = 0 := q_Wt N hw
    have hι : s w - w ∈ II N.F N.F' := hU w (hWtU w hw)
    have hps : pI N (s w) = s w - w := by
      have := map_add (pI N) (s w - w) w
      rwa [sub_add_cancel, p_II N h0 hι, hpw, add_zero] at this
    have hqs : qI N (s w) = 0 := by
      have := map_add (qI N) (s w - w) w
      rwa [sub_add_cancel, q_X N (hIIX _ hι), hqw, add_zero] at this
    rw [hfa, levi_apply, hpw, hqw]
    simp only [sub_zero, map_zero, add_zero, zero_add, LinearEquiv.coe_coe]
    rw [hps, hqs, sub_zero, sub_sub_cancel]
    exact htr w (hermFramePairNormalForm_complement_orthogonal_frameSpan N hw (lastVector_mem_jointSpan_left N)) (hermFramePairNormalForm_complement_orthogonal_frameSpan N hw (hIIV0 d hdII))
  have hfI : ∀ y ∈ N.Ist, f y = trans H d N.F.z (N.T : K) τ (qI N (s y)) := by
    intro y hy
    have hqy : qI N y = y := q_Ist N hy
    have hpy : pI N y = 0 := by
      have := pq N y
      rwa [hqy] at this
    rw [hfa, levi_apply, hpy, hqy]
    simp only [sub_zero, sub_self, map_zero, add_zero, zero_add, LinearEquiv.coe_coe]
  have hdec : ∀ y, qI N y = 0 → ∃ w ∈ N.Wt, ∃ u ∈ V0 N.F N.F', w + u = y := by
    intro y hy
    have hy' : y ∈ N.Wt ⊔ (V0 N.F N.F' ⊔ N.Ist) := by rw [htop]; exact Submodule.mem_top
    obtain ⟨w, hw, v, hv, rfl⟩ := Submodule.mem_sup.1 hy'
    obtain ⟨u, hu, i, hi, rfl⟩ := Submodule.mem_sup.1 hv
    have hq : qI N (w + (u + i)) = i := by
      rw [map_add, map_add, q_Wt N hw, projectionOntoDualIsotropicSpan_frameSpan_eq_zero N hu, q_Ist N hi, zero_add, zero_add]
    rw [hq] at hy
    exact ⟨w, hw, u, hu, by rw [hy, add_zero]⟩
  have hFs : ∀ G : FlagD H r, G.InN (s : V →ₗ[K] V) → (∀ a : Fin r, G.e a.castSucc ∈ V0 N.F N.F') →
      (∀ y, (∀ a : Fin r, H.B (G.e a.castSucc) y = 0) → qI N y = 0) →
      (∀ w ∈ N.Wt, s w - w ∈ G.X) → G.InN f := by
    intro G hG hGV0 hGq hGw
    refine ⟨hfiso, ⟨hinj, hsurj⟩, fun a => ?_, fun y hy => ?_⟩
    · rw [hfV0 _ (hGV0 a)]
      exact hG.2.2.1 a
    · obtain ⟨w, hw, u, hu, rfl⟩ := hdec y (hGq y hy)
      have e : f (w + u) - (w + u) = (s (w + u) - (w + u)) - (s w - w) := by
        rw [map_add, map_add, hfw w hw, hfV0 u hu]
        abel
      rw [e]
      exact sub_mem (hG.2.2.2 _ hy) (hGw w hw)
  have hcoe : ((LinearEquiv.ofBijective f ⟨hinj, hsurj⟩ : V ≃ₗ[K] V) : V →ₗ[K] V) = f :=
    LinearMap.ext fun x => rfl
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, ?_, fun y hy => hfV0 y hy, fun y hy => hfI y hy⟩
  show _ ∈ N.R ⊓ N.fixing N.Wt
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · show _ ∈ Subgroup.closure _
    apply Subgroup.subset_closure
    show N.F.InN _ ∧ N.F'.InN _
    rw [hcoe]
    exact ⟨hFs N.F hF (fun a => isotropicSpan_le_jointSpan_left N (e_mem_Xa N.F a a.isLt))
        (fun y hy => q_zero N fun b _ => symm0 H (hy b)) (fun w hw => hIIX _ (hU w (hWtU w hw))),
      hFs N.F' hF' (fun a => isotropicSpan_le_jointSpan_right N (e_mem_Xa N.F' a a.isLt))
        (fun y hy => q_zero N fun b hb =>
          symm0 H (orth_of N.F' (hIIX' _ (e_mem_II N b hb)) fun b' _ => hy b'))
        (fun w hw => hIIX' _ (hU w (hWtU w hw)))⟩
  · show _ ∈ fixingSubgroup (V ≃ₗ[K] V) ((N.Wt : Submodule K V) : Set V)
    rw [mem_fixingSubgroup_iff]
    intro y hy
    exact hfw y hy

end Main

theorem dual_congr {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
    (𝔫 : Ideal (𝓞 K)) (hn : ∀ x ∈ 𝔫, ∃ y ∈ 𝔫, (y : K) = star (x : K)) (τ : 𝓞 K) (s : V ≃ₗ[K] V)
    (hF : ∀ x y, H.B (s x) (s y) = H.B x y) (Q : Submodule (𝓞 K) V)
    (hQ : ∀ b : Fin r, ∀ t ∈ N.aa b, s.symm (t • N.F.e b.castSucc) ∈ Q) (hzQ : N.F.z ∈ Q)
    (hc1 : ∀ x ∈ Q, s x - x ∈ 𝔫 • N.P0) (h' : V) (hh' : h' ∈ 𝔫 • N.P0)
    (eh : (N.T : K) • h' = s N.F.z - N.F.z) (x : V) (hx : x ∈ Pst N) (hx' : x ∈ N.Ist) :
    trans H (s N.F.z - N.F.z) N.F.z N.T τ (qI N (s x)) - x ∈ 𝔫 • N.P0 := by
  have hT0 : ((N.T : ℕ) : K) ≠ 0 := by rw [← N.hT]; exact N.F.hT
  have hyx : qI N (s x) - x ∈ 𝔫 • Pst N := by
    rw [show qI N (s x) - x = qI N (s x - x) by rw [map_sub, q_Ist N hx'], qI_apply]
    refine Submodule.sum_mem _ fun b hb => ?_
    have hb' : N.j ≤ b.val := (Finset.mem_filter.1 hb).2
    refine coef_mem N 𝔫 b hb' _ fun u hu => ?_
    have hsu : star u ∈ N.aa b := by
      show star u ∈ ipow N.𝔡 _
      exact ipow_star N.𝔡 N.𝔡_ne N.𝔡_star _ hu
    have hv : s.symm (star u • N.F.e b.castSucc) ∈ Q := hQ b (star u) hsu
    have hd : star u • N.F.e b.castSucc - s.symm (star u • N.F.e b.castSucc) ∈ 𝔫 • N.P0 := by
      have h1 := hc1 _ hv
      rwa [LinearEquiv.apply_symm_apply] at h1
    obtain ⟨m, hm, hmx⟩ := pair_ideal N 𝔫 hn hx hd
    refine ⟨-m, 𝔫.neg_mem hm, ?_⟩
    have e2 : H.B x (s.symm (star u • N.F.e b.castSucc)) = H.B (s x) (star u • N.F.e b.castSucc) := by
      rw [← hF x, LinearEquiv.apply_symm_apply]
    have e3 : ∀ v, H.B v (star u • N.F.e b.castSucc) = u * H.B v (N.F.e b.castSucc) := by
      intro v
      rw [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul]
    rw [map_sub, e2, e3, e3] at hmx
    show algebraMap (𝓞 K) K (-m) = _
    rw [map_neg]
    show -((m : K)) = _
    rw [hmx]
    simp only [map_sub, LinearMap.sub_apply]
    ring
  have hyP : qI N (s x) ∈ Pst N := by
    have h2 := (Pst N).add_mem hx (Submodule.smul_le_right hyx)
    rwa [show x + (qI N (s x) - x) = qI N (s x) by abel] at h2
  obtain ⟨m, hm, hmy⟩ := pair_ideal N 𝔫 hn hyP hh'
  have hyz : H.B (qI N (s x)) N.F.z = 0 := projectionOntoDualIsotropicSpan_orthogonal_anisotropic N (s x)
  have hBh : ((N.T : ℕ) : K)⁻¹ * H.B (qI N (s x)) (s N.F.z - N.F.z) = (m : K) := by
    rw [← eh, LinearMap.map_smulₛₗ, starRingEnd_apply, star_natCast, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hT0, one_mul, hmy]
  rw [trans_apply, hyz, mul_zero, zero_smul, sub_zero, hBh, ← eh]
  have c1 : (m : K) • N.F.z = m • N.F.z := algebraMap_smul K m N.F.z
  have c2 : ((τ : K) * (m : K)) • (((N.T : ℕ) : K) • h') = (τ * m * (N.T : 𝓞 K)) • h' := by
    rw [smul_smul, ← algebraMap_smul K (τ * m * (N.T : 𝓞 K)) h', map_mul, map_mul, map_natCast]
  rw [c1, c2, show ∀ a b c d : V, a + b + c - d = (a - d) + b + c from fun a b c d => by abel]
  exact add_mem (add_mem (Submodule.smul_mono le_rfl (Pst_le N) hyx)
    (Submodule.smul_mem_smul hm (hermFramePairNormalForm_anisotropic_mem_referenceLattice N))) (Submodule.smul_mem _ _ hh')

private theorem smul_e_castSucc_mem_P0_of_lt_j {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
    (N : NF H r) (a : Fin r) (ha : a.val < N.j) {t : K} (ht : t ∈ N.aa a) :
    t • N.F'.e a.castSucc ∈ N.P0 := by
  unfold NF.P0
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_right
  exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha (mem_line _ ht))

private theorem symm_smul_e_castSucc_mem_P0_inf_of_unipotent {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
    (N : NF H r) (𝔫 : Ideal (𝓞 K)) (s : V ≃ₗ[K] V)
    (hun : ((s : V →ₗ[K] V) - 1) ^ (2 * r + 1) = 0) (hc : ∀ x ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'),
      s x - x ∈ (Ideal.span {(N.T : 𝓞 K)} * 𝔫) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'))) :
    ∀ b : Fin r, ∀ t ∈ N.aa b, s.symm (t • N.F.e b.castSucc) ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') := by
  intro b t ht
  refine symm_mem s (2 * r + 1) hun _ (fun x hx => Submodule.smul_le_right (hc x hx)) ?_
  exact Submodule.mem_inf.2 ⟨hermFramePairNormalForm_smul_frame_mem_referenceLattice N b ht, (Submodule.restrictScalars_mem _ _ _).2
    (Submodule.smul_mem _ t (isotropicSpan_le_jointSpan_left N (e_mem_Xa N.F b b.isLt)))⟩

private theorem exists_mem_smul_P0_T_smul_eq_sub_z {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
    (N : NF H r) (𝔫 : Ideal (𝓞 K)) (s : V ≃ₗ[K] V) (hc : ∀ x ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'),
      s x - x ∈ (Ideal.span {(N.T : 𝓞 K)} * 𝔫) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'))) :
    ∃ h' ∈ 𝔫 • N.P0, ((N.T : ℕ) : K) • h' = s N.F.z - N.F.z := by
  have hzQ : N.F.z ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') :=
    Submodule.mem_inf.2 ⟨hermFramePairNormalForm_anisotropic_mem_referenceLattice N, (Submodule.restrictScalars_mem _ _ _).2 (lastVector_mem_jointSpan_left N)⟩
  have hz := hc N.F.z hzQ
  rw [Submodule.mul_smul, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hz
  obtain ⟨h', hh'Q, eh0⟩ := hz
  refine ⟨h', Submodule.smul_mono le_rfl inf_le_left hh'Q, ?_⟩
  rw [← eh0, ← algebraMap_smul K (N.T : 𝓞 K) h', map_natCast]

private theorem sub_mem_smul_P0_of_congr_T_mul {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
    (N : NF H r) (𝔫 : Ideal (𝓞 K)) (s : V ≃ₗ[K] V) (hc : ∀ x ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'),
      s x - x ∈ (Ideal.span {(N.T : 𝓞 K)} * 𝔫) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'))) :
    ∀ x ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'), s x - x ∈ 𝔫 • N.P0 := by
  intro x hx
  have h1 := hc x hx
  rw [Submodule.mul_smul] at h1
  exact Submodule.smul_mono le_rfl inf_le_left (Submodule.smul_le_right h1)

private theorem lift_congruence_lemma_6 {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
    (N : NF H r) (𝔫 : Ideal (𝓞 K))
    (hn : ∀ x ∈ 𝔫, ∃ y ∈ 𝔫, (y : K) = star (x : K)) (τ : 𝓞 K) (s s' : V ≃ₗ[K] V)
    (hF : ∀ x y, H.B (s x) (s y) = H.B x y) (hun : ((s : V →ₗ[K] V) - 1) ^ (2 * r + 1) = 0) (hc : ∀ x ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'),
      s x - x ∈ (Ideal.span {(N.T : 𝓞 K)} * 𝔫) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')))
    (hs'I : ∀ y ∈ N.Ist, s' y = trans H (s N.F.z - N.F.z) N.F.z N.T τ (qI N (s y)))
    (a : Fin r) (ha : N.j ≤ a.val) (t : K) (ht : t ∈ ipow N.𝔡 ((r : ℤ) - a.val)) :
    s' (t • N.ist a) - t • N.ist a ∈ 𝔫 • N.P0 := by
  have hzQ : N.F.z ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') :=
    Submodule.mem_inf.2 ⟨hermFramePairNormalForm_anisotropic_mem_referenceLattice N, (Submodule.restrictScalars_mem _ _ _).2 (lastVector_mem_jointSpan_left N)⟩
  obtain ⟨h', hh', eh⟩ := exists_mem_smul_P0_T_smul_eq_sub_z N 𝔫 s hc
  have hxI : t • N.ist a ∈ N.Ist := by
    unfold NF.Ist
    exact Submodule.smul_mem _ t (Submodule.subset_span ⟨a, ha, rfl⟩)
  rw [hs'I _ hxI]
  exact dual_congr N 𝔫 hn τ s hF _ (symm_smul_e_castSucc_mem_P0_inf_of_unipotent N 𝔫 s hun hc) hzQ
    (sub_mem_smul_P0_of_congr_T_mul N 𝔫 s hc) h' hh' eh _ (mem_Pst N a ha ht) hxI

private theorem sub_mem_smul_P0_of_eqOn_V0 {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
    (N : NF H r) (𝔫 : Ideal (𝓞 K)) (s s' : V ≃ₗ[K] V) (hc : ∀ x ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'),
      s x - x ∈ (Ideal.span {(N.T : 𝓞 K)} * 𝔫) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')))
    (hs'V : ∀ y ∈ V0 N.F N.F', s' y = s y) (x : V) (hV : x ∈ V0 N.F N.F') (hP : x ∈ N.P0) :
    s' x - x ∈ 𝔫 • N.P0 := by
  rw [hs'V x hV]
  exact sub_mem_smul_P0_of_congr_T_mul N 𝔫 s hc x (Submodule.mem_inf.2 ⟨hP, (Submodule.restrictScalars_mem _ _ _).2 hV⟩)

private theorem lift_congruence_lemma {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
    (N : NF H r) (𝔫 : Ideal (𝓞 K))
    (hn : ∀ x ∈ 𝔫, ∃ y ∈ 𝔫, (y : K) = star (x : K)) (τ : 𝓞 K) (s s' : V ≃ₗ[K] V)
    (hF : ∀ x y, H.B (s x) (s y) = H.B x y) (hun : ((s : V →ₗ[K] V) - 1) ^ (2 * r + 1) = 0) (hc : ∀ x ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'),
      s x - x ∈ (Ideal.span {(N.T : 𝓞 K)} * 𝔫) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')))
    (hs'V : ∀ y ∈ V0 N.F N.F', s' y = s y)
    (hs'I : ∀ y ∈ N.Ist, s' y = trans H (s N.F.z - N.F.z) N.F.z N.T τ (qI N (s y))) :
    N.P0 ≤ (𝔫 • N.P0).comap (((s' : V →ₗ[K] V) - LinearMap.id).restrictScalars (𝓞 K)) := by
  apply normalForm_baseLattice_le_dualSpan_sup_line N
  · intro a t ht
    exact sub_mem_smul_P0_of_eqOn_V0 N 𝔫 s s' hc hs'V _
      (Submodule.smul_mem _ t (isotropicSpan_le_jointSpan_left N (e_mem_Xa N.F a a.isLt))) (hermFramePairNormalForm_smul_frame_mem_referenceLattice N a ht)
  · intro a ha t ht
    exact sub_mem_smul_P0_of_eqOn_V0 N 𝔫 s s' hc hs'V _
      (Submodule.smul_mem _ t (isotropicSpan_le_jointSpan_right N (e_mem_Xa N.F' a a.isLt))) (smul_e_castSucc_mem_P0_of_lt_j N a ha ht)
  · intro t ht
    obtain ⟨m, rfl⟩ := Submodule.mem_one.1 ht
    refine sub_mem_smul_P0_of_eqOn_V0 N 𝔫 s s' hc hs'V _ (Submodule.smul_mem _ _ (lastVector_mem_jointSpan_left N)) ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ m (hermFramePairNormalForm_anisotropic_mem_referenceLattice N)
  · intro a ha t ht
    exact lift_congruence_lemma_6 N 𝔫 hn τ s s' hF hun hc hs'I a ha t ht

theorem lift_congruence : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ 𝔫 : Ideal (𝓞 K), (∀ x ∈ 𝔫, ∃ y ∈ 𝔫, (y : K) = star (x : K)) → ∀ s ∈ N.R, (∀ x ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'), s x - x ∈ (Ideal.span {(N.T : 𝓞 K)} * 𝔫) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'))) → ∃ s' ∈ N.Rs, (∀ y ∈ V0 N.F N.F', s' y = s y) ∧ ∀ x ∈ N.P0, s' x - x ∈ 𝔫 • N.P0 := by
  intro K V _ _ _ _ _ _ _ _ H hK r N 𝔫 hn s hs hc
  obtain ⟨hNF, -, hcompl, -, -, -, -, -, -, -, -, hPi⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨⟨-, -, -, -, h0, -⟩, -⟩ := hNF
  obtain ⟨τ, hτ⟩ := GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram K hK
  have hsR := (GlobalTheory.UnipStab.mem_R N s).1 hs
  have htop : N.Wt ⊔ (V0 N.F N.F' ⊔ N.Ist) = ⊤ := by rw [← hPi]; exact hcompl.sup_eq_top
  have hU' : ∀ y ∈ uPerp N.F N.F', s.symm y - y ∈ II N.F N.F' := fun y hy =>
    GlobalTheory.UnipStab.sub_mem_II N (N.R.inv_mem hs) hy
  obtain ⟨s', hs'R, hs'V, hs'I⟩ := exists_lift N h0 htop (τ : K) hτ s hsR.1 hsR.2
    (fun y hy => GlobalTheory.UnipStab.sub_mem_II N hs hy) hU'
  refine ⟨s', hs'R, hs'V, fun x hx => ?_⟩
  have h7 := lift_congruence_lemma N 𝔫 hn τ s s' hsR.1.1 (GlobalTheory.UnipStab.pow_eq_zero hsR.1) hc hs'V hs'I hx
  exact h7

end GlobalTheory.DegCnt.LiftS
