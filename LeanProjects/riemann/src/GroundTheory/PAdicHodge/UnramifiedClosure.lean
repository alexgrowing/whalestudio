import Mathlib
import GroundTheory.PAdicHodge.GaloisOnCp
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.UnramifiedClosureCountableNeighbourhoods
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Polynomial Filter Topology

variable (p : ℕ) [hp : Fact p.Prime]

def primeToPRoots : Set (PadicAlgCl p) := {x | ∃ m : ℕ, 0 < m ∧ m.Coprime p ∧ x ^ m = 1}

def unramifiedClosure : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p] (primeToPRoots p)

def maxUnramified (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    IntermediateField ℚ_[p] (PadicAlgCl p) :=
  K ⊓ unramifiedClosure p

variable {p}

theorem mem_maxUnramified {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {x : PadicAlgCl p} :
    x ∈ maxUnramified p K ↔ x ∈ K ∧ x ∈ unramifiedClosure p :=
  Iff.rfl

theorem mem_unramifiedClosure_of_pow_eq_one {x : PadicAlgCl p} {m : ℕ} (hm : 0 < m)
    (hc : m.Coprime p) (hx : x ^ m = 1) : x ∈ unramifiedClosure p :=
  IntermediateField.subset_adjoin _ _ ⟨m, hm, hc, hx⟩

theorem gal_mem_unramifiedClosure (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {x : PadicAlgCl p}
    (hx : x ∈ unramifiedClosure p) : τ x ∈ unramifiedClosure p := by
  have h : (unramifiedClosure p).map (τ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) ≤
      unramifiedClosure p := by
    rw [unramifiedClosure, IntermediateField.adjoin_map]
    apply IntermediateField.adjoin_le_iff.2
    rintro _ ⟨y, ⟨m, hm, hc, hy⟩, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hc, by rw [← map_pow, hy, map_one]⟩
  exact h ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)

theorem norm_natCast_p_algCl_lt_one : ‖(p : PadicAlgCl p)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem norm_natCast_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends]
  exact norm_natCast_p_algCl_lt_one

theorem norm_natCast_p_pos : 0 < ‖(p : ℂ_[p])‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)

theorem norm_sub_le_max_of_ultrametric {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E] (a b : E) :
    ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg, ← norm_neg b]
  exact IsUltrametricDist.norm_add_le_max a (-b)

theorem mem_unramifiedClosure_of_forall_approx {β : PadicAlgCl p}
    (h : ∀ m : ℕ, ∃ u ∈ unramifiedClosure p, ‖β - u‖ ≤ ‖(p : PadicAlgCl p)‖ ^ m) :
    β ∈ unramifiedClosure p := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup (unramifiedClosure p),
    IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have hnorm : ∀ z, ‖σ z‖ = ‖z‖ := fun z => (spectralNorm_eq_of_equiv σ z).symm
  have key : ∀ m : ℕ, ‖σ β - β‖ ≤ ‖(p : PadicAlgCl p)‖ ^ m := fun m => by
    obtain ⟨u, hu, hbu⟩ := h m
    have hσu : σ u = u := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ u hu
    have e : σ β - β = σ (β - u) - (β - u) := by rw [map_sub, hσu]; ring
    rw [e]
    refine (norm_sub_le_max_of_ultrametric _ _).trans (max_le ?_ hbu)
    rw [hnorm]
    exact hbu
  by_contra hne
  have hpos : 0 < ‖σ β - β‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (norm_natCast_p_algCl_lt_one (p := p))
  exact absurd (key m) (not_le.2 hm)

theorem exists_eq_of_pow_eq_self {ω : ℂ_[p]} {r : ℕ} (hr : 1 ≤ r) (h : ω ^ p ^ r = ω) :
    ∃ u ∈ unramifiedClosure p, (u : ℂ_[p]) = ω := by
  by_cases h0 : ω = 0
  · exact ⟨0, zero_mem _, by rw [h0]; rfl⟩
  set n := p ^ r - 1 with hn
  have hq : 2 ≤ p ^ r := hp.out.two_le.trans (Nat.le_self_pow (by omega) p)
  have hnpos : 0 < n := by omega
  have hqn : p ^ r = n + 1 := by omega
  have hω : ω ^ n = 1 := by
    rw [hqn, pow_succ] at h
    exact (mul_eq_right₀ h0).1 h
  have hcop : n.Coprime p := by
    have h1 : n.Coprime (n + 1) := Nat.coprime_self_add_right.2 (Nat.coprime_one_right n)
    rw [← hqn] at h1
    exact h1.coprime_dvd_right (dvd_pow_self p (by omega))

  set P : (PadicAlgCl p)[X] := X ^ n - 1
  have hmon : P.Monic := monic_X_pow_sub_C 1 (by omega)
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hP := hsplit.eq_prod_roots_of_monic hmon
  have hev : (P.map (algebraMap (PadicAlgCl p) ℂ_[p])).eval ω = 0 := by
    simp [P, hω]
  rw [hP] at hev
  simp only [Polynomial.map_multiset_prod, eval_multiset_prod, Multiset.map_map] at hev
  obtain ⟨x, hx, ha0⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 hev)
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, eval_sub,
    eval_X, eval_C] at ha0
  have hxroot : x ^ n = 1 := by
    have := (mem_roots hmon.ne_zero).1 hx
    rw [IsRoot, eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] at this
    exact this
  exact ⟨x, mem_unramifiedClosure_of_pow_eq_one hnpos hcop hxroot, (sub_eq_zero.1 ha0).symm⟩

section Approx

variable {F : Type*} [NormedField F] [IsUltrametricDist F]

omit hp in

theorem norm_pow_sub_pow_le {a b : F} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_mul, norm_pow, norm_pow]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) ha) (pow_nonneg (norm_nonneg _) _)
    (pow_le_one₀ (norm_nonneg _) hb)

omit hp in

theorem norm_pow_p_sub_pow_p_le {a b : F} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hp1 : ‖(p : F)‖ ≤ 1)
    {e : ℕ} (he : 1 ≤ e) (hab : ‖a - b‖ ≤ ‖(p : F)‖ ^ e) :
    ‖a ^ p - b ^ p‖ ≤ ‖(p : F)‖ ^ (e + 1) := by
  rw [← geom_sum₂_mul, norm_mul, pow_succ, mul_comm (‖(p : F)‖ ^ e)]
  refine mul_le_mul ?_ hab (norm_nonneg _) (norm_nonneg _)
  have hsum : ∑ i ∈ Finset.range p, b ^ i * b ^ (p - 1 - i) = (p : F) * b ^ (p - 1) := by
    rw [Finset.sum_congr rfl fun i hi => (by
      rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega :
        b ^ i * b ^ (p - 1 - i) = b ^ (p - 1)), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsplit : ∑ i ∈ Finset.range p, a ^ i * b ^ (p - 1 - i) =
      (p : F) * b ^ (p - 1) + ∑ i ∈ Finset.range p, (a ^ i - b ^ i) * b ^ (p - 1 - i) := by
    rw [← hsum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hb)
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_mul, norm_pow]
    have hpe : ‖(p : F)‖ ^ e ≤ ‖(p : F)‖ := by
      calc ‖(p : F)‖ ^ e ≤ ‖(p : F)‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hp1 he
        _ = ‖(p : F)‖ := pow_one _
    exact (mul_le_mul (((norm_pow_sub_pow_le ha hb i).trans hab).trans hpe)
      (pow_le_one₀ (norm_nonneg _) hb) (by positivity) (norm_nonneg _)).trans (mul_one _).le

omit hp in

theorem norm_pow_pow_sub_pow_pow_le {a b : F} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hp1 : ‖(p : F)‖ ≤ 1)
    {e : ℕ} (he : 1 ≤ e) (hab : ‖a - b‖ ≤ ‖(p : F)‖ ^ e) (r : ℕ) :
    ‖a ^ p ^ r - b ^ p ^ r‖ ≤ ‖(p : F)‖ ^ (e + r) := by
  induction r with
  | zero => simpa using hab
  | succ r ih =>
    rw [pow_succ, pow_mul, pow_mul, ← add_assoc]
    exact norm_pow_p_sub_pow_p_le (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha)
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hb) hp1 (by omega) ih

end Approx

theorem exists_approx_of_pow_sub {z : ℂ_[p]} (hz : ‖z‖ ≤ 1) {r m : ℕ} (hr : 1 ≤ r)
    (h : ‖z ^ p ^ r - z‖ ≤ ‖(p : ℂ_[p])‖ ^ m) :
    ∃ u ∈ unramifiedClosure p, ‖z - (u : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨0, zero_mem _, by simpa using hz⟩
  have hp1 : ‖(p : ℂ_[p])‖ ≤ 1 := norm_natCast_p_lt_one.le
  set q := p ^ r
  set u : ℕ → ℂ_[p] := fun j => z ^ q ^ j with hu
  have hnorm : ∀ j, ‖u j‖ ≤ 1 := fun j => by
    simp only [hu, norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
  have hsucc : ∀ j, u (j + 1) = u j ^ q := fun j => by simp only [hu, pow_succ, pow_mul]
  have hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ ‖(p : ℂ_[p])‖ ^ (m + j) := by
    intro j
    induction j with
    | zero => simpa [hu, q] using h
    | succ j ih =>
      have key := norm_pow_pow_sub_pow_pow_le (hnorm (j + 1)) (hnorm j) hp1 (by omega) ih r
      have e1 : u (j + 1) ^ p ^ r = u (j + 1 + 1) := (hsucc (j + 1)).symm
      have e2 : u j ^ p ^ r = u (j + 1) := (hsucc j).symm
      rw [e1, e2] at key
      exact key.trans
        (pow_le_pow_of_le_one (norm_nonneg _) hp1 (show m + (j + 1) ≤ m + j + r by omega))
  have hcauchy : CauchySeq u := by
    refine cauchySeq_of_le_geometric ‖(p : ℂ_[p])‖ (‖(p : ℂ_[p])‖ ^ m) norm_natCast_p_lt_one
      fun j => ?_
    rw [dist_comm, dist_eq_norm, ← pow_add]
    exact hstep j
  obtain ⟨ω, hω⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hclose : ∀ j, ‖u j - z‖ ≤ ‖(p : ℂ_[p])‖ ^ m := by
    intro j
    induction j with
    | zero => simp [hu]
    | succ j ih =>
      have e : u (j + 1) - z = (u (j + 1) - u j) + (u j - z) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hstep j).trans
        (pow_le_pow_of_le_one (norm_nonneg _) hp1 (by omega))) ih)
  have hωz : ‖ω - z‖ ≤ ‖(p : ℂ_[p])‖ ^ m := by
    have ht : Tendsto (fun j => ‖u j - z‖) atTop (𝓝 ‖ω - z‖) :=
      (continuous_norm.tendsto _).comp (hω.sub_const z)
    exact le_of_tendsto ht (Eventually.of_forall hclose)
  have hfix : ω ^ q = ω := by
    have h1 : Tendsto (fun j => u j ^ q) atTop (𝓝 (ω ^ q)) := hω.pow q
    have h2 : Tendsto (fun j => u j ^ q) atTop (𝓝 ω) := by
      simp_rw [← hsucc]
      exact (tendsto_add_atTop_iff_nat 1).2 hω
    exact tendsto_nhds_unique h1 h2
  obtain ⟨v, hv, hvω⟩ := exists_eq_of_pow_eq_self hr hfix
  refine ⟨v, hv, ?_⟩
  rw [hvω, ← norm_neg, neg_sub]
  exact hωz

theorem exists_lt_norm_pow_sub_lt {c : PadicAlgCl p} (hc : ‖c‖ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (f : ℕ → ℕ) : ∃ k₀ k₁, k₀ < k₁ ∧ ‖c ^ f k₁ - c ^ f k₀‖ < ε :=
  _root_.GroundTheory.Variant₂.N1.exists_lt_norm_pow_sub_pow_lt hc hε f

theorem eventually_approx_pow {c : ℂ_[p]} (hc : ‖c‖ ≤ 1) (m : ℕ) :
    ∃ K : ℕ, ∀ k ≥ K, ∃ u ∈ unramifiedClosure p,
      ‖c ^ p ^ k - (u : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ m := by
  set δ := ‖(p : ℂ_[p])‖ ^ m
  have hδ : 0 < δ := pow_pos norm_natCast_p_pos m
  have hδ1 : δ ≤ 1 := pow_le_one₀ (norm_nonneg _) norm_natCast_p_lt_one.le
  obtain ⟨c', hc'⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)).exists_dist_lt c hδ
  rw [dist_eq_norm] at hc'
  have hc'1 : ‖(c' : ℂ_[p])‖ ≤ 1 := by
    have e : (c' : ℂ_[p]) = c - (c - c') := by ring
    rw [e]
    exact (norm_sub_le_max_of_ultrametric _ _).trans (max_le hc (hc'.le.trans hδ1))
  have hc'1' : ‖c'‖ ≤ 1 := by rwa [PadicComplex.norm_extends] at hc'1
  obtain ⟨k₀, k₁, hlt, hnear⟩ := exists_lt_norm_pow_sub_lt hc'1' hδ (fun k => p ^ k)
  have hnear' : ‖(c' : ℂ_[p]) ^ p ^ k₁ - (c' : ℂ_[p]) ^ p ^ k₀‖ < δ := by
    have e : (c' : ℂ_[p]) ^ p ^ k₁ - (c' : ℂ_[p]) ^ p ^ k₀ = ((c' ^ p ^ k₁ - c' ^ p ^ k₀ : PadicAlgCl p) : ℂ_[p]) := by
      simp only [UniformSpace.Completion.coe_sub, PadicComplex.coe_eq, map_pow]
    rw [e, PadicComplex.norm_extends]
    exact hnear
  refine ⟨k₀, fun k hk => ?_⟩
  set r := k₁ - k₀
  have hr : 1 ≤ r := by omega
  set z := c ^ p ^ k
  have hz : ‖z‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc
  have hzq : z ^ p ^ r = c ^ p ^ (k + r) := by rw [← pow_mul, ← pow_add]
  have hkr : k + r = k₁ + (k - k₀) := by omega
  have hk' : k = k₀ + (k - k₀) := by omega
  have hA : ‖c ^ p ^ (k + r) - (c' : ℂ_[p]) ^ p ^ (k + r)‖ < δ :=
    (norm_pow_sub_pow_le hc hc'1 _).trans_lt hc'
  have hB : ‖(c' : ℂ_[p]) ^ p ^ (k + r) - (c' : ℂ_[p]) ^ p ^ k‖ < δ := by
    have e1 : (c' : ℂ_[p]) ^ p ^ (k + r) = ((c' : ℂ_[p]) ^ p ^ k₁) ^ p ^ (k - k₀) := by
      rw [← pow_mul, ← pow_add, hkr]
    have e2 : (c' : ℂ_[p]) ^ p ^ k = ((c' : ℂ_[p]) ^ p ^ k₀) ^ p ^ (k - k₀) := by
      rw [← pow_mul, ← pow_add, ← hk']
    rw [e1, e2]
    refine (norm_pow_sub_pow_le ?_ ?_ _).trans_lt hnear' <;>
      · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc'1
  have hC : ‖(c' : ℂ_[p]) ^ p ^ k - c ^ p ^ k‖ < δ := by
    rw [← norm_neg, neg_sub]
    exact (norm_pow_sub_pow_le hc hc'1 _).trans_lt hc'
  have hsum : ‖z ^ p ^ r - z‖ ≤ δ := by
    have e : z ^ p ^ r - z = (c ^ p ^ (k + r) - (c' : ℂ_[p]) ^ p ^ (k + r)) +
        (((c' : ℂ_[p]) ^ p ^ (k + r) - (c' : ℂ_[p]) ^ p ^ k) + ((c' : ℂ_[p]) ^ p ^ k - c ^ p ^ k)) := by
      rw [hzq]; ring
    rw [e]
    exact ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA.le
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hB.le hC.le))))
  exact exists_approx_of_pow_sub hz hr hsum

end GroundTheory.PAdicHodge
