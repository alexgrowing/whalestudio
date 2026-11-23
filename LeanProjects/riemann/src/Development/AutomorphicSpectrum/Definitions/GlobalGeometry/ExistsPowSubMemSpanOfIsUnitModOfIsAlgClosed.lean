import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {F : Type} [Field F] [NumberField F]

abbrev evC (z : (Σ k, ι k) → ℂ) (g : MRing ι) : ℂ := eval z (map (Int.castRingHom ℂ) g)

def OverInt (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) : Prop :=
  (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) ∧
    ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ a : 𝓞 F, φ (a : F) ∈ chartRingZ y c

def PtOver (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (z : (Σ k, ι k) → ℂ) : Prop :=
  z ∈ mcPts (mCoordIdeal y) ∧ ∀ (a : F) (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d → IsMultiHomog h d →
    aeval y g = φ a * aeval y h → evC z g = σ a * evC z h

def IsUnitSec (P : Ideal (MRing ι)) (f g : MRing ι) : Prop :=
  ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W → ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P

structure IsPlaceWeight (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ) : Prop where
  inv : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z
  smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  near : ∀ σ z, PtOver y φ σ z → ∀ᶠ z' in nhds z, u z' = t σ

def IsPlaceWeight.shift {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} {s : (F →+* ℂ) → ℝ} {u : ((Σ k, ι k) → ℂ) → ℝ}
    (hu : IsPlaceWeight y φ s u) (A : HermLine ι) : HermLine ι :=
  A.tensor (HermLine.ofWeight u hu.inv)

def meanEmb (t : (F →+* ℂ) → ℝ) : ℝ := (∑ σ : F →+* ℂ, t σ) / (Module.finrank ℚ F : ℝ)

structure FlatHerm (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (A : HermLine ι) where
  M : ℕ
  M_pos : 0 < M
  f : MRing ι
  g : MRing ι
  df : K → ℕ
  dg : K → ℕ
  hf : IsMultiHomog f df
  hg : IsMultiHomog g dg
  deg : ∀ k, (df k : ℤ) - dg k = M * A.a k
  f_ne : f ∉ mCoordIdeal y
  g_ne : g ∉ mCoordIdeal y
  unit : IsUnitSec (mCoordIdeal y) f g
  κ : (F →+* ℂ) → ℝ
  κ_pos : ∀ σ, 0 < κ σ
  κ_conj : ∀ σ, κ (ComplexEmbedding.conjugate σ) = κ σ
  norm : ∀ σ z, PtOver y φ σ z → ‖evC z f‖ = (κ σ * A.h z) ^ M * ‖evC z g‖

def FlatHerm.ht {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} {A : HermLine ι} (S : FlatHerm y φ A) : ℝ :=
  -meanEmb fun σ => Real.log (S.κ σ)

end GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.Inh

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat

variable (F : Type) [Field F] [NumberField F]

abbrev Idx : Unit → Type := fun _ => Option (Module.Free.ChooseBasisIndex ℤ (𝓞 F))

def intPt (i : Option (Module.Free.ChooseBasisIndex ℤ (𝓞 F))) : 𝓞 F :=
  i.elim 1 (RingOfIntegers.basis F)

def pt (p : Σ k, Idx F k) : F := (intPt F p.2 : F)

theorem pt_none : pt F ⟨(), none⟩ = 1 := by simp [pt, intPt]

theorem mem_of_inv_mem {S : Subalgebra ℤ F} {x : F} (hx : x ≠ 0) (hi : IsIntegral ℤ x) (h : x⁻¹ ∈ S) :
    x ∈ S := by
  obtain ⟨q, hq, h0⟩ := hi
  rcases Nat.eq_zero_or_pos q.natDegree with hd | hd
  · rw [hq.natDegree_eq_zero.mp hd] at h0; simp at h0
  obtain ⟨m, hm⟩ : ∃ m, q.natDegree = m + 1 := ⟨q.natDegree - 1, by omega⟩
  rw [Polynomial.eval₂_eq_sum_range, hm, Finset.sum_range_succ] at h0
  have hc : q.coeff (m + 1) = 1 := by rw [← hm]; exact hq.coeff_natDegree
  rw [hc, map_one, one_mul] at h0
  have : x = -∑ i ∈ Finset.range (m + 1), algebraMap ℤ F (q.coeff i) * x⁻¹ ^ (m - i) := by
    have hxm : x ^ m ≠ 0 := pow_ne_zero _ hx
    apply mul_left_cancel₀ hxm
    rw [mul_neg, Finset.mul_sum, ← pow_succ, eq_neg_iff_add_eq_zero, add_comm, ← h0]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hi'
    simp only [Nat.add_sub_cancel_left, pow_add, inv_pow]
    field_simp
  rw [this]
  exact neg_mem (Subalgebra.sum_mem _ fun i _ => mul_mem (S.algebraMap_mem _) (pow_mem h _))

theorem overInt_pt : OverInt (pt F) (RingHom.id F) := by
  refine ⟨fun k => ⟨none, by rw [pt_none]; exact one_ne_zero⟩, fun c hc a => ?_⟩
  have hg : ∀ p, pt F p / pt F ⟨(), c ()⟩ ∈ chartRingZ (pt F) c := fun p =>
    Algebra.subset_adjoin ⟨p, rfl⟩
  have h1 : pt F ⟨(), c ()⟩ ∈ chartRingZ (pt F) c := by
    refine mem_of_inv_mem F (hc ()) (intPt F (c ())).isIntegral_coe ?_
    have := hg ⟨(), none⟩
    rwa [pt_none, one_div] at this
  have h2 : ∀ p, pt F p ∈ chartRingZ (pt F) c := fun p => by
    have := mul_mem (hg p) h1
    rwa [div_mul_cancel₀ _ (hc ())] at this
  rw [← (RingOfIntegers.basis F).sum_repr a]
  simp only [RingHom.id_apply, map_sum, map_zsmul, RingOfIntegers.coe_eq_algebraMap]
  exact Subalgebra.sum_mem _ fun i _ => zsmul_mem (h2 ⟨(), some i⟩) _

theorem X_none_notMem (W : Ideal (MRing (Idx F))) (hW : W.IsPrime) (hP : mCoordIdeal (pt F) ≤ W)
    (hr : IsRelevant W) : (X ⟨(), none⟩ : MRing (Idx F)) ∉ W := by
  intro h0
  obtain ⟨j, hj⟩ := hr ()
  obtain ⟨q, hq, hz⟩ := (intPt F j).isIntegral_coe
  have hG : (∑ i ∈ Finset.range (q.natDegree + 1), C (q.coeff i) * X ⟨(), j⟩ ^ i *
      X ⟨(), none⟩ ^ (q.natDegree - i) : MRing (Idx F)) ∈ mCoordIdeal (pt F) := by
    rw [mCoordIdeal, RingHom.mem_ker, map_sum]
    have : ∀ i ∈ Finset.range (q.natDegree + 1), mConeMap (pt F) (C (q.coeff i) * X ⟨(), j⟩ ^ i *
        X ⟨(), none⟩ ^ (q.natDegree - i) : MRing (Idx F)) =
        C (algebraMap ℤ F (q.coeff i) * pt F ⟨(), j⟩ ^ i) * X () ^ q.natDegree := by
      intro i hi
      have hi' : i ≤ q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hi'
      simp only [mConeMap, map_mul, map_pow, aeval_X, pt_none, map_one, one_mul, he,
        Nat.add_sub_cancel_left, eq_intCast, map_intCast]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← map_sum]
    rw [Polynomial.eval₂_eq_sum_range] at hz
    have hz' : ∑ i ∈ Finset.range (q.natDegree + 1), algebraMap ℤ F (q.coeff i) * pt F ⟨(), j⟩ ^ i = 0 := hz
    rw [hz', map_zero, zero_mul]
  have hG' := hP hG
  rw [Finset.sum_range_succ, hq.coeff_natDegree, Nat.sub_self, pow_zero, map_one, one_mul, mul_one] at hG'
  have hs : (∑ i ∈ Finset.range q.natDegree, C (q.coeff i) * X ⟨(), j⟩ ^ i *
      X ⟨(), none⟩ ^ (q.natDegree - i) : MRing (Idx F)) ∈ W :=
    W.sum_mem fun i hi => W.mul_mem_left _ (W.pow_mem_of_mem h0 _ (by
      have := Finset.mem_range.mp hi; omega))
  exact hj (hW.mem_of_pow_mem _ ((W.add_mem_iff_right hs).mp hG'))

def fs : HermLine (Idx F) where
  a := 1
  h z := √(∑ p, ‖z p‖ ^ 2)
  pos z hz := by
    obtain ⟨i, hi⟩ := hz ()
    exact Real.sqrt_pos.mpr (Finset.sum_pos' (fun _ _ => by positivity)
      ⟨⟨(), i⟩, Finset.mem_univ _, by positivity⟩)
  smul c z _ := by
    simp only [norm_mul, mul_pow, Pi.one_apply, zpow_one, Fintype.prod_unique]
    have : ∑ p : Σ k, Idx F k, ‖c p.1‖ ^ 2 * ‖z p‖ ^ 2 = ‖c default‖ ^ 2 * ∑ p, ‖z p‖ ^ 2 := by
      rw [Finset.mul_sum]
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

theorem homog_X (i : Idx F ()) : IsMultiHomog (X ⟨(), i⟩ : MRing (Idx F)) (fun _ => 1) := by
  classical
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  rw [Finset.sum_eq_single i] <;> simp +contextual [Finsupp.single_apply, eq_comm]

theorem sum_pos (σ : F →+* ℂ) : 0 < ∑ p, ‖σ (pt F p)‖ ^ 2 :=
  Finset.sum_pos' (fun _ _ => by positivity) ⟨⟨(), none⟩, Finset.mem_univ _, by simp [pt_none]⟩

def flatFs : FlatHerm (pt F) (RingHom.id F) (fs F) where
  M := 1
  M_pos := one_pos
  f := X ⟨(), none⟩
  g := 1
  df := fun _ => 1
  dg := fun _ => 0
  hf := homog_X F none
  hg := by
    intro m hm k
    rw [← C_1, C_apply] at hm
    have := Finset.mem_singleton.mp (support_monomial_subset hm)
    simp [this]
  deg k := by simp [fs]
  f_ne := by simp [mCoordIdeal, RingHom.mem_ker, mConeMap, pt_none]
  g_ne := by simp [mCoordIdeal, RingHom.mem_ker]
  unit W hW hP hr := ⟨1, X ⟨(), none⟩, (Ideal.ne_top_iff_one W).mp hW.ne_top, X_none_notMem F W hW hP hr, by simp⟩
  κ σ := (√(∑ p, ‖σ (pt F p)‖ ^ 2))⁻¹
  κ_pos σ := inv_pos.mpr (Real.sqrt_pos.mpr (sum_pos F σ))
  κ_conj σ := by simp [ComplexEmbedding.conjugate_coe_eq]
  norm σ z hz := by
    have h : ∀ p, z p = σ (pt F p) * z ⟨(), none⟩ := fun p => by
      have := hz.2 (pt F p) _ _ _ (homog_X F p.2) (homog_X F none) (by simp [pt_none])
      simpa [evC] using this
    have h2 : ∑ p, ‖z p‖ ^ 2 = (∑ p, ‖σ (pt F p)‖ ^ 2) * ‖z ⟨(), none⟩‖ ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun p _ => by rw [h p, norm_mul, mul_pow]
    have h3 := Real.sqrt_pos.mpr (sum_pos F σ)
    simp only [evC, map_X, eval_X, map_one, norm_one, mul_one, pow_one, fs]
    rw [h2, Real.sqrt_mul (sum_pos F σ).le, Real.sqrt_sq (norm_nonneg _)]
    field_simp

theorem ptOver_pt (σ : F →+* ℂ) : PtOver (pt F) (RingHom.id F) σ (fun p => σ (pt F p)) := by
  have e : ∀ g : MRing (Idx F), evC (fun p => σ (pt F p)) g = σ (aeval (pt F) g) := fun g => by
    induction g using MvPolynomial.induction_on with
    | C a => simp [evC]
    | add p q hp hq => simp only [evC, map_add] at *; rw [hp, hq]
    | mul_X p i hp => simp only [evC, map_mul, map_X, eval_X, aeval_X] at *; rw [hp]
  refine ⟨⟨fun k => ⟨none, by cases k; simp [pt_none]⟩, fun f hf => ?_⟩, fun a d g h _ _ H => by
    rw [e, e, H, map_mul]; rfl⟩
  have hf' : mConeMap (pt F) f = 0 := hf
  have e2 : ∀ g : MRing (Idx F), eval (fun _ : Unit => (1 : F)) (mConeMap (pt F) g) = aeval (pt F) g := fun g => by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => rw [map_mul, map_mul, hp, map_mul]; simp [mConeMap]
  have := e f
  rw [← e2, hf'] at this
  simpa using this

theorem ht_pos : 0 < (flatFs F).ht := by
  have h : ∀ σ : F →+* ℂ, Real.log ((flatFs F).κ σ) < 0 := fun σ => by
    refine Real.log_neg ((flatFs F).κ_pos σ) (inv_lt_one_of_one_lt₀ ?_)
    rw [Real.lt_sqrt zero_le_one, one_pow]
    obtain ⟨i⟩ := (RingOfIntegers.basis F).index_nonempty
    have hi : pt F ⟨(), some i⟩ ≠ 0 := by
      simpa [pt, intPt] using (RingOfIntegers.basis F).ne_zero i
    have := Finset.single_lt_sum (s := Finset.univ) (f := fun p => ‖σ (pt F p)‖ ^ 2) (i := ⟨(), none⟩)
      (j := ⟨(), some i⟩) (by simp) (Finset.mem_univ _) (Finset.mem_univ _)
      (by have : σ (pt F ⟨(), some i⟩) ≠ 0 := by simpa using hi
          positivity) (fun _ _ _ => by positivity)
    simpa [pt_none] using this
  unfold FlatHerm.ht meanEmb
  rw [neg_pos]
  exact div_neg_of_neg_of_pos (Finset.sum_neg (fun σ _ => h σ) Finset.univ_nonempty)
    (Nat.cast_pos.mpr Module.finrank_pos)

theorem isPlaceWeight_const (c : ℝ) : IsPlaceWeight (pt F) (RingHom.id F) (fun _ => c) (fun _ => c) :=
  ⟨fun _ _ _ => rfl, contDiffOn_const, fun _ _ _ => Filter.Eventually.of_forall fun _ => rfl⟩

example (c : ℝ) : meanEmb (fun _ : F →+* ℂ => c) = c := by
  have : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  simp only [meanEmb, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul]
  field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.Inh
