import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsShortBasisAdaptedOfSubsetSpan
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SumFinsuppAntidiagProdPowDivMultiFactorial

noncomputable section

open Module Submodule MvPolynomial NumberField

namespace GlobalTheory

theorem exists_short_basis_of_ratSpan {V E ι : Type*} [AddCommGroup V] [Module ℚ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Submodule ℤ V) (φ : V →+ E) {ε : ℝ} (hε : 0 < ε)
    (hφ : ∀ x ∈ H, x ≠ 0 → ε ≤ ‖φ x‖) (v : ι → V) (hvH : ∀ j, v j ∈ H)
    (hsp : (H : Set V) ⊆ span ℚ (Set.range v)) {r : ℝ} (hr : ∀ j, ‖φ (v j)‖ ≤ r) {R : ℕ}
    (hR : R = finrank ℚ (span ℚ (Set.range v))) :
    ∃ b : Basis (Fin R) ℤ H, ∀ i, ‖φ (b i)‖ ^ 2 ≤ ((R + 3 : ℝ) / 4) * r ^ 2 := by
  classical
  let ψ : H →ₗ[ℤ] E := φ.toIntLinearMap ∘ₗ H.subtype
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h
    have := hφ x x.2 (fun h' => h (Subtype.ext h'))
    have hx' : φ x = 0 := hx
    rw [hx', norm_zero] at this
    linarith
  let L : Submodule ℤ E := LinearMap.range ψ
  haveI : DiscreteTopology L := by
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have : ({0} : Set L) = Metric.ball 0 ε := by
      ext y
      simp only [Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right]
      refine ⟨fun h => by simpa [h] using hε, fun h => ?_⟩
      obtain ⟨_, x, rfl⟩ := y
      by_contra h0
      have hx : (x : V) ≠ 0 := fun h' => h0 (by
        have : x = 0 := Subtype.ext h'
        simp [this])
      exact absurd (hφ x x.2 hx) (not_le.2 h)
    rw [this]; exact Metric.isOpen_ball
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℝ (fun j => φ (v j))
  haveI : Finite κ := hli.finite
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  have hli' := hli.comp e.symm e.symm.injective
  have hL : ∀ i, (((fun j => φ (v j)) ∘ a) ∘ e.symm) i ∈ L := fun i => ⟨⟨_, hvH _⟩, rfl⟩
  have hsub : (L : Set E) ⊆ span ℝ (Set.range (((fun j => φ (v j)) ∘ a) ∘ e.symm)) := by
    rw [e.symm.surjective.range_comp, hspan]
    rintro _ ⟨x, rfl⟩
    have key : ∀ y ∈ span ℚ (Set.range v), φ y ∈ span ℝ (Set.range fun j => φ (v j)) := by
      intro y hy
      induction hy using span_induction with
      | mem y hy => obtain ⟨j, rfl⟩ := hy; exact subset_span ⟨j, rfl⟩
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
      | smul q y _ hy =>
        rw [show φ (q • y) = (q : ℝ) • φ y by simpa using map_ratCast_smul φ ℚ ℝ q y]
        exact smul_mem _ _ hy
    exact key x (hsp x.2)
  obtain ⟨b, -, hb⟩ := exists_short_basis_adapted_of_subset_span L hli' hL hsub
  let b' : Basis (Fin n) ℤ H := b.map (LinearEquiv.ofInjective ψ hψ).symm
  have hb' : ∀ i, φ (b' i) = b i := fun i => by
    have := LinearEquiv.ofInjective_apply ψ (h := hψ) (b' i)
    simp only [b', Basis.map_apply, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have hn : n = R := by
    have h1 : LinearIndependent ℚ (fun i => (b' i : V)) :=
      (LinearIndependent.iff_fractionRing ℤ ℚ).1
        (b'.linearIndependent.map' H.subtype H.ker_subtype)
    have h2 : span ℚ (Set.range fun i => (b' i : V)) = span ℚ (Set.range v) := by
      refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
      · rintro _ ⟨i, rfl⟩; exact hsp (b' i).2
      · rintro _ ⟨j, rfl⟩
        have h3 := b'.mem_span (⟨v j, hvH j⟩ : H)
        have h4 := Submodule.mem_map_of_mem (f := H.subtype) h3
        rw [Submodule.map_span, ← Set.range_comp] at h4
        exact span_subset_span ℤ ℚ _ h4
    rw [hR, ← h2, finrank_span_eq_card h1, Fintype.card_fin]
  subst hn
  refine ⟨b', fun i => ?_⟩
  rw [hb']
  refine (hb i).trans ((norm_sq_add_sum_Iio_le (r := r) fun j _ => hr (a (e.symm j))).trans
    (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)))
  have : ((i : ℕ) + 1 : ℝ) ≤ n := by exact_mod_cast i.2
  linarith

namespace MvPoly

variable {K σ : Type*} [Field K]

def integralPart (W : Submodule K (MvPolynomial σ K)) : Submodule ℤ (MvPolynomial σ K) :=
  W.restrictScalars ℤ ⊓ coeffsIn σ (integralClosure ℤ K).toSubmodule

theorem mem_integralPart {W : Submodule K (MvPolynomial σ K)} {P : MvPolynomial σ K} :
    P ∈ integralPart W ↔ P ∈ W ∧ ∀ α, IsIntegral ℤ (P.coeff α) := Iff.rfl

theorem smul_mem_integralPart {W : Submodule K (MvPolynomial σ K)} (c : 𝓞 K)
    {P : MvPolynomial σ K} (hP : P ∈ integralPart W) : c • P ∈ integralPart W :=
  ⟨W.smul_mem (c : K) hP.1, fun α => by
    change IsIntegral ℤ (coeff α ((c : K) • P))
    rw [coeff_smul, smul_eq_mul]
    exact c.isIntegral_coe.mul (hP.2 α)⟩

theorem span_ringOfIntegers_basis_integralPart {W : Submodule K (MvPolynomial σ K)} {ι : Type*}
    (b : Basis ι ℤ (integralPart W)) :
    (span (𝓞 K) (Set.range fun i => (b i : MvPolynomial σ K))).restrictScalars ℤ =
      integralPart W := by
  refine le_antisymm (fun P hP => ?_) (fun P hP => ?_)
  · change P ∈ span (𝓞 K) _ at hP
    induction hP using span_induction with
    | mem y hy => obtain ⟨j, rfl⟩ := hy; exact (b j).2
    | zero => simp
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul c y _ hy => exact smul_mem_integralPart c hy
  · have h4 := Submodule.mem_map_of_mem (f := (integralPart W).subtype) (b.mem_span ⟨P, hP⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h4
    exact span_subset_span ℤ (𝓞 K) _ h4

variable [NumberField K] [Fintype σ]

def conjCoeffs (K σ : Type*) [Field K] [NumberField K] [Fintype σ] [DecidableEq σ] (D : ℕ) :
    MvPolynomial σ K →+ EuclideanSpace ℂ ((K →+* ℂ) × monomialsLE σ D) where
  toFun P := WithLp.toLp 2 fun p => p.1 (P.coeff p.2)
  map_zero' := by ext; simp
  map_add' P Q := by ext; simp

theorem norm_conjCoeffs_sq [DecidableEq σ] {D : ℕ} {P : MvPolynomial σ K}
    (hP : P.totalDegree ≤ D) :
    ‖conjCoeffs K σ D P‖ ^ 2 = ∑ s : K →+* ℂ, l2Norm (map s P) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [l2Norm_eq_sqrt_sum_of_subset
    ((support_map_subset s P).trans (support_subset_monomialsLE.2 hP)),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), ← Finset.sum_coe_sort (monomialsLE σ D)]
  simp only [conjCoeffs, coeff_map, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

omit [NumberField K] in

theorem finrank_le_one_add_pow {W : Submodule K (MvPolynomial σ K)} {D : ℕ}
    (hD : ∀ P ∈ W, P.totalDegree ≤ D) : finrank K W ≤ (1 + D) ^ Fintype.card σ := by
  have h : W ≤ restrictTotalDegree σ K D := fun P hP => (mem_restrictTotalDegree σ D P).2 (hD P hP)
  refine (Submodule.finrank_mono h).trans ?_
  rw [finrank_restrictTotalDegree]
  exact choose_add_le_one_add_pow _ _

theorem exists_basis_integralPart_sum_l2Norm_sq_le {κ : Type*}
    (W : Submodule K (MvPolynomial σ K)) {D : ℕ} (hD : ∀ P ∈ W, P.totalDegree ≤ D)
    (S : Set (MvPolynomial σ K)) (hSH : S ⊆ integralPart W) (hSW : span K S = W) {B : ℝ}
    (hB : ∀ P ∈ S, ∀ s : K →+* ℂ, l2Norm (map s P) ≤ B)
    (ω : κ → 𝓞 K) (hω : span ℚ (Set.range fun k => (ω k : K)) = ⊤) {A : ℝ}
    (hA : ∀ (s : K →+* ℂ) k, ‖s (ω k)‖ ≤ A) {R : ℕ} (hR : R = finrank ℚ K * finrank K W) :
    ∃ b : Basis (Fin R) ℤ (integralPart W), ∀ i,
      √(∑ s : K →+* ℂ, l2Norm (map s (b i : MvPolynomial σ K)) ^ 2) ≤
        √((R + 3) / 4) * √(finrank ℚ K) * A * B := by
  classical
  let v : κ × S → MvPolynomial σ K := fun p => ω p.1 • (p.2 : MvPolynomial σ K)
  have hvH : ∀ p, v p ∈ integralPart W := fun p => smul_mem_integralPart _ (hSH p.2.2)
  have hsp : span ℚ (Set.range v) = W.restrictScalars ℚ := by
    refine le_antisymm (span_le.2 ?_) fun P hP => ?_
    · rintro _ ⟨p, rfl⟩; exact (hvH p).1
    · have hP' : P ∈ span K S := hSW ▸ hP
      have key : ∀ c : K, c • P ∈ span ℚ (Set.range v) := by
        clear hP
        induction hP' using span_induction with
        | mem y hy =>
          intro c
          have hc : c ∈ span ℚ (Set.range fun k => (ω k : K)) := hω ▸ mem_top
          induction hc using span_induction with
          | mem c hc => obtain ⟨k, rfl⟩ := hc; exact subset_span ⟨(k, ⟨y, hy⟩), rfl⟩
          | zero => simp
          | add c c' _ _ h h' => rw [add_smul]; exact add_mem h h'
          | smul q c _ h => rw [smul_assoc]; exact smul_mem _ _ h
        | zero => simp
        | add y z _ _ hy hz => intro c; rw [smul_add]; exact add_mem (hy c) (hz c)
        | smul c' y _ hy => intro c; rw [smul_smul]; exact hy _
      simpa using key 1
  have hφ : ∀ P ∈ integralPart W, P ≠ 0 → 1 ≤ ‖conjCoeffs K σ D P‖ := by
    intro P hP h0
    obtain ⟨α, hα⟩ := support_nonempty.2 h0
    obtain ⟨s, hs⟩ := exists_conjugate_one_le_norm (K := K) (α := ⟨P.coeff α, hP.2 α⟩)
      (fun h => mem_support_iff.1 hα (congrArg Subtype.val h))
    exact hs.trans (PiLp.norm_apply_le (conjCoeffs K σ D P)
      (s, ⟨α, support_subset_monomialsLE.2 (hD P hP.1) hα⟩))
  have hr : ∀ p, ‖conjCoeffs K σ D (v p)‖ ≤ √(finrank ℚ K) * A * B := by
    intro p
    have h1 : ∀ s : K →+* ℂ, l2Norm (map s (v p)) ≤ A * B := fun s => by
      have : map s (v p) = s (ω p.1) • map s (p.2 : MvPolynomial σ K) := by
        ext α
        rw [coeff_smul, coeff_map, coeff_map, smul_eq_mul, ← map_mul]
        rfl
      rw [this, vectorL2Norm_const_mul]
      exact mul_le_mul (hA s _) (hB _ p.2.2 s) (l2Norm_nonneg _) ((norm_nonneg _).trans (hA s p.1))
    have h0 : 0 ≤ A * B := (l2Norm_nonneg _).trans (h1 (Classical.arbitrary _))
    rw [mul_assoc]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [norm_conjCoeffs_sq (hD _ (hvH p).1), mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      ← Embeddings.card K ℂ, ← nsmul_eq_mul, ← Finset.card_univ]
    exact Finset.sum_le_card_nsmul _ _ _ fun s _ => pow_le_pow_left₀ (l2Norm_nonneg _) (h1 s) 2
  obtain ⟨b, hb⟩ := exists_short_basis_of_ratSpan (integralPart W) (conjCoeffs K σ D) one_pos hφ v
    hvH (by rw [hsp]; exact fun P hP => hP.1) hr (R := R)
    (by rw [hsp, hR]; exact Module.finrank_mul_finrank ℚ K W)
  refine ⟨b, fun i => ?_⟩
  have hne : Nonempty (κ × S) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h2 : (b i : MvPolynomial σ K) ∈ span ℚ (Set.range v) := hsp ▸ (b i).2.1
    rw [Set.range_eq_empty, span_empty, mem_bot] at h2
    exact b.ne_zero i (Subtype.ext h2)
  have h0 : 0 ≤ √(finrank ℚ K) * A * B := (norm_nonneg _).trans (hr hne.some)
  rw [← norm_conjCoeffs_sq (hD _ (b i).2.1), mul_assoc, mul_assoc, ← mul_assoc (√(finrank ℚ K)),
    ← Real.sqrt_sq h0, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt (hb i)

theorem exists_reduced_basis_integralPart {κ : Type*}
    (W : Submodule K (MvPolynomial σ K)) {D : ℕ} (hD : ∀ P ∈ W, P.totalDegree ≤ D)
    (S : Set (MvPolynomial σ K)) (hSH : S ⊆ integralPart W) (hSW : span K S = W) {B : ℝ}
    (hB : ∀ P ∈ S, ∀ s : K →+* ℂ, l1Norm (map s P) ≤ B)
    (ω : κ → 𝓞 K) (hω : span ℚ (Set.range fun k => (ω k : K)) = ⊤) {A : ℝ}
    (hA : ∀ (s : K →+* ℂ) k, ‖s (ω k)‖ ≤ A) {R : ℕ} (hR : R = finrank ℚ K * finrank K W) :
    R ≤ finrank ℚ K * (1 + D) ^ Fintype.card σ ∧
    ∃ b : Basis (Fin R) ℤ (integralPart W),
      (∀ i (s : K →+* ℂ), l2Norm (map s (b i : MvPolynomial σ K)) ≤
        √((R + 3) / 4) * √(finrank ℚ K) * A * B) ∧
      (∀ i (s : K →+* ℂ), l1Norm (map s (b i : MvPolynomial σ K)) ≤
        (1 + D : ℝ) ^ ((Fintype.card σ : ℝ) / 2) * (√((R + 3) / 4) * √(finrank ℚ K) * A * B)) ∧
      (span (𝓞 K) (Set.range fun i => (b i : MvPolynomial σ K))).restrictScalars ℤ =
        integralPart W := by
  refine ⟨hR ▸ Nat.mul_le_mul_left _ (finrank_le_one_add_pow hD), ?_⟩
  obtain ⟨b, hb⟩ := exists_basis_integralPart_sum_l2Norm_sq_le W hD S hSH hSW
    (fun P hP s => (l2Norm_le_l1Norm _).trans (hB P hP s)) ω hω hA hR
  have h2 : ∀ i (s : K →+* ℂ), l2Norm (map s (b i : MvPolynomial σ K)) ≤
      √((R + 3) / 4) * √(finrank ℚ K) * A * B := fun i s =>
    (Real.le_sqrt_of_sq_le (Finset.single_le_sum
      (f := fun s : K →+* ℂ => l2Norm (map s (b i : MvPolynomial σ K)) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ s))).trans (hb i)
  refine ⟨b, h2, fun i s => ?_, span_ringOfIntegers_basis_integralPart b⟩
  have hdeg : (map s (b i : MvPolynomial σ K)).totalDegree ≤ D :=
    Finset.sup_le fun α hα =>
      (le_totalDegree (support_map_subset s _ hα)).trans (hD _ (b i).2.1)
  refine (l1Norm_le_sqrt_choose_mul_l2Norm hdeg).trans
    (mul_le_mul ?_ (h2 i s) (l2Norm_nonneg _) (by positivity))
  rw [Real.sqrt_le_left (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_mul_cancel₀,
    Real.rpow_natCast]
  exact_mod_cast choose_add_le_one_add_pow _ _

example : (X 0 : MvPolynomial (Fin 1) ℚ) ∈ integralPart (span ℚ {X 0}) ∧
    (1 / 2 : ℚ) • (X 0 : MvPolynomial (Fin 1) ℚ) ∉ integralPart (span ℚ {X 0}) := by
  refine ⟨⟨mem_span_singleton_self _, fun α => ?_⟩, fun h => ?_⟩
  · change IsIntegral ℤ (coeff α (X 0))
    rw [coeff_X]
    split_ifs
    exacts [isIntegral_one, isIntegral_zero]
  · have h1 := (mem_integralPart.1 h).2 (Finsupp.single 0 1)
    rw [coeff_smul, coeff_X, if_pos rfl, smul_eq_mul, mul_one] at h1
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
    rw [eq_intCast] at hm
    have h2 : (2 * m : ℤ) = 1 := by exact_mod_cast (by rw [hm]; norm_num : (2 * m : ℚ) = 1)
    omega

end MvPoly

end GlobalTheory
