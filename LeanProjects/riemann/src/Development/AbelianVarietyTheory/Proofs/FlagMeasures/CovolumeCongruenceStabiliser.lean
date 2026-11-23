import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExponentialUnipotentStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRootStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentLieLatticeDomainVolumeBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoveringSetExpLieLatticeRootGroupStatement

open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped ENNReal Classical

namespace GlobalTheory.LoopV.Cov
open MeasureTheory Pointwise

theorem fund_sub {E : Type} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
    (μ : Measure E) [μ.IsAddLeftInvariant] (Λ Λ' : Submodule ℤ E) [Countable Λ] (hle : Λ' ≤ Λ)
    {Q : Type} [Finite Q] (f : Λ → Q) (hf : ∀ a b : Λ, f a = f b → (a : E) - b ∈ Λ')
    (Ω : Set E) (hm : MeasurableSet Ω) (hΩ : IsAddFundamentalDomain Λ Ω μ) :
    ∃ Ω' : Set E, MeasurableSet Ω' ∧ IsAddFundamentalDomain Λ' Ω' μ ∧
      μ Ω' ≤ (Nat.card Q : ℝ≥0∞) * μ Ω := by
  classical
  let s : Setoid Λ := ⟨fun a b => (a : E) - b ∈ Λ', ⟨fun a => by simp,
    fun {a b} h => by simpa [neg_sub] using Λ'.neg_mem h,
    fun {a b c} h1 h2 => by simpa [sub_add_sub_cancel] using Λ'.add_mem h1 h2⟩⟩
  have hinj : Function.Injective (fun c : Quotient s => f c.out) := by
    intro c₁ c₂ h
    rw [← Quotient.out_eq c₁, ← Quotient.out_eq c₂]
    exact Quotient.sound (hf _ _ h)
  haveI : Finite (Quotient s) := Finite.of_injective _ hinj
  letI : Fintype (Quotient s) := Fintype.ofFinite _
  letI : Fintype Q := Fintype.ofFinite _
  have hmeas : MeasurableSet (⋃ c : Quotient s, (fun x => ((c.out : Λ) : E) + x) ⁻¹' Ω) :=
    MeasurableSet.iUnion fun c => measurable_const_add _ hm
  refine ⟨_, hmeas, ⟨hmeas.nullMeasurableSet, ?_, ?_⟩, ?_⟩
  · filter_upwards [hΩ.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    have hc : (((⟦g⟧ : Quotient s).out : Λ) : E) - g ∈ Λ' := Quotient.mk_out (s := s) g
    refine ⟨⟨(g : E) - ((⟦g⟧ : Quotient s).out : Λ), by simpa [neg_sub] using Λ'.neg_mem hc⟩,
      Set.mem_iUnion.2 ⟨⟦g⟧, ?_⟩⟩
    change (((⟦g⟧ : Quotient s).out : Λ) : E) + (((g : E) - ((⟦g⟧ : Quotient s).out : Λ)) + x) ∈ Ω
    have hg' : (g : E) + x ∈ Ω := hg
    convert hg' using 1
    abel
  · intro g₁ g₂ hne
    have hg₁ : (g₁ : E) ∈ Λ := hle g₁.2
    have hg₂ : (g₂ : E) ∈ Λ := hle g₂.2
    let a₁ : Quotient s → Λ := fun c => ⟨(g₁ : E) - (c.out : Λ), Λ.sub_mem hg₁ (c.out : Λ).2⟩
    let a₂ : Quotient s → Λ := fun c => ⟨(g₂ : E) - (c.out : Λ), Λ.sub_mem hg₂ (c.out : Λ).2⟩
    have hsub : (g₁ +ᵥ ⋃ c : Quotient s, (fun x => ((c.out : Λ) : E) + x) ⁻¹' Ω) ∩
        (g₂ +ᵥ ⋃ c : Quotient s, (fun x => ((c.out : Λ) : E) + x) ⁻¹' Ω) ⊆
        ⋃ c₁, ⋃ c₂, (a₁ c₁ +ᵥ Ω) ∩ (a₂ c₂ +ᵥ Ω) := by
      rintro y ⟨hy1, hy2⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_iUnion] at hy1 hy2
      obtain ⟨c₁, hc₁⟩ := hy1
      obtain ⟨c₂, hc₂⟩ := hy2
      refine Set.mem_iUnion.2 ⟨c₁, Set.mem_iUnion.2 ⟨c₂, ?_, ?_⟩⟩
      · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        change ((c₁.out : Λ) : E) + (-(g₁ : E) + y) ∈ Ω at hc₁
        change -((g₁ : E) - ((c₁.out : Λ) : E)) + y ∈ Ω
        convert hc₁ using 1
        abel
      · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        change ((c₂.out : Λ) : E) + (-(g₂ : E) + y) ∈ Ω at hc₂
        change -((g₂ : E) - ((c₂.out : Λ) : E)) + y ∈ Ω
        convert hc₂ using 1
        abel
    refine measure_mono_null hsub (measure_iUnion_null fun c₁ => measure_iUnion_null fun c₂ => ?_)
    refine hΩ.aedisjoint (fun heq => hne ?_)
    have he : (g₁ : E) - ((c₁.out : Λ) : E) = (g₂ : E) - ((c₂.out : Λ) : E) :=
      congrArg Subtype.val heq
    have hcc : (((c₁.out : Λ) : E) - ((c₂.out : Λ) : E)) ∈ Λ' := by
      have : ((c₁.out : Λ) : E) - ((c₂.out : Λ) : E) = (g₁ : E) - g₂ :=
        (sub_eq_sub_iff_sub_eq_sub.1 he).symm
      rw [this]
      exact Λ'.sub_mem g₁.2 g₂.2
    have hceq : c₁ = c₂ := by
      rw [← Quotient.out_eq c₁, ← Quotient.out_eq c₂]
      exact Quotient.sound hcc
    subst hceq
    apply Subtype.ext
    have := he
    simpa using this
  · calc μ (⋃ c : Quotient s, (fun x => ((c.out : Λ) : E) + x) ⁻¹' Ω)
        ≤ ∑ c : Quotient s, μ ((fun x => ((c.out : Λ) : E) + x) ⁻¹' Ω) :=
          measure_iUnion_fintype_le _ _
      _ = ∑ _c : Quotient s, μ Ω := by
          refine Finset.sum_congr rfl fun c _ => ?_
          exact measure_preimage_add μ _ Ω
      _ = (Fintype.card (Quotient s) : ℝ≥0∞) * μ Ω := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (Nat.card Q : ℝ≥0∞) * μ Ω := by
          gcongr
          rw [Nat.card_eq_fintype_card]
          exact_mod_cast Fintype.card_le_of_injective _ hinj

theorem expT_map {K F : Type} [Field K] [Field F] {N : ℕ} (φ : K →+* F)
    (x : Matrix (Fin N) (Fin N) K) : expT (x.map φ) = (expT x).map φ := by
  have hp : ∀ i : ℕ, (x.map φ) ^ i = (x ^ i).map φ := fun i => (map_pow φ.mapMatrix x i).symm
  ext a b
  simp only [expT, hp, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    map_sum, map_mul, map_inv₀, map_natCast]

theorem expT_conj {K : Type} [Field K] {N : ℕ} (U x : Matrix (Fin N) (Fin N) K)
    (hU : IsUnit U.det) : expT (U * x * U⁻¹) = U * expT x * U⁻¹ := by
  have hp : ∀ i : ℕ, (U * x * U⁻¹) ^ i = U * x ^ i * U⁻¹ := by
    intro i
    induction i with
    | zero => simp [Matrix.mul_nonsing_inv _ hU]
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hU]
  unfold expT
  simp only [hp]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem det_upUni {K : Type} [Field K] {N : ℕ} {U : Matrix (Fin N) (Fin N) K} (h : IsUpUni U) :
    U.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => (h i j).1 hij)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem det_loUni {K : Type} [Field K] {N : ℕ} {L : Matrix (Fin N) (Fin N) K} (h : IsLoUni L) :
    L.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular L (fun i j hij => (h i j).1 hij)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem lieU_sub {K : Type} [Field K] {N : ℕ} {Z x y : Matrix (Fin N) (Fin N) K}
    (hx : x ∈ lieU Z) (hy : y ∈ lieU Z) : x - y ∈ lieU Z := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨fun i j h => by rw [Matrix.sub_apply, hx1 i j h, hy1 i j h, sub_zero], fun i j h => ?_⟩
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, hx2 i j h, hy2 i j h, sub_zero]

theorem lieU_zero {K : Type} [Field K] {N : ℕ} (Z : Matrix (Fin N) (Fin N) K) :
    (0 : Matrix (Fin N) (Fin N) K) ∈ lieU Z := ⟨fun i j _ => by simp, fun i j _ => by simp⟩

private lemma strUp_mul' {K : Type} [Field K] {N : ℕ} {x y : Matrix (Fin N) (Fin N) K}
    (hx : StrUp x) (hy : StrUp y) : StrUp (x * y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases le_or_gt k i with hk | hk
  · rw [hx i k hk, zero_mul]
  · rw [hy k j (le_of_lt (lt_of_le_of_lt hij hk)), mul_zero]

private lemma strLo_mul' {K : Type} [Field K] {N : ℕ} {x y : Matrix (Fin N) (Fin N) K}
    (hx : StrLo x) (hy : StrLo y) : StrLo (x * y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases le_or_gt i k with hk | hk
  · rw [hx i k hk, zero_mul]
  · rw [hy k j (le_of_lt (lt_of_lt_of_le hk hij)), mul_zero]

theorem lieU_mul {K : Type} [Field K] {N : ℕ} {Z x y : Matrix (Fin N) (Fin N) K}
    (hZ : Z.det ≠ 0) (hx : x ∈ lieU Z) (hy : y ∈ lieU Z) : x * y ∈ lieU Z := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have key : (Z * x * Z.adjugate) * (Z * y * Z.adjugate) = Z.det • (Z * (x * y) * Z.adjugate) := by
    have h1 : (Z * x * Z.adjugate) * (Z * y * Z.adjugate) = Z * x * (Z.adjugate * Z) * y * Z.adjugate := by
      simp only [Matrix.mul_assoc]
    rw [h1, Matrix.adjugate_mul]
    simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
  refine ⟨strUp_mul' hx1 hy1, fun i j hij => ?_⟩
  have h3 := strLo_mul' hx2 hy2 i j hij
  rw [key, Matrix.smul_apply, smul_eq_mul] at h3
  exact (mul_eq_zero.1 h3).resolve_left hZ

theorem roots_trans {K : Type} [Field K] {N : ℕ} {w : Matrix (Fin N) (Fin N) K}
    (R : Finset (Fin N × Fin N)) (hw : w.det ≠ 0)
    (h : ∀ x, x ∈ lieU w ↔ ∀ i j, (i, j) ∉ R → x i j = 0) (a b c : Fin N)
    (hab : (a, b) ∈ R) (hbc : (b, c) ∈ R) : (a, c) ∈ R := by
  by_contra hac
  have hx : Matrix.single a b (1 : K) ∈ lieU w := (h _).2 fun i j hij => by
    rw [Matrix.single_apply]
    split_ifs with h'
    · obtain ⟨rfl, rfl⟩ := h'
      exact absurd hab hij
    · rfl
  have hy : Matrix.single b c (1 : K) ∈ lieU w := (h _).2 fun i j hij => by
    rw [Matrix.single_apply]
    split_ifs with h'
    · obtain ⟨rfl, rfl⟩ := h'
      exact absurd hbc hij
    · rfl
  have hxy := lieU_mul hw hx hy
  rw [Matrix.single_mul_single_same, one_mul] at hxy
  have h0 := (h _).1 hxy a c hac
  simp [Matrix.single_apply] at h0

theorem exists_lattice {K : Type} [Field K] [NumberField K] {ι : Type} (τ : ι → (K →+* ℂ)) {N : ℕ}
    (Z U : Matrix (Fin N) (Fin N) K) (R : Finset (Fin N × Fin N)) (J : Ideal (𝓞 K)) :
    ∃ Λ : Submodule ℤ (ι → R → ℂ), ∀ c, c ∈ Λ ↔ ∃ x ∈ lieU Z, EntIn J x ∧
      ∀ v (q : R), c v q = τ v ((U * x * U⁻¹) q.1.1 q.1.2) := by
  let H : AddSubgroup (ι → R → ℂ) :=
    { carrier := {c | ∃ x ∈ lieU Z, EntIn J x ∧ ∀ v (q : R), c v q = τ v ((U * x * U⁻¹) q.1.1 q.1.2)}
      add_mem' := by
        rintro a b ⟨x, hx, hxJ, hxa⟩ ⟨y, hy, hyJ, hyb⟩
        refine ⟨x + y, by simpa using lieU_sub hx (lieU_sub (lieU_zero Z) hy), fun i j => ?_,
          fun v q => ?_⟩
        · obtain ⟨o, ho, e⟩ := hxJ i j
          obtain ⟨o', ho', e'⟩ := hyJ i j
          exact ⟨o + o', J.add_mem ho ho', by simp [← e, ← e']⟩
        · rw [Pi.add_apply, Pi.add_apply, hxa, hyb, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply,
            map_add]
      zero_mem' := ⟨0, lieU_zero Z, fun i j => ⟨0, J.zero_mem, by simp⟩, fun v q => by simp⟩
      neg_mem' := by
        rintro a ⟨x, hx, hxJ, hxa⟩
        refine ⟨-x, by simpa using lieU_sub (lieU_zero Z) hx, fun i j => ?_, fun v q => ?_⟩
        · obtain ⟨o, ho, e⟩ := hxJ i j
          exact ⟨-o, J.neg_mem ho, by simp [← e]⟩
        · rw [Pi.neg_apply, Pi.neg_apply, hxa, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply,
            map_neg] }
  exact ⟨AddSubgroup.toIntSubmodule H, fun c => Iff.rfl⟩

theorem ofRoots_sub_one {K : Type} [Field K] {N : ℕ} (φ : K →+* ℂ) (R : Finset (Fin N × Fin N))
    (hR : ∀ q ∈ R, q.1 < q.2) (y : Matrix (Fin N) (Fin N) K) (hy : ∀ i j, (i, j) ∉ R → y i j = 0)
    (c : R → ℂ) (hc : ∀ q : R, c q = φ (y q.1.1 q.1.2)) : ofRoots R c - 1 = y.map φ := by
  ext i j
  by_cases h : (i, j) ∈ R
  · have hij : i ≠ j := ne_of_lt (hR _ h)
    simp [ofRoots, h, hij, hc ⟨(i, j), h⟩]
  · have hy0 := hy i j h
    by_cases hij : i = j
    · subst hij
      simp [ofRoots, h, hy0]
    · simp [ofRoots, h, hij, hy0]

theorem discrete_lattice {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
    (τ : ι → (K →+* ℂ)) (hτ : ∀ w : InfinitePlace K, ∃ v, InfinitePlace.mk (τ v) = w) {N : ℕ}
    (U : Matrix (Fin N) (Fin N) K) (hU : IsUnit U.det) (R : Finset (Fin N × Fin N))
    (hR : ∀ q ∈ R, q.1 < q.2) (J : Ideal (𝓞 K)) (Λ : Submodule ℤ (ι → R → ℂ))
    (hΛ : ∀ c ∈ Λ, ∃ x : Matrix (Fin N) (Fin N) K, (∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) ∧
      EntIn J x ∧ ∀ v (q : R), c v q = τ v ((U * x * U⁻¹) q.1.1 q.1.2)) :
    DiscreteTopology Λ := by
  classical
  let Φ : (ι → R → ℂ) → (ι → Fin N → Fin N → ℂ) := fun c v i j =>
    ∑ q : R, τ v (U⁻¹ i q.1.1) * τ v (U q.1.2 j) * c v q
  have hΦ : Continuous Φ := by
    refine continuous_pi fun v => continuous_pi fun i => continuous_pi fun j => ?_
    refine continuous_finset_sum _ fun q _ => ?_
    exact continuous_const.mul ((continuous_apply q).comp (continuous_apply v))
  have hΦ0 : Φ 0 = 0 := by
    funext v i j
    simp [Φ]
  obtain ⟨δ, hδ, hδΦ⟩ := Metric.continuous_iff.1 hΦ 0 1 one_pos
  have key : ∀ c ∈ Λ, ‖c‖ < δ → c = 0 := by
    intro c hc hcδ
    obtain ⟨x, hxR, hxJ, hxc⟩ := hΛ c hc
    have hsmall : ∀ v i j, ‖τ v (x i j)‖ < 1 := by
      intro v i j
      have h1 : dist (Φ c) (Φ 0) < 1 := hδΦ c (by rw [dist_zero_right]; exact hcδ)
      rw [hΦ0, dist_zero_right] at h1
      have h2 : τ v (x i j) = Φ c v i j := by
        have hx : x = U⁻¹ * (U * x * U⁻¹) * U := by
          simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one,
            Matrix.nonsing_inv_mul_cancel_left _ _ hU]
        conv_lhs => rw [hx]
        rw [GlobalTheory.LieCovol.mul_mul_apply _ _ _ R hxR, map_sum, ← Finset.sum_coe_sort R]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [map_mul, map_mul, hxc v q]
      rw [h2]
      exact lt_of_le_of_lt ((norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans
        (norm_le_pi_norm (Φ c) v))) h1
    have hx0 : x = 0 := by
      ext i j
      obtain ⟨o, -, e⟩ := hxJ i j
      rw [Matrix.zero_apply, ← e]
      by_contra hne
      have ho : o ≠ 0 := fun h => hne (by simp [h])
      obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
      have hlt : ∀ z : InfinitePlace K, z ((o : 𝓞 K) : K) < 1 := by
        intro z
        obtain ⟨v, hv⟩ := hτ z
        rw [← hv, InfinitePlace.apply, e]
        exact hsmall v i j
      exact absurd (InfinitePlace.one_le_of_lt_one ho (fun z _ => hlt z)) (not_le.2 (hlt w))
    funext v q
    rw [hxc v q, hx0]
    simp
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hset : ({0} : Set Λ) = Subtype.val ⁻¹' Metric.ball (0 : ι → R → ℂ) δ := by
    ext ⟨c, hc⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    constructor
    · intro h
      have hc0 : c = 0 := congrArg Subtype.val h
      rw [hc0, norm_zero]
      exact hδ
    · intro h
      exact Subtype.ext (key c hc h)
  rw [hset]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

theorem covolume_congruence_stabiliser : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ)) (N : ℕ) (L U : Matrix (Fin N) (Fin N) K) (p : Point K N) (I : Ideal (𝓞 K)) (B : ℝ) (Bv : ι → ℝ), (∀ v a, τ v (star a) = starRingEnd ℂ (τ v a)) → (∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w) → finrank ℚ K = 2 * Fintype.card ι → IsLoUni L → IsUpUni U → EntIn ⊤ (L * ptMat p * U) → I ≠ ⊥ → 1 ≤ B → (∀ (t : ℕ) (A A' : Fin t → Fin N) (v : ι), ‖τ v (((L * ptMat p * U).submatrix A A').det)‖ ≤ Bv v) → ∏ v, max 1 (Bv v) ≤ B → ∃ Ω : Set (ι → roots (ptMat p) → ℂ), MeasurableSet Ω ∧ MeasureTheory.volume Ω ≤ ENNReal.ofReal ((|(discr K : ℝ)| ^ (1 / 2 : ℝ) * (4 * (N : ℝ) ^ 2) ^ (Fintype.card ι) * B ^ 4 * (Ideal.absNorm I : ℝ) * (N.factorial : ℝ) ^ (2 * Fintype.card ι)) ^ (N ^ 2)) ∧ ∀ c : ι → roots (ptMat p) → ℂ, ∃ a ∈ stabU (L * ptMat p * U), EntIn I (a - 1) ∧ (fun v (q : roots (ptMat p)) => ((U * a * U⁻¹).map (τ v) * ofRoots (roots (ptMat p)) (c v) : Matrix (Fin N) (Fin N) ℂ) q.1.1 q.1.2) ∈ Ω := by
  classical
  intro K _ _ _ ι _ τ N L U p I B Bv hstar hτ hrk hL hU hZ hI hB hBv hprod
  obtain ⟨hstab, hlie, hstabp, hliep⟩ := GlobalTheory.T.gramUnipotentStabilizer_bruhatCell_conj_root K N L U p hL hU
  have hUdet : IsUnit U.det := by rw [det_upUni hU]; exact isUnit_one
  have hZdet : (L * ptMat p * U).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_mul, det_loUni hL, det_upUni hU, one_mul, mul_one]
    exact (GlobalTheory.LoopV.Cell.ptMat_det p).ne_zero
  have hRlt : ∀ q ∈ roots (ptMat p), q.1 < q.2 := by
    intro q hq
    simp only [roots, Finset.mem_filter] at hq
    exact hq.2.1
  have hsupp : ∀ x ∈ lieU (L * ptMat p * U), ∀ i j, (i, j) ∉ roots (ptMat p) →
      (U * x * U⁻¹) i j = 0 := fun x hx => (hliep _).1 ((hlie x).1 hx)
  have hτ' : ∀ w : InfinitePlace K, ∃ v, InfinitePlace.mk (τ v) = w := fun w => (hτ w).exists
  obtain ⟨Λ₀, hΛ₀⟩ := exists_lattice τ (L * ptMat p * U) U (roots (ptMat p)) ⊤
  obtain ⟨Ω₀, hΩ₀m, hΩ₀, hΩ₀v⟩ := GlobalTheory.T.gramUnipotentLieLattice_domain_volume_bound K ι τ N L U p B Bv hstar hτ hrk hL hU hZ hB hBv
    hprod Λ₀ hΛ₀
  obtain ⟨Λ', hΛ'⟩ := exists_lattice τ (L * ptMat p * U) U (roots (ptMat p))
    (Ideal.span {(N.factorial : 𝓞 K)} * I)
  have hle : Λ' ≤ Λ₀ := by
    intro c hc
    obtain ⟨x, hx, hxJ, hxc⟩ := (hΛ' c).1 hc
    refine (hΛ₀ c).2 ⟨x, hx, fun i j => ?_, hxc⟩
    obtain ⟨o, -, e⟩ := hxJ i j
    exact ⟨o, Submodule.mem_top, e⟩
  haveI hd₀ : DiscreteTopology Λ₀ := discrete_lattice τ hτ' U hUdet _ hRlt ⊤ Λ₀ (fun c hc => by
    obtain ⟨x, hx, hxT, hxc⟩ := (hΛ₀ c).1 hc
    exact ⟨x, hsupp x hx, hxT, hxc⟩)
  have hd' : DiscreteTopology Λ' := discrete_lattice τ hτ' U hUdet _ hRlt _ Λ' (fun c hc => by
    obtain ⟨x, hx, hxT, hxc⟩ := (hΛ' c).1 hc
    exact ⟨x, hsupp x hx, hxT, hxc⟩)
  haveI : Countable Λ₀ := GlobalTheory.LoopV.Cover.countable_of_discrete Λ₀

  have hJnorm : Ideal.absNorm (Ideal.span {(N.factorial : 𝓞 K)} * I) =
      N.factorial ^ (2 * Fintype.card ι) * Ideal.absNorm I := by
    rw [map_mul, Ideal.absNorm_span_singleton]
    congr 1
    have hcast : ((N.factorial : 𝓞 K)) = algebraMap ℤ (𝓞 K) (N.factorial : ℤ) := by simp
    rw [hcast, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, hrk, Int.natAbs_pow,
      Int.natAbs_natCast]
  have hcardJ : Nat.card (𝓞 K ⧸ (Ideal.span {(N.factorial : 𝓞 K)} * I)) =
      N.factorial ^ (2 * Fintype.card ι) * Ideal.absNorm I := by
    rw [← hJnorm, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 K ⧸ (Ideal.span {(N.factorial : 𝓞 K)} * I)) := Nat.finite_of_card_ne_zero (by
    rw [hcardJ]
    exact mul_ne_zero (pow_ne_zero _ (Nat.factorial_ne_zero N))
      (Ideal.absNorm_eq_zero_iff.not.2 hI))
  have hch : ∀ c : Λ₀, ∃ x ∈ lieU (L * ptMat p * U), EntIn ⊤ x ∧
      ∀ v (q : roots (ptMat p)), (c : ι → roots (ptMat p) → ℂ) v q =
        τ v ((U * x * U⁻¹) q.1.1 q.1.2) := fun c => (hΛ₀ c).1 c.2
  choose X hXl hXT hXc using hch
  have hXT' : ∀ c i j, ∃ o : 𝓞 K, ((o : 𝓞 K) : K) = X c i j := fun c i j => by
    obtain ⟨o, -, e⟩ := hXT c i j
    exact ⟨o, e⟩
  choose o ho using hXT'
  let f : Λ₀ → (Fin N → Fin N → 𝓞 K ⧸ (Ideal.span {(N.factorial : 𝓞 K)} * I)) :=
    fun c i j => Ideal.Quotient.mk _ (o c i j)
  have hf : ∀ a b : Λ₀, f a = f b → (a : ι → roots (ptMat p) → ℂ) - b ∈ Λ' := by
    intro a b hab
    refine (hΛ' _).2 ⟨X a - X b, lieU_sub (hXl a) (hXl b), fun i j => ⟨o a i j - o b i j, ?_, ?_⟩,
      fun v q => ?_⟩
    · exact Ideal.Quotient.eq.1 (congrFun (congrFun hab i) j)
    · simp [ho]
    · rw [Pi.sub_apply, Pi.sub_apply, hXc a v q, hXc b v q, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.sub_apply, map_sub]
  obtain ⟨Ω', hΩ'm, hΩ', hΩ'v⟩ := fund_sub MeasureTheory.volume Λ₀ Λ' hle f hf Ω₀ hΩ₀m hΩ₀
  have hcardQ : (Nat.card (Fin N → Fin N → 𝓞 K ⧸ (Ideal.span {(N.factorial : 𝓞 K)} * I)) : ℝ) =
      ((N.factorial : ℝ) ^ (2 * Fintype.card ι) * (Ideal.absNorm I : ℝ)) ^ (N ^ 2) := by
    rw [Nat.card_fun, Nat.card_fun, hcardJ, Nat.card_fin]
    push_cast
    ring
  have hfin : MeasureTheory.volume Ω' ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hΩ₀v)) hΩ'v

  have hconv : ∀ c ∈ Λ', ∀ x ∈ lieU (L * ptMat p * U),
      (∀ v (q : roots (ptMat p)), c v q = τ v ((U * x * U⁻¹) q.1.1 q.1.2)) →
      ∀ v, expT (ofRoots (roots (ptMat p)) (c v) - 1) = (U * expT x * U⁻¹).map (τ v) := by
    intro c _ x hx hxc v
    rw [ofRoots_sub_one (τ v) _ hRlt (U * x * U⁻¹) (hsupp x hx) (c v) (hxc v), expT_map,
      expT_conj U x hUdet]
  have hgrp := (GlobalTheory.T.exponential_unipotent_stabilizer K N (L * ptMat p * U) I hZdet)
  have htrans : ∀ a b c : Fin N, (a, b) ∈ roots (ptMat p) → (b, c) ∈ roots (ptMat p) →
      (a, c) ∈ roots (ptMat p) := fun a b c hab hbc =>
    roots_trans _ (GlobalTheory.LoopV.Cell.ptMat_det p).ne_zero hliep a b c hab hbc
  have hclos : ∀ x ∈ Λ', ∀ y ∈ Λ', ∃ z ∈ Λ', ∀ v,
      expT (ofRoots (roots (ptMat p)) (x v) - 1) * expT (ofRoots (roots (ptMat p)) (y v) - 1) =
        expT (ofRoots (roots (ptMat p)) (z v) - 1) := by
    intro x hx y hy
    obtain ⟨X₁, hX₁, hX₁J, hX₁c⟩ := (hΛ' x).1 hx
    obtain ⟨X₂, hX₂, hX₂J, hX₂c⟩ := (hΛ' y).1 hy
    obtain ⟨W, hW, hWJ, hWe⟩ := hgrp.2 X₁ hX₁ X₂ hX₂ hX₁J hX₂J
    have hz : (fun v (q : roots (ptMat p)) => τ v ((U * W * U⁻¹) q.1.1 q.1.2)) ∈ Λ' :=
      (hΛ' _).2 ⟨W, hW, hWJ, fun v q => rfl⟩
    refine ⟨_, hz, fun v => ?_⟩
    rw [hconv x hx X₁ hX₁ hX₁c v, hconv y hy X₂ hX₂ hX₂c v, hconv _ hz W hW (fun v q => rfl) v,
      ← Matrix.map_mul]
    congr 1
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hUdet]
    rw [← Matrix.mul_assoc (expT X₁), hWe]
  obtain ⟨Ω, hΩm, hΩv, hΩcov⟩ := GlobalTheory.T.exists_covering_set_exp_lie_lattice_rootGroup ι N (roots (ptMat p)) Λ' Ω' hRlt htrans hΩ'm hΩ'
    hfin hd' hclos
  refine ⟨Ω, hΩm, ?_, fun c => ?_⟩
  · rw [hΩv]
    refine hΩ'v.trans ?_
    calc (Nat.card (Fin N → Fin N → 𝓞 K ⧸ (Ideal.span {(N.factorial : 𝓞 K)} * I)) : ℝ≥0∞) *
          MeasureTheory.volume Ω₀
        ≤ (Nat.card (Fin N → Fin N → 𝓞 K ⧸ (Ideal.span {(N.factorial : 𝓞 K)} * I)) : ℝ≥0∞) *
          ENNReal.ofReal ((|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ (N ^ 2) *
            ((4 * (N : ℝ) ^ 2) ^ (Fintype.card ι) * B ^ 4) ^ (N ^ 2)) := by gcongr
      _ = ENNReal.ofReal ((Nat.card (Fin N → Fin N → 𝓞 K ⧸
            (Ideal.span {(N.factorial : 𝓞 K)} * I)) : ℝ) *
          ((|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ (N ^ 2) *
            ((4 * (N : ℝ) ^ 2) ^ (Fintype.card ι) * B ^ 4) ^ (N ^ 2))) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ = _ := by
          rw [hcardQ]
          congr 1
          ring
  · obtain ⟨x, hx, hxΩ⟩ := hΩcov c
    obtain ⟨X₁, hX₁, hX₁J, hX₁c⟩ := (hΛ' x).1 hx
    obtain ⟨hst, hI', -⟩ := hgrp.1 X₁ hX₁ hX₁J
    refine ⟨expT X₁, hst, hI', ?_⟩
    have h := hconv x hx X₁ hX₁ hX₁c
    simp only [h] at hxΩ
    exact hxΩ

end GlobalTheory.LoopV.Cov
