import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TsumIdealEqSumClassGroup
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassGroupCoprimeRepresentative
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLSeriesEulerProduct

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeStrip

open Classical in

theorem tsum_ideal_eq_sum_classGroup_of_summable {K : Type} [Field K] [NumberField K]
    (b : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰) (G : Ideal (𝓞 K) → ℂ) (H : ClassGroup (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hb : Function.Bijective (fun c => ClassGroup.mk0 (b c))) (h0 : G ⊥ = 0) (hsum : Summable G)
    (hH : ∀ c I, I ≠ ⊥ → H c (I * b c) = G I) :
    ∑' I, G I = ∑ c, ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ (b c : Ideal (𝓞 K))}, H c J := by
  let S : ClassGroup (𝓞 K) → Set (Ideal (𝓞 K)) :=
    fun c => {I | I ≠ ⊥ ∧ (I * (b c : Ideal (𝓞 K))).IsPrincipal}
  have h1 : ∀ I, G I = ∑ c, (S c).indicator G I := by
    intro I
    by_cases hI : I = ⊥
    · subst hI
      rw [h0]
      exact (Finset.sum_eq_zero fun c _ => Set.indicator_of_notMem (fun h => h.1 rfl) _).symm
    · obtain ⟨c, hc, hu⟩ := GlobalTheory.existsUnique_isPrincipal_mul_classRep b hb I hI
      rw [Finset.sum_eq_single c]
      · exact (Set.indicator_of_mem (show I ∈ S c from ⟨hI, hc⟩) _).symm
      · intro c' _ hne
        exact Set.indicator_of_notMem (fun h => hne (hu c' h.2)) _
      · simp
  rw [tsum_congr h1, Summable.tsum_finsetSum (fun c _ => hsum.indicator (S c))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← tsum_subtype, ← GlobalTheory.tsum_isPrincipal_mul_eq (b c : Ideal (𝓞 K))
    (mem_nonZeroDivisors_iff_ne_zero.mp (b c).2) (H c)]
  exact tsum_congr fun I => (hH c I.1 I.2.1).symm

variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]

def classUnitPart (φ : I → K →+* ℂ) (n : I → ℤ) (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ) (α : 𝓞 K) : ℂ :=
  open Classical in if m = ⊤ then 1 else X (Ideal.span {α}) * (wt φ n (α : K))⁻¹

def classPartFun (φ : I → K →+* ℂ) (n : I → ℤ) (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ) (b : Ideal (𝓞 K))
    (α : 𝓞 K) : ℂ :=
  open Classical in if α ∈ b then classUnitPart φ n m X α else 0

theorem wt_ne_zero_of_ne_zero (φ : I → K →+* ℂ) (n : I → ℤ) {α : 𝓞 K} (hα : α ≠ 0) : wt φ n (α : K) ≠ 0 := by
  have hαK : (α : K) ≠ 0 := fun h => hα (RingOfIntegers.coe_eq_zero_iff.mp h)
  intro h
  have := norm_wt φ n hαK
  rw [h, norm_zero] at this
  exact zero_ne_one this

section

variable {φ : I → K →+* ℂ} {n : I → ℤ} {m : Ideal (𝓞 K)} {X : Ideal (𝓞 K) → ℂ}

theorem classPartFun_mul_wt
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) {α : 𝓞 K} (hα : α ≠ 0) :
    classPartFun φ n m X b α * wt φ n (α : K) = open Classical in if α ∈ b then X (Ideal.span {α}) else 0 := by
  unfold classPartFun classUnitPart
  by_cases hb : α ∈ b
  · rw [if_pos hb, if_pos hb]
    by_cases hm : m = ⊤
    · rw [if_pos hm, one_mul, hβ α hα (hm ▸ Submodule.mem_top)]
    · rw [if_neg hm, mul_assoc, inv_mul_cancel₀ (wt_ne_zero_of_ne_zero φ n hα), mul_one]
  · rw [if_neg hb, if_neg hb, zero_mul]

theorem classUnitPart_eq_of_inv
    (hmul : ∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b)
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (hm : m ≠ ⊤) {α γ : 𝓞 K} (h : γ * α - 1 ∈ m) :
    classUnitPart φ n m X α = wt φ n (γ : K) * (X (Ideal.span {γ}))⁻¹ := by
  have hγα : γ * α ≠ 0 := by
    intro h0
    rw [h0, zero_sub] at h
    exact hm ((Ideal.eq_top_iff_one m).2 (by simpa using m.neg_mem h))
  have hα : α ≠ 0 := right_ne_zero_of_mul hγα
  have hγ : γ ≠ 0 := left_ne_zero_of_mul hγα
  have key := hβ _ hγα h
  rw [← Ideal.span_singleton_mul_span_singleton, hmul] at key
  have hc : ((γ * α : 𝓞 K) : K) = (γ : K) * α := by push_cast; rfl
  rw [hc, wt_mul] at key
  have hwα := wt_ne_zero_of_ne_zero φ n hα
  have hwγ := wt_ne_zero_of_ne_zero φ n hγ
  have hXγ : X (Ideal.span {γ}) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at key
    exact mul_ne_zero hwγ hwα key.symm
  unfold classUnitPart
  rw [if_neg hm]
  field_simp
  linear_combination key

theorem classUnitPart_add
    (hmul : ∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b)
    (hzero : ∀ a : Ideal (𝓞 K), a ⊔ m ≠ ⊤ → X a = 0)
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    {α μ : 𝓞 K} (hμ : μ ∈ m) :
    classUnitPart φ n m X (α + μ) = classUnitPart φ n m X α := by
  by_cases hm : m = ⊤
  · simp [classUnitPart, hm]
  have hsup : Ideal.span {α + μ} ⊔ m = Ideal.span {α} ⊔ m := by
    apply le_antisymm
    · exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.add_mem _
        (Ideal.mem_sup_left (Ideal.mem_span_singleton_self α)) (Ideal.mem_sup_right hμ))) le_sup_right
    · refine sup_le ((Ideal.span_singleton_le_iff_mem _).2 ?_) le_sup_right
      have h : (α + μ) + -μ ∈ Ideal.span {α + μ} ⊔ m :=
        Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_right (m.neg_mem hμ))
      simpa using h
  by_cases hc : Ideal.span {α} ⊔ m = ⊤
  · have h1 : (1 : 𝓞 K) ∈ Ideal.span {α} ⊔ m := hc ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨γ, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have e1 : γ * α - 1 ∈ m := by
      have e : γ * α - 1 = -z := by rw [← hyz]; ring
      rw [e]; exact m.neg_mem hz
    have e2 : γ * (α + μ) - 1 ∈ m := by
      have e : γ * (α + μ) - 1 = (γ * α - 1) + γ * μ := by ring
      rw [e]; exact m.add_mem e1 (m.mul_mem_left γ hμ)
    rw [classUnitPart_eq_of_inv hmul hβ hm e1, classUnitPart_eq_of_inv hmul hβ hm e2]
  · have hc' : Ideal.span {α + μ} ⊔ m ≠ ⊤ := hsup ▸ hc
    simp only [classUnitPart, if_neg hm, hzero _ hc, hzero _ hc', zero_mul]

theorem classPartFun_add
    (hmul : ∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b)
    (hzero : ∀ a : Ideal (𝓞 K), a ⊔ m ≠ ⊤ → X a = 0)
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) {α μ : 𝓞 K} (hμ : μ ∈ m * b) :
    classPartFun φ n m X b (α + μ) = classPartFun φ n m X b α := by
  have hμm : μ ∈ m := (Ideal.mul_le_inf.trans inf_le_left) hμ
  have hμb : μ ∈ b := (Ideal.mul_le_inf.trans inf_le_right) hμ
  unfold classPartFun
  by_cases h : α ∈ b
  · rw [if_pos h, if_pos (b.add_mem h hμb), classUnitPart_add hmul hzero hβ hμm]
  · have h' : α + μ ∉ b := fun h' => h (by simpa using b.sub_mem h' hμb)
    rw [if_neg h, if_neg h']

theorem classPartFun_unit
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) (u : (𝓞 K)ˣ) (α : 𝓞 K) :
    classPartFun φ n m X b ((u : 𝓞 K) * α) * wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) =
      classPartFun φ n m X b α * wt φ n (α : K) := by
  by_cases hα : α = 0
  · subst hα; simp
  have huα : (u : 𝓞 K) * α ≠ 0 := mul_ne_zero u.ne_zero hα
  rw [classPartFun_mul_wt hβ b huα, classPartFun_mul_wt hβ b hα, Ideal.span_singleton_mul_left_unit u.isUnit]
  have hiff : (u : 𝓞 K) * α ∈ b ↔ α ∈ b :=
    ⟨fun h => by simpa using b.mul_mem_left ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) h, fun h => b.mul_mem_left _ h⟩
  by_cases h : α ∈ b
  · rw [if_pos h, if_pos (hiff.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

theorem pval_classPartFun
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b J : Ideal (𝓞 K)) [J.IsPrincipal] (hJ : J ≠ ⊥) :
    pval (classPartFun φ n m X b) φ n J = open Classical in if J ≤ b then X J else 0 := by
  have hg : Submodule.IsPrincipal.generator J ≠ 0 := by
    rwa [Ne, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero]
  have hle : Submodule.IsPrincipal.generator J ∈ b ↔ J ≤ b := by
    conv_rhs => rw [← Ideal.span_singleton_generator J]
    exact (Ideal.span_singleton_le_iff_mem b).symm
  unfold pval
  rw [classPartFun_mul_wt hβ b hg, Ideal.span_singleton_generator]
  by_cases h : J ≤ b
  · rw [if_pos (hle.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hle.1 h')), if_neg h]

theorem pSeries_classPartFun
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) (s : ℂ) :
    pSeries (classPartFun φ n m X b) φ n s =
      ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b}, X J.1 * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) := by
  classical
  let f : Ideal (𝓞 K) → ℂ := fun J => (if J ≤ b then X J else 0) * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s)
  let g : Ideal (𝓞 K) → ℂ := fun J => X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s)
  have h1 : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal},
      (haveI := J.2.2; pval (classPartFun φ n m X b) φ n J.1) * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) = f J.1 := by
    rintro ⟨J, hJ, hP⟩
    simp only [f]
    rw [pval_classPartFun hβ b J hJ]
  unfold pSeries
  rw [tsum_congr h1]
  have e1 := tsum_subtype {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} f
  have e2 := tsum_subtype {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} g
  refine e1.trans (Eq.trans ?_ e2.symm)
  refine tsum_congr fun J => ?_
  by_cases hJ : J ≠ ⊥ ∧ J.IsPrincipal
  · by_cases h : J ≤ b
    · rw [Set.indicator_of_mem (show J ∈ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} from hJ),
        Set.indicator_of_mem (show J ∈ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} from ⟨hJ.1, hJ.2, h⟩)]
      simp only [f, g, if_pos h]
    · rw [Set.indicator_of_mem (show J ∈ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} from hJ),
        Set.indicator_of_notMem (show J ∉ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} from fun h' => h h'.2.2)]
      simp only [f, if_neg h, zero_mul]
  · rw [Set.indicator_of_notMem (show J ∉ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} from hJ),
      Set.indicator_of_notMem (show J ∉ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} from
        fun h' => hJ ⟨h'.1, h'.2.1⟩)]

end

theorem heckeSeries_eq_sum_pSeries : ∀ (K : Type) [Field K] [NumberField K] (I : Type) [Fintype I] (φ : I → K →+* ℂ) (n : I → ℤ) (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b) → (∀ a : Ideal (𝓞 K), a ≠ ⊥ → a ⊔ m = ⊤ → ‖X a‖ = 1) → (∀ a : Ideal (𝓞 K), a ⊔ m ≠ ⊤ → X a = 0) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = GlobalTheory.HeckeStrip.wt φ n (β : K)) → ∃ (r : ℕ) (c : Fin r → ℂ) (B : Fin r → ℕ) (M : Fin r → Ideal (𝓞 K)) (F : Fin r → 𝓞 K → ℂ), (∀ k, 0 < B k) ∧ (∀ k, M k ≠ ⊥) ∧ (∀ k (α μ : 𝓞 K), μ ∈ M k → F k (α + μ) = F k α) ∧ (∀ k (u : (𝓞 K)ˣ) (α : 𝓞 K), F k ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F k α * GlobalTheory.HeckeStrip.wt φ n (α : K)) ∧ ∀ s : ℂ, 1 < s.re → ∑' a : Ideal (𝓞 K), X a * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-s) = ∑ k, c k * ((B k : ℕ) : ℂ) ^ s * GlobalTheory.HeckeStrip.pSeries (F k) φ n s := by
  intro K _ _ I _ φ n m X hm hX0 hmul hnorm hzero hβ
  choose b hb hbm using GlobalTheory.exists_integral_ideal_in_class_coprime K m hm
  have hbij : Function.Bijective (fun c => ClassGroup.mk0 (b c)) := by
    have e : (fun c => ClassGroup.mk0 (b c)) = id := funext hb
    rw [e]; exact Function.bijective_id
  have hb0 : ∀ c, (b c : Ideal (𝓞 K)) ≠ ⊥ := fun c => nonZeroDivisors.coe_ne_zero (b c)
  have hXb : ∀ c, X (b c) ≠ 0 := fun c h => by
    have := hnorm _ (hb0 c) (hbm c)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hNb : ∀ c, Ideal.absNorm (b c : Ideal (𝓞 K)) ≠ 0 := fun c h => hb0 c (Ideal.absNorm_eq_zero_iff.mp h)
  let e := Fintype.equivFin (ClassGroup (𝓞 K))
  refine ⟨Fintype.card (ClassGroup (𝓞 K)), fun k => (X (b (e.symm k)))⁻¹,
    fun k => Ideal.absNorm (b (e.symm k) : Ideal (𝓞 K)), fun k => m * (b (e.symm k) : Ideal (𝓞 K)),
    fun k => classPartFun φ n m X (b (e.symm k)), fun k => Nat.pos_of_ne_zero (hNb _),
    fun k => mul_ne_zero hm (hb0 _), fun k α μ hμ => classPartFun_add hmul hzero hβ _ hμ,
    fun k u α => classPartFun_unit hβ _ u α, fun s hs => ?_⟩
  have hXle : ∀ J, ‖X J‖ ≤ 1 := by
    intro J
    by_cases h0 : J = ⊥
    · rw [h0, hX0, norm_zero]; exact zero_le_one
    by_cases hc : J ⊔ m = ⊤
    · rw [hnorm J h0 hc]
    · rw [hzero J hc, norm_zero]; exact zero_le_one
  have hsum : Summable fun J : Ideal (𝓞 K) => X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) :=
    (GlobalTheory.Mem.summable_norm_absNorm_cpow K hs).of_norm_bounded fun J => by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hXle J)
  have hH : ∀ c (J : Ideal (𝓞 K)), J ≠ ⊥ →
      (X (b c))⁻¹ * ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
        (X (J * (b c : Ideal (𝓞 K))) * ((Ideal.absNorm (J * (b c : Ideal (𝓞 K))) : ℕ) : ℂ) ^ (-s)) =
      X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) := by
    intro c J _
    have hpow : ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
        ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) = 1 := by
      rw [Complex.cpow_neg, mul_inv_cancel₀]
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      exact Or.inl (Nat.cast_ne_zero.mpr (hNb c))
    rw [hmul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    calc (X (b c))⁻¹ * ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
          (X J * X (b c) * (((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) *
            ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)))
        = X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) * ((X (b c))⁻¹ * X (b c)) *
          (((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
            ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) := by ring
      _ = X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) := by rw [inv_mul_cancel₀ (hXb c), hpow, mul_one, mul_one]
  rw [tsum_ideal_eq_sum_classGroup_of_summable b (fun J => X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s))
    (fun c J => (X (b c))⁻¹ * ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
      (X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s))) hbij (by simp only [hX0, zero_mul]) hsum hH]
  refine (Equiv.sum_comp e.symm _).symm.trans (Finset.sum_congr rfl fun k _ => ?_)
  beta_reduce
  rw [tsum_mul_left, pSeries_classPartFun hβ]

end GlobalTheory.HeckeStrip
