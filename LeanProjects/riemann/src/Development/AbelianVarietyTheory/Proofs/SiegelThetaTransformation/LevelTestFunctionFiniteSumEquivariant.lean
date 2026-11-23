import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructurePropertiesStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.RecSum

open TensLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}

theorem cop_mul {𝔪 : Ideal (𝓞 E)} {s t : 𝓞 E} (hs : IsCoprime (Ideal.span {s}) 𝔪)
    (ht : IsCoprime (Ideal.span {t}) 𝔪) : IsCoprime (Ideal.span {s * t}) 𝔪 := by
  rw [← Ideal.span_singleton_mul_span_singleton]
  exact hs.mul_left ht

theorem cop_one (𝔪 : Ideal (𝓞 E)) : IsCoprime (Ideal.span {(1 : 𝓞 E)}) 𝔪 := by
  rw [Ideal.span_singleton_one, ← Ideal.one_eq_top]
  exact isCoprime_one_left

theorem cop_nat {𝔪 : Ideal (𝓞 E)} {s M : ℕ} (h : s.Coprime M) (hM : (M : 𝓞 E) ∈ 𝔪) :
    IsCoprime (Ideal.span {(s : 𝓞 E)}) 𝔪 := by
  obtain ⟨a, b, hab⟩ : IsCoprime (s : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.2 h
  refine Ideal.isCoprime_iff_exists.2 ⟨a * s, Ideal.mul_mem_left _ _ (Ideal.subset_span rfl),
    b * M, Ideal.mul_mem_left _ _ hM, ?_⟩
  exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab

theorem map_smul_mem {A B : Lt E r} (f : (Fin r → E) →ₗ[𝓞 E] (Fin r → E)) (hf : ∀ v ∈ A, f v ∈ B)
    (𝔪 : Ideal (𝓞 E)) {u : Fin r → E} (hu : u ∈ 𝔪 • A) : f u ∈ 𝔪 • B := by
  refine Submodule.smul_induction_on hu (fun a ha v hv => ?_) fun x y hx hy => ?_
  · rw [map_smul]; exact Submodule.smul_mem_smul ha (hf v hv)
  · rw [map_add]; exact add_mem hx hy

theorem mul_smul_mem {A B : Lt E r} {s : 𝓞 E} (hf : ∀ v ∈ A, s • v ∈ B)
    (𝔪 : Ideal (𝓞 E)) {u : Fin r → E} (hu : u ∈ 𝔪 • A) : s • u ∈ 𝔪 • B :=
  map_smul_mem (LinearMap.lsmul (𝓞 E) _ s) hf 𝔪 hu

variable (X) in

def Near (𝔪 : Ideal (𝓞 E)) (N : Lt E r) : Prop :=
  ∃ s : 𝓞 E, IsCoprime (Ideal.span {s}) 𝔪 ∧ (∀ v ∈ N, s • v ∈ X.Λ) ∧ ∀ v ∈ X.Λ, s • v ∈ N

theorem near_of_mem {D : Level X} {L : Lt E r} (hL : L ∈ D.lats) : Near X D.𝔪 L := by
  obtain ⟨-, s, hs, h⟩ := hL
  exact ⟨s, hs.of_mul_right_left, h⟩

theorem Near.inf {𝔪 : Ideal (𝓞 E)} {L L' : Lt E r} (h : Near X 𝔪 L) (h' : Near X 𝔪 L') :
    Near X 𝔪 (L ⊓ L') := by
  obtain ⟨s, hs, h1, h2⟩ := h
  obtain ⟨t, ht, h3, h4⟩ := h'
  refine ⟨s * t, cop_mul hs ht, fun v hv => ?_, fun v hv => ⟨?_, ?_⟩⟩
  · rw [mul_comm, mul_smul]; exact X.Λ.smul_mem _ (h1 v hv.1)
  · rw [mul_comm, mul_smul]; exact L.smul_mem _ (h2 v hv)
  · rw [mul_smul]; exact L'.smul_mem _ (h4 v hv)

section Congruence

variable {𝔪 : Ideal (𝓞 E)} {u v w : Fin r → E}

theorem cong_refl (u : Fin r → E) : Cong X 𝔪 u u :=
  ⟨1, cop_one _, by rw [sub_self, smul_zero]; exact zero_mem _⟩

theorem cong_symm (h : Cong X 𝔪 u v) : Cong X 𝔪 v u := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, hs, by rw [← neg_sub, smul_neg]; exact neg_mem h⟩

theorem cong_trans (h : Cong X 𝔪 u v) (h' : Cong X 𝔪 v w) : Cong X 𝔪 u w := by
  obtain ⟨s, hs, h⟩ := h
  obtain ⟨t, ht, h'⟩ := h'
  refine ⟨s * t, cop_mul hs ht, ?_⟩
  have : (s * t) • (u - w) = t • s • (u - v) + s • t • (v - w) := by
    rw [smul_smul, smul_smul, mul_comm t, ← smul_add, sub_add_sub_cancel]
  rw [this]
  exact add_mem (Submodule.smul_mem _ _ h) (Submodule.smul_mem _ _ h')

theorem cong_map {γ : GL (Fin r) E} (hγ : Near X 𝔪 (mapL γ X.Λ)) (h : Cong X 𝔪 u v) :
    Cong X 𝔪 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) := by
  obtain ⟨s, hs, h⟩ := h
  obtain ⟨t, ht, h1, -⟩ := hγ
  refine ⟨t * s, cop_mul ht hs, ?_⟩
  have := mul_smul_mem h1 𝔪 (map_smul_mem (B := mapL γ X.Λ)
    ((Matrix.toLin' (γ : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E))
    (fun v hv => Submodule.mem_map_of_mem hv) 𝔪 h)
  rw [map_smul, map_sub, smul_smul] at this
  exact this

end Congruence

section Tensor

variable {M : ℕ} {Λ : Lt E n} {𝔪 𝔠 : Ideal (𝓞 E)} {N : Lt E r} {y : Matrix (Fin n) (Fin r) E}

theorem tens_mono (Λ : Lt E n) {A B : Lt E r} (h : A ≤ B) : tens Λ A ≤ tens Λ B :=
  tens_le fun _ hv _ hu => pure_mem hv (h hu)

theorem ctr_smul (a : E) (y : Matrix (Fin n) (Fin r) E) (v : Fin n → E) :
    ctr (a • y) v = a • ctr y v := by
  funext j
  simp [ctr, Finset.sum_apply, Finset.mul_sum, mul_left_comm]

theorem what₂ (hΛ : Λ ∈ Vset E n M) (hM : (M : 𝓞 E) ∈ 𝔪) :
    ∃ s : 𝓞 E, IsCoprime (Ideal.span {s}) 𝔪 ∧ ∀ (N : Lt E r) (y : Matrix (Fin n) (Fin r) E),
      (y ∈ tens Λ N → ∀ k, s • y k ∈ N) ∧ ((∀ k, y k ∈ N) → ∀ w ∈ Λ, s • ctr y w ∈ N) := by
  obtain ⟨s, -, hs, h1, h2⟩ := hΛ.2.2
  have e : ∀ (y : Matrix (Fin n) (Fin r) E) (w : Fin n → E),
      ctr y ((s : E) • w) = (s : 𝓞 E) • ctr y w := fun y w => by
    funext j
    change _ = (s : E) * ctr y w j
    simp [ctr, cc, Finset.sum_apply, Finset.mul_sum, mul_assoc]
  refine ⟨s, cop_nat hs hM, fun N y => ⟨fun hy k => ?_, fun hy w hw => ?_⟩⟩
  · have := (mem_tens_iff hΛ N y).1 hy _
      (h2 (Pi.single k 1) (Submodule.subset_span ⟨k, rfl⟩))
    rw [e, ctr, Finset.sum_eq_single k] at this
    · simpa [cc] using this
    · intro j _ hj; simp [hj, cc]
    · simp
  · rw [← e]
    exact (mem_tens_iff (Base.stdL_mem_Vset n 1) N y).1 ((mem_tens_stdL N y).2 hy) _ (h1 w hw)

theorem cong_of_mem (hΛ : Λ ∈ Vset E n M) (hM : (M : 𝓞 E) ∈ 𝔪) (hN : Near X 𝔪 N)
    {y y' : Matrix (Fin n) (Fin r) E} (hy : y - y' ∈ tens Λ ((𝔠 * 𝔪) • N)) (k : Fin n) :
    Cong X 𝔪 (y k) (y' k) := by
  obtain ⟨s, hs, h⟩ := what₂ (r := r) hΛ hM
  obtain ⟨t, ht, h1, -⟩ := hN
  refine ⟨t * s, cop_mul ht hs, ?_⟩
  rw [mul_smul]
  have h2 : s • (y k - y' k) ∈ (𝔠 * 𝔪) • N := (h ((𝔠 * 𝔪) • N) (y - y')).1 hy k
  have h3 : (𝔠 * 𝔪) • N ≤ 𝔪 • N := Submodule.smul_mono_left Ideal.mul_le_right
  exact mul_smul_mem h1 𝔪 (h3 h2)

theorem mem_of_cong (hΛ : Λ ∈ Vset E n M) (hM : (M : 𝓞 E) ∈ 𝔪) (hN : Near X 𝔪 N)
    (hc : IsCoprime 𝔠 𝔪) {y y' : Matrix (Fin n) (Fin r) E} (hy : y - y' ∈ tens Λ (𝔠 • N))
    (hk : ∀ k, Cong X 𝔪 (y k) (y' k)) : y - y' ∈ tens Λ ((𝔠 * 𝔪) • N) := by
  obtain ⟨s, hs, h⟩ := what₂ (r := r) hΛ hM
  obtain ⟨t, ht, -, h1⟩ := hN
  choose p hp hq using hk
  have hP : IsCoprime (Ideal.span {∏ k, p k}) 𝔪 := by
    rw [← Ideal.prod_span_singleton]
    exact IsCoprime.prod_left fun k _ => hp k
  rw [mem_tens_iff hΛ] at hy ⊢
  intro w hw
  have h2 := (h (𝔪 • X.Λ) (((∏ k, p k : 𝓞 E) : E) • (y - y'))).2 (fun k => by
    change (∏ k, p k) • (y k - y' k) ∈ _
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k), mul_smul]
    exact Submodule.smul_mem _ _ (hq k)) w hw
  rw [ctr_smul] at h2
  have h3 : (t * (s * ∏ k, p k)) • ctr (y - y') w ∈ 𝔪 • N := by
    rw [mul_smul, mul_smul]; exact mul_smul_mem h1 𝔪 h2
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Ideal.isCoprime_iff_exists.1 (hc.mul_left (cop_mul ht (cop_mul hs hP)))
  obtain ⟨c, hc', rfl⟩ := Ideal.mem_mul_span_singleton.1 ha
  rw [← one_smul (𝓞 E) (ctr _ w), ← hab, add_smul]
  refine add_mem ?_ ?_
  · rw [Submodule.mul_smul, mul_smul c]; exact Submodule.smul_mem_smul hc' h3
  · rw [mul_comm, Submodule.mul_smul]; exact Submodule.smul_mem_smul hb (hy w hw)

theorem exists_rows (hΛ : Λ ∈ Vset E n M) (hM : (M : 𝓞 E) ∈ 𝔪) (hN : Near X 𝔪 N)
    (hc : IsCoprime 𝔠 𝔪) {u : Matrix (Fin n) (Fin r) E} (hu : ∀ k, u k ∈ X.Λ) :
    ∃ y ∈ tens Λ (𝔠 • N), ∀ k, Cong X 𝔪 (y k) (u k) := by
  obtain ⟨s, hs, h⟩ := what₂ (r := r) hΛ hM
  obtain ⟨t, ht, -, h1⟩ := hN
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 (hc.mul_left (cop_mul ht hs))
  refine ⟨(a : E) • u, (mem_tens_iff hΛ _ _).2 fun w hw => ?_, fun k => ⟨1, cop_one _, ?_⟩⟩
  · obtain ⟨c, hc', rfl⟩ := Ideal.mem_mul_span_singleton.1 ha
    rw [ctr_smul]
    change (c * (t * s)) • ctr u w ∈ _
    rw [mul_smul, mul_smul]
    exact Submodule.smul_mem_smul hc' (h1 _ ((h _ _).2 hu w hw))
  · change (1 : 𝓞 E) • (a • u k - u k) ∈ _
    rw [one_smul, eq_sub_of_add_eq hab, sub_smul, one_smul, sub_sub_cancel_left]
    exact neg_mem (Submodule.smul_mem_smul hb (hu k))

theorem half_mem (hΛ : Λ ∈ Vset E n M) (hy : y ∈ tens Λ ((Ideal.span {2} * 𝔠) • N)) :
    ∃ z ∈ tens Λ (𝔠 • N), y = 2 • z := by
  refine ⟨(2⁻¹ : E) • y, ?_, ?_⟩
  · rw [mem_tens_iff hΛ] at hy ⊢
    intro w hw
    rw [ctr_smul]
    have := hy w hw
    rw [Submodule.mul_smul] at this
    refine Submodule.smul_induction_on this (fun a ha v hv => ?_) fun x y hx hy => ?_
    · obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      have e : (2⁻¹ : E) • (b * 2) • v = b • v := by
        funext j
        change (2⁻¹ : E) * (((b : E) * 2) * v j) = (b : E) * v j
        field_simp
      rw [e]
      exact Submodule.smul_mem _ _ hv
    · rw [smul_add]; exact add_mem hx hy
  · rw [← Nat.cast_smul_eq_nsmul E, smul_smul]; simp

theorem row_mul (y : Matrix (Fin n) (Fin r) E) (A : Matrix (Fin r) (Fin r) E) (k : Fin n) :
    (y * Aᵀ) k = A *ᵥ y k := by
  funext j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem mul_mem_tens {A B : Lt E r} {γ : Matrix (Fin r) (Fin r) E} (h : ∀ u ∈ A, γ *ᵥ u ∈ B)
    (hy : y ∈ tens Λ A) : y * γᵀ ∈ tens Λ B := by
  refine tens_le (H := (tens Λ B).comap (AddMonoidHom.mk' (fun y => y * γᵀ)
    fun a b => Matrix.add_mul a b _)) (fun v hv u hu => ?_) hy
  change vecMulVec v u * γᵀ ∈ tens Λ B
  rw [vecMulVec_mul, vecMul_transpose]
  exact pure_mem hv (h u hu)

end Tensor

section Vacua

variable {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {w : E}
  {A : AddSubgroup (Matrix (Fin n) (Fin r) E)} {v : TF n g}

theorem isVac_smul (hv : IsVac X bas w A v) {c : ℂ} (hc : ‖c‖ = 1) : IsVac X bas w A (c • v) := by
  refine ⟨TensVac.sb_smul c hv.1, ?_, fun y hy => ?_⟩
  · rw [TensVac.ip_smul_left c hv.1 (TensVac.sb_smul c hv.1), TensVac.ip_smul_right c hv.1 hv.1,
      hv.2.1, mul_one, Complex.mul_conj', hc]
    simp
  · rw [TensVac.heisG_smul, smul_comm, hv.2.2 y hy]

theorem unitv_smul (hv : IsVac X bas w A v) (a : ℂ) : unitv (a • v) = (a / ‖a‖) • v := by
  rw [unitv, TensVac.ip_smul_left a hv.1 (TensVac.sb_smul a hv.1),
    TensVac.ip_smul_right a hv.1 hv.1, hv.2.1, mul_one, Complex.mul_conj', ← Complex.ofReal_pow,
    Complex.ofReal_re, Real.sqrt_sq (norm_nonneg a), smul_smul, div_eq_inv_mul]

theorem epsW_mul {γ : GL (Fin r) E} (hγ : IsUn X γ) (y : Matrix (Fin n) (Fin r) E) :
    epsW X w (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) = epsW X w y := by
  simp only [epsW, row_mul, ← Matrix.mulVec_smul, EF_def, hγ _ _]

theorem mul_inv_transpose (γ : GL (Fin r) E) (y : Matrix (Fin n) (Fin r) E) :
    y * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᵀ * (γ : Matrix (Fin r) (Fin r) E)ᵀ = y := by
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]

theorem inv_mulVec (γ : GL (Fin r) E) (u : Fin r → E) :
    ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ (γ : Matrix (Fin r) (Fin r) E) *ᵥ u = u := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem isVac_wG (hs : IsSympl X bas) (hn : Even n) {γ : GL (Fin r) E} (hγ : IsUn X γ)
    {Λ : Lt E n} {S : Lt E r} (hv : IsVac X bas w (tens Λ S) v) :
    IsVac X bas w (tens Λ (mapL γ S)) (wG X bas idx γ v) := by
  have H := wG_laws E r X g bas idx n hs hn γ hγ
  refine ⟨(H v hv.1).1, ((H v hv.1).2.2.1 v hv.1).1.trans hv.2.1, fun y hy => ?_⟩
  have h1 : y * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᵀ ∈ tens Λ S := by
    refine mul_mem_tens ?_ hy
    rintro _ ⟨u, hu, rfl⟩
    exact (inv_mulVec γ u).symm ▸ hu
  rw [← mul_inv_transpose γ y, epsW_mul hγ, ← (H v hv.1).2.2.2.2.2.2,
    ← (H _ ((heisG_laws E r X g bas idx n hs hn).2.2.2 _ v hv.1).1).2.2.2.1, hv.2.2 _ h1]

theorem isSB_sum {ι : Type} (s : Finset ι) (f : ι → TF n g) (hf : ∀ i, IsSB (f i)) :
    IsSB (∑ i ∈ s, f i) :=
  Finset.sum_induction f IsSB (fun a b ha hb => (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ _ _ a b ha hb).1) isSB_zero
    fun i _ => hf i

theorem wG_sum (hs : IsSympl X bas) (hn : Even n) {γ : GL (Fin r) E} (hγ : IsUn X γ) {ι : Type}
    (s : Finset ι) (f : ι → TF n g) (hf : ∀ i, IsSB (f i)) :
    wG X bas idx γ (∑ i ∈ s, f i) = ∑ i ∈ s, wG X bas idx γ (f i) := by
  have H := wG_laws E r X g bas idx n hs hn γ hγ
  induction s using Finset.induction_on with
  | empty => simpa using (H 0 isSB_zero).2.2.2.1 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact ((H _ (hf a)).2.2.1 _ (isSB_sum s f hf)).2.1

theorem heis_add (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) (D : Level X)
    {M : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) {L : Lt E r} (hL : SelfD X L)
    (hS : SelfD X (D.sh L)) (hv : IsVac X bas D.w (tens Λ (D.sh L)) v)
    {y δ : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪) • L))
    (hδ : δ ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)) :
    heisG X bas (y + δ) v = heisG X bas y v := by
  obtain ⟨y', hy', rfl⟩ := half_mem hΛ hy
  rw [mul_assoc] at hδ
  obtain ⟨z, hz, rfl⟩ := half_mem hΛ hδ
  have hle : (conjI D.𝔪 * D.𝔪) • L ≤ D.sh L := fun u hu b _ =>
    Submodule.smul_mem _ b (Submodule.smul_mono_left Ideal.mul_le_right hu)
  have hzS := tens_mono Λ hle hz
  have hG : TensVac.Good X D.w (tens Λ (D.sh L)) := ⟨tens_fg hΛ hS.1, tens_selfDual hΛ hS,
    fun y hy => epsW_semichar hΛ hS D.w_int D.w_tr hy⟩
  have h1 := hv.2.2 _ (nsmul_mem hzS 2)
  rw [hG.eps_two hs hzS, one_smul] at h1
  have h2 := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (2 • y') v hv.1).2.2.1 (2 • z)
  obtain ⟨k, hk⟩ := (tens_selfDual hΛ hL y').1 (tens_mono Λ Submodule.smul_le_right hy') _
    (nsmul_mem (tens_mono Λ Submodule.smul_le_right hz) 2)
  have h3 : ∑ i, EF X ((2 • y') i) ((2 • z) i) = 2 * k := by
    rw [← hk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (2 • y') i = 2 • y' i := rfl
    rw [e, EF_eq_bilin, EF_eq_bilin, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
  rw [h1, h3, show -(π * I * (((2 : ℚ) * k : ℚ) : ℂ)) = ((-k : ℤ) : ℂ) * (2 * π * I) by
    push_cast; ring, Complex.exp_int_mul_two_pi_mul_I, one_smul] at h2
  exact h2.symm

end Vacua

section Main

variable {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {D : Level X} {M : ℕ} {Λ : Lt E n} {L : Lt E r}

theorem cop_level (D : Level X) : IsCoprime (Ideal.span {2} * conjI D.𝔪) D.𝔪 :=
  D.odd.symm.mul_left D.cop.symm

theorem red_congr {u u' : Fin r → Fin r → E} {k : GL (Fin r) (𝓞 E ⧸ D.𝔪)}
    (h : ∀ i, Cong X D.𝔪 (u i) (u' i)) (h' : D.Red u' k) : D.Red u k := by
  obtain ⟨k', e, h'⟩ := h'
  exact ⟨k', e, fun i => cong_trans (h i) (h' i)⟩

theorem phi_eq_sum (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (he : Even n) (hn : r ≤ n)
    (hM : (M : 𝓞 E) ∈ D.𝔪) (hΛ : Λ ∈ Vset E n M) (hL : L ∈ D.lats) (v₀ : Lt E r → TF n g)
    (hv : IsVac X bas D.w (tens Λ (D.sh L)) (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))))
    {ι : Type} [Fintype ι] (f : ι → Matrix (Fin n) (Fin r) E)
    (h1 : ∀ i, f i ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪) • L))
    (h2 : ∀ i j, (∀ k, Cong X D.𝔪 (f i k) (f j k)) → i = j)
    (h3 : ∀ y, D.dat hn y ≠ 0 → ∃ i, ∀ k, Cong X D.𝔪 (y k) (f i k)) :
    D.phi bas hn v₀ L Λ = ∑ i, D.dat hn (f i) • heisG X bas (f i)
      (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) := by
  obtain ⟨-, -, -, hl, -, hd, -⟩ := GlobalTheory.T.level_structure_properties E r X g bas idx n hs he D hn
  unfold Level.phi
  generalize unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)) = v at hv ⊢
  let q : ι → tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸
      (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _ :=
    fun i => QuotientAddGroup.mk ⟨f i, h1 i⟩
  have hq : ∀ c i, c = q i ↔ f i - (c.out : Matrix (Fin n) (Fin r) E) ∈
      tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L) := fun c i => by
    conv_lhs => rw [← QuotientAddGroup.out_eq' c]
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, neg_add_eq_sub]
    rfl
  have hc : ∀ i k, Cong X D.𝔪 (f i k) (((q i).out : Matrix (Fin n) (Fin r) E) k) := fun i =>
    cong_of_mem hΛ hM (near_of_mem hL) ((hq _ i).1 rfl)
  have hinj : Function.Injective q := fun i j e =>
    h2 i j fun k => cong_trans (hc i k) (e ▸ cong_symm (hc j k))
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.image q), Finset.sum_image hinj.injOn]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd _ _ (hc i), ← heis_add idx hs he D hΛ hL.1 (hl L hL).1 hv (q i).out.2 ((hq _ i).1 rfl),
      add_sub_cancel]
  · intro c hc0
    obtain ⟨i, hi⟩ := h3 (c.out : Matrix (Fin n) (Fin r) E) fun h => hc0 (by simp only [h, zero_smul])
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, ((hq c i).2 ?_).symm⟩)
    exact mem_of_cong hΛ hM (near_of_mem hL) (cop_level D) (sub_mem (h1 i) c.out.2)
      fun k => cong_symm (hi k)

theorem exists_reps (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (he : Even n) (hn : r ≤ n)
    (hM : (M : 𝓞 E) ∈ D.𝔪) (hΛ : Λ ∈ Vset E n M) {N : Lt E r} (hN : Near X D.𝔪 N) :
    ∃ f : D.J → Matrix (Fin n) (Fin r) E,
      (∀ i, f i ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪) • N)) ∧
      (∀ i j, (∀ k, Cong X D.𝔪 (f i k) (f j k)) → i = j) ∧
      (∀ y, D.dat hn y ≠ 0 → ∃ i, ∀ k, Cong X D.𝔪 (y k) (f i k)) ∧ ∀ i, ‖D.dat hn (f i)‖ = 1 := by
  obtain ⟨-, hu, -, -, hlam, -⟩ := GlobalTheory.T.level_structure_properties E r X g bas idx n hs he D hn
  have H : ∀ κ : D.J, ∃ y ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪) • N),
      D.Red (fun i => y (Fin.castLE hn i)) κ ∧ ∀ k : Fin n, r ≤ (k : ℕ) → Cong X D.𝔪 (y k) 0 := by
    intro κ
    choose k' hk' using fun i j => Ideal.Quotient.mk_surjective (I := D.𝔪) (κ.1.1 i j)
    obtain ⟨y, hy, hc⟩ := exists_rows hΛ hM hN (cop_level D)
      (u := fun k => if h : (k : ℕ) < r then ∑ j, k' j ⟨k, h⟩ • D.β j else 0) fun k => by
        split_ifs
        · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (D.β_mem j)
        · exact zero_mem _
    refine ⟨y, hy, ⟨Matrix.of k', by ext i j; exact hk' i j, fun i => ?_⟩, fun k hk => ?_⟩
    · have := hc (Fin.castLE hn i)
      rw [dif_pos (show ((Fin.castLE hn i : Fin n) : ℕ) < r from i.2)] at this
      exact this
    · have := hc k
      rwa [dif_neg (not_lt.2 hk)] at this
  choose f h1 h2 h3 using H
  refine ⟨f, h1, fun i j h => Subtype.ext (hu _ _ _ (h2 i) (red_congr (fun a => h _) (h2 j))),
    fun y hy => ?_, fun i => ?_⟩
  · unfold Level.dat at hy
    split_ifs at hy with h
    swap
    · exact (hy rfl).elim
    obtain ⟨⟨κ, a, ha, hκ⟩, h0⟩ := h
    refine ⟨κ, fun k => ?_⟩
    by_cases hk : (k : ℕ) < r
    · obtain ⟨b, hb, hf⟩ := h2 κ
      refine cong_trans (hκ ⟨k, hk⟩) (cong_trans ⟨1, cop_one _, ?_⟩ (cong_symm (hf ⟨k, hk⟩)))
      rw [one_smul, ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [← sub_smul]
      exact Submodule.smul_mem_smul
        (Ideal.Quotient.eq.1 (congrFun (congrFun (ha.trans hb.symm) j) _)) (D.β_mem j)
    · exact cong_trans (h0 k (not_lt.1 hk)) (cong_symm (h3 κ k (not_lt.1 hk)))
  · rw [Level.dat, dif_pos ⟨⟨i, h2 i⟩, h3 i⟩]
    exact hlam _

theorem finite_J (D : Level X) : Finite D.J := by
  haveI : Finite (𝓞 E ⧸ D.𝔪) := Ideal.finiteQuotientOfFreeOfNeBot _ D.ne_bot
  infer_instance

theorem unitv_proj (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (he : Even n)
    (hΛ : Λ ∈ Vset E n M) {S : Lt E r} (hS : SelfD X S) {v₀ v : TF n g}
    (h0 : IsVac X bas D.w (tens (stdL E n) S) v₀) (hv : IsVac X bas D.w (tens Λ S) v) :
    SW.ip v₀ v ≠ 0 ∧
      unitv (projA X bas D.w (tens Λ S) v₀) = (SW.ip v₀ v / ‖SW.ip v₀ v‖) • v := by
  constructor
  · intro h
    have := (TensVac.vacua E r X g bas idx n hs he D.w D.w_int D.w_tr S hS M _
      (Base.stdL_mem_Vset n M)).2.2.2 S hS Λ hΛ v₀ v h0 hv
    simp [h] at this
  · rw [(TensVac.vacua E r X g bas idx n hs he D.w D.w_int D.w_tr S hS M Λ hΛ).2.2.1 v₀ h0.1 v hv,
      unitv_smul hv]

theorem isVac_unitv (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (he : Even n)
    (hΛ : Λ ∈ Vset E n M) {S : Lt E r} (hS : SelfD X S) {v₀ : TF n g}
    (h0 : IsVac X bas D.w (tens (stdL E n) S) v₀) :
    IsVac X bas D.w (tens Λ S) (unitv (projA X bas D.w (tens Λ S) v₀)) := by
  obtain ⟨v, hv⟩ := (TensVac.vacua E r X g bas idx n hs he D.w D.w_int D.w_tr S hS M Λ hΛ).1
  obtain ⟨h1, h2⟩ := unitv_proj idx hs he hΛ hS h0 hv
  rw [h2]
  refine isVac_smul hv ?_
  rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 h1)]

theorem wG_unitv (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (he : Even n)
    (hΛ : Λ ∈ Vset E n M) {S : Lt E r} (hS : SelfD X S) {γ : GL (Fin r) E} (hγ : IsUn X γ)
    (hS' : SelfD X (mapL γ S)) {v₀ v₀' : TF n g} (h0 : IsVac X bas D.w (tens (stdL E n) S) v₀)
    (h0' : IsVac X bas D.w (tens (stdL E n) (mapL γ S)) v₀') {t : ℂ} (ht : ‖t‖ = 1)
    (e : wG X bas idx γ v₀ = t • v₀') :
    wG X bas idx γ (unitv (projA X bas D.w (tens Λ S) v₀)) =
      t • unitv (projA X bas D.w (tens Λ (mapL γ S)) v₀') := by
  have H := wG_laws E r X g bas idx n hs he γ hγ
  obtain ⟨v, hv⟩ := (TensVac.vacua E r X g bas idx n hs he D.w D.w_int D.w_tr S hS M Λ hΛ).1
  have hv' := isVac_wG (idx := idx) hs he hγ hv
  rw [(unitv_proj idx hs he hΛ hS h0 hv).2, (unitv_proj idx hs he hΛ hS' h0' hv').2,
    (H v hv.1).2.2.2.1, ← ((H v₀ h0.1).2.2.1 v hv.1).1, e, TensVac.ip_smul_left t h0'.1 hv'.1,
    norm_mul, ht, one_mul, smul_smul, mul_div_assoc]

end Main

theorem phi_sum_equivariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ L ∈ D.lats, ∀ Λ ∈ Vset E n M, IsSB (D.phi bas hn v₀ L Λ) ∧ IsVac X bas D.w (tens Λ (D.sh L)) (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) ∧ (∀ L' ∈ D.lats, ∃ s : Finset (Matrix (Fin n) (Fin r) E), s.card = Nat.card D.J ∧ (∀ y ∈ s, y ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪) • (L ⊓ L')) ∧ ‖D.dat hn y‖ = 1 ∧ ∀ y' ∈ s, (∀ k, Cong X D.𝔪 (y k) (y' k)) → y = y') ∧ D.phi bas hn v₀ L Λ = ∑ y ∈ s, D.dat hn y • heisG X bas y (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) ∧ D.phi bas hn v₀ L' Λ = ∑ y ∈ s, D.dat hn y • heisG X bas y (unitv (projA X bas D.w (tens Λ (D.sh L')) (v₀ L')))) ∧ ∀ γ ∈ D.grp, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → ∀ t : ℂ, ‖t‖ = 1 → wG X bas idx γ (v₀ L) = t • v₀ (mapL γ L) → wG X bas idx γ (D.phi bas hn v₀ L Λ) = (t * ((D.lam k : ℂˣ) : ℂ)⁻¹) • D.phi bas hn v₀ (mapL γ L) Λ := by
  intro E _ _ _ r X g bas idx n hs he D hn M _ hM v₀ h0 L hL Λ hΛ
  obtain ⟨hX, -, hg, hl, -, -, hd⟩ := GlobalTheory.T.level_structure_properties E r X g bas idx n hs he D hn
  haveI := finite_J D
  haveI : Fintype D.J := Fintype.ofFinite _
  have hv := fun L hL => isVac_unitv idx hs he hΛ (hl L hL).1 (h0 L hL)
  have hsb : ∀ (c : ℂ) (y : Matrix (Fin n) (Fin r) E) (v : TF n g), IsSB v →
      IsSB (c • heisG X bas y v) := fun c y v h =>
    TensVac.sb_smul c ((heisG_laws E r X g bas idx n hs he).2.2.2 y v h).1
  obtain ⟨f, h1, h2, h3, -⟩ := exists_reps idx hs he hn hM hΛ (near_of_mem hL)
  have hf := phi_eq_sum idx hs he hn hM hΛ hL v₀ (hv L hL) f h1 h2 h3
  refine ⟨hf ▸ isSB_sum _ _ fun i => hsb _ _ _ (hv L hL).1, hv L hL, fun L' hL' => ?_,
    fun γ hγ κ hκ t ht e => ?_⟩
  · obtain ⟨f, h1, h2, h3, h4⟩ :=
      exists_reps idx hs he hn hM hΛ ((near_of_mem hL).inf (near_of_mem hL'))
    have hinj : Function.Injective f := fun i j e => h2 i j fun k => e ▸ cong_refl _
    refine ⟨Finset.univ.image f, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]
    · intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      refine ⟨h1 i, h4 i, fun y' hy' h => ?_⟩
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy'
      rw [h2 i j h]
    · rw [Finset.sum_image hinj.injOn]
      exact phi_eq_sum idx hs he hn hM hΛ hL v₀ (hv L hL) f
        (fun i => tens_mono Λ (smul_mono_right _ inf_le_left) (h1 i)) h2 h3
    · rw [Finset.sum_image hinj.injOn]
      exact phi_eq_sum idx hs he hn hM hΛ hL' v₀ (hv L' hL') f
        (fun i => tens_mono Λ (smul_mono_right _ inf_le_right) (h1 i)) h2 h3
  · have hu := ((hg γ).1 hγ).1
    obtain ⟨hL', hsh⟩ := (hl L hL).2.2.2 γ hγ
    have n1 := near_of_mem ((hl _ hX).2.2.2 γ hγ).1
    have n2 := near_of_mem ((hl _ hX).2.2.2 γ⁻¹ (inv_mem hγ)).1
    have hw := wG_unitv idx hs he hΛ (hl L hL).1 hu (hsh ▸ (hl _ hL').1) (h0 L hL)
      (hsh ▸ h0 _ hL') ht e
    rw [← hsh] at hw
    have hf' := phi_eq_sum idx hs he hn hM hΛ hL' v₀ (hv _ hL')
      (fun i => f i * (γ : Matrix (Fin r) (Fin r) E)ᵀ)
      (fun i => mul_mem_tens (fun u hu => map_smul_mem (B := mapL γ L)
        ((Matrix.toLin' (γ : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E))
        (fun v hv => Submodule.mem_map_of_mem hv) _ hu) (h1 i))
      (fun i j h => h2 i j fun k => by
        have := cong_map n2 (h k)
        rwa [row_mul, row_mul, inv_mulVec, inv_mulVec] at this)
      (fun y hy => by
        rw [← mul_inv_transpose γ y, hd γ hγ κ hκ] at hy
        obtain ⟨i, hi⟩ := h3 _ (right_ne_zero_of_mul hy)
        refine ⟨i, fun k => ?_⟩
        rw [← mul_inv_transpose γ y, row_mul, row_mul (f i)]
        exact cong_map n1 (hi k))
    have H := wG_laws E r X g bas idx n hs he γ hu
    rw [hf, hf', wG_sum hs he hu _ _ fun i => hsb _ _ _ (hv L hL).1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(H _ ((heisG_laws E r X g bas idx n hs he).2.2.2 _ _ (hv L hL).1).1).2.2.2.1,
      (H _ (hv L hL).1).2.2.2.2.2.2, hw, TensVac.heisG_smul, hd γ hγ κ hκ, smul_smul, smul_smul]
    congr 1
    have := (D.lam κ).ne_zero
    field_simp

end GlobalTheory.SW.RecSum
