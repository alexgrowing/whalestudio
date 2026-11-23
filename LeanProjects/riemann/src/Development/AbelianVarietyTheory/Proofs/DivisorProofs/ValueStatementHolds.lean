import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluckerMinorsProportionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMinorOfIntegralMatrixStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem mem_range_iff_norm_le (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) :
    x ∈ (algebraMap 𝓞_ℂ_[p] ℂ_[p]).range ↔ ‖x‖ ≤ 1 := by
  rw [← coe_valued]
  constructor
  · rintro ⟨y, rfl⟩
    exact_mod_cast (Valuation.mem_valuationSubring_iff _ _).1 y.2
  · intro h
    exact ⟨⟨x, (Valuation.mem_valuationSubring_iff _ _).2 (by exact_mod_cast h)⟩, rfl⟩

theorem norm_det_le_one {p : ℕ} [Fact p.Prime] {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ_[p])
    (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  choose N hN using fun i j => (mem_range_iff_norm_le p (M i j)).2 (h i j)
  have e : M = (Matrix.of N).map (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := by ext i j; exact (hN i j).symm
  rw [e]
  change ‖((algebraMap 𝓞_ℂ_[p] ℂ_[p]).mapMatrix (Matrix.of N)).det‖ ≤ 1
  rw [← RingHom.map_det]
  exact (mem_range_iff_norm_le p _).1 ⟨_, rfl⟩

theorem exists_perm_inl {p q : ℕ} (f : Fin p → Fin p ⊕ Fin q) (hf : Function.Injective f) :
    ∃ π : Equiv.Perm (Fin p ⊕ Fin q), ∀ k, π (Sum.inl k) = f k := by
  classical
  have hc : Fintype.card ((Set.range f)ᶜ : Set (Fin p ⊕ Fin q)) = q := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective hf]; simp
  let e2 : Fin q ≃ ((Set.range f)ᶜ : Set (Fin p ⊕ Fin q)) := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨(Equiv.sumCongr (Equiv.ofInjective f hf) e2).trans (Equiv.Set.sumCompl (Set.range f)), fun k => ?_⟩
  simp [Equiv.Set.sumCompl_apply_inl]

theorem exists_perm_inr {p q : ℕ} (f : Fin q → Fin p ⊕ Fin q) (hf : Function.Injective f) :
    ∃ π : Equiv.Perm (Fin p ⊕ Fin q), ∀ k, π (Sum.inr k) = f k := by
  classical
  have hc : Fintype.card ((Set.range f)ᶜ : Set (Fin p ⊕ Fin q)) = p := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective hf]; simp
  let e2 : Fin p ≃ ((Set.range f)ᶜ : Set (Fin p ⊕ Fin q)) := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨((Equiv.sumCongr e2 (Equiv.ofInjective f hf)).trans (Equiv.sumComm _ _)).trans
    (Equiv.Set.sumCompl (Set.range f)), fun k => ?_⟩
  simp [Equiv.Set.sumCompl_apply_inl]

section Pt

variable {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p)

omit [NumberField E] in
theorem pairV_eq_zero' {χ χ' : 𝓞 E →+* ℂ_[p]} {w x : P.V} (hw : w ∈ EigenSplit.eigenSub P.actV χ)
    (hx : x ∈ EigenSplit.eigenSub P.actV χ') {a : 𝓞 E} (ha : χ a ≠ χ' (star a)) :
    P.pairV w x = 0 := by
  have h1 := P.pairV_act a w x
  rw [EigenSplit.mem_eigenSub.1 hw, EigenSplit.mem_eigenSub.1 hx, map_smul, map_smul,
    LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
  exact (mul_eq_mul_right_iff.1 h1).resolve_left ha

open Classical in
theorem pairV_proj_right {j₀ : E →+* ℂ_[p]} {x : P.V}
    (hx : x ∈ P.eigV ((embO P.integers j₀).comp (starRingEnd (𝓞 E)))) (y : P.V) :
    P.pairV y x = P.pairV (EigenSplit.proj (isSplitting_embO P.integers) P.actV j₀ y) x := by
  classical
  have hinj : ∀ i i' : E →+* ℂ_[p], (∀ a, embO P.integers i a = embO P.integers i' a) → i = i' := fun i i' H =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => by
      have := congrArg (algebraMap 𝓞_ℂ_[p] ℂ_[p]) (H a)
      rwa [algebraMap_embO, algebraMap_embO] at this)
  conv_lhs => rw [← EigenSplit.sum_proj (isSplitting_embO P.integers) P.actV y]
  rw [map_sum, LinearMap.sum_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), add_eq_left]
  refine Finset.sum_eq_zero fun j hj => ?_
  obtain ⟨a, ha⟩ := not_forall.1 fun H => Finset.ne_of_mem_erase hj (hinj j j₀ H)
  refine pairV_eq_zero' P (EigenSplit.proj_mem _ P.actV j y) hx (a := a) fun H => ha (P.integers.hom_inj ?_)
  simpa [starRingEnd_apply] using H

open Classical in
theorem eq_zero_of_pairV {j₁ : E →+* ℂ_[p]} {z : P.V}
    (hz : z ∈ P.eigV ((embO P.integers j₁).comp (starRingEnd (𝓞 E))))
    (h : ∀ w ∈ P.eigV (embO P.integers j₁), P.pairV z w = 0) : z = 0 := by
  have key : ∀ y : P.V, P.pairV z y = 0 := fun y => by
    have hm : EigenSplit.proj (isSplitting_embO P.integers) P.actV j₁ y ∈ P.eigV (embO P.integers j₁) :=
      EigenSplit.proj_mem (isSplitting_embO P.integers) P.actV j₁ y
    have e4 := h _ hm
    have e2 := pairV_proj_right P hz y
    have e3 := P.pairV_swap (EigenSplit.proj (isSplitting_embO P.integers) P.actV j₁ y) z
    have e1 := P.pairV_swap z y
    rw [e4, neg_zero] at e3
    rw [e3] at e2
    rw [e1, e2, neg_zero]
  refine P.eq_of_pairV fun t => ?_
  rw [key]
  exact (LinearMap.map_zero₂ P.pairV _).symm

end Pt

section Pt2

variable {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p)

omit [NumberField E] in
theorem pairV_mem_range {w x : P.V} (hw : w ∈ P.latT) (hx : x ∈ P.latT) :
    P.pairV w x ∈ (algebraMap 𝓞_ℂ_[p] ℂ_[p]).range := by
  obtain ⟨w, rfl⟩ := hw
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply]; exact add_mem ha hb
  | tmul c s =>
    obtain ⟨d, hd⟩ := (P.mem_latT_iff x).1 hx s
    have e : (algebraMap 𝓞_ℂ_[p] ℂ_[p] c ⊗ₜ s : P.V) = algebraMap 𝓞_ℂ_[p] ℂ_[p] c • (1 ⊗ₜ s) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    refine ⟨-(c * d), ?_⟩
    rw [P.inclT_tmul, e, map_smul, LinearMap.smul_apply, P.pairV_swap, ← hd]
    simp

omit [NumberField E] in
theorem smul_mem_latT {a : ℂ_[p]} (ha : ‖a‖ ≤ 1) {x : P.V} (hx : x ∈ P.latT) : a • x ∈ P.latT := by
  obtain ⟨c, rfl⟩ := (mem_range_iff_norm_le p a).2 ha
  rw [algebraMap_smul]
  exact P.latT.smul_mem c hx

variable {J : Type} [Fintype J] [DecidableEq J] {t s : J → P.V} {u : ℂ_[p]}

omit [NumberField E] in
theorem coord_of_mem_span (hd : ∀ i j, P.pairV (s i) (t j) = if i = j then u else 0) (hu : u ≠ 0) {x : P.V}
    (hx : x ∈ Submodule.span ℂ_[p] (Set.range t)) : x = ∑ j, (-P.pairV x (s j) / u) • t j := by
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ_[p]).1 hx
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have : P.pairV (∑ i, d i • t i) (s j) = -(d j * u) := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    simp only [fun i => P.pairV_swap (t i) (s j), hd, mul_neg, Finset.sum_neg_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [this, neg_neg, mul_div_assoc, div_self hu, _root_.mul_one]

omit [NumberField E] in
theorem sum_pair_mul_eq_zero (hd : ∀ i j, P.pairV (s i) (t j) = if i = j then u else 0) (hu : u ≠ 0) {w₁ w₂ : P.V}
    (h0 : P.pairV w₁ w₂ = 0) (hw : w₂ ∈ Submodule.span ℂ_[p] (Set.range t)) :
    ∑ i, P.pairV w₁ (t i) * P.pairV w₂ (s i) = 0 := by
  have e := coord_of_mem_span P hd hu hw
  rw [e] at h0
  simp only [map_sum, map_smul, smul_eq_mul] at h0
  have : ∑ i, P.pairV w₁ (t i) * P.pairV w₂ (s i) = -u * ∑ j, -P.pairV w₂ (s j) / u * P.pairV w₁ (t j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [this, h0, mul_zero]

omit [NumberField E] in
theorem beta_sat {χ : 𝓞 E →+* 𝓞_ℂ_[p]} (ht : ∀ i, t i ∈ P.latTSub χ) (hs : ∀ i, s i ∈ P.latT) (hu : ‖u‖ = 1)
    (hd : ∀ i j, P.pairV (s i) (t j) = if i = j then u else 0) (hsp : P.eigV χ ≤ Submodule.span ℂ_[p] (Set.range t))
    {m : ℕ} {w : Fin m → P.V} (hw : IsLatBasis ℂ_[p] (P.latTSub χ) w) :
    (∀ k i, ‖P.pairV (w k) (s i)‖ ≤ 1) ∧
      ∀ a : Fin m → ℂ_[p], (∀ i, ‖∑ k, a k * P.pairV (w k) (s i)‖ ≤ 1) → ∀ k, ‖a k‖ ≤ 1 := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hwm : ∀ k, w k ∈ P.latTSub χ := fun k => (hw.2.le (Submodule.subset_span ⟨k, rfl⟩)).1
  refine ⟨fun k i => (mem_range_iff_norm_le p _).1 (pairV_mem_range P (hwm k).1 (hs i)), fun a ha k => ?_⟩
  have hx : ∑ k, a k • w k ∈ P.eigV χ := Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hwm k).2
  have e := coord_of_mem_span P hd hu0 (hsp hx)
  have hb : ∀ j, P.pairV (∑ k, a k • w k) (s j) = ∑ k, a k * P.pairV (w k) (s j) := fun j => by
    simp [map_sum, map_smul]
  have hL : ∑ k, a k • w k ∈ P.latT := by
    rw [e]
    refine Submodule.sum_mem _ fun j _ => smul_mem_latT P ?_ (ht j).1
    rw [norm_div, norm_neg, hu, div_one, hb]
    exact ha j
  have := (hw.sum_mem_iff a).1 ⟨hL, hx⟩ k
  exact (mem_range_iff_norm_le p _).1 this

end Pt2

section Pt3

variable {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p)
variable {J : Type} [Fintype J] [DecidableEq J] {t s : J → P.V} {u : ℂ_[p]}

open Classical in
theorem alpha_sat {j₀ j₁ : E →+* ℂ_[p]}
    (hj : embO P.integers j₁ = (embO P.integers j₀).comp (starRingEnd (𝓞 E)))
    (ht : ∀ i, t i ∈ P.latTSub (embO P.integers j₁)) (hs : ∀ i, s i ∈ P.latT) (hu : ‖u‖ = 1)
    (hd : ∀ i j, P.pairV (s i) (t j) = if i = j then u else 0)
    (hsp : P.eigV (embO P.integers j₁) ≤ Submodule.span ℂ_[p] (Set.range t))
    {m : ℕ} {w : Fin m → P.V}
    (hw : IsLatBasis ℂ_[p] (P.latTQuot (σ := fun φ : E →+* ℂ_[p] => embO P.integers φ)
      (isSplitting_embO P.integers) j₀) w) :
    (∀ k i, ‖P.pairV (w k) (t i)‖ ≤ 1) ∧
      ∀ a : Fin m → ℂ_[p], (∀ i, ‖∑ k, a k * P.pairV (w k) (t i)‖ ≤ 1) → ∀ k, ‖a k‖ ≤ 1 := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have htE : ∀ i, t i ∈ P.eigV ((embO P.integers j₀).comp (starRingEnd (𝓞 E))) := fun i => hj ▸ (ht i).2
  have hLa : ∀ k, w k ∈ P.latTQuot (σ := fun φ : E →+* ℂ_[p] => embO P.integers φ)
      (isSplitting_embO P.integers) j₀ := fun k => (hw.2.le (Submodule.subset_span ⟨k, rfl⟩)).1
  have hint : ∀ x ∈ P.latTQuot (σ := fun φ : E →+* ℂ_[p] => embO P.integers φ)
      (isSplitting_embO P.integers) j₀, ∀ i, P.pairV x (t i) ∈ (algebraMap 𝓞_ℂ_[p] ℂ_[p]).range := by
    rintro _ ⟨y, hy, rfl⟩ i
    show P.pairV (EigenSplit.proj (isSplitting_embO P.integers) P.actV j₀ y) (t i) ∈ _
    rw [← pairV_proj_right P (htE i)]
    exact pairV_mem_range P hy (ht i).1
  refine ⟨fun k i => (mem_range_iff_norm_le p _).1 (hint _ (hLa k) i), fun a ha k => ?_⟩
  have hb : ∀ i, P.pairV (∑ k, a k • w k) (t i) = ∑ k, a k * P.pairV (w k) (t i) := fun i => by
    simp [map_sum, map_smul]
  have hy : (∑ i, (P.pairV (∑ k, a k • w k) (t i) / u) • s i) ∈ P.latT :=
    Submodule.sum_mem _ fun i _ => smul_mem_latT P (by rw [norm_div, hu, div_one, hb]; exact ha i) (hs i)
  have hyt : ∀ i, P.pairV (∑ i, (P.pairV (∑ k, a k • w k) (t i) / u) • s i) (t i) =
      P.pairV (∑ k, a k • w k) (t i) := fun i => by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hd, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    field_simp
  have hzE : EigenSplit.proj (isSplitting_embO P.integers) P.actV j₀
      (∑ i, (P.pairV (∑ k, a k • w k) (t i) / u) • s i) - ∑ k, a k • w k ∈
      P.eigV ((embO P.integers j₁).comp (starRingEnd (𝓞 E))) := by
    have e : (embO P.integers j₁).comp (starRingEnd (𝓞 E)) = embO P.integers j₀ := by
      rw [hj]; ext a; simp
    rw [e]
    have h1 : EigenSplit.proj (isSplitting_embO P.integers) P.actV j₀
        (∑ i, (P.pairV (∑ k, a k • w k) (t i) / u) • s i) ∈ P.eigV (embO P.integers j₀) :=
      EigenSplit.proj_mem (isSplitting_embO P.integers) P.actV j₀ _
    have h2 : ∀ k, w k ∈ P.eigV (embO P.integers j₀) := fun k =>
      eigQuotLat_le P.actV (isSplitting_embO P.integers) j₀ P.latT (hLa k)
    exact Submodule.sub_mem _ h1 (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (h2 k))
  have key : ∀ z : P.V, (∀ i, P.pairV z (t i) = 0) → ∀ w' ∈ P.eigV (embO P.integers j₁), P.pairV z w' = 0 :=
    fun z hz w' hw' => by
      obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ_[p]).1 (hsp hw')
      simp only [map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero]
  have hzt : ∀ i, P.pairV (EigenSplit.proj (isSplitting_embO P.integers) P.actV j₀
      (∑ i, (P.pairV (∑ k, a k • w k) (t i) / u) • s i) - ∑ k, a k • w k) (t i) = 0 := fun i => by
    rw [map_sub, LinearMap.sub_apply, ← pairV_proj_right P (htE i), hyt, sub_self]
  have hz := eq_zero_of_pairV P hzE (key _ hzt)
  rw [sub_eq_zero] at hz
  have hmem : ∑ k, a k • w k ∈ P.latTQuot (σ := fun φ : E →+* ℂ_[p] => embO P.integers φ)
      (isSplitting_embO P.integers) j₀ := hz ▸ ⟨_, hy, rfl⟩
  exact (mem_range_iff_norm_le p _).1 ((hw.sum_mem_iff a).1 hmem k)

end Pt3

theorem valueSt : ValueSt := by
  intro E _ _ _ H Dw l c p _ _ _ hs P τ t s u hD w₁ w₂ _ he₂ horth hL₁ hL₂
  classical
  obtain ⟨ht, hsl, hu, hd, hsp⟩ := hD
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hj : embO P.integers (embAt c ℂ_[p] (conjEmb τ.1)) =
      (embO P.integers (embAt c ℂ_[p] τ.1)).comp (starRingEnd (𝓞 E)) :=
    embInt_conj hs P.integers τ.1
  have hA := alpha_sat P hj ht hsl hu hd hsp (w := w₁) (by rw [htLat_psi P τ] at hL₁; exact hL₁)
  have hB := beta_sat P ht hsl hu hd hsp (w := w₂) (by rw [htLat_conj P τ] at hL₂; exact hL₂)
  let α : Matrix (Fin (Dw.mult τ.1)) (Ind Dw τ.1) ℂ_[p] := Matrix.of fun k i => P.pairV (w₁ k) (t i)
  let β : Matrix (Fin (Dw.mult (conjEmb τ.1))) (Ind Dw τ.1) ℂ_[p] := Matrix.of fun k i => P.pairV (w₂ k) (s i)
  obtain ⟨f₁, hf₁, hn₁⟩ := GlobalTheory.T.exists_unit_minor_of_integral_matrix p α hA.1 hA.2
  obtain ⟨f₂, hf₂, hn₂⟩ := GlobalTheory.T.exists_unit_minor_of_integral_matrix p β hB.1 hB.2
  obtain ⟨π₀, hπ₀⟩ := exists_perm_inl f₁ hf₁
  obtain ⟨π₁, hπ₁⟩ := exists_perm_inr f₂ hf₂
  have e₀ : α.submatrix id (π₀ ∘ Sum.inl) = α.submatrix id f₁ := by
    ext k k'; simp only [Matrix.submatrix_apply, id, Function.comp_apply, hπ₀]
  have e₁ : β.submatrix id (π₁ ∘ Sum.inr) = β.submatrix id f₂ := by
    ext k k'; simp only [Matrix.submatrix_apply, id, Function.comp_apply, hπ₁]
  have hαβ : α * β.transpose = 0 := by
    ext k k'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, α, β, Matrix.of_apply]
    exact sum_pair_mul_eq_zero P hd hu0 (horth k k') (hsp (he₂ k'))
  have hne : ∀ {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ_[p]), ‖M.det‖ = 1 → M.det ≠ 0 :=
    fun M h h0 => by rw [h0, norm_zero] at h; exact zero_ne_one h
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.plucker_minors_proportional α β hαβ ⟨π₀, by rw [e₀]; exact hne _ hn₁⟩ ⟨π₁, by rw [e₁]; exact hne _ hn₂⟩
  have hnα : ∀ π : Equiv.Perm (Ind Dw τ.1), ‖(α.submatrix id (π ∘ Sum.inl)).det‖ ≤ 1 :=
    fun π => norm_det_le_one _ fun k k' => hA.1 _ _
  have hnβ : ∀ π : Equiv.Perm (Ind Dw τ.1), ‖(β.submatrix id (π ∘ Sum.inr)).det‖ ≤ 1 :=
    fun π => norm_det_le_one _ fun k k' => hB.1 _ _
  have hsign : ∀ π : Equiv.Perm (Ind Dw τ.1), ‖((Equiv.Perm.sign π : ℤ) : ℂ_[p])‖ = 1 := by
    intro π; rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  have h1 := congrArg norm (hlam π₀)
  have h2 := congrArg norm (hlam π₁)
  rw [norm_mul, norm_mul, hsign, _root_.one_mul, e₀, hn₁] at h1
  rw [norm_mul, norm_mul, hsign, _root_.one_mul, e₁, hn₂, _root_.mul_one] at h2
  refine ⟨lam, le_antisymm (h2 ▸ hnα π₁) ?_, fun π => hlam π, π₀, ?_⟩
  · by_contra hlt
    push_neg at hlt
    have := mul_le_mul_of_nonneg_left (hnβ π₀) (norm_nonneg lam)
    rw [_root_.mul_one, ← h1] at this
    exact absurd (this.trans_lt hlt) (lt_irrefl _)
  · show ‖(α.submatrix id (π₀ ∘ Sum.inl)).det‖ = 1
    rw [e₀]; exact hn₁

end GlobalTheory.FlatModel
