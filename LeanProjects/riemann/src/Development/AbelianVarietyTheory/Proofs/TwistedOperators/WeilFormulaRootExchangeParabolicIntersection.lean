import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise

noncomputable section
namespace GlobalTheory.RootEx.QuotStep

section Abstract

theorem integral_comp_mp {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ρ : Measure Y}
    {T : X → Y} (hT : MeasurePreserving T μ ρ) {f : Y → ℂ} (hf : AEStronglyMeasurable f ρ) :
    ∫ x, f (T x) ∂μ = ∫ y, f y ∂ρ := by
  rw [← integral_map hT.measurable.aemeasurable (by rwa [hT.map_eq]), hT.map_eq]

theorem integral_swap_three {X B U : Type} [MeasurableSpace X] [MeasurableSpace B] [MeasurableSpace U]
    (μ : Measure X) (β : Measure B) (ρ : Measure U) [SFinite μ] [SFinite β] [SFinite ρ]
    (Φ : X × (B × U) → ℂ) (hΦ : Integrable Φ (μ.prod (β.prod ρ))) :
    ∫ x, ∫ y, Φ (x, y) ∂(β.prod ρ) ∂μ = ∫ b, ∫ x, ∫ u, Φ (x, (b, u)) ∂ρ ∂μ ∂β := by
  have h1 : ∫ x, ∫ y, Φ (x, y) ∂(β.prod ρ) ∂μ = ∫ x, ∫ b, ∫ u, Φ (x, (b, u)) ∂ρ ∂β ∂μ :=
    integral_congr_ae (hΦ.prod_right_ae.mono fun x hx => integral_prod _ hx)
  have h2 : Integrable (Φ ∘ MeasurableEquiv.prodAssoc) ((μ.prod β).prod ρ) :=
    ((measurePreserving_prodAssoc μ β ρ).integrable_comp_emb
      MeasurableEquiv.prodAssoc.measurableEmbedding).2 hΦ
  rw [h1]
  exact integral_integral_swap (f := fun x b => ∫ u, Φ (x, (b, u)) ∂ρ) h2.integral_prod_left

theorem exists_average {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [TopologicalSpace X] [TopologicalSpace U] [MeasurableSpace X] [MeasurableSpace U]
    [OpensMeasurableSpace (X × U)] [T2Space X] [T2Space U]
    (μ : Measure X) (ρ : Measure U) [SFinite μ] [SFinite ρ] [IsFiniteMeasureOnCompacts (μ.prod ρ)]
    [(μ.prod ρ).IsOpenPosMeasure]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (ι : X × U → G) (hι : Continuous ι) (t₁ : X × U) (h₁ : ι t₁ = 1)
    (hprop : ∀ C : Set G, IsCompact C → ∃ D, IsCompact D ∧ ∀ t, ι t ∈ C → t ∈ D)
    (δ : X → ℝ) (hδ : Continuous δ) (hδ0 : ∀ x, 0 < δ x)
    (hinv : ∀ φ : G → ℂ, Continuous φ → ∀ t, ∫ x, ∫ u, (δ x : ℂ) * φ (ι (x, u) * ι t) ∂ρ ∂μ =
      ∫ x, ∫ u, (δ x : ℂ) * φ (ι (x, u)) ∂ρ ∂μ)
    (f : G → ℂ) (hf : IsLocallyConstant f) (Ω : Set G) (hΩ : IsCompact Ω)
    (hsupp : ∀ h, f h ≠ 0 → ∃ t, ∃ w ∈ Ω, h = ι t * w)
    (hfδ : ∀ t h, f (ι t * h) = δ t.1 * f h) :
    ∃ F ∈ SB G, ∀ h, f h = ∫ x, ∫ u, F (ι (x, u) * h) ∂ρ ∂μ := by
  classical
  set C : Set G := Ω * (K : Set G) with hC
  have hCc : IsCompact C := hΩ.mul hKc
  have hlc : ∀ {Y : Type} (a : G → Y), (∀ h, ∀ κ ∈ K, a (h * κ) = a h) → IsLocallyConstant a := by
    intro Y a ha
    rw [IsLocallyConstant.iff_eventually_eq]
    intro h
    have : IsOpen {y : G | h⁻¹ * y ∈ K} := hKo.preimage (continuous_const.mul continuous_id)
    filter_upwards [this.mem_nhds (show h⁻¹ * h ∈ K by simp [one_mem])] with y hy
    rw [← ha h _ hy, mul_inv_cancel_left]
  let χ : G → ℝ := C.indicator fun _ => 1
  have hCK : ∀ h, ∀ κ ∈ K, h ∈ C → h * κ ∈ C := by
    rintro _ κ hκ ⟨w, hw, j, hj, rfl⟩
    exact ⟨w, hw, j * κ, mul_mem hj hκ, (mul_assoc _ _ _).symm⟩
  have hχK : ∀ h, ∀ κ ∈ K, χ (h * κ) = χ h := by
    intro h κ hκ
    by_cases hh : h ∈ C
    · simp [χ, hh, hCK h κ hκ hh]
    · have : h * κ ∉ C := fun h' => hh (by simpa using hCK _ _ (inv_mem hκ) h')
      simp [χ, hh, this]
  have hχ := hlc χ hχK
  let A : G → ℂ := fun h => ∫ x, ∫ u, (δ x : ℂ) * (χ (ι (x, u) * h) : ℂ) ∂ρ ∂μ
  have hA : IsLocallyConstant A := hlc A fun h κ hκ => by
    simp only [A, ← mul_assoc, hχK _ κ hκ]
  have hAι : ∀ t h, A (ι t * h) = A h := fun t h => by
    simp only [A, ← mul_assoc]
    exact hinv (fun g => (χ (g * h) : ℂ))
      (Complex.continuous_ofReal.comp (hχ.continuous.comp (continuous_id.mul continuous_const))) t
  have hA0 : ∀ w ∈ Ω, A w ≠ 0 := by
    intro w hw
    let a : X × U → ℝ := fun t => δ t.1 * χ (ι t * w)
    have ha : Continuous a := (hδ.comp continuous_fst).mul (hχ.continuous.comp (hι.mul continuous_const))
    obtain ⟨D, hD, hD'⟩ := hprop _ (hCc.image (continuous_mul_right w⁻¹))
    have hs : HasCompactSupport a := by
      refine HasCompactSupport.of_support_subset_isCompact hD fun t ht => hD' t ?_
      by_contra hn
      refine ht ?_
      have : ι t * w ∉ C := fun h' => hn ⟨_, h', by simp⟩
      simp [a, χ, this]
    have hpos : 0 < ∫ t, a t ∂(μ.prod ρ) := by
      refine ha.integral_pos_of_hasCompactSupport_nonneg_nonzero hs (x := t₁)
        (fun t => mul_nonneg (hδ0 _).le (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) ?_
      have : w ∈ C := ⟨w, hw, 1, one_mem _, mul_one _⟩
      simp [a, χ, h₁, this, (hδ0 _).ne']
    rw [integral_prod _ (ha.integrable_of_hasCompactSupport hs)] at hpos
    have e : A w = ((∫ x, ∫ u, a (x, u) ∂ρ ∂μ : ℝ) : ℂ) := by
      simp only [A, a, ← integral_complex_ofReal, Complex.ofReal_mul]
    rw [e]
    exact_mod_cast hpos.ne'
  refine ⟨fun h => f h * (A h)⁻¹ * (χ h : ℂ), ⟨(hf.mul (hA.comp fun z => z⁻¹)).mul (hχ.comp fun z : ℝ => (z : ℂ)), ?_⟩, fun h => ?_⟩
  · refine HasCompactSupport.of_support_subset_isCompact hCc fun t ht => ?_
    by_contra hn
    exact ht (by simp [χ, hn])
  · have e : ∀ x u, f (ι (x, u) * h) * (A (ι (x, u) * h))⁻¹ * (χ (ι (x, u) * h) : ℂ) =
        f h * (A h)⁻¹ * ((δ x : ℂ) * (χ (ι (x, u) * h) : ℂ)) := fun x u => by
      rw [hfδ, hAι]; ring
    simp only [e, integral_const_mul]
    by_cases h0 : f h = 0
    · simp [h0]
    · obtain ⟨t, w, hw, rfl⟩ := hsupp h h0
      have := hA0 w hw
      rw [← hAι t] at this
      have e2 : (∫ x, (δ x : ℂ) * ∫ u, (χ (ι (x, u) * (ι t * w)) : ℂ) ∂ρ ∂μ) = A (ι t * w) := by
        simp only [A, integral_const_mul]
      rw [e2, inv_mul_cancel_right₀ this]

end Abstract

section Pattern
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]

open Classical in

def ext (S : ι × ι → Prop) (e : {rs // S rs} → k) : Matrix ι ι k :=
  Matrix.of fun r s => if h : S (r, s) then e ⟨(r, s), h⟩ else 0

omit [Fintype ι] [DecidableEq ι] in
theorem ext_pos {S : ι × ι → Prop} (e : {rs // S rs} → k) {r s : ι} (h : S (r, s)) :
    ext S e r s = e ⟨(r, s), h⟩ := by simp [ext, h]

omit [Fintype ι] [DecidableEq ι] in
theorem ext_neg {S : ι × ι → Prop} (e : {rs // S rs} → k) {r s : ι} (h : ¬ S (r, s)) :
    ext S e r s = 0 := by simp [ext, h]

variable {b : ι → ℕ} {S : ι × ι → Prop}

def chart (hS : ∀ rs, S rs → b rs.1 < b rs.2) (e : {rs // S rs} → k) : GL ι k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + ext S e) (by
    rw [Radical.Uni.det (b := b) fun r s hrs => by
      rw [Matrix.add_apply, ext_neg e fun h => absurd (hS _ h) (not_lt.2 hrs), add_zero]]
    exact one_ne_zero)

variable (hS : ∀ rs, S rs → b rs.1 < b rs.2)

theorem chart_val (e : {rs // S rs} → k) : (chart hS e).val = 1 + ext S e := rfl

theorem chart_pos (e : {rs // S rs} → k) (i : {rs // S rs}) : (chart hS e).val i.1.1 i.1.2 = e i := by
  have : i.1.1 ≠ i.1.2 := fun h => absurd (hS _ i.2) (by rw [h]; exact lt_irrefl _)
  rw [chart_val, Matrix.add_apply, Matrix.one_apply_ne this, zero_add, ext_pos e i.2]

theorem chart_neg (e : {rs // S rs} → k) {r s : ι} (h : ¬ S (r, s)) :
    (chart hS e).val r s = (1 : Matrix ι ι k) r s := by
  rw [chart_val, Matrix.add_apply, ext_neg e h, add_zero]

theorem chart_entries (g : GL ι k) (hg : ∀ r s, ¬ S (r, s) → g.val r s = (1 : Matrix ι ι k) r s) :
    chart hS (fun i => g.val i.1.1 i.1.2) = g := by
  ext r s
  by_cases h : S (r, s)
  · exact chart_pos hS _ ⟨(r, s), h⟩
  · rw [chart_neg hS _ h, hg r s h]

theorem chart_zero : chart hS (0 : {rs // S rs} → k) = 1 := by
  refine Eq.trans ?_ (chart_entries hS 1 fun _ _ _ => rfl)
  congr 1
  funext i
  have : i.1.1 ≠ i.1.2 := fun h => absurd (hS _ i.2) (by rw [h]; exact lt_irrefl _)
  simp [Matrix.one_apply_ne this]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [Fintype ι] [DecidableEq ι] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_ext (S : ι × ι → Prop) (r s : ι) : Continuous fun e : {rs // S rs} → k => ext S e r s := by
  by_cases h : S (r, s)
  · simp only [ext_pos _ h]; exact continuous_apply _
  · simp only [ext_neg _ h]; exact continuous_const

theorem continuous_chart : Continuous (chart hS : ({rs // S rs} → k) → GL ι k) := by
  rw [SplitFlip.isEmbedding_val_GL.continuous_iff]
  exact continuous_matrix fun r s => continuous_const.add (continuous_ext S r s)

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem integral_chart_mul_right [Fintype {rs // S rs}] (m : GL ι k)
    (hm : ∀ r s, ¬ S (r, s) → m.val r s = (1 : Matrix ι ι k) r s)
    (hm' : ∀ e r s, ¬ S (r, s) → (chart hS e * m).val r s = (1 : Matrix ι ι k) r s)
    (φ : GL ι k → ℂ) (hφ : Continuous φ) :
    ∫ e, φ (chart hS e * m) ∂(Measure.pi fun _ => ν) = ∫ e, φ (chart hS e) ∂(Measure.pi fun _ => ν) := by
  haveI := secondCountable k
  haveI := t2Space k
  have hT := GlobalTheory.SgLoc.TriShift.measurePreserving_triangular ν (fun i : {rs // S rs} => b i.1.2)
    (fun i e => (m.val - 1) i.1.1 i.1.2 + ∑ t, ext S e i.1.1 t * (m.val - 1) t i.1.2)
    (fun i => (continuous_const.add (continuous_finset_sum _ fun t _ =>
      (continuous_ext S _ _).mul continuous_const)).measurable)
    (fun i x y hxy => by
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h2 : S (t, i.1.2)
      · by_cases h1 : S (i.1.1, t)
        · rw [ext_pos _ h1, ext_pos _ h1, hxy _ (hS _ h2)]
        · rw [ext_neg _ h1, ext_neg _ h1]
      · rw [Matrix.sub_apply, hm _ _ h2, sub_self, mul_zero, mul_zero])
  rw [← integral_comp_mp hT (f := fun e => φ (chart hS e)) (hφ.comp (continuous_chart hS)).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  dsimp only
  rw [← chart_entries hS _ (hm' e)]
  congr 2
  funext i
  have hne : i.1.1 ≠ i.1.2 := fun h => absurd (hS _ i.2) (by rw [h]; exact lt_irrefl _)
  have : (chart hS e * m).val = 1 + (ext S e + ((m.val - 1) + ext S e * (m.val - 1))) := by
    rw [Units.val_mul, chart_val]; noncomm_ring
  rw [this, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.add_apply, ext_pos e i.2]
  rfl

theorem measurePreserving_mul {n : Type} [Fintype n] [Fintype {rs // S rs}]
    [Fintype {rs : ι × ι // b rs.1 < b rs.2}] (j : n → ι × ι) (hj : Function.Injective j)
    (hjS : ∀ x, ¬ S (j x)) (hjb : ∀ x, b (j x).1 < b (j x).2)
    (hcov : ∀ rs, b rs.1 < b rs.2 → S rs ∨ ∃ x, j x = rs)
    (E : (n → k) → GL ι k) (hE : ∀ β x, (E β).val (j x).1 (j x).2 = β x)
    (hE' : ∀ β r s, (∀ x, j x ≠ (r, s)) → (E β).val r s = (1 : Matrix ι ι k) r s) :
    MeasurePreserving (fun (y : (n → k) × ({rs // S rs} → k)) (i : {rs : ι × ι // b rs.1 < b rs.2}) =>
        (chart hS y.2 * E y.1).val i.1.1 i.1.2)
      ((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν)) (Measure.pi fun _ => ν) := by
  classical
  haveI := secondCountable k
  haveI := t2Space k
  let S' : ι × ι → Prop := fun rs => b rs.1 < b rs.2
  let σ : n ⊕ {rs // S rs} ≃ {rs // S' rs} := Equiv.ofBijective
    (Sum.elim (fun x => ⟨j x, hjb x⟩) fun i => ⟨i.1, hS _ i.2⟩) (by
      constructor
      · rintro (x | x) (y | y) h <;> simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
        · rw [hj h]
        · exact absurd (h ▸ y.2) (hjS x)
        · exact absurd (h ▸ x.2) (hjS y)
        · rw [Subtype.ext h]
      · rintro ⟨rs, h⟩
        rcases hcov rs h with h' | ⟨x, rfl⟩
        · exact ⟨Sum.inr ⟨rs, h'⟩, rfl⟩
        · exact ⟨Sum.inl x, rfl⟩)
  have hT := GlobalTheory.SgLoc.TriShift.measurePreserving_triangular ν (fun i : {rs // S' rs} => b i.1.2 - b i.1.1)
    (fun i e => ∑ t, (if S (i.1.1, t) then ext S' e i.1.1 t else 0) *
      (if S (t, i.1.2) then 0 else ext S' e t i.1.2))
    (fun i => (continuous_finset_sum _ fun t _ => by
      refine Continuous.mul ?_ ?_ <;> split_ifs <;>
        first | exact continuous_const | exact continuous_ext S' _ _).measurable)
    (fun i x y hxy => by
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h1 : S' (i.1.1, t)
      · by_cases h2 : S' (t, i.1.2)
        · have h1' : b i.1.1 < b t := h1
          have h2' : b t < b i.1.2 := h2
          rw [ext_pos _ h1, ext_pos _ h1, ext_pos _ h2, ext_pos _ h2,
            hxy ⟨_, h1⟩ (by dsimp only; omega), hxy ⟨_, h2⟩ (by dsimp only; omega)]
        · simp [ext_neg _ h2]
      · simp [ext_neg _ h1])
  have hJ := (measurePreserving_piCongrLeft (fun _ : {rs // S' rs} => ν) σ).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : n ⊕ {rs // S rs} => ν))
  convert hT.comp hJ using 1
  funext ⟨β, e⟩ i
  set ε := (MeasurableEquiv.piCongrLeft (fun _ : {rs // S' rs} => k) σ
    ((MeasurableEquiv.sumPiEquivProdPi fun _ : n ⊕ {rs // S rs} => k).symm (β, e))) with hε
  have h1 : ∀ x, ε (σ (Sum.inl x)) = β x := fun x => by
    rw [hε, MeasurableEquiv.piCongrLeft_apply_apply]; rfl
  have h2 : ∀ x, ε (σ (Sum.inr x)) = e x := fun x => by
    rw [hε, MeasurableEquiv.piCongrLeft_apply_apply]; rfl
  have hA : ∀ r s, (if S (r, s) then ext S' ε r s else 0) = ext S e r s := fun r s => by
    split_ifs with h
    · rw [ext_pos _ h, ext_pos (S := S') _ (hS _ h)]; exact h2 ⟨_, h⟩
    · rw [ext_neg _ h]
  have hB : ∀ r s, (if S (r, s) then 0 else ext S' ε r s) = ((E β).val - 1) r s := fun r s => by
    by_cases hx : ∃ x, j x = (r, s)
    · obtain ⟨x, hx⟩ := hx
      obtain rfl : (j x).1 = r := congrArg Prod.fst hx
      obtain rfl : (j x).2 = s := congrArg Prod.snd hx
      have hne : (j x).1 ≠ (j x).2 := fun h => absurd (hjb x) (by rw [h]; exact lt_irrefl _)
      rw [if_neg (hjS x), ext_pos (S := S') _ (hjb x), Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero, hE]
      exact h1 x
    · rw [Matrix.sub_apply, hE' β r s fun x h => hx ⟨x, h⟩, sub_self]
      split_ifs with h
      · rfl
      · exact ext_neg _ fun h' => (hcov _ h').elim h hx
  have hne : i.1.1 ≠ i.1.2 := fun h => absurd i.2 (by rw [h]; exact lt_irrefl _)
  have : (chart hS e * E β).val = 1 + ((ext S e + ((E β).val - 1)) + ext S e * ((E β).val - 1)) := by
    rw [Units.val_mul, chart_val]; noncomm_ring
  change _ = ε i + ∑ t, (if S (i.1.1, t) then ext S' ε i.1.1 t else 0) *
      (if S (t, i.1.2) then 0 else ext S' ε t i.1.2)
  simp only [hA, hB]
  rw [this, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.add_apply, Matrix.add_apply, ← hA, ← hB,
    ext_pos (S := S') ε i.2]
  congr 1
  split_ifs <;> simp

end Pattern

section Concrete
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

abbrev Both (n : Type) (c p : ℕ) (rs : (n ⊕ Fin c) × (n ⊕ Fin c)) : Prop :=
  lev p rs.1 < lev p rs.2 ∧ lev (p + 1) rs.1 < lev (p + 1) rs.2

abbrev chartN (q : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev q rs.1 < lev q rs.2} → k) : GL (n ⊕ Fin c) k :=
  chart (b := lev q) (S := fun rs => lev q rs.1 < lev q rs.2) (fun _ h => h) e

abbrev chartB (p : ℕ) (e : {rs // Both n c p rs} → k) : GL (n ⊕ Fin c) k :=
  chart (b := lev p) (S := Both n c p) (fun _ h => h.1) e

theorem chartN_mem (q : ℕ) (e) : (chartN q e : GL (n ⊕ Fin c) k) ∈ N k n c q :=
  (Radical.mem_N_iff _).2 fun _ _ h => chart_neg _ _ (not_lt.2 h)

theorem chartN_entries {q : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c q) :
    chartN q (fun i => g.val i.1.1 i.1.2) = g :=
  chart_entries _ g fun r s h => (Radical.mem_N_iff _).1 hg r s (not_lt.1 h)

theorem mem_inf_iff {p : ℕ} (g : GL (n ⊕ Fin c) k) : g ∈ N k n c p ⊓ N k n c (p + 1) ↔
    ∀ r s, ¬ Both n c p (r, s) → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := by
  rw [Subgroup.mem_inf, Radical.mem_N_iff, Radical.mem_N_iff]
  constructor
  · rintro ⟨h1, h2⟩ r s h
    rcases not_and_or.1 h with h | h
    · exact h1 r s (not_lt.1 h)
    · exact h2 r s (not_lt.1 h)
  · exact fun h => ⟨fun r s hrs => h r s fun h' => absurd h'.1 (not_lt.2 hrs),
      fun r s hrs => h r s fun h' => absurd h'.2 (not_lt.2 hrs)⟩

theorem chartB_mem (p : ℕ) (e) : (chartB p e : GL (n ⊕ Fin c) k) ∈ N k n c p ⊓ N k n c (p + 1) :=
  (mem_inf_iff _).2 fun _ _ h => chart_neg _ _ h

theorem exists_of_mem_inf {p : ℕ} {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c p ⊓ R k n c (p + 1)) :
    ∃ x e, r = embX c x * chartB p e := by
  obtain ⟨x, g, hg, rfl⟩ := Radical.exists_of_mem_R hr.1
  obtain ⟨y, g', hg', e⟩ := Radical.exists_of_mem_R hr.2
  obtain rfl : y = x := by
    apply Units.ext
    rw [← Radical.toBlocks₁₁_embX_mul x hg, ← Radical.toBlocks₁₁_embX_mul y hg', e]
  obtain rfl : g = g' := mul_left_cancel e
  exact ⟨y, _, by rw [chartB, chart_entries _ g ((mem_inf_iff g).1 ⟨hg, hg'⟩)]⟩

theorem colE_neg (q : ℕ) (β : n → k) : colE c q β * colE c q (-β) = 1 := by
  apply Units.ext
  simp only [colE, upU, Units.val_mul, fromBlocks_multiply, Units.val_one, ← fromBlocks_one]
  congr 1 <;> simp
  ext r i
  by_cases h : i.val + 1 = q <;> simp [h]

theorem conj_colE (q : ℕ) (x : GL n k) (β : n → k) :
    embX c x * colE c q β * (embX c x)⁻¹ = colE c q (x.val.mulVec β) := by
  apply Units.ext
  rw [Radical.conj_val]
  simp only [colE, upU, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.mul_one, Units.mul_inv, Matrix.zero_mul]
  congr 1
  ext r i
  simp only [Matrix.mul_apply, Matrix.of_apply]
  split_ifs <;> simp [mulVec, dotProduct]

theorem col_apply {p : ℕ} (hp : p < c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p ⊓ N k n c (p + 1)) (β : n → k)
    (x : n) : (g * colE c (p + 1) β).val (Sum.inl x) (Sum.inr ⟨p, hp⟩) = β x := by
  have h1 := (Radical.mem_N_iff _).1 hg.2
  have h2 : ∀ y, g.val (Sum.inl x) (Sum.inl y) = (1 : Matrix n n k) x y := fun y => by
    rw [h1 _ _ (by simp [lev])]; simp [Matrix.one_apply]
  have h3 : g.val (Sum.inl x) (Sum.inr ⟨p, hp⟩) = 0 := by
    rw [h1 _ _ (by simp [lev])]; simp
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, h2, h3, Matrix.one_apply]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_embX : Continuous (embX c : GL n k → GL (n ⊕ Fin c) k) := by
  rw [SplitFlip.isEmbedding_val_GL.continuous_iff]
  exact Units.continuous_val.matrix_fromBlocks continuous_const continuous_const continuous_const

theorem continuous_colE (q : ℕ) : Continuous (colE c q : (n → k) → GL (n ⊕ Fin c) k) := by
  rw [SplitFlip.isEmbedding_val_GL.continuous_iff]
  refine Continuous.matrix_fromBlocks continuous_const (continuous_matrix fun r i => ?_) continuous_const
    continuous_const
  simp only [Matrix.of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem proper_chart {q : ℕ} {b : n ⊕ Fin c → ℕ} {S : (n ⊕ Fin c) × (n ⊕ Fin c) → Prop}
    (hS : ∀ rs, S rs → b rs.1 < b rs.2) (hq : ∀ e, (chart hS e : GL (n ⊕ Fin c) k) ∈ N k n c q)
    (C : Set (GL (n ⊕ Fin c) k)) (hC : IsCompact C) :
    ∃ D, IsCompact D ∧ ∀ t : GL n k × ({rs // S rs} → k), embX c t.1 * chart hS t.2 ∈ C → t ∈ D := by
  haveI := t2Space k
  have c1 : Continuous fun g : GL (n ⊕ Fin c) k => g.val.toBlocks₁₁ :=
    continuous_matrix fun r s => Units.continuous_val.matrix_elem _ _
  have hX := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage
    ((hC.image c1).prod ((hC.image (c1.comp continuous_inv)).image MulOpposite.continuous_op))
  have c2 : Continuous fun (y : GL n k × GL (n ⊕ Fin c) k) (i : {rs // S rs}) =>
      ((embX c y.1)⁻¹ * y.2).val i.1.1 i.1.2 :=
    continuous_pi fun i => (Units.continuous_val.comp
      ((continuous_embX.comp continuous_fst).inv.mul continuous_snd)).matrix_elem _ _
  refine ⟨_, hX.prod ((hX.prod hC).image c2), fun t ht => ?_⟩
  have h1 : t.1 ∈ Units.embedProduct (Matrix n n k) ⁻¹' ((fun g : GL (n ⊕ Fin c) k => g.val.toBlocks₁₁) '' C) ×ˢ
      (MulOpposite.op '' (((fun g : GL (n ⊕ Fin c) k => g.val.toBlocks₁₁) ∘ fun a => a⁻¹) '' C)) := by
    refine ⟨⟨_, ht, Radical.toBlocks₁₁_embX_mul _ (hq _)⟩, _, ⟨_, ht, rfl⟩, congrArg MulOpposite.op ?_⟩
    rw [← Radical.toBlocks₁₁_embX_mul t.1⁻¹ (Radical.conj_mem t.1 (inv_mem (hq t.2))), map_inv,
      mul_assoc, inv_mul_cancel_left, ← _root_.mul_inv_rev]
    rfl
  refine ⟨h1, (t.1, _), ⟨h1, ht⟩, funext fun i => ?_⟩
  simp only [inv_mul_cancel_left]
  exact chart_pos hS _ i

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem integral_volN (q : ℕ) (φ : GL (n ⊕ Fin c) k → ℂ) :
    ∫ u : N k n c q, φ u ∂(volN ν n c q) = ∫ e, φ (chartN q e) ∂(Measure.pi fun _ => ν) := by
  haveI := secondCountable k
  let eqv : N k n c q ≃ᵐ ({rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev q rs.1 < lev q rs.2} → k) :=
    { toFun := fun g rs => (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2
      invFun := fun e => ⟨chartN q e, chartN_mem q e⟩
      left_inv := fun g => Subtype.ext (chartN_entries g.2)
      right_inv := fun e => funext fun i => chart_pos (b := lev q) (fun _ h => h) e i
      measurable_toFun := (continuous_pi fun i =>
        (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _).measurable
      measurable_invFun := ((continuous_chart _).subtype_mk _).measurable }
  have : volN ν n c q = (Measure.pi fun _ => ν).map eqv.symm := by
    rw [MeasurableEquiv.map_symm]
    unfold volN
    congr!
  rw [this, integral_map_equiv]
  rfl

def IsSplit (p q : ℕ) (E : (n → k) → GL (n ⊕ Fin c) k) : Prop :=
  ∃ T : (n → k) × ({rs // Both n c p rs} → k) →
      ({rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev q rs.1 < lev q rs.2} → k),
    MeasurePreserving T ((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν)) (Measure.pi fun _ => ν) ∧
      ∀ y, chartN q (T y) = chartB p y.2 * E y.1

theorem isSplit_col {p : ℕ} (hp : p < c) : IsSplit (n := n) ν p p (colE c (p + 1)) := by
  refine ⟨_, measurePreserving_mul (b := lev p) (S := Both n c p) (fun _ h => h.1) ν
    (fun x => (Sum.inl x, Sum.inr ⟨p, hp⟩)) (fun x y h => by simpa using h) (fun x => by simp [lev])
    (fun x => by simp [lev]) ?_ (colE c (p + 1)) (fun β x => by simp [colE, upU]) ?_,
    fun y => chartN_entries (mul_mem (chartB_mem p _).1 (Radical.colE_mem _ (Nat.lt_succ_self p)))⟩
  · rintro ⟨r | r, s | s⟩ <;> simp [Both, lev, Fin.ext_iff] <;> omega
  · rintro β (r | r) (s | s) h <;> simp [colE, upU, Matrix.one_apply]
    intro hs
    exact absurd (by simp [Fin.ext_iff, hs]) (h r)

theorem isSplit_row {p : ℕ} (hp1 : 1 ≤ p) (hp : p < c) : IsSplit (n := n) ν p (p + 1) (rowE c p) := by
  refine ⟨_, measurePreserving_mul (b := lev (p + 1)) (S := Both n c p) (fun _ h => h.2) ν
    (fun x => (Sum.inr ⟨p - 1, by omega⟩, Sum.inl x)) (fun x y h => by simpa using h)
    (fun x => by simp [lev]; omega)
    (fun x => by simp [lev]; omega) ?_ (rowE c p) (fun β x => by simp [rowE, lowU]; omega) ?_,
    fun y => chartN_entries (mul_mem (chartB_mem p _).2 (Radical.rowE_mem _ (Nat.lt_succ_self p)))⟩
  · rintro ⟨r | r, s | s⟩ <;> simp [Both, lev, Fin.ext_iff] <;> omega
  · rintro β (r | r) (s | s) h <;> simp [rowE, lowU, Matrix.one_apply]
    intro hs
    exact absurd (by simp [Fin.ext_iff, ← hs]) (h s)

theorem average_step {p q : ℕ} {E : (n → k) → GL (n ⊕ Fin c) k} (hE : IsSplit ν p q E)
    (μX : Measure (GL n k)) [μX.IsHaarMeasure] {F : GL (n ⊕ Fin c) k → ℂ} (hF : F ∈ SB (GL (n ⊕ Fin c) k))
    (h : GL (n ⊕ Fin c) k) :
    ∫ β, ∫ x, ∫ e, F (embX c x * chartB p e * (E β * h)) ∂(Measure.pi fun _ => ν) ∂μX ∂(Measure.pi fun _ => ν) =
      ∫ x, (∫ u : N k n c q, F (embX c x * (u : GL (n ⊕ Fin c) k) * h) ∂(volN ν n c q)) ∂μX := by
  haveI := secondCountable k
  haveI := t2Space k
  obtain ⟨T, hT, hT'⟩ := hE
  let a : GL n k × ({rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev q rs.1 < lev q rs.2} → k) → ℂ :=
    fun t => F (embX c t.1 * chartN q t.2 * h)
  have ha : Continuous a := hF.1.continuous.comp (((continuous_embX.comp continuous_fst).mul
    ((continuous_chart _).comp continuous_snd)).mul continuous_const)
  obtain ⟨D, hD, hD'⟩ := proper_chart _ (chartN_mem (k := k) (n := n) (c := c) q) _
    (hF.2.isCompact.image (continuous_mul_right h⁻¹))
  have hs : HasCompactSupport a :=
    HasCompactSupport.of_support_subset_isCompact hD fun t ht => hD' t ⟨_, subset_tsupport _ ht, by simp⟩
  have hi := ((MeasurePreserving.id μX).prod hT).integrable_comp_of_integrable
    (ha.integrable_of_hasCompactSupport hs)
  have h3 := integral_swap_three μX _ _ _ hi
  simp only [Function.comp_apply, Prod.map, id, a, hT', mul_assoc] at h3
  simp only [mul_assoc]
  rw [← h3]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [integral_volN ν q fun u => F (embX c x * (u * h)), ← integral_comp_mp hT
    (f := fun e => F (embX c x * (chartN q e * h))) (hF.1.continuous.comp (continuous_const.mul
      ((continuous_chart _).mul continuous_const))).aestronglyMeasurable]
  simp only [hT', mul_assoc]

theorem integral_conj {p : ℕ} (hp1 : 1 ≤ p) (hp : p < c) (x : GL n k) (ψ : GL (n ⊕ Fin c) k → ℂ)
    (hψ : Continuous ψ) :
    ∫ e, ψ (embX c x * chartB p e * (embX c x)⁻¹) ∂(Measure.pi fun _ => ν) =
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (-((c : ℝ) - 2 * p)) : ℝ) : ℂ) *
        ∫ e, ψ (chartB p e) ∂(Measure.pi fun _ => ν) := by
  haveI := secondCountable k
  haveI := t2Space k
  obtain ⟨T, hT, hT'⟩ := isSplit_col (n := n) ν hp
  set K : Set (n → k) := Set.pi Set.univ fun _ => (𝒪[k] : Set k) with hK
  have hKo : IsOpen K := isOpen_set_pi Set.finite_univ fun _ _ => Model.isOpen_int
  have hKc : IsCompact K := isCompact_univ_pi fun _ => Model.isCompact_int
  let ρ : (n → k) → ℂ := K.indicator fun _ => 1
  have hρ : Continuous ρ := IsClopen.continuous_indicator ⟨hKc.isClosed, hKo⟩ continuous_const
  have hρ0 : ∫ β, ρ β ∂(Measure.pi fun _ => ν) ≠ 0 := by
    have h0 : (Measure.pi fun _ : n => ν) K ≠ 0 := (hKo.measure_pos _ ⟨0, fun _ _ => zero_mem _⟩).ne'
    have ht : (Measure.pi fun _ : n => ν) K ≠ ⊤ := hKc.measure_lt_top.ne
    simp only [ρ, integral_indicator_const _ hKo.measurableSet]
    simp [Measure.real, ENNReal.toReal_eq_zero_iff, h0, ht]
  let B : GL (n ⊕ Fin c) k → n → k := fun g y => g.val (Sum.inl y) (Sum.inr ⟨p, hp⟩)
  have hB : Continuous B := continuous_pi fun y => Units.continuous_val.matrix_elem _ _
  let φ : GL (n ⊕ Fin c) k → ℂ := fun g => ρ (B g) * ψ (g * colE c (p + 1) (-B g))
  have hφ : Continuous φ := (hρ.comp hB).mul (hψ.comp (continuous_id.mul ((continuous_colE _).comp hB.neg)))
  have hφ' : ∀ g ∈ N k n c p ⊓ N k n c (p + 1), ∀ β, φ (g * colE c (p + 1) β) = ρ β * ψ g := fun g hg β => by
    have : B (g * colE c (p + 1) β) = β := funext (col_apply hp hg β)
    simp only [φ, this, mul_assoc, colE_neg, mul_one]
  have key := (VolN.volN_haar_and_modulus k n c p hp1 hp.le ν).2.2.2.2 x φ
  rw [integral_volN ν p fun u => φ (embX c x * u * (embX c x)⁻¹), integral_volN ν p φ,
    ← integral_comp_mp hT (f := fun e => φ (embX c x * chartN p e * (embX c x)⁻¹))
      (hφ.comp ((continuous_const.mul (continuous_chart _)).mul continuous_const)).aestronglyMeasurable,
    ← integral_comp_mp hT (f := fun e => φ (chartN p e)) (hφ.comp (continuous_chart _)).aestronglyMeasurable] at key
  have e1 : ∀ y : (n → k) × ({rs // Both n c p rs} → k),
      φ (embX c x * (chartB p y.2 * colE c (p + 1) y.1) * (embX c x)⁻¹) =
        ρ (x.val.mulVec y.1) * ψ (embX c x * chartB p y.2 * (embX c x)⁻¹) := fun y => by
    rw [← hφ' _ ⟨Radical.conj_mem x (chartB_mem p _).1, Radical.conj_mem x (chartB_mem p _).2⟩, ← conj_colE]
    congr 1
    group
  simp only [hT', e1, hφ' _ (chartB_mem p _)] at key
  rw [integral_prod_mul (fun β => ρ (x.val.mulVec β)) fun e => ψ (embX c x * chartB p e * (embX c x)⁻¹),
    integral_prod_mul ρ fun e => ψ (chartB p e), integral_comp_mulVec_eq_smul] at key
  have hpos := nabs_pos' (Matrix.GeneralLinearGroup.det x)
  set A := nabs k (Matrix.GeneralLinearGroup.det x)
  have e2 : A ^ (-((c : ℝ) - 2 * p)) = A * A ^ (-((c : ℝ) + 1 - 2 * p)) := by
    rw [show -((c : ℝ) - 2 * p) = 1 + -((c : ℝ) + 1 - 2 * p) by ring, Real.rpow_add hpos, Real.rpow_one]
  have hA : (A : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [Complex.real_smul, Complex.real_smul, Complex.ofReal_inv] at key
  rw [e2, Complex.ofReal_mul]
  refine mul_left_cancel₀ (mul_ne_zero (inv_ne_zero hA) hρ0) ?_
  rw [key]
  field_simp

end Concrete

theorem quotInt_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ) (_ : IsLocallyConstant f) (_ : ∃ Ω, IsCompact Ω ∧ ∀ h, f h ≠ 0 → ∃ r ∈ R k n c p ⊓ R k n c (p + 1), ∃ w ∈ Ω, h = r * w) (_ : ∀ (x : GL n k), ∀ u ∈ N k n c p ⊓ N k n c (p + 1), ∀ h, f (embX c x * u * h) = ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) - 2 * p) : ℝ) : ℂ) * f h), ∃ z, IsQuotInt ν μX μG p (fun h => ∫ β : n → k, f (colE c (p + 1) β * h) ∂(Measure.pi fun _ => ν)) z ∧ IsQuotInt ν μX μG (p + 1) (fun h => ∫ u : n → k, f (rowE c p u * h) ∂(Measure.pi fun _ => ν)) z := by
  intro k _ _ _ _ _ _ n _ _ c p hp1 hp ν _ μX _ μG _ f hf hΩ hfe
  haveI := secondCountable k
  haveI := t2Space k
  obtain ⟨Ω, hΩ, hsupp⟩ := hΩ
  let δ : GL n k → ℝ := fun x => nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) - 2 * p)
  have hδm : ∀ x y, δ (x * y) = δ x * δ y := fun x y => by
    simp only [δ, map_mul, Model.nabs_mul]
    exact Real.mul_rpow (nabs_pos' _).le (nabs_pos' _).le
  have hδc : Continuous δ := (((isLocallyConstant_nabs k).comp_continuous Matrix.GeneralLinearGroup.continuous_det).comp
    (fun t : ℝ => t ^ ((c : ℝ) - 2 * p))).continuous
  refine (exists_average μX (Measure.pi fun _ : {rs // Both n c p rs} => ν) (KO k (n ⊕ Fin c))
    SplitFlip.isOpen_KO SplitFlip.isCompact_KO (fun t => embX c t.1 * chartB p t.2)
    ((continuous_embX.comp continuous_fst).mul ((continuous_chart _).comp continuous_snd)) (1, 0)
    (by simp [chart_zero]) (proper_chart _ fun e => (chartB_mem p e).1) δ hδc
    (fun x => Real.rpow_pos_of_pos (nabs_pos' _) _) ?_ f hf Ω hΩ ?_
    (fun t h => hfe t.1 _ (chartB_mem p t.2) h)).elim fun F ⟨hF, hav⟩ => ?_
  · rintro φ hφ ⟨y, m⟩
    have e : ∀ x, ∫ u, (δ x : ℂ) * φ (embX c x * chartB p u * (embX c y * chartB p m)) ∂(Measure.pi fun _ => ν) =
        ∫ u, (δ (x * y) : ℂ) * φ (embX c (x * y) * chartB p u) ∂(Measure.pi fun _ => ν) := fun x => by
      have h1 := integral_conj ν hp1 hp y⁻¹ (fun g => φ (embX c (x * y) * (g * chartB p m)))
        (hφ.comp (continuous_const.mul (continuous_id.mul continuous_const)))
      have h2 := integral_chart_mul_right (b := lev p) (S := Both n c p) (fun _ h => h.1) ν (chartB p m)
        ((mem_inf_iff _).1 (chartB_mem p m)) (fun e => (mem_inf_iff _).1 (mul_mem (chartB_mem p e) (chartB_mem p m)))
        (fun g => φ (embX c (x * y) * g)) (hφ.comp (continuous_const.mul continuous_id))
      have h3 : nabs k (Matrix.GeneralLinearGroup.det y⁻¹) ^ (-((c : ℝ) - 2 * p)) = δ y := by
        have : nabs k (Matrix.GeneralLinearGroup.det y⁻¹) = (nabs k (Matrix.GeneralLinearGroup.det y))⁻¹ := by
          simp [nabs]
        rw [this, Real.inv_rpow (nabs_pos' _).le, Real.rpow_neg (nabs_pos' _).le, inv_inv]
      rw [h2, h3] at h1
      rw [integral_const_mul, integral_const_mul, hδm, Complex.ofReal_mul, mul_assoc, ← h1]
      simp only [map_mul, map_inv, inv_inv, mul_assoc, mul_inv_cancel_left]
    refine (integral_congr_ae (Filter.Eventually.of_forall e)).trans ?_
    exact integral_mul_right_eq_self
      (fun x => ∫ u, (δ x : ℂ) * φ (embX c x * chartB p u) ∂(Measure.pi fun _ => ν)) y
  · intro h hh
    obtain ⟨r, hr, w, hw, rfl⟩ := hsupp h hh
    obtain ⟨x, e, rfl⟩ := exists_of_mem_inf hr
    exact ⟨(x, e), w, hw, rfl⟩
  · refine ⟨∫ h, F h ∂μG, ⟨F, hF, fun h => ?_, rfl⟩, ⟨F, hF, fun h => ?_, rfl⟩⟩
    · simp only [hav]
      exact average_step ν (isSplit_col ν hp) μX hF h
    · simp only [hav]
      exact average_step ν (isSplit_row ν hp1 hp) μX hF h

end GlobalTheory.RootEx.QuotStep
