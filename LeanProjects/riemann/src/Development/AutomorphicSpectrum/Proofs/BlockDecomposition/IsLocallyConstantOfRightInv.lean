import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

open MeasureTheory GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.QSplitPf

section Top

variable {B : Type} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]

theorem isLocallyConstant_of_rightInv {X : Type} {V : Subgroup B} (hV : IsOpen (V : Set B)) {f : B → X}
    (hf : ∀ v ∈ V, ∀ y, f (y * v) = f y) : IsLocallyConstant f := by
  intro s
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have h1 : (fun z => y⁻¹ * z) ⁻¹' (V : Set B) ∈ nhds y := by
    apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
    simpa using hV.mem_nhds V.one_mem
  filter_upwards [h1] with z hz
  have h2 := hf _ hz y
  rw [mul_inv_cancel_left] at h2
  show f z ∈ s
  rw [h2]
  exact hy

variable [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

theorem setIntegral_subgroup (β : Measure B) [β.IsHaarMeasure] (K U : Subgroup B) (hKo : IsOpen (K : Set B))
    (hKc : IsCompact (K : Set B)) (hU : IsOpen (U : Set B)) (f : B → ℂ) (hf : ∀ u ∈ U, ∀ y, f (y * u) = f y) :
    ∫ y in (K : Set B), f y ∂β = (β.real K : ℂ) * avg (fun k : K => f k) := by
  set u : K → ℂ := fun k => f k with hu
  set R := rStab u with hR
  have hUR : U.subgroupOf K ≤ R := by
    intro k hk x
    exact hf k hk x
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hRo : IsOpen (R : Set K) :=
    Subgroup.isOpen_mono hUR (hU.preimage continuous_subtype_val)
  haveI : Finite (K ⧸ R) := Subgroup.quotient_finite_of_isOpen R hRo
  haveI := Fintype.ofFinite (K ⧸ R)
  set R' : Subgroup B := R.map K.subtype with hR'
  have hR'o : IsOpen (R' : Set B) := by
    have : (R' : Set B) = Subtype.val '' (R : Set K) := by
      ext y; simp [hR', Subgroup.mem_map]
    rw [this]
    exact hKo.isOpenMap_subtype_val _ hRo
  have hR'K : (R' : Set B) ⊆ K := by
    rintro _ ⟨r, -, rfl⟩
    exact r.2
  let A : K ⧸ R → Set B := fun t => (fun y => ((t.out : K) : B)⁻¹ * y) ⁻¹' (R' : Set B)
  have hAm : ∀ t, MeasurableSet (A t) := fun t =>
    (hR'o.preimage (continuous_const.mul continuous_id)).measurableSet
  have hAmeas : ∀ t, β (A t) = β R' := fun t => measure_preimage_mul β _ _
  have hAd : Pairwise (Function.onFun Disjoint A) := by
    intro t t' htt
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨r, hr, hry⟩ ⟨r', hr', hry'⟩
    apply htt
    have e1 : ((t.out : K) : B) * r = y := by
      simp only [Subgroup.coe_subtype] at hry
      rw [hry]; group
    have e2 : ((t'.out : K) : B) * r' = y := by
      simp only [Subgroup.coe_subtype] at hry'
      rw [hry']; group
    have e3 : (t.out * r : K) = t'.out * r' := Subtype.ext (by simp [e1, e2])
    have e4 : ((t.out : K) : K ⧸ R) = ((t'.out : K) : K ⧸ R) := by
      rw [QuotientGroup.eq]
      have : (t.out)⁻¹ * t'.out = r * r'⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, e3]; group
      rw [this]
      exact R.mul_mem hr (R.inv_mem hr')
    simpa using e4
  have hAU : ⋃ t, A t = (K : Set B) := by
    ext y
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · rintro ⟨t, ht⟩
      have h1 := hR'K ht
      have h2 := K.mul_mem (t.out).2 h1
      simpa using h2
    · intro hy
      refine ⟨((⟨y, hy⟩ : K) : K ⧸ R), ?_⟩
      set t : K ⧸ R := ((⟨y, hy⟩ : K) : K ⧸ R) with ht
      have h1 : ((t.out : K) : K ⧸ R) = ((⟨y, hy⟩ : K) : K ⧸ R) := by rw [QuotientGroup.out_eq']
      rw [QuotientGroup.eq] at h1
      exact ⟨_, h1, by simp⟩
  have key : ∀ (g : B → ℂ) (c : K ⧸ R → ℂ), (∀ t, ∀ y ∈ A t, g y = c t) →
      ∫ y in (K : Set B), g y ∂β = (β.real R' : ℂ) * ∑ t, c t := by
    intro g c hg
    have hfin : β R' ≠ ⊤ := (lt_of_le_of_lt (measure_mono hR'K) hKc.measure_lt_top).ne
    have hint : ∀ t, IntegrableOn g (A t) β := by
      intro t
      refine (integrableOn_const (C := c t) (by rw [hAmeas t]; exact hfin)).congr_fun ?_ (hAm t)
      intro y hy
      exact (hg t y hy).symm
    rw [← hAU, integral_iUnion_fintype hAm hAd hint, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [setIntegral_congr_fun (hAm t) (fun y hy => hg t y hy), setIntegral_const, Measure.real, Measure.real,
      hAmeas t]
    simp
  have h1 := key (fun _ => 1) (fun _ => 1) (fun _ _ _ => rfl)
  have h2 := key f (fun t => u t.out) (by
    rintro t y ⟨r, hr, hry⟩
    have e1 : y = ((t.out : K) : B) * r := by
      simp only [Subgroup.coe_subtype] at hry
      rw [hry]; group
    rw [e1]
    exact hr t.out)
  have hcard : ((Fintype.card (K ⧸ R) : ℕ) : ℂ) ≠ 0 := by
    have : Fintype.card (K ⧸ R) ≠ 0 := Fintype.card_ne_zero
    exact_mod_cast this
  have hidx : R.index = Fintype.card (K ⧸ R) := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  rw [setIntegral_const] at h1
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Complex.real_smul] at h1
  rw [h2, h1, avg, ← hR, hidx, finsum_eq_sum_of_fintype]
  field_simp

end Top

section Norm

variable {B : Type} [Group B]

def cc (Γ' K : Subgroup B) (x : B) : ℕ := Nat.card (Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup B)

def oo (Γ' K : Subgroup B) (y : B) : B :=
  Quotient.out (DoubleCoset.mk Γ' K y : DoubleCoset.Quotient (Γ' : Set B) (K : Set B))

def rr (Γ' K : Subgroup B) (y : B) : ℝ≥0∞ :=
  if (oo Γ' K y)⁻¹ * y ∈ K then ((cc Γ' K (oo Γ' K y) : ℕ) : ℝ≥0∞)⁻¹ else 0

theorem oo_mul_right (Γ' K : Subgroup B) {k : B} (hk : k ∈ K) (y : B) : oo Γ' K (y * k) = oo Γ' K y := by
  have : DoubleCoset.mk Γ' K (y * k) = DoubleCoset.mk Γ' K y :=
    ((DoubleCoset.eq Γ' K y (y * k)).2 ⟨1, Γ'.one_mem, k, hk, by simp⟩).symm
  simp only [oo, this]

theorem oo_mul_left (Γ' K : Subgroup B) {h : B} (hh : h ∈ Γ') (y : B) : oo Γ' K (h * y) = oo Γ' K y := by
  have : DoubleCoset.mk Γ' K (h * y) = DoubleCoset.mk Γ' K y :=
    ((DoubleCoset.eq Γ' K y (h * y)).2 ⟨h, hh, 1, K.one_mem, by simp⟩).symm
  simp only [oo, this]

theorem rr_mul_right (Γ' K : Subgroup B) {k : B} (hk : k ∈ K) (y : B) : rr Γ' K (y * k) = rr Γ' K y := by
  have h1 : (oo Γ' K y)⁻¹ * (y * k) ∈ K ↔ (oo Γ' K y)⁻¹ * y ∈ K := by
    rw [← mul_assoc]
    exact K.mul_mem_cancel_right hk
  simp only [rr, oo_mul_right Γ' K hk, h1]

theorem tsum_rr (Γ' K : Subgroup B)
    (hfin : ∀ x : B, Finite (Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup B)) (y : B) :
    ∑' γ : Γ', rr Γ' K ((γ : B) * y) = 1 := by
  obtain ⟨h, k, hh, hk, ho⟩ := DoubleCoset.mk_out_eq_mul Γ' K y
  set o := oo Γ' K y with hodef
  have ho' : o = h * y * k := ho
  set D : Subgroup B := Γ' ⊓ K.map (MulAut.conj o).toMonoidHom with hD
  haveI : Finite D := hfin o
  haveI := Fintype.ofFinite D
  set c : ℝ≥0∞ := ((cc Γ' K o : ℕ) : ℝ≥0∞)⁻¹ with hc
  have hterm : ∀ γ : Γ', rr Γ' K (((γ * ⟨h, hh⟩ : Γ') : B) * y) =
      (D : Set B).indicator (fun _ => c) (γ : B) := by
    intro γ
    have e1 : (((γ * ⟨h, hh⟩ : Γ') : B) * y) = γ * (h * y) := by simp [mul_assoc]
    have e2 : oo Γ' K (((γ * ⟨h, hh⟩ : Γ') : B) * y) = o := by
      rw [e1, oo_mul_left Γ' K γ.2, oo_mul_left Γ' K hh]
    have e3 : h * y = o * k⁻¹ := by rw [ho']; group
    have e4 : o⁻¹ * (((γ * ⟨h, hh⟩ : Γ') : B) * y) ∈ K ↔ (γ : B) ∈ D := by
      rw [e1, e3]
      have e5 : o⁻¹ * ((γ : B) * (o * k⁻¹)) = (o⁻¹ * γ * o) * k⁻¹ := by group
      rw [e5, K.mul_mem_cancel_right (K.inv_mem hk), hD, Subgroup.mem_inf]
      constructor
      · intro hm
        exact ⟨γ.2, ⟨_, hm, by simp [MulAut.conj_apply]; group⟩⟩
      · rintro ⟨-, x, hx, hxe⟩
        have : (γ : B) = o * x * o⁻¹ := by
          rw [← hxe]; simp [MulAut.conj_apply]
        rw [this]
        have e6 : o⁻¹ * (o * x * o⁻¹) * o = x := by group
        rw [e6]
        exact hx
    simp only [rr, e2, e4]
    by_cases hm : (γ : B) ∈ D
    · rw [if_pos hm, Set.indicator_of_mem (show (γ : B) ∈ (D : Set B) from hm)]
    · rw [if_neg hm, Set.indicator_of_notMem (show (γ : B) ∉ (D : Set B) from hm)]
  have hle : (D : Set B) ⊆ Γ' := fun x hx => hx.1
  calc ∑' γ : Γ', rr Γ' K ((γ : B) * y)
      = ∑' γ : Γ', rr Γ' K (((γ * ⟨h, hh⟩ : Γ') : B) * y) :=
        ((Equiv.mulRight (⟨h, hh⟩ : Γ')).tsum_eq fun γ : Γ' => rr Γ' K ((γ : B) * y)).symm
    _ = ∑' γ : Γ', (D : Set B).indicator (fun _ => c) (γ : B) :=
        tsum_congr hterm
    _ = ∑' b : B, (D : Set B).indicator (fun _ => c) b := by
        have e7 := tsum_subtype (Γ' : Set B) (fun b => (D : Set B).indicator (fun _ => c) b)
        have e8 : (Γ' : Set B).indicator (fun b => (D : Set B).indicator (fun _ => c) b) =
            (D : Set B).indicator (fun _ => c) := by
          funext b
          by_cases hb : b ∈ (Γ' : Set B)
          · rw [Set.indicator_of_mem hb]
          · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (fun hd => hb (hle hd))]
        exact e7.trans (by rw [e8])
    _ = ∑' d : D, c := (tsum_subtype (D : Set B) (fun _ => c)).symm
    _ = 1 := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
        have e10 : cc Γ' K o = Fintype.card D := by
          rw [cc, Nat.card_eq_fintype_card]
        rw [e10]
        exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp)

end Norm

section Main

variable {B : Type} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]

theorem measurable_rr (Γ' K : Subgroup B) (hKo : IsOpen (K : Set B)) : Measurable (rr Γ' K) := fun s _ =>
  (isLocallyConstant_of_rightInv hKo (fun _ hk y => rr_mul_right Γ' K hk y) s).measurableSet

theorem integral_term (β : Measure B) [β.IsHaarMeasure] (K U : Subgroup B) (hKo : IsOpen (K : Set B))
    (hKc : IsCompact (K : Set B)) (hU : IsOpen (U : Set B)) (F : B → ℂ) (hF : ∀ u ∈ U, ∀ y, F (y * u) = F y)
    (q : B) (c : ℂ) :
    Integrable (fun y => if q⁻¹ * y ∈ K then F y * c else 0) β ∧
    ∫ y, (if q⁻¹ * y ∈ K then F y * c else 0) ∂β = (β.real K : ℂ) * avg (fun k : K => F (q * k)) * c := by
  have hf : ∀ u ∈ U, ∀ y, F (q * (y * u)) = F (q * y) := fun u hu y => by
    rw [← mul_assoc, hF u hu]
  have hcont : Continuous fun z => F (q * z) :=
    (isLocallyConstant_of_rightInv hU hf).continuous
  have hKm : MeasurableSet (K : Set B) := hKo.measurableSet
  have hI : IntegrableOn (fun z => F (q * z)) (K : Set B) β :=
    hcont.continuousOn.integrableOn_compact' hKc hKm
  let g : B → ℂ := fun z => (K : Set B).indicator (fun z => F (q * z)) z * c
  have hg : Integrable g β := ((integrable_indicator_iff hKm).2 hI).mul_const c
  have he : (fun y => if q⁻¹ * y ∈ K then F y * c else 0) = fun y => g (q⁻¹ * y) := by
    funext y
    by_cases hy : q⁻¹ * y ∈ K
    · simp only [g, if_pos hy, Set.indicator_of_mem (show q⁻¹ * y ∈ (K : Set B) from hy), mul_inv_cancel_left]
    · simp only [g, if_neg hy, Set.indicator_of_notMem (show q⁻¹ * y ∉ (K : Set B) from hy), zero_mul]
  rw [he]
  refine ⟨hg.comp_mul_left q⁻¹, ?_⟩
  rw [integral_mul_left_eq_self g q⁻¹]
  simp only [g]
  rw [integral_mul_const, integral_indicator hKm, setIntegral_subgroup β K U hKo hKc hU _ hf]

theorem integral_mul_rr (β : Measure B) [β.IsHaarMeasure] (Γ' K U : Subgroup B) (hKo : IsOpen (K : Set B))
    (hKc : IsCompact (K : Set B)) (hU : IsOpen (U : Set B)) (F : B → ℂ) (hF : ∀ u ∈ U, ∀ y, F (y * u) = F y)
    (hS : {q : DoubleCoset.Quotient (Γ' : Set B) (K : Set B) | ∃ k ∈ K, F (Quotient.out q * k) ≠ 0}.Finite) :
    ∫ y, F y * (((rr Γ' K y).toReal : ℝ) : ℂ) ∂β = (β.real K : ℂ) * dcSum Γ' K F := by
  set S := hS.toFinset with hSdef
  let c : DoubleCoset.Quotient (Γ' : Set B) (K : Set B) → ℂ := fun q => ((cc Γ' K (Quotient.out q) : ℕ) : ℂ)⁻¹
  have hpt : ∀ y, F y * (((rr Γ' K y).toReal : ℝ) : ℂ) =
      ∑ q ∈ S, if (Quotient.out q)⁻¹ * y ∈ K then F y * c q else 0 := by
    intro y
    set q₀ : DoubleCoset.Quotient (Γ' : Set B) (K : Set B) := DoubleCoset.mk Γ' K y with hq₀
    have hoo : oo Γ' K y = Quotient.out q₀ := rfl
    have hne : ∀ q, q ≠ q₀ → ¬ (Quotient.out q)⁻¹ * y ∈ K := by
      intro q hq hm
      apply hq
      have e1 : DoubleCoset.mk Γ' K (Quotient.out q) = q₀ :=
        (DoubleCoset.eq Γ' K _ y).2 ⟨1, Γ'.one_mem, (Quotient.out q)⁻¹ * y, hm, by group⟩
      rw [← e1]
      exact (DoubleCoset.out_eq' Γ' K q).symm
    have hrr : (((rr Γ' K y).toReal : ℝ) : ℂ) = if (Quotient.out q₀)⁻¹ * y ∈ K then c q₀ else 0 := by
      simp only [rr, hoo]
      by_cases hm : (Quotient.out q₀)⁻¹ * y ∈ K
      · simp [if_pos hm, c, ENNReal.toReal_inv]
      · simp [if_neg hm]
    rw [hrr]
    by_cases hq : q₀ ∈ S
    · rw [Finset.sum_eq_single q₀ (fun q _ hq' => if_neg (hne q hq')) (fun h => absurd hq h)]
      by_cases hm : (Quotient.out q₀)⁻¹ * y ∈ K
      · simp [if_pos hm]
      · simp [if_neg hm]
    · rw [Finset.sum_eq_zero]
      · by_cases hm : (Quotient.out q₀)⁻¹ * y ∈ K
        · have : F y = 0 := by
            by_contra h0
            apply hq
            rw [hSdef, Set.Finite.mem_toFinset]
            exact ⟨_, hm, by simpa using h0⟩
          simp [this]
        · simp [if_neg hm]
      · intro q hqS
        have hqq : q ≠ q₀ := fun h => hq (h ▸ hqS)
        exact if_neg (hne q hqq)
  have hterm := fun q => integral_term β K U hKo hKc hU F hF (Quotient.out q) (c q)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finset_sum S (fun q _ => (hterm q).1), dcSum,
    finsum_eq_sum_of_support_subset (s := S), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [(hterm q).2]
    simp only [c, cc]
    rw [div_eq_mul_inv, mul_assoc]
  · intro q hq
    by_contra hqS
    apply hq
    have h0 : (fun k : K => F (Quotient.out q * k)) = fun _ => 0 := by
      funext k
      by_contra h0
      apply hqS
      rw [Finset.mem_coe, hSdef, Set.Finite.mem_toFinset]
      exact ⟨k, k.2, h0⟩
    simp only [h0]
    simp [avg]

end Main

theorem core (hQ : QIndep) {G A B : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    [MeasurableSingletonClass G] [Group A] [MeasurableSpace A] [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (α : Measure A) [SFinite α] (β : Measure B) [β.IsHaarMeasure] [SFinite β] (e : G →* A × B) (he : Measurable e)
    (hmap : μ.map e = α.prod β) (Γ : Subgroup G) [Countable Γ] (Γ' K U : Subgroup B)
    (hΓ : Γ.map ((MonoidHom.snd A B).comp e) = Γ') (hinj : ∀ γ ∈ Γ, (e γ).2 = 1 → γ = 1)
    (hKo : IsOpen (K : Set B)) (hKc : IsCompact (K : Set B)) (hUo : IsOpen (U : Set B))
    (F₁ : A → ℂ) (F₂ : B → ℂ) (hF₁ : Measurable F₁) (hl₁ : ∀ γ ∈ Γ, ∀ x, F₁ ((e γ).1 * x) = F₁ x)
    (hl₂ : ∀ γ ∈ Γ', ∀ y, F₂ (γ * y) = F₂ y) (hr₂ : ∀ u ∈ U, ∀ y, F₂ (y * u) = F₂ y)
    (hS : {q : DoubleCoset.Quotient (Γ' : Set B) (K : Set B) | ∃ k ∈ K, F₂ (Quotient.out q * k) ≠ 0}.Finite)
    (hfin : ∀ x : B, Finite (Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup B)) :
    PositivityTheory.Rg.Tf.Loc.quotIntegral μ Γ Measure.count (fun x => F₁ (e x).1 * F₂ (e x).2) =
      (β.real K : ℂ) * (∫ x, F₁ x ∂α) * dcSum Γ' K F₂ := by
  have hF₂ : Measurable F₂ := fun s _ => (isLocallyConstant_of_rightInv hUo hr₂ s).measurableSet
  have hrm := measurable_rr Γ' K hKo
  have hmem : ∀ γ : Γ, (e (γ : G)).2 ∈ Γ' := fun γ => by
    rw [← hΓ]; exact ⟨γ, γ.2, rfl⟩
  let φ : Γ → Γ' := fun γ => ⟨(e (γ : G)).2, hmem γ⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      have h1 : (e ((a : G) * (b : G)⁻¹)).2 = 1 := by
        have h2 : (e (a : G)).2 = (e (b : G)).2 := congrArg Subtype.val hab
        simp [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, h2]
      have h3 := hinj _ (Γ.mul_mem a.2 (Γ.inv_mem b.2)) h1
      exact Subtype.ext (mul_inv_eq_one.1 h3)
    · rintro ⟨y, hy⟩
      rw [← hΓ] at hy
      obtain ⟨γ, hγ, rfl⟩ := hy
      exact ⟨⟨γ, hγ⟩, rfl⟩
  have hρ : PositivityTheory.Rg.Tf.Loc.IsQuotNormaliser Γ Measure.count (fun x => rr Γ' K (e x).2) := by
    refine ⟨hrm.comp (measurable_snd.comp he), fun g => ?_⟩
    rw [lintegral_count]
    have e1 : ∀ h : Γ, rr Γ' K (e ((h : G) * g)).2 = rr Γ' K (((φ h : Γ') : B) * (e g).2) := fun h => by
      simp [φ, map_mul, Prod.snd_mul]
    rw [tsum_congr e1]
    have e2 := (Equiv.ofBijective φ hφ).tsum_eq fun γ : Γ' => rr Γ' K ((γ : B) * (e g).2)
    simp only [Equiv.ofBijective_apply] at e2
    rw [e2]
    exact tsum_rr Γ' K hfin _
  have hFm : Measurable fun x => F₁ (e x).1 * F₂ (e x).2 :=
    (hF₁.comp (measurable_fst.comp he)).mul (hF₂.comp (measurable_snd.comp he))
  have hFi : ∀ h ∈ Γ, ∀ g, F₁ (e (h * g)).1 * F₂ (e (h * g)).2 = F₁ (e g).1 * F₂ (e g).2 := by
    intro h hh g
    have hm : (e h).2 ∈ Γ' := hmem ⟨h, hh⟩
    rw [map_mul, Prod.fst_mul, Prod.snd_mul, hl₁ h hh, hl₂ _ hm]
  rw [hQ G μ Γ _ _ hFm hFi hρ]
  let R : B → ℂ := fun y => F₂ y * (((rr Γ' K y).toReal : ℝ) : ℂ)
  have hRm : Measurable R := hF₂.mul (Complex.measurable_ofReal.comp hrm.ennreal_toReal)
  have hpm : Measurable fun p : A × B => F₁ p.1 * R p.2 :=
    (hF₁.comp measurable_fst).mul (hRm.comp measurable_snd)
  have e3 : ∫ g, F₁ (e g).1 * F₂ (e g).2 * (((rr Γ' K (e g).2).toReal : ℝ) : ℂ) ∂μ =
      ∫ p, F₁ p.1 * R p.2 ∂(μ.map e) := by
    rw [integral_map he.aemeasurable hpm.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => by simp only [R, mul_assoc])
  rw [e3, hmap, integral_prod_mul F₁ R, integral_mul_rr β Γ' K U hKo hKc hUo F₂ hr₂ hS]
  ring

theorem qSplitOf : QSplitOf :=
  fun hQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ _ α _ β _ _ e he hmap Γ _ Γ' K U hΓ hinj hKo hKc hUo F₁ F₂ hF₁ _ hl₁ hl₂ hr₂
    hS hfin => core hQ μ α β e he hmap Γ Γ' K U hΓ hinj hKo hKc hUo F₁ F₂ hF₁ hl₁ hl₂ hr₂ hS hfin

end GlobalTheory.CompanionTheory.QSplitPf
