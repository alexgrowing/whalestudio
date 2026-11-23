import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HaarOn

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped ENNReal

namespace Formalism.L2.S.Pv.FolnerAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def subOf (S : Set G) (h1 : (1 : G) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hi : ∀ a ∈ S, a⁻¹ ∈ S) :
    Subgroup G where
  carrier := S
  mul_mem' := fun ha hb => hm _ ha _ hb
  one_mem' := h1
  inv_mem' := fun ha => hi _ ha

def LeftHaarSub (S : Set G) (μS : Measure G) : Prop :=
  IsClosed S ∧ (1 : G) ∈ S ∧ (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) ∧ (∀ a ∈ S, a⁻¹ ∈ S) ∧
    SigmaFinite μS ∧ μS ≠ 0 ∧ μS Sᶜ = 0 ∧ (∀ s ∈ S, μS.map (fun x => s * x) = μS)

theorem leftOf {S : Set G} {μS : Measure G} (h : IsHaarSub S μS) : LeftHaarSub S μS := by
  obtain ⟨a, b, c, d, e, f, g, h', -⟩ := h
  exact ⟨a, b, c, d, e, f, g, h'⟩

theorem haarSub_prop {S : Set G} {μ ν : Measure G} (hμ : LeftHaarSub S μ) (hν : LeftHaarSub S ν) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν := by
  obtain ⟨hC, h1, hm, hi, -, -, -, -⟩ := id hμ
  let H : Subgroup G := subOf S h1 hm hi
  have hemb : MeasurableEmbedding (Subtype.val : H → G) := MeasurableEmbedding.subtype_coe hC.measurableSet
  have key : ∀ ρ : Measure G, LeftHaarSub S ρ →
      (ρ.comap (Subtype.val : H → G)).map Subtype.val = ρ ∧
      IsMulLeftInvariant (ρ.comap (Subtype.val : H → G)) ∧
      SigmaFinite (ρ.comap (Subtype.val : H → G)) ∧ ρ.comap (Subtype.val : H → G) ≠ 0 := by
    intro ρ hρ
    obtain ⟨-, -, -, -, hσ, h0, hc, hl⟩ := hρ
    have hmap : (ρ.comap (Subtype.val : H → G)).map Subtype.val = ρ := by
      rw [hemb.map_comap, Subtype.range_coe_subtype]
      exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hc)
    refine ⟨hmap, ⟨fun s => ?_⟩, ?_, ?_⟩
    · ext A hA
      rw [Measure.map_apply (measurable_const_mul s) hA, hemb.comap_apply, hemb.comap_apply]
      have e : Subtype.val '' ((fun x : H => s * x) ⁻¹' A) =
          (fun y : G => (s : G) * y) ⁻¹' (Subtype.val '' A) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨s * x, hx, rfl⟩
        · rintro ⟨a, ha, hay⟩
          refine ⟨s⁻¹ * a, ?_, ?_⟩
          · show s * (s⁻¹ * a) ∈ A
            rwa [mul_inv_cancel_left]
          · show (s : G)⁻¹ * a = y
            rw [hay, inv_mul_cancel_left]
      rw [e, ← Measure.map_apply (measurable_const_mul (s : G)) (hemb.measurableSet_image' hA),
        hl _ s.2]
    · exact SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmap]; exact hσ)
    · intro h
      apply h0
      rw [← hmap, h, Measure.map_zero]
  obtain ⟨hμm, hμi, hμσ, hμ0⟩ := key μ hμ
  obtain ⟨hνm, hνi, hνσ, hν0⟩ := key ν hν
  set μ' := μ.comap (Subtype.val : H → G) with hμ'
  set ν' := ν.comap (Subtype.val : H → G) with hν'
  obtain ⟨n, hn⟩ : ∃ n, ν' (spanningSets (μ' + ν') n) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hν0
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets (μ' + ν')]
    exact measure_iUnion_null hcon
  set A := spanningSets (μ' + ν') n with hA
  have hAm : MeasurableSet A := measurableSet_spanningSets _ n
  have hAfin : (μ' + ν') A < ⊤ := measure_spanningSets_lt_top _ n
  rw [Measure.add_apply] at hAfin
  have hμA : μ' A ≠ ⊤ := (lt_of_le_of_lt le_self_add hAfin).ne
  have hνA : ν' A ≠ ⊤ := (lt_of_le_of_lt le_add_self hAfin).ne
  haveI : BorelSpace H := Subtype.borelSpace (H : Set G)
  haveI : SecondCountableTopology H := by
    first
      | exact inferInstanceAs (SecondCountableTopology (H : Set G))
      | exact TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  haveI : MeasurableMul₂ H := ContinuousMul.measurableMul₂
  haveI : MeasurableInv H := ContinuousInv.measurableInv
  have heq : μ' = (μ' A / ν' A) • ν' := measure_eq_div_smul μ' ν' hn hνA
  refine ⟨μ' A / ν' A, ?_, ENNReal.div_ne_top hμA hn, ?_⟩
  · intro hc
    apply hμ0
    rw [heq, hc, zero_smul]
  · calc μ = μ'.map Subtype.val := hμm.symm
      _ = ((μ' A / ν' A) • ν').map Subtype.val := by rw [← heq]
      _ = (μ' A / ν' A) • ν'.map Subtype.val := Measure.map_smul _ _ _
      _ = (μ' A / ν' A) • ν := by rw [hνm]

def cjB (b : G) (y : G) : G := b⁻¹ * y * b

theorem cjB_mul (b x y : G) : cjB b (x * y) = cjB b x * cjB b y := by
  simp only [cjB, mul_assoc, mul_inv_cancel_left]

theorem continuous_cjB (b : G) : Continuous (cjB b) := by
  exact (continuous_const.mul continuous_id).mul continuous_const

theorem map_cjB {S : Set G} {μ : Measure G} (hμ : LeftHaarSub S μ) (b : G) (hb : ∀ s, s ∈ S ↔ cjB b s ∈ S) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ.map (cjB b) = c • μ := by
  have hcont : Continuous (cjB b) := continuous_cjB b
  have hinv1 : ∀ y, cjB b⁻¹ (cjB b y) = y := by
    intro y
    simp [cjB, mul_assoc]
  have hinv2 : ∀ y, cjB b (cjB b⁻¹ y) = y := by
    intro y
    simp [cjB, mul_assoc]
  let E : G ≃ₜ G :=
    { toFun := cjB b, invFun := cjB b⁻¹, left_inv := hinv1, right_inv := hinv2,
      continuous_toFun := hcont, continuous_invFun := continuous_cjB _ }
  let M : G ≃ᵐ G := E.toMeasurableEquiv
  have hmap : ∀ A : Set G, (μ.map (cjB b)) A = μ (cjB b ⁻¹' A) := fun A => by
    exact MeasurableEquiv.map_apply M A
  obtain ⟨hC, h1, hm, hi, hσ, h0, hc, hl⟩ := hμ
  have hL : LeftHaarSub S (μ.map (cjB b)) := by
    refine ⟨hC, h1, hm, hi, ?_, ?_, ?_, ?_⟩
    · haveI := hσ
      show SigmaFinite (μ.map M)
      first
        | exact M.sigmaFinite_map
        | exact MeasurableEquiv.sigmaFinite_map M
        | (refine SigmaFinite.of_map _ M.measurable.aemeasurable ?_
           rw [Measure.map_map M.symm.measurable M.measurable, M.symm_comp_self, Measure.map_id]
           exact hσ)
    · intro h
      exact h0 ((Measure.map_eq_zero_iff hcont.measurable.aemeasurable).1 h)
    · rw [hmap]
      convert hc using 2
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, hb x]
    · intro s hs
      rw [Measure.map_map (continuous_mul_left s).measurable hcont.measurable]
      have e1 : (fun x => s * x) ∘ cjB b = cjB b ∘ (fun y => (b * s * b⁻¹) * y) := by
        funext y
        simp [cjB, mul_assoc]
      have hs' : b * s * b⁻¹ ∈ S := by
        rw [hb]
        simpa [cjB, mul_assoc] using hs
      rw [e1, ← Measure.map_map hcont.measurable (continuous_mul_left _).measurable, hl _ hs']
  exact haarSub_prop hL ⟨hC, h1, hm, hi, hσ, h0, hc, hl⟩

theorem cjB_pow_iff {S : Set G} {a : G} (ha : ∀ s, s ∈ S ↔ cjB a s ∈ S) (m : ℕ) (s : G) :
    s ∈ S ↔ cjB (a ^ m) s ∈ S := by
  induction m with
  | zero => simp [cjB]
  | succ m ih =>
    rw [ih, ha (cjB (a ^ m) s)]
    have e : cjB a (cjB (a ^ m) s) = cjB (a ^ (m + 1)) s := by
      simp [cjB, pow_succ, mul_assoc]
    rw [e]

private theorem preimage_cjB_lemma {S : Set G} {μ : Measure G} (hμ : LeftHaarSub S μ) (b : G)
    (hb : ∀ s, s ∈ S ↔ cjB b s ∈ S) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ A : Set G, μ (cjB b ⁻¹' A) = c * μ A := by
  obtain ⟨c, hc0, hctop, hceq⟩ := map_cjB hμ b hb
  have hinv1 : ∀ y, cjB b⁻¹ (cjB b y) = y := by
    intro y
    simp [cjB, mul_assoc]
  have hinv2 : ∀ y, cjB b (cjB b⁻¹ y) = y := by
    intro y
    simp [cjB, mul_assoc]
  let E : G ≃ₜ G :=
    { toFun := cjB b, invFun := cjB b⁻¹, left_inv := hinv1, right_inv := hinv2,
      continuous_toFun := continuous_cjB b, continuous_invFun := continuous_cjB _ }
  let M : G ≃ᵐ G := E.toMeasurableEquiv
  refine ⟨c, hc0, hctop, fun A => ?_⟩
  have h1 : (μ.map (cjB b)) A = μ (cjB b ⁻¹' A) := by
    exact MeasurableEquiv.map_apply M A
  rw [← h1, hceq, Measure.smul_apply, smul_eq_mul]

theorem isFolner_of_contract {S : Set G} {μS : Measure G} (hS : IsHaarSub S μS) (C : Set G) (f : G → ℝ)
    (hf : Continuous f) (hfC : ∀ c ∈ C, ∀ x, f (c * x) = f x) (hfK : ∀ ρ : ℝ, IsCompact ({x | f x ≤ ρ} ∩ S))
    (a : G) (ha : ∀ s, s ∈ S ↔ cjB a s ∈ S)
    (hcontr : ∀ K : Set G, IsCompact K → K ⊆ S → ∀ U : Set G, IsOpen U → C ⊆ U →
      ∀ᶠ m : ℕ in atTop, ∀ k ∈ K, cjB (a ^ m) k ∈ U) :
    IsFolner S μS := by
  obtain ⟨hSC, hS1, hSm, hSi, hSσ, hS0, hSc, hSl, hSK, -, -⟩ := id hS
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ → Set G, L = fun ρ => {x | f x ≤ ρ} ∩ S := ⟨_, rfl⟩
  have hLmem : ∀ ρ x, x ∈ L ρ ↔ f x ≤ ρ ∧ x ∈ S := by
    intro ρ x
    rw [hLdef]
    rfl
  have hLc : ∀ ρ, IsCompact (L ρ) := by
    rw [hLdef]
    exact hfK
  have hLm : ∀ ρ, MeasurableSet (L ρ) := fun ρ => (hLc ρ).isClosed.measurableSet
  have hLfin : ∀ ρ, μS (L ρ) ≠ ⊤ := fun ρ => (hSK _ (hLc ρ)).ne
  have hLmono : Monotone L := by
    intro ρ₁ ρ₂ h x hx
    rw [hLmem] at hx ⊢
    exact ⟨hx.1.trans h, hx.2⟩
  intro K hK hKS ε hε
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, μS (L n) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hS0
    have hsub : (Set.univ : Set G) ⊆ (⋃ n : ℕ, L n) ∪ Sᶜ := by
      intro x _
      by_cases hx : x ∈ S
      · left
        obtain ⟨n, hn⟩ := exists_nat_ge (f x)
        exact Set.mem_iUnion.2 ⟨n, (hLmem _ _).2 ⟨hn, hx⟩⟩
      · right
        exact hx
    rw [← Measure.measure_univ_eq_zero]
    exact measure_mono_null hsub (measure_union_null (measure_iUnion_null hcon) hSc)
  have hcount : Set.Countable {t : ℝ | 0 < μS {x | f x = t}} :=
    Measure.countable_meas_level_set_pos hf.measurable
  obtain ⟨ρ, hρI, hρN⟩ : ∃ ρ ∈ Set.Icc (n₀ : ℝ) (n₀ + 1), ρ ∉ {t : ℝ | 0 < μS {x | f x = t}} := by
    by_contra hcon
    push_neg at hcon
    have h0 : volume (Set.Icc (n₀ : ℝ) (n₀ + 1)) = 0 :=
      measure_mono_null hcon (hcount.measure_zero volume)
    rw [Real.volume_Icc] at h0
    simp at h0
  have hlevel : μS {x | f x = ρ} = 0 := by
    simp only [Set.mem_setOf_eq, not_lt, nonpos_iff_eq_zero] at hρN
    exact hρN
  have hV0 : μS (L ρ) ≠ 0 := by
    intro h
    exact hn₀ (measure_mono_null (hLmono hρI.1) h)
  have hmonoSeq : Monotone fun n : ℕ => L (ρ - 1 / ((n : ℝ) + 1)) := by
    intro i j hij
    apply hLmono
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    have : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    linarith
  have hunion : (⋃ n : ℕ, L (ρ - 1 / ((n : ℝ) + 1))) = {x | f x < ρ} ∩ S := by
    ext x
    simp only [Set.mem_iUnion, hLmem, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn, hx⟩
      refine ⟨?_, hx⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · rintro ⟨hx, hxS⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨n, by linarith, hxS⟩
  have hVeq : μS ({x | f x < ρ} ∩ S) = μS (L ρ) := by
    apply le_antisymm
    · apply measure_mono
      intro x hx
      exact (hLmem _ _).2 ⟨le_of_lt hx.1, hx.2⟩
    · calc μS (L ρ) ≤ μS (({x | f x < ρ} ∩ S) ∪ {x | f x = ρ}) := by
            apply measure_mono
            intro x hx
            rw [hLmem] at hx
            rcases hx.1.lt_or_eq with h | h
            · exact Or.inl ⟨h, hx.2⟩
            · exact Or.inr h
        _ ≤ μS ({x | f x < ρ} ∩ S) + μS {x | f x = ρ} := measure_union_le _ _
        _ = μS ({x | f x < ρ} ∩ S) := by rw [hlevel, add_zero]
  have hlim : Tendsto (fun n : ℕ => μS (L (ρ - 1 / ((n : ℝ) + 1)))) atTop (𝓝 (μS (L ρ))) := by
    rw [← hVeq, ← hunion]
    first
      | exact tendsto_measure_iUnion_atTop hmonoSeq
      | exact tendsto_measure_iUnion hmonoSeq
  have hlt : μS (L ρ) < (1 + ε) * μS (L ρ) := by
    rw [add_mul, one_mul]
    exact ENNReal.lt_add_right (hLfin ρ) (mul_ne_zero hε.ne' hV0)
  obtain ⟨n, hn⟩ := ((ENNReal.Tendsto.const_mul hlim (Or.inl hV0)).eventually (lt_mem_nhds hlt)).exists
  have hn' : μS (L ρ) < (1 + ε) * μS (L (ρ - 1 / ((n : ℝ) + 1))) := hn
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  set ρ' := ρ - 1 / ((n : ℝ) + 1) with hρ'
  set U : Set G := {x | ∀ t ∈ L ρ', f (x * t) < f t + 1 / ((n : ℝ) + 1)} with hUdef
  have hUo : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x₀ hx₀
    have hx0' : ∀ t ∈ L ρ', f (x₀ * t) < f t + 1 / ((n : ℝ) + 1) := hx₀
    have hcont : Continuous fun z : G × G => f (z.1 * z.2) - f z.2 :=
      (hf.comp (continuous_fst.mul continuous_snd)).sub (hf.comp continuous_snd)
    have hev : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ L ρ', f (x * y) < f y + 1 / ((n : ℝ) + 1) :=
      (hLc ρ').eventually_forall_of_forall_eventually fun y hy => by
        have hxy : f (x₀ * y) - f y < 1 / ((n : ℝ) + 1) := by
          have := hx0' y hy
          linarith
        exact ((hcont.tendsto (x₀, y)).eventually (gt_mem_nhds hxy)).mono fun z hz => by
          have hz' : f (z.1 * z.2) - f z.2 < 1 / ((n : ℝ) + 1) := hz
          linarith
    exact hev
  have hCU : C ⊆ U := by
    intro c hc
    show ∀ t ∈ L ρ', f (c * t) < f t + 1 / ((n : ℝ) + 1)
    intro t _
    rw [hfC c hc t]
    linarith
  obtain ⟨m, hmU⟩ := (hcontr K hK hKS U hUo hCU).exists
  have hb := cjB_pow_iff ha m
  obtain ⟨c, hc0, hctop, hpre⟩ := preimage_cjB_lemma (leftOf hS) (a ^ m) hb
  refine ⟨cjB (a ^ m) ⁻¹' L ρ, (continuous_cjB _).measurable (hLm ρ), ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : cjB (a ^ m) x ∈ L ρ := hx
    exact (hb x).2 ((hLmem _ _).1 hx').2
  · rw [hpre]
    exact pos_iff_ne_zero.2 (mul_ne_zero hc0 hV0)
  · rw [hpre]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hctop) (lt_top_iff_ne_top.2 (hLfin ρ))
  · have hρρ : ρ' ≤ ρ := by linarith
    have hsub : cjB (a ^ m) ⁻¹' L ρ' ⊆
        {t | t ∈ cjB (a ^ m) ⁻¹' L ρ ∧ ∀ k ∈ K, k * t ∈ cjB (a ^ m) ⁻¹' L ρ} := by
      intro t ht
      have ht0 : cjB (a ^ m) t ∈ L ρ' := ht
      have ht' := (hLmem _ _).1 ht0
      refine ⟨hLmono hρρ ht0, fun k hk => ?_⟩
      show cjB (a ^ m) (k * t) ∈ L ρ
      rw [cjB_mul, hLmem]
      refine ⟨?_, hSm _ ((hb k).1 (hKS hk)) _ ht'.2⟩
      have hkU : ∀ t ∈ L ρ', f (cjB (a ^ m) k * t) < f t + 1 / ((n : ℝ) + 1) := hmU k hk
      have := hkU _ ht0
      linarith [ht'.1]
    calc μS (cjB (a ^ m) ⁻¹' L ρ) = c * μS (L ρ) := hpre _
      _ ≤ c * ((1 + ε) * μS (L ρ')) := mul_le_mul_of_nonneg_left hn'.le zero_le
      _ = (1 + ε) * (c * μS (L ρ')) := by ring
      _ = (1 + ε) * μS (cjB (a ^ m) ⁻¹' L ρ') := by rw [hpre]
      _ ≤ (1 + ε) * μS {t | t ∈ cjB (a ^ m) ⁻¹' L ρ ∧ ∀ k ∈ K, k * t ∈ cjB (a ^ m) ⁻¹' L ρ} :=
        mul_le_mul_of_nonneg_left (measure_mono hsub) zero_le

end Formalism.L2.S.Pv.FolnerAbs
