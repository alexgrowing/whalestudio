import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bridge
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ConjDesc
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NormInj
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.SgIterateEqSelf
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ContractI
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.StrictNormal
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.UnitNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

private theorem exists_rep {G : Type} [Group G] (H U : Subgroup G) (y : G) :
    ∃ r : G → G, (∀ g, ∃ h ∈ H, ∃ u ∈ U, g = h * r g * u) ∧ (∀ g, ∀ h ∈ H, ∀ u ∈ U, r (h * g * u) = r g) ∧ r y = y := by
  classical
  let s := DoubleCoset.setoid (H : Set G) (U : Set G)
  have hs : ∀ a b, s.r a b ↔ ∃ h ∈ H, ∃ u ∈ U, b = h * a * u := fun a b => DoubleCoset.rel_iff
  refine ⟨fun g => if Quotient.mk s g = Quotient.mk s y then y else (Quotient.mk s g).out, fun g => ?_, fun g h hh u hu => ?_,
    if_pos rfl⟩
  · apply (hs _ _).1
    apply Quotient.exact (s := s)
    dsimp only
    split_ifs with h
    · exact h.symm
    · exact Quotient.out_eq _
  · have : Quotient.mk s (h * g * u) = Quotient.mk s g := (Quotient.sound ((hs _ _).2 ⟨h, hh, u, hu, rfl⟩)).symm
    simp only [this]

private theorem quot_dcoset {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (H U : Subgroup G)
    (hH : IsClosed (H : Set G)) (hc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hUo : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G))
    (ν : Measure H) [ν.IsHaarMeasure] (y : G) (c : ℂ) (F : G → ℂ) (S : Set G)
    (hS : ∀ g, g ∈ S ↔ ∃ h ∈ H, ∃ u ∈ U, g = h * y * u) (hF : ∀ g, F g = S.indicator (fun _ => c) g) :
    quotIntegral μ H ν F = c * (((μ U).toReal / (ν {h | y⁻¹ * h * y ∈ U}).toReal : ℝ) : ℂ) := by
  classical
  have hcomm : ∀ a b : H, a * b = b * a := fun a b => Subtype.ext (hc _ a.2 _ b.2)
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  haveI : ν.IsInvInvariant := by
    letI : CommGroup H := { (inferInstance : Group H) with mul_comm := hcomm }
    exact Measure.IsHaarMeasure.isInvInvariant_of_regular ν
  let V : G → Set H := fun r => {h | r⁻¹ * h * r ∈ U}
  have hVo : ∀ r, IsOpen (V r) := fun r => hUo.preimage (by fun_prop : Continuous fun h : H => r⁻¹ * h * r)
  have hV0 : ∀ r, ν (V r) ≠ 0 := fun r => (hVo r).measure_ne_zero ν ⟨1, by simp [V]⟩
  have hVt : ∀ r, ν (V r) ≠ ⊤ := fun r => by
    refine IsCompact.measure_ne_top ?_
    have h1 : Topology.IsClosedEmbedding fun h : H => r⁻¹ * h * r :=
      ((Homeomorph.mulLeft r⁻¹).trans (Homeomorph.mulRight r)).isClosedEmbedding.comp hH.isClosedEmbedding_subtypeVal
    exact h1.isCompact_preimage hUc
  obtain ⟨r, hr1, hr2, hr3⟩ := exists_rep H U y
  have hrr : ∀ g, ∀ u ∈ U, r (g * u) = r g := fun g u hu => by simpa using hr2 g 1 H.one_mem u hu
  have hrl : ∀ g, ∀ h ∈ H, r (h * g) = r g := fun g h hh => by simpa using hr2 g h hh 1 U.one_mem
  have hop : ∀ T : Set G, (∀ g ∈ T, ∀ u ∈ U, g * u ∈ T) → IsOpen T := fun T hT => by
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨{x | g⁻¹ * x ∈ U}, fun x hx => by simpa using hT g hg _ hx,
      hUo.preimage (by fun_prop : Continuous fun x : G => g⁻¹ * x), by simp⟩
  let ρ : G → ENNReal := fun g => if (r g)⁻¹ * g ∈ U then (ν (V (r g)))⁻¹ else 0
  have hρ : IsQuotNormaliser H ν ρ := by
    constructor
    · refine fun s _ => (hop _ fun g hg u hu => ?_).measurableSet
      have : ρ (g * u) = ρ g := by
        simp only [ρ, hrr g u hu, ← mul_assoc, U.mul_mem_cancel_right hu]
      simpa only [Set.mem_preimage, this] using hg
    · intro g
      obtain ⟨h0, hh0, u0, hu0, e⟩ := hr1 g
      have : ∀ h : H, ρ (h * g) = ((fun x => (⟨h0, hh0⟩ : H) * x) ⁻¹' V (r g)).indicator (fun _ => (ν (V (r g)))⁻¹) h := by
        intro h
        have e2 : (r g)⁻¹ * (h * g) = (r g)⁻¹ * (h0 * h) * r g * u0 := by
          rw [hc h0 hh0 h h.2]
          nth_rewrite 2 [e]
          group
        simp only [ρ, hrl g h h.2, e2, U.mul_mem_cancel_right hu0, Set.indicator_apply, Set.mem_preimage, V, Set.mem_setOf_eq,
          Subgroup.coe_mul]
      rw [lintegral_congr this, lintegral_indicator_const ((hVo _).preimage (by fun_prop)).measurableSet,
        measure_preimage_mul, ENNReal.inv_mul_cancel (hV0 _) (hVt _)]
  have hSo : IsOpen S := hop S fun g hg u hu => by
    obtain ⟨h, hh, v, hv, rfl⟩ := (hS g).1 hg
    exact (hS _).2 ⟨h, hh, v * u, U.mul_mem hv hu, by group⟩
  have hSl : ∀ h ∈ H, ∀ g, h * g ∈ S ↔ g ∈ S := by
    have : ∀ h ∈ H, ∀ g ∈ S, h * g ∈ S := fun h hh g hg => by
      obtain ⟨h', hh', v, hv, rfl⟩ := (hS g).1 hg
      exact (hS _).2 ⟨h * h', H.mul_mem hh hh', v, hv, by group⟩
    exact fun h hh g => ⟨fun hg => by simpa using this _ (H.inv_mem hh) _ hg, this h hh g⟩
  have hex : ∃ ρ, IsQuotNormaliser H ν ρ := ⟨ρ, hρ⟩
  have hm : Measurable (S.indicator fun _ => (1 : ENNReal)) := measurable_const.indicator hSo.measurableSet
  have key : ∫⁻ g, S.indicator (fun _ => 1) g * hex.choose g ∂μ = (ν (V y))⁻¹ * μ U := by
    rw [lintegral_normaliser_eq hm (fun h hh g => by simp only [Set.indicator_apply, hSl h hh g]) hex.choose_spec hρ]
    have : ∀ g, S.indicator (fun _ => 1) g * ρ g = ((fun x => y⁻¹ * x) ⁻¹' U).indicator (fun _ => (ν (V y))⁻¹) g := by
      intro g
      by_cases hg : g ∈ S
      · obtain ⟨h, hh, u, hu, e⟩ := (hS g).1 hg
        have : r g = y := by rw [e, hr2 y h hh u hu, hr3]
        simp [ρ, hg, this, Set.indicator_apply]
      · have : g ∉ (fun x => y⁻¹ * x) ⁻¹' U := fun h => hg ((hS g).2 ⟨1, H.one_mem, _, h, by group⟩)
        simp [hg, this]
    rw [lintegral_congr this, lintegral_indicator_const (hUo.preimage (by fun_prop)).measurableSet, measure_preimage_mul]
  have hfin : ∫⁻ g, S.indicator (fun _ => 1) g * hex.choose g ∂μ ≠ ⊤ := by
    rw [key]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (hV0 y)) hUc.measure_ne_top
  have hm2 : Measurable fun g => S.indicator (fun _ => (1 : ENNReal)) g * hex.choose g := hm.mul hex.choose_spec.1
  rw [quotIntegral, dif_pos hex]
  have : ∀ g, F g * ((hex.choose g).toReal : ℂ) = c * ((S.indicator (fun _ => 1) g * hex.choose g).toReal : ℂ) := by
    intro g
    by_cases hg : g ∈ S <;> simp [hF, hg]
  rw [integral_congr_ae (Filter.Eventually.of_forall this), integral_const_mul, integral_complex_ofReal,
    integral_toReal hm2.aemeasurable (ae_lt_top hm2 hfin), key, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul]

section One

open GlobalTheory.SmGL hiding iwahori

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem mem_iw {g : GL (Fin n) E} : g ∈ GlobalTheory.SmGL.iwahori E (Fin n) ↔
    ((∀ i j, valuation E (g.val i j) ≤ 1) ∧ ∀ i j, valuation E (g⁻¹.val i j) ≤ 1) ∧
      ∀ i j, j < i → valuation E (g.val i j) < 1 := by
  rw [mem_iwahori, GlobalTheory.SplitFlip.mem_KO_iff]
  rfl

private theorem sg_mem {σ : E ≃+* E} (hσ : Isom σ) {g : GL (Fin n) E} (hg : g ∈ GlobalTheory.SmGL.iwahori E (Fin n)) :
    sg σ g ∈ GlobalTheory.SmGL.iwahori E (Fin n) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_iw.1 hg
  rw [mem_iw, ← map_inv]
  exact ⟨⟨fun i j => (hσ _).le.trans (h1 i j), fun i j => (hσ _).le.trans (h2 i j)⟩,
    fun i j h => (hσ _).le.trans_lt (h3 i j h)⟩

private theorem sg_cont {σ : E ≃+* E} (hσ : Isom σ) : Continuous (sg σ : GL (Fin n) E → GL (Fin n) E) := by
  have hc : Continuous σ := by
    refine continuous_of_continuousAt_zero σ.toAddMonoidHom ?_
    rw [ContinuousAt, map_zero]
    refine ((IsValuativeTopology.hasBasis_nhds_zero E).tendsto_iff (IsValuativeTopology.hasBasis_nhds_zero E)).2 ?_
    intro γ _
    exact ⟨γ, trivial, fun x hx => (hσ x).trans_lt hx⟩
  exact Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map hc, Units.continuous_coe_inv.matrix_map hc⟩

private theorem strict_mul {t s : Fin n → Eˣ} (ht : Strict t) (hs : s ∈ torusO E (Fin n)) : Strict (t * s) := fun i j h => by
  simpa [hs i, hs j] using ht i j h

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem map_diag {F : Type} [Field F] (f : E →+* F) (u : Fin n → Eˣ) :
    Matrix.GeneralLinearGroup.map f (diagT E (Fin n) u) = diagT F (Fin n) fun i => Units.map (f : E →* F) (u i) := by
  apply Units.ext
  show (diagT E (Fin n) u).val.map f = _
  rw [val_diagT, val_diagT, Matrix.diagonal_map (map_zero f)]
  rfl

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem diag_comm (u v : Fin n → Eˣ) :
    diagT E (Fin n) u * diagT E (Fin n) v = diagT E (Fin n) v * diagT E (Fin n) u := by
  rw [← map_mul, ← map_mul, mul_comm]

private theorem cent_diag {σ : E ≃+* E} {q : ℕ} (hσ : Cyc σ q) {d : Fin n → Eˣ} (hd : Strict d) {δ y c : GL (Fin n) E}
    (hy : y⁻¹ * δ * sg σ y = diagT E (Fin n) d) (hc : c⁻¹ * δ * sg σ c = δ) : ∃ u, y⁻¹ * c * y = diagT E (Fin n) u := by
  refine strictNormal E n σ q hσ d d hd hd _ ?_
  rw [← hy, map_mul, map_mul, map_inv]
  calc _ = y⁻¹ * (c⁻¹ * δ * sg σ c) * sg σ y := by group
    _ = _ := by rw [hc]

private theorem contract {σ : E ≃+* E} (hσ : Isom σ) {t : Fin n → Eˣ} (ht : Strict t) {δ g : GL (Fin n) E}
    (hg : g⁻¹ * δ * sg σ g ∈ iwahoriCoset t) : ∃ κ ∈ GlobalTheory.SmGL.iwahori E (Fin n), ∃ s ∈ torusO E (Fin n),
      (g * κ⁻¹)⁻¹ * δ * sg σ (g * κ⁻¹) = diagT E (Fin n) (t * s) := by
  obtain ⟨κ, hκ, s, hs, e⟩ := contractI E n σ hσ t ht _ hg
  refine ⟨κ, hκ, s, hs, ?_⟩
  rw [map_mul, map_inv]
  calc _ = κ * (g⁻¹ * δ * sg σ g) * (sg σ κ)⁻¹ := by group
    _ = _ := by rw [e]; group

private theorem one_field [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] (μ : Measure (GL (Fin n) E))
    [μ.IsHaarMeasure] {σ : E ≃+* E} {q : ℕ} (hσ : Cyc σ q)
    (hfix : ∀ u : Eˣ, ∃ p : Eˣ, σ p = p ∧ valuation E (p : E) = valuation E (u : E))
    {t s : Fin n → Eˣ} (ht : Strict t) (hs : s ∈ torusO E (Fin n)) {δ y : GL (Fin n) E}
    (hy : y⁻¹ * δ * sg σ y = diagT E (Fin n) (t * s)) (H : Subgroup (GL (Fin n) E))
    (hH : ∀ c, c ∈ H ↔ c⁻¹ * δ * sg σ c = δ) (ν : Measure H) [ν.IsHaarMeasure] (c : ℂ) (F : GL (Fin n) E → ℂ)
    (hF : ∀ g, F g = (iwahoriCoset t).indicator (fun _ => c) (g⁻¹ * δ * sg σ g)) :
    quotIntegral μ H ν F = c * (((μ (GlobalTheory.SmGL.iwahori E (Fin n))).toReal /
      (ν {h | y⁻¹ * h * y ∈ GlobalTheory.SmGL.iwahori E (Fin n)}).toReal : ℝ) : ℂ) := by
  have hcs := sg_cont (n := n) hσ.isom
  refine quot_dcoset μ H _ ?_ ?_ (IwahoriOnto.isOpen_iwahori E _) (IwahoriOnto.isCompact_iwahori E _) ν y c F
    {g | g⁻¹ * δ * sg σ g ∈ iwahoriCoset t} (fun g => ⟨fun hg => ?_, ?_⟩) (fun g => (hF g).trans rfl)
  · rw [show (H : Set (GL (Fin n) E)) = {c | c⁻¹ * δ * sg σ c = δ} from Set.ext hH]
    exact isClosed_eq (by fun_prop) continuous_const
  · intro a ha b hb
    obtain ⟨u, hu⟩ := cent_diag hσ (strict_mul ht hs) hy ((hH a).1 ha)
    obtain ⟨v, hv⟩ := cent_diag hσ (strict_mul ht hs) hy ((hH b).1 hb)
    have := diag_comm u v
    rw [← hu, ← hv] at this
    calc a * b = y * ((y⁻¹ * a * y) * (y⁻¹ * b * y)) * y⁻¹ := by group
      _ = _ := by rw [this]; group
  · obtain ⟨κ, hκ, s', hs', e⟩ := contract hσ.isom ht hg
    obtain ⟨u, hu⟩ := strictNormal E n σ q hσ _ _ (strict_mul ht hs) (strict_mul ht hs') (y⁻¹ * (g * κ⁻¹)) (by
      rw [← hy, ← e, map_mul _ y⁻¹, map_inv]; group)
    choose p hp hp' using fun i => hfix (u i)
    have hsp : sg σ (diagT E (Fin n) p) = diagT E (Fin n) p := by
      rw [sg, map_diag]
      congr 1
      funext i
      exact Units.ext (hp i)
    refine ⟨y * diagT E (Fin n) p * y⁻¹, (hH _).2 ?_, diagT E (Fin n) (p⁻¹ * u) * κ,
      mul_mem (diagT_mem_iwahori fun i => ?_) hκ, ?_⟩
    · rw [map_mul, map_mul, map_inv, hsp]
      calc _ = y * ((diagT E (Fin n) p)⁻¹ * ((y⁻¹ * δ * sg σ y) * diagT E (Fin n) p)) * (sg σ y)⁻¹ := by group
        _ = _ := by rw [hy, diag_comm, ← hy]; group
    · simp [hp' i]
    · rw [map_mul, map_inv, ← hu]; group
  · rintro ⟨h, hh, u, hu, rfl⟩
    refine ⟨u⁻¹, inv_mem hu, diagT E (Fin n) s * sg σ u, mul_mem (diagT_mem_iwahori hs) (sg_mem hσ.isom hu), ?_⟩
    rw [map_mul, map_mul]
    calc _ = u⁻¹ * (y⁻¹ * (h⁻¹ * δ * sg σ h) * sg σ y) * sg σ u := by group
      _ = _ := by rw [(hH h).1 hh, hy, map_mul]; group

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem nrm_diag (σ : E ≃+* E) (q : ℕ) (u : Fin n → Eˣ) :
    (nrm σ q (diagT E (Fin n) u)).val = Matrix.diagonal fun i => ∏ j ∈ Finset.range q, σ^[j] (u i) := by
  induction q with
  | zero => simp [nrm]
  | succ q ih =>
    have : ((sg σ)^[q] (diagT E (Fin n) u)).val = Matrix.diagonal fun i => σ^[q] (u i) := by
      ext i j
      rw [sg_iterate_apply, val_diagT, Matrix.diagonal_apply, Matrix.diagonal_apply]
      split_ifs
      · rfl
      · exact Function.iterate_fixed (map_zero σ) q
    rw [nrm_succ, Units.val_mul, ih, this, Matrix.diagonal_mul_diagonal]
    simp only [Finset.prod_range_succ]

private theorem iw_eq : iwahori (m := n) E = (GlobalTheory.SmGL.iwahori E (Fin n) : Set (GL (Fin n) E)) := by
  ext g
  rw [SetLike.mem_coe, mem_iwahori]
  rfl

private theorem fn_eq (t : Fin n → Eˣ) : iwahoriFn E (diagT E (Fin n) t) = (iwahoriCoset t).indicator fun _ => 1 := by
  rw [iwahoriFn, iw_eq]
  rfl

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem pow_eq (ϖ : Eˣ) (a : Fin n → ℤ) : diagPow ϖ a = diagT E (Fin n) fun i => ϖ ^ a i :=
  Units.ext (val_diagT ..).symm

private theorem strict_pow {ϖ : Eˣ} (h : valuation E (ϖ : E) < 1) {a : Fin n → ℤ} (ha : StrictAnti a) :
    Strict fun i => ϖ ^ a i := fun i j hij => by
  have h0 : 0 < valuation E (ϖ : E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact (zpow_lt_zpow_iff_right_of_lt_one₀ h0 h).2 (ha hij)

private theorem val_dec {π : E} (h : valuation E π < 1) (hm : ∀ x, valuation E x < 1 → valuation E x ≤ valuation E π) :
    π ≠ 0 ∧ ∀ y : E, y ≠ 0 → ∃ a : ℤ, valuation E y = valuation E (π ^ a) := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  have h1 : valuation E (p : E) < 1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hp.not_isUnit
  have h0 : 0 < valuation E (p : E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 fun e => hp.ne_zero (Subtype.ext e))
  have dec : ∀ y : E, y ≠ 0 → ∃ a : ℤ, valuation E y = valuation E (p : E) ^ a := fun y hy => by
    obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := E) hp hy
    have h1 : valuation E (algebraMap 𝒪[E] E (u : 𝒪[E])) = 1 := (Valuation.integer.integers (valuation E)).valuation_unit u
    exact ⟨a, by rw [hu, Units.smul_def, Algebra.smul_def, map_mul, h1, one_mul, map_zpow₀]; rfl⟩
  have hπ : π ≠ 0 := (Valuation.ne_zero_iff (valuation E)).1 (h0.trans_le (hm _ h1)).ne'
  obtain ⟨a, ha⟩ := dec π hπ
  have e : valuation E π = valuation E (p : E) := by
    refine le_antisymm ?_ (hm _ h1)
    have : 0 < a := by
      rw [ha, ← zpow_zero (valuation E (p : E))] at h
      exact (zpow_lt_zpow_iff_right_of_lt_one₀ h0 h1).1 h
    rw [ha]
    simpa using (zpow_le_zpow_iff_right_of_lt_one₀ h0 h1 (m := a) (n := 1)).2 this
  exact ⟨hπ, fun y hy => by simpa only [map_zpow₀, e] using dec y hy⟩

end One

section Two

open GlobalTheory.SmGL hiding iwahori

variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] {n : ℕ}

private theorem incl_mem (g : GL (Fin n) k) :
    (incl g : GL (Fin n) E) ∈ GlobalTheory.SmGL.iwahori E (Fin n) ↔ g ∈ GlobalTheory.SmGL.iwahori k (Fin n) := by
  have hm := ValuativeExtension.mapValueGroupWithZero_strictMono (A := k) (B := E)
  have h1 : ∀ x : k, valuation E (algebraMap k E x) ≤ 1 ↔ valuation k x ≤ 1 := fun x => by
    rw [← hm.le_iff_le, map_one, ValuativeExtension.mapValueGroupWithZero_valuation]
  have h2 : ∀ x : k, valuation E (algebraMap k E x) < 1 ↔ valuation k x < 1 := fun x => by
    rw [← hm.lt_iff_lt, map_one, ValuativeExtension.mapValueGroupWithZero_valuation]
  rw [mem_iw, mem_iw, ← map_inv]
  simp only [← h1, ← h2]
  rfl

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem val_one (x : k) : valuation E (algebraMap k E x) = 1 ↔ valuation k x = 1 := by
  rw [← (ValuativeExtension.mapValueGroupWithZero_strictMono (A := k) (B := E)).injective.eq_iff, map_one,
    ValuativeExtension.mapValueGroupWithZero_valuation]

private theorem strict_map {t : Fin n → kˣ} (ht : Strict t) :
    Strict fun i => Units.map (algebraMap k E : k →* E) (t i) := fun i j h => by
  simpa using ValuativeExtension.mapValueGroupWithZero_strictMono (A := k) (B := E) (ht i j h)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [ValuativeExtension k E] in
private theorem nrm_incl (σ : E ≃ₐ[k] E) (q : ℕ) (ϖ : kˣ) (a : Fin n → ℤ) (s : Fin n → Eˣ) (s₀ : Fin n → kˣ)
    (h : ∀ i, ∏ j ∈ Finset.range q, (σ : E ≃+* E)^[j] (s i) = algebraMap k E (s₀ i)) :
    nrm (σ : E ≃+* E) q (diagT E (Fin n) ((fun i => Units.map (algebraMap k E : k →* E) (ϖ ^ a i)) * s)) =
      incl (diagT k (Fin n) ((fun i => ϖ ^ ((q : ℤ) * a i)) * s₀)) := by
  apply Units.ext
  rw [nrm_diag, incl, map_diag, val_diagT]
  congr 1
  funext i
  have h1 : ∀ j (x : k), (σ : E ≃+* E)^[j] (algebraMap k E x) = algebraMap k E x := fun j x =>
    Function.iterate_fixed (σ.commutes x) j
  simp only [Pi.mul_apply, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, iterate_map_mul, h1, Finset.prod_mul_distrib, h,
    Finset.prod_const, Finset.card_range, map_mul]
  rw [mul_comm (q : ℤ), zpow_mul, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]

private theorem down [FiniteDimensional k E] [IsGalois k E] {σ : E ≃ₐ[k] E} (hg : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) {q : ℕ}
    (hσ : Cyc (σ : E ≃+* E) q) {s : Fin n → Eˣ} (hs : s ∈ torusO E (Fin n)) :
    ∃ s₀ ∈ torusO k (Fin n), ∀ i, ∏ j ∈ Finset.range q, (σ : E ≃+* E)^[j] (s i) = algebraMap k E (s₀ i) := by
  have key : ∀ x : E, valuation E x = 1 → ∃ y : kˣ, valuation k (y : k) = 1 ∧
      ∏ j ∈ Finset.range q, (σ : E ≃+* E)^[j] x = algebraMap k E y := by
    intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have h1 : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) (∏ j ∈ Finset.range q, (σ : E ≃+* E)^[j] x) := by
      have e := (Finset.prod_range_succ' (fun j => (σ : E ≃+* E)^[j] x) q).symm.trans (Finset.prod_range_succ _ q)
      rw [hσ.ord] at e
      refine Eq.trans ?_ (mul_right_cancel₀ hx0 e)
      rw [AlgEquiv.smul_def, map_prod]
      exact Finset.prod_congr rfl fun j _ => (Function.iterate_succ_apply' (σ : E ≃+* E) j x).symm
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 ((IsGalois.mem_bot_iff_fixed _).2 fun τ => Subgroup.zpowers_le.2 h1 (hg τ))
    have h2 : ∀ j, valuation E ((σ : E ≃+* E)^[j] x) = 1 := fun j => by
      induction j with
      | zero => exact hx
      | succ j ih => rw [Function.iterate_succ_apply', hσ.isom, ih]
    have h3 : valuation k y = 1 := (val_one (E := E) y).1 (by rw [hy, map_prod]; exact Finset.prod_eq_one fun j _ => h2 j)
    exact ⟨Units.mk0 y (by rintro rfl; simp at h3), h3, hy.symm⟩
  choose s₀ h1 h2 using fun i => key _ (hs i)
  exact ⟨s₀, h1, h2⟩

private theorem up {σ : E ≃ₐ[k] E} {q : ℕ} (hσ : Unram (σ : E ≃+* E) q) {s₀ : Fin n → kˣ} (hs : s₀ ∈ torusO k (Fin n)) :
    ∃ s ∈ torusO E (Fin n), ∀ i, ∏ j ∈ Finset.range q, (σ : E ≃+* E)^[j] (s i) = algebraMap k E (s₀ i) := by
  choose s h1 h2 using fun i => unitNorm E _ q hσ _ ((val_one _).2 (hs i)) (σ.commutes _)
  exact ⟨fun i => Units.mk0 (s i) (fun e => by simpa [e] using h1 i), h1, h2⟩

end Two

open GlobalTheory.SmGL hiding iwahori in
theorem UpperTheory.ConvolutionTheory.Loc.elemMatch :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
        [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], IsUnramifiedLoc k E → ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
        (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)), μE.IsHaarMeasure → μk.IsHaarMeasure → ∀ ϖ : kˣ, IsUniformiser (ϖ : k) → ∀ a : Fin n → ℤ, StrictlyDominant a →
        Match σ μE μk (iwahoriFn E (incl (diagPow ϖ a)))
          ((((μE (iwahori (m := n) E)).toReal / (μk (iwahori (m := n) k)).toReal : ℝ) : ℂ) •
            iwahoriFn k (diagPow ϖ fun i => (Module.finrank k E : ℤ) * a i)) := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ hu σ hg n _ _ _ _ μE μk hE hk ϖ hϖ a ha
  obtain ⟨hc, hun, hb⟩ := bridge k E σ
  obtain ⟨hsg, hnr, -, hcl, -⟩ := hb n
  replace hun := hun hu hg
  set q := Module.finrank k E with hq
  have htE := strict_map (E := E) (strict_pow hϖ.1 ha)
  have htq : Strict fun i => ϖ ^ ((q : ℤ) * a i) :=
    strict_pow hϖ.1 fun i j h => mul_lt_mul_of_pos_left (ha h) (by exact_mod_cast hc.pos)
  have hN := nrm_incl σ q ϖ a
  rw [pow_eq, pow_eq, incl, map_diag, fn_eq, fn_eq]
  set tE : Fin n → Eˣ := fun i => Units.map (algebraMap k E : k →* E) (ϖ ^ a i)
  set tq : Fin n → kˣ := fun i => ϖ ^ ((q : ℤ) * a i)
  have hr : Cyc (RingEquiv.refl k) 1 := ⟨fun _ => rfl, one_pos, fun _ => rfl⟩
  have hrE : Cyc (RingEquiv.refl E) 1 := ⟨fun _ => rfl, one_pos, fun _ => rfl⟩
  have kside : ∀ γ z : GL (Fin n) k, z⁻¹ * γ * z ∈ iwahoriCoset tq → ∃ δ ∈ iwahoriCoset tE, IsNormOf σ δ γ := by
    intro γ z hz
    obtain ⟨κ, -, s₀, hs₀, e⟩ := contract (σ := RingEquiv.refl k) hr.isom htq (δ := γ) (g := z) hz
    obtain ⟨s, hs, e'⟩ := up hun hs₀
    refine ⟨diagT E (Fin n) (tE * s), ⟨1, one_mem _, _, diagT_mem_iwahori hs, by rw [map_mul, one_mul]⟩,
      (incl (z * κ⁻¹))⁻¹, ?_⟩
    rw [← hnr, hN s s₀ e', ← e, map_mul, map_mul, map_inv, inv_inv]
    rfl
  have zero : ∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})) (c : ℂ), (∀ z, z⁻¹ * γ * z ∉ iwahoriCoset tq) →
      orbIntegralC μk γ μγ (c • (iwahoriCoset tq).indicator fun _ => (1 : ℂ)) = 0 := fun γ μγ c h => by
    simp [orbIntegralC, quotIntegral, h]
  refine ⟨fun δ γ h μδ μγ hδ hh _ _ hm => ?_, fun γ μγ _ hγ _ => zero γ μγ _ fun z hz => ?_⟩
  swap
  · obtain ⟨δ, -, hδ⟩ := kside γ z hz
    exact hγ ⟨δ, hδ⟩
  have hγ : IsRegSemisimple γ := by
    rw [IsTwRegSemisimple, hh, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at hδ
    rw [IsRegSemisimple, ← Polynomial.separable_map (algebraMap k E), ← Matrix.charpoly_map]
    exact hδ
  by_cases hA : ∃ x, x⁻¹ * δ * sg (σ : E ≃+* E) x ∈ iwahoriCoset tE
  swap
  · rw [zero γ μγ _ fun z hz => ?_]
    · have : ∀ x, twConj (sigmaGL σ) x δ ∉ iwahoriCoset tE := fun x hx => hA ⟨x, hx⟩
      simp [twOrbIntegralC, quotIntegral, this]
    · obtain ⟨δ', h1, h2⟩ := kside γ z hz
      obtain ⟨x, rfl⟩ := normInj k E σ hg n γ hγ δ δ' ⟨h, hh⟩ h2
      exact hA ⟨x, h1⟩
  obtain ⟨x, hx⟩ := hA
  obtain ⟨κ, -, s, hs, hy⟩ := contract hc.isom htE hx
  generalize x * κ⁻¹ = y at hy
  obtain ⟨s₀, hs₀, e⟩ := down hg hc hs
  have h1 : incl (diagT k (Fin n) (tq * s₀)) = (y⁻¹ * h) * incl γ * (y⁻¹ * h)⁻¹ := by
    rw [← hN s s₀ e, ← hy, nrm_conj hc.ord, hnr, hh]
    group
  obtain ⟨z, hz⟩ := conjDesc k E n γ _ hγ ⟨_, h1⟩
  have hfix : ∀ u : Eˣ, ∃ p : Eˣ, (σ : E ≃+* E) p = p ∧ valuation E (p : E) = valuation E (u : E) := by
    intro u
    obtain ⟨π, h1, h2⟩ := hu
    obtain ⟨h3, h4⟩ := val_dec h1 h2
    obtain ⟨m, hm⟩ := h4 u u.ne_zero
    refine ⟨Units.mk0 _ (zpow_ne_zero m h3), ?_, hm.symm⟩
    rw [Units.val_mk0, ← map_zpow₀]
    exact σ.commutes _
  rw [twOrbIntegralC, orbIntegralC, one_field μE hc hfix htE hs hy (twCent (sigmaGL σ) δ) (fun _ => Iff.rfl) μδ 1
      (fun g => (iwahoriCoset tE).indicator (fun _ => 1) (twConj (sigmaGL σ) g δ)) (fun _ => rfl),
    one_field μk hr (fun u => ⟨u, rfl, rfl⟩) htq hs₀ (δ := γ) (y := z⁻¹) (by rw [hz, inv_inv]; rfl) (Subgroup.centralizer {γ})
      (fun c => by
        rw [Subgroup.mem_centralizer_singleton_iff, mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]
        rfl) μγ
      (((μE (iwahori (m := n) E)).toReal / (μk (iwahori (m := n) k)).toReal : ℝ) : ℂ) _
      (fun g => by
        show (_ : ℂ) * (iwahoriCoset tq).indicator (fun _ => (1 : ℂ)) (g⁻¹ * γ * g) = (iwahoriCoset tq).indicator (fun _ => (_ : ℂ)) (g⁻¹ * γ * g)
        by_cases h : g⁻¹ * γ * g ∈ iwahoriCoset tq <;> simp [h]), iw_eq, iw_eq]
  obtain ⟨w, hw⟩ := strictNormal E n _ 1 hrE _ _ (strict_map (strict_mul htq hs₀)) (strict_map (strict_mul htq hs₀))
    (y⁻¹ * h * incl z⁻¹) (by
      rw [← map_diag]
      show _ * incl _ * (y⁻¹ * h * incl z⁻¹) = incl _
      nth_rewrite 1 [h1]
      rw [hz, map_mul, map_mul, map_inv]
      group)
  have hS : MeasurableSet {g : GL (Fin n) E | incl z * g * (incl z)⁻¹ ∈ GlobalTheory.SmGL.iwahori E (Fin n)} :=
    ((IwahoriOnto.isOpen_iwahori E _).preimage (f := fun g : GL (Fin n) E => incl z * g * (incl z)⁻¹) (by fun_prop)).measurableSet
  have hv := congrArg (fun m : Measure (GL (Fin n) E) => m {g | incl z * g * (incl z)⁻¹ ∈ GlobalTheory.SmGL.iwahori E (Fin n)}) hm
  rw [Measure.map_apply (by fun_prop) hS,
    Measure.map_apply (f := fun t : Subgroup.centralizer {γ} => (incl (t : GL (Fin n) k) : GL (Fin n) E))
      (hcl.continuous.comp continuous_subtype_val).measurable hS] at hv
  have e1 : μδ {c | y⁻¹ * c * y ∈ GlobalTheory.SmGL.iwahori E (Fin n)} = μγ {c | z⁻¹⁻¹ * c * z⁻¹ ∈ GlobalTheory.SmGL.iwahori k (Fin n)} := by
    convert hv using 2
    · ext c
      obtain ⟨u, hu⟩ := cent_diag hc (strict_mul htE hs) hy c.2
      have : incl z * (h⁻¹ * (c : GL (Fin n) E) * h) * (incl z)⁻¹ = y⁻¹ * (c : GL (Fin n) E) * y := by
        calc _ = (y⁻¹ * h * incl z⁻¹)⁻¹ * ((y⁻¹ * (c : GL (Fin n) E) * y) * (y⁻¹ * h * incl z⁻¹)) := by rw [map_inv]; group
          _ = _ := by rw [hu, hw, diag_comm, inv_mul_cancel_left]
      simp only [Set.mem_setOf_eq, Set.mem_preimage, this]
    · ext c
      simp only [Set.mem_setOf_eq, Set.mem_preimage, ← incl_mem (E := E), map_mul, map_inv, inv_inv]
  have h0 : (μk (GlobalTheory.SmGL.iwahori k (Fin n))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨(IwahoriOnto.isOpen_iwahori k _).measure_ne_zero μk ⟨1, one_mem _⟩,
      (IwahoriOnto.isCompact_iwahori k _).measure_ne_top⟩
  rw [e1, one_mul, ← Complex.ofReal_mul, div_mul_div_cancel₀ h0]
