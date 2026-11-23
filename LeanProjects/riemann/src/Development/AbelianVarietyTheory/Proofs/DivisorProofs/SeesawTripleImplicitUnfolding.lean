import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEvaluationInfinitePart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalZetaIntegralUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedFactorNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableAbsNormRpowHeightOneSpectrum

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)

namespace GlobalTheory.ThK.UnrVacB

open GlobalTheory.LocIdeal GlobalTheory.TateUnr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_locL_sub_one_le (ν : Chr F E) (w : HeightOneSpectrum (𝓞 E)) {s : ℕ} (hs : 1 ≤ s) :
    ‖locL (charFam ν) w (s : ℂ) - 1‖ ≤ 2 * (Ideal.absNorm w.asIdeal : ℝ) ^ (-(s : ℝ)) := by
  have hN : (2 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm w
  have hx : ‖npow w (-(s : ℂ))‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (-(s : ℝ)) := by
    rw [norm_npow]; simp
  have hh : (Ideal.absNorm w.asIdeal : ℝ) ^ (-(s : ℝ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg (by linarith), Real.rpow_natCast, one_div]
    exact inv_anti₀ (by norm_num) (hN.trans (le_self_pow₀ (by linarith) (by omega)))
  unfold locL charFam
  split_ifs
  · rw [eulerFac_singleton]
    set x : ℂ := (val ν w : ℂ) * npow w (-(s : ℂ)) with hxdef
    have hx' : ‖x‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (-(s : ℝ)) := by rw [hxdef, norm_mul, norm_val, one_mul, hx]
    have h1 : (1 / 2 : ℝ) ≤ ‖1 - x‖ := by
      have := norm_sub_norm_le (1 : ℂ) x
      rw [norm_one] at this
      linarith
    have h0 : 1 - x ≠ 0 := fun h => by rw [h, norm_zero] at h1; norm_num at h1
    rw [show (1 - x)⁻¹ - 1 = x / (1 - x) by field_simp; ring, norm_div, div_le_iff₀ (by linarith), ← hx']
    nlinarith [norm_nonneg x]
  · rw [eulerFac_zero, sub_self, norm_zero]
    positivity

theorem summable_Lv_sub_one (ν : Chr F E) {s : ℕ} (hs : 2 ≤ s) :
    Summable fun v : Pl F => ‖Lv (charFam ν) v (s : ℂ) - 1‖ := by
  let a : HeightOneSpectrum (𝓞 E) → ℝ := fun w => ‖locL (charFam ν) w (s : ℂ) - 1‖
  have ha : Summable a := Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun w => norm_locL_sub_one_le ν w (by omega))
    ((GlobalTheory.summable_absNorm_rpow_heightOneSpectrum E s (by exact_mod_cast (by omega : 1 < s))).mul_left 2)
  let f : HeightOneSpectrum (𝓞 E) → Pl F := fun w => w.under (𝓞 F)
  have hb : HasSum (fun v : Pl F => ∑ w ∈ aboveF (L := E) F v, a w) (∑' w, a w) := by
    refine ((Equiv.sigmaFiberEquiv f).hasSum_iff.2 ha.hasSum).sigma fun v => ?_
    let e : {w // w ∈ aboveF (L := E) F v} ≃ {w // f w = v} := Equiv.subtypeEquivRight fun w => mem_aboveF
    exact e.hasSum_iff.1 (Finset.hasSum (aboveF (L := E) F v) a)
  refine Summable.of_norm_bounded_eventually (hb.summable.mul_left 2) ?_
  filter_upwards [hb.summable.tendsto_cofinite_zero.eventually (ge_mem_nhds one_pos)] with v hv
  have h0 : 0 ≤ ∑ w ∈ aboveF (L := E) F v, a w := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h1 := Finset.norm_prod_one_add_sub_one_le (aboveF (L := E) F v) fun w => locL (charFam ν) w (s : ℂ) - 1
  simp only [add_sub_cancel] at h1
  have h2 := Real.abs_exp_sub_one_le (x := ∑ w ∈ aboveF (L := E) F v, a w) (by rwa [abs_of_nonneg h0])
  rw [abs_of_nonneg h0] at h2
  rw [norm_norm]
  exact h1.trans ((le_abs_self _).trans h2)

theorem eventually_count_eq_zero (𝔞 : FractionalIdeal (𝓞 E)⁰ E) :
    ∀ᶠ v : Pl F in cofinite, ∀ w ∈ aboveF (L := E) F v, FractionalIdeal.count E w 𝔞 = 0 := by
  refine Filter.eventually_cofinite.2 (((Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors 𝔞)).image
    (fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F))).subset fun v hv => ?_)
  simp only [Set.mem_ofPred_eq, not_forall] at hv
  obtain ⟨w, hw, h⟩ := hv
  exact ⟨w, h, mem_aboveF.1 hw⟩

theorem unrFac_of_count (ν : Chr F E) {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (s : ℂ) {v : Pl F}
    (h : ∀ w ∈ aboveF (L := E) F v, FractionalIdeal.count E w 𝔞 = 0) : unrFac ν 𝔞 s v = Lv (charFam ν) v s := by
  rw [unrFac, Finset.prod_eq_one, one_mul]
  intro w hw
  rw [h w hw]
  simp [npow]

theorem summable_unrFac_sub_one (ν : Chr F E) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) {s : ℕ} (hs : 2 ≤ s) :
    Summable fun v : Pl F => ‖unrFac ν 𝔞 (s : ℂ) v - 1‖ :=
  (summable_Lv_sub_one ν hs).congr_cofinite
    ((eventually_count_eq_zero (F := F) 𝔞).mono fun v hv => by simp only [unrFac_of_count ν _ hv])

open Classical in

def tateInt (ν : Chr F E) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (s : ℕ) (v : Pl F) (l : (AE F E)ˣ) : ℂ :=
  if compFin F E v (l : AE F E) ∈ locId v 𝔞 then (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ s else 0

theorem integral_tateInt {ν : Chr F E} {v : Pl F} (hν : ∀ w ∈ aboveF (L := E) F v, UnrAt ν w)
    {μ : Measure (idelesAt E (evFin F v))} (hμ : IsNormE E v μ) {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0) {s : ℕ}
    (hs : 1 ≤ s) : ∫ l : idelesAt E (evFin F v), tateInt ν 𝔞 s v l.1 ∂μ = unrFac ν 𝔞 (s : ℂ) v :=
  tate_unr ν v hν μ hμ 𝔞 h𝔞 s hs

theorem integrable_tateInt {ν : Chr F E} {v : Pl F} (hν : ∀ w ∈ aboveF (L := E) F v, UnrAt ν w)
    {μ : Measure (idelesAt E (evFin F v))} (hμ : IsNormE E v μ) {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0) {s : ℕ}
    (hs : 1 ≤ s) : Integrable (fun l : idelesAt E (evFin F v) => tateInt ν 𝔞 s v l.1) μ := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_tateInt hν hμ h𝔞 hs]
  refine unrFac_ne_zero_of_re_pos _ _ ?_ v
  rw [Complex.natCast_re]
  exact_mod_cast hs

theorem norm_tateInt (ν : Chr F E) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (s : ℕ) (v : Pl F) (l : (AE F E)ˣ) :
    ((‖tateInt ν 𝔞 s v l‖ : ℝ) : ℂ) = tateInt 1 𝔞 s v l := by
  unfold tateInt
  split_ifs
  · rw [norm_mul, Circle.norm_coe]
    simp
  · simp

theorem integral_norm_tateInt (ν : Chr F E) {v : Pl F}
    {μ : Measure (idelesAt E (evFin F v))} (hμ : IsNormE E v μ) {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0) {s : ℕ}
    (hs : 1 ≤ s) :
    ((∫ l : idelesAt E (evFin F v), ‖tateInt ν 𝔞 s v l.1‖ ∂μ : ℝ) : ℂ) = unrFac (1 : Chr F E) 𝔞 (s : ℂ) v := by
  rw [← integral_complex_ofReal, ← integral_tateInt (fun w _ x _ => by simp [locChar]) hμ h𝔞 hs]
  simp only [norm_tateInt]

theorem chr_unit {ν : Chr F E} {v : Pl F} (hν : ∀ w ∈ aboveF (L := E) F v, UnrAt ν w) {l : (AE F E)ˣ}
    (hl : l ∈ unitsAt E v) : (ν l : ℂ) = 1 := by
  have h := chr_eq_prod_val_zpow ν v hν ⟨l, unitsAt_le v hl⟩
  rw [(GlobalTheory.TateUnits.mem_unitsAt_iff_ordV_eq_zero v ⟨l, unitsAt_le v hl⟩).1 hl] at h
  simpa using h

theorem tateInt_unit {ν : Chr F E} {v : Pl F} (hν : ∀ w ∈ aboveF (L := E) F v, UnrAt ν w)
    {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0) (s : ℕ) {l u : (AE F E)ˣ} (hl : l ∈ idelesAt E (evFin F v))
    (hu : u ∈ unitsAt E v) : tateInt ν 𝔞 s v (l * u) = tateInt ν 𝔞 s v l := by
  have hu' := unitsAt_le v hu
  have h1 := mem_locId_iff_count_le_ordV v 𝔞 h𝔞 (⟨l, hl⟩ * ⟨u, hu'⟩)
  rw [ordV_mul, (GlobalTheory.TateUnits.mem_unitsAt_iff_ordV_eq_zero v ⟨u, hu'⟩).1 hu, add_zero,
    ← mem_locId_iff_count_le_ordV v 𝔞 h𝔞 ⟨l, hl⟩] at h1
  have h2 : compFin F E v ((l * u : (AE F E)ˣ) : AE F E) ∈ locId v 𝔞 ↔ compFin F E v (l : AE F E) ∈ locId v 𝔞 := h1
  unfold tateInt
  rw [h2, map_mul, map_mul, absE_of_mem_unitsAt hu, mul_one, Circle.coe_mul, chr_unit hν hu, mul_one]

theorem tateInt_eq_one {ν : Chr F E} {v : Pl F} (hν : ∀ w ∈ aboveF (L := E) F v, UnrAt ν w)
    {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0) (h0 : ∀ w ∈ aboveF (L := E) F v, FractionalIdeal.count E w 𝔞 = 0) (s : ℕ)
    {u : (AE F E)ˣ} (hu : u ∈ unitsAt E v) : tateInt ν 𝔞 s v u = 1 := by
  have hu' := unitsAt_le v hu
  have h1 := (mem_locId_iff_count_le_ordV v 𝔞 h𝔞 ⟨u, hu'⟩).2 fun w => by
    rw [(GlobalTheory.TateUnits.mem_unitsAt_iff_ordV_eq_zero v ⟨u, hu'⟩).1 hu, h0 w.1 w.2]; rfl
  rw [tateInt, if_pos h1, chr_unit hν hu, absE_of_mem_unitsAt hu]
  simp

end GlobalTheory.ThK.UnrVacB

namespace GlobalTheory.ThK.UnrVacB

theorem unr_vac_integrands : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (_hKP : KP) (B : Base F E) {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b} {H : Plane E (b + 2) b}
    {H' : Plane E (a + (b + 2)) (a + b)}, CfgB B G G₁ H H' →
    ∀ {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {om₁ : Rep σ G₁.V G₁.W} {om₁' : Rep σ G₁.V' G₁.W},
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ {e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)}, IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (ei' : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev' : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei' ≠ 0 → (∀ v, ev' v (G.M'.vac v) = G₁.M'.vac v ∧
      (SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)).map (ev' v) = SB (Fin b × Fin (a + b) → Fv F v)) →
    (∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ),
      (∀ v, φ v ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
      e' (pure f φ) = pure (ei' f) fun v => ev' v (φ v)) →
    ∀ {K : Subgroup (UA σ G.V'.J)}, IsStab B K →
    ∀ (μv : ∀ v : Pl F, Measure (idelesAt E (evFin F v))), (∀ v, IsNormE E v (μv v)) →
    ∀ (T : Finset (Pl F)), X.T ⊆ T → ∀ y : Fin b × Fin (a + b) → AF F,
    (∀ v ∉ T, ∀ l l' : (AE F E)ˣ, l ∈ idelesAt E (evFin F v) → l⁻¹ * l' ∈ unitsAt E v →
      coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (G.M'.vac v) 1 l' (fun i => evFin F v (y i)) =
      coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (G.M'.vac v) 1 l (fun i => evFin F v (y i))) ∧
    (∀ᶠ v in cofinite, ∀ l ∈ unitsAt E v,
      coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (G.M'.vac v) 1 l (fun i => evFin F v (y i)) = 1) ∧
    (∀ v ∉ T, Integrable (fun l : idelesAt E (evFin F v) =>
      coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (G.M'.vac v) 1 l.1 (fun i => evFin F v (y i))) (μv v)) ∧
    Summable (fun v : {v : Pl F // v ∉ T} => ∫ l : idelesAt E (evFin F v.1),
      ‖coneFinInt B G.M' om' v.1 (ev' v.1) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (G.M'.vac v.1) 1 l.1
        (fun i => evFin F v.1 (y i))‖ ∂(μv v.1) - 1) ∧
    (∀ v ∉ T, ∫ l : idelesAt E (evFin F v),
      coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (G.M'.vac v) 1 l.1 (fun i => evFin F v (y i)) ∂(μv v) =
      unrFac X.ν (H.𝔟⁻¹ * conjI σ H'.𝔟) ((((a - (b + 2)) / 2 + 1 : ℕ) : ℂ)) v * G₁.M'.vac v (fun i => evFin F v (y i))) ∧
    Summable (fun v : {v : Pl F // v ∉ T} => ‖unrFac X.ν (H.𝔟⁻¹ * conjI σ H'.𝔟) ((((a - (b + 2)) / 2 + 1 : ℕ) : ℂ)) v.1 - 1‖) := by
  intro F E _ _ _ _ _ σ _ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ e' he' ei' ev' hei hev hpure K _ μv hμ T hXT y
  have hB := hT.base
  have h𝔟 := (GlobalTheory.AdaptedPlaneIdeal.ideal_ne_zero_and_count_eq_zero F E σ B H G.V' G₁.V' 0 (b + 1) _ _ hB hT.geo.hV' hC.hH
    (by omega) (by omega)).1
  have h𝔠 := (GlobalTheory.SkewPlaneIdeal.skewPlaneIdeal_ne_zero_and_count_eq_zero F E σ B H' G.W G₁.W a (a + b + 1) _ _ hB
    hT.geo.hW hC.hH' (by omega) (by omega)).1
  have h𝔞 : H.𝔟⁻¹ * conjI σ H'.𝔟 ≠ 0 := mul_ne_zero (inv_ne_zero h𝔟) (conjI_ne_zero σ h𝔠)
  have hs : 2 ≤ (a - (b + 2)) / 2 + 1 := by have := hT.geo.eBig; omega
  generalize (a - (b + 2)) / 2 + 1 = s at hs ⊢
  have hunr : ∀ v ∉ T, ∀ w ∈ aboveF (L := E) F v, UnrAt X.ν w := fun v hv w hw => by
    have hw' : w ∉ above E (X.T : Set (Pl F)) := fun h => hv (hXT (by
      have h1 : w.under (𝓞 F) ∈ (X.T : Set (Pl F)) := h
      rwa [GlobalTheory.LFun.mem_aboveF.1 hw] at h1))
    rw [Chars.ν, div_eq_mul_inv]
    exact (hT.chars.unrα w hw').mul (hT.chars.unrβ w hw').inv
  have key : ∀ v, ∀ l ∈ idelesAt E (evFin F v),
      coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν s (G.M'.vac v) 1 l (fun i => evFin F v (y i)) =
        G₁.M'.vac v (fun i => evFin F v (y i)) * tateInt X.ν (H.𝔟⁻¹ * conjI σ H'.𝔟) s v l := fun v l hl => by
    have h1 : locOp v (om' (1, 1)) (G.M'.vac v) = G.M'.vac v :=
      locOp_of_fix (fun Φ _ => by rw [← Prod.one_eq_mk, map_one]; rfl) (hT.geo.hM'.vac v).1
    rw [coneFinInt, h1, GlobalTheory.ThK.UnrSuppB.evShift_vac B G G₁ H H' hB hT.geo hT₁.geo hC e' he' ei' ev' hei hev hpure v l hl,
      tateInt]
    split_ifs <;> simp [mul_assoc]
  have hvac : ∀ᶠ v : Pl F in cofinite, G₁.M'.vac v (fun i => evFin F v (y i)) = 1 := by
    have hy : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (y i) ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun i => (y i).2.2
    filter_upwards [hT₁.geo.hM'.std, hy] with v h1 h2
    rw [h1, Set.indicator_of_mem (show (fun i => evFin F v (y i)) ∈ {x : Fin b × Fin (a + b) → Fv F v |
      ∀ i, x i ∈ v.adicCompletionIntegers F} from h2)]
    rfl
  refine ⟨fun v hv l l' hl hu => ?_, ?_, fun v hv => ?_, ?_, fun v hv => ?_,
    (summable_unrFac_sub_one X.ν _ hs).subtype _⟩
  · have e : l' = l * (l⁻¹ * l') := (mul_inv_cancel_left _ _).symm
    rw [key v l hl, key v l' (e ▸ mul_mem hl (unitsAt_le v hu)), ← tateInt_unit (hunr v hv) h𝔞 s hl hu, ← e]
  · filter_upwards [hvac, eventually_count_eq_zero (F := F) (H.𝔟⁻¹ * conjI σ H'.𝔟), T.eventually_cofinite_notMem]
      with v h1 h2 h3 l hl
    rw [key v l (unitsAt_le v hl), h1, one_mul, tateInt_eq_one (hunr v h3) h𝔞 h2 s hl]
  · simp only [fun l : idelesAt E (evFin F v) => key v l.1 l.2]
    exact (integrable_tateInt (hunr v hv) (hμ v) h𝔞 (by omega)).const_mul _
  · refine Summable.subtype (f := fun v : Pl F => ∫ l : idelesAt E (evFin F v),
      ‖coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν s (G.M'.vac v) 1 l.1 (fun i => evFin F v (y i))‖ ∂(μv v) - 1)
      ?_ _
    refine Summable.of_norm_bounded_eventually (summable_unrFac_sub_one (1 : Chr F E) (H.𝔟⁻¹ * conjI σ H'.𝔟) hs) ?_
    filter_upwards [hvac] with v h1
    simp only [fun l : idelesAt E (evFin F v) => key v l.1 l.2, h1, one_mul]
    rw [← integral_norm_tateInt X.ν (hμ v) h𝔞 (by omega : 1 ≤ s), ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real]
  · simp only [fun l : idelesAt E (evFin F v) => key v l.1 l.2]
    rw [integral_const_mul, integral_tateInt (hunr v hv) (hμ v) h𝔞 (by omega), mul_comm]

end GlobalTheory.ThK.UnrVacB

end
