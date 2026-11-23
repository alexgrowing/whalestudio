import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralIdeleMajorantFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaConeSwap

theorem tsum_integral_integral {ι K L : Type} [Countable ι] [MeasurableSpace K] [MeasurableSpace L] (μK : Measure K)
    [IsFiniteMeasure μK] (μ : Measure L) [SFinite μ] (f : ι → K → L → ℂ) (hm : ∀ i, Measurable (Function.uncurry (f i)))
    (b : L → ENNReal) (hb : ∀ k l, ∑' i, ‖f i k l‖ₑ ≤ b l) (hI : ∫⁻ l, b l ∂μ < ⊤) :
    ∑' i, ∫ k, ∫ l, f i k l ∂μ ∂μK = ∫ k, ∫ l, ∑' i, f i k l ∂μ ∂μK := by
  have h1 : ∀ k, ∑' i, ∫⁻ l, ‖f i k l‖ₑ ∂μ ≤ ∫⁻ l, b l ∂μ := fun k => by
    rw [← lintegral_tsum fun i => ((hm i).of_uncurry_left (x := k)).enorm.aemeasurable]
    exact lintegral_mono (hb k)
  have h2 : ∀ i, StronglyMeasurable fun k => ∫ l, f i k l ∂μ := fun i =>
    (hm i).stronglyMeasurable.integral_prod_right
  rw [← integral_tsum (fun i => (h2 i).aestronglyMeasurable)]
  · refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    exact (integral_tsum (fun i => ((hm i).of_uncurry_left (x := k)).aestronglyMeasurable)
      ((h1 k).trans_lt hI).ne).symm
  · rw [← lintegral_tsum fun i => (h2 i).measurable.enorm.aemeasurable]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun _ => ∫⁻ l, b l ∂μ) fun k => ?_) ?_)
    · exact (ENNReal.tsum_le_tsum fun i => enorm_integral_le_lintegral_enorm _).trans (h1 k)
    · rw [lintegral_const]
      exact ENNReal.mul_lt_top hI (measure_lt_top _ _)

section Sch

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.DiffDecay GlobalTheory.XTermDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem tsum_norm_pureA_le {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    ∃ (p : Seminorm ℂ (SInf F κ)) (C : ℝ), Continuous p ∧ 0 ≤ C ∧ ∀ f : SInf F κ,
      ∑' ξ : κ → F, ‖pureA F f g (fun i => algebraMap F (AF F) (ξ i))‖ ≤ C * p f := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨N, hN, hK⟩ := exists_nat_mul_integral_of_isCompact F hg.2.isCompact
  haveI := discreteTopology_denomLattice F κ hN
  set L := denomLattice F κ N with hLdef
  set k := Module.finrank ℤ L + 1 with hkdef
  have hu : Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k :=
    GlobalTheory.ThetaAdmitted.summable_one_add_norm_inv_pow L (Nat.lt_succ_self _)
  set M := ∑' z : L, ((1 + ‖z‖)⁻¹) ^ k with hMdef
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hM0 : 0 ≤ M := tsum_nonneg fun z => by positivity
  refine ⟨(Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), B * 2 ^ k * M,
    Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm i,
    by positivity, fun f => ?_⟩
  set S := (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ) f with hSdef
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hf : ∀ x, ‖f x‖ ≤ 2 ^ k * S * ((1 + ‖x‖)⁻¹) ^ k := by
    intro x
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl f x
    rw [norm_iteratedFDeriv_zero] at h
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact h
  let Sset : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ L}
  have hsupp : ∀ ξ, ξ ∉ Sset → g (fun i => algebraMap F (Af F) (ξ i)) = 0 := by
    intro ξ hξ
    by_contra h0
    apply hξ
    refine fun i => ?_
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ (subset_tsupport _ h0) i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  have hΦ : pureA F f g ∈ schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hsn := summable_norm_of_mem_schA F hΦ
  let a : (κ → F) → ℂ := fun ξ => pureA F f g (fun i => algebraMap F (AF F) (ξ i))
  have ha : ∀ ξ, a ξ = f (fun i => mixedEmbedding F (ξ i)) *
      g (fun i => algebraMap F (Af F) (ξ i)) := fun ξ => pureA_algebraMap F f g ξ
  have hsupa : Function.support (fun ξ => ‖a ξ‖) ⊆ Sset := by
    intro ξ hξ
    by_contra h
    apply hξ
    simp only [ha, hsupp ξ h, mul_zero, norm_zero]
  let j : Sset → L := fun ξ => ⟨_, ξ.2⟩
  have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
  have hle : ∀ ξ : Sset, ‖a ξ‖ ≤ B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k := by
    intro ξ
    have h1 := hB (fun i => algebraMap F (Af F) (ξ.1 i))
    have h2 : ‖f (fun i => mixedEmbedding F (ξ.1 i))‖ ≤ 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k := hf (j ξ)
    rw [ha, norm_mul]
    calc ‖f (fun i => mixedEmbedding F (ξ.1 i))‖ * ‖g (fun i => algebraMap F (Af F) (ξ.1 i))‖
        ≤ (2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k) * B := mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      _ = B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k := by ring
  have hsumS : Summable fun ξ : Sset => B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k :=
    (hu.comp_injective hj).mul_left _
  calc _ = ∑' ξ, ‖a ξ‖ := rfl
    _ = ∑' ξ : Sset, ‖a ξ‖ := (tsum_subtype_eq_of_support_subset hsupa).symm
    _ ≤ ∑' ξ : Sset, B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k :=
        Summable.tsum_le_tsum hle (hsn.subtype _) hsumS
    _ = B * 2 ^ k * S * ∑' ξ : Sset, ((1 + ‖j ξ‖)⁻¹) ^ k := tsum_mul_left
    _ ≤ B * 2 ^ k * S * M := by
        gcongr
        exact tsum_comp_le_tsum_of_inj hu (fun z => by positivity) hj
    _ = B * 2 ^ k * M * S := by ring

theorem tsum_norm_le_of_weak {T : Type} (Ψ : T → (κ → AF F) → ℂ) (hΨ : ∀ t, Ψ t ∈ schA F κ)
    (hb : ∀ l ∈ (adeleClass F).adm κ, ∃ C : ℝ, ∀ t, ‖l (Ψ t)‖ ≤ C) :
    ∃ C : ℝ, ∀ t, ∑' ξ : κ → F, ‖Ψ t (fun i => algebraMap F (AF F) (ξ i))‖ ≤ C := by
  obtain ⟨m, g, f, hg, hdec, hf⟩ := exists_decomp Ψ hΨ hb
  choose p C hp hC hpC using fun j => tsum_norm_pureA_le (hg j)
  choose D hD using fun j => hf j (p j) (hp j)
  refine ⟨∑ j, C j * D j, fun t => ?_⟩
  have hs : ∀ j, Summable fun ξ : κ → F => ‖pureA F (f j t) (g j) (fun i => algebraMap F (AF F) (ξ i))‖ := fun j =>
    summable_norm_of_mem_schA F (Submodule.subset_span ⟨f j t, g j, hg j, rfl⟩)
  calc _ ≤ ∑' ξ : κ → F, ∑ j, ‖pureA F (f j t) (g j) (fun i => algebraMap F (AF F) (ξ i))‖ := by
        refine (summable_norm_of_mem_schA F (hΨ t)).tsum_le_tsum (fun ξ => ?_) (summable_sum fun j _ => hs j)
        rw [hdec t, Finset.sum_apply]
        exact norm_sum_le _ _
    _ = ∑ j, ∑' ξ : κ → F, ‖pureA F (f j t) (g j) (fun i => algebraMap F (AF F) (ξ i))‖ :=
        Summable.tsum_finsetSum fun j _ => hs j
    _ ≤ _ := Finset.sum_le_sum fun j _ => (hpC j _).trans (mul_le_mul_of_nonneg_left (hD j t) (hC j))

theorem schr_add (ψ : AddChar (AF F) ℂ) (s u : (κ → AF F) × (κ → AF F)) (Φ : (κ → AF F) → ℂ) :
    schr ψ (s + u) Φ = ψ (⅟(2 : AF F) * (s.1 ⬝ᵥ u.2 + u.1 ⬝ᵥ s.2) - s.1 ⬝ᵥ u.2) • schr ψ s (schr ψ u Φ) := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add,
    Prod.fst_add, Prod.snd_add, add_assoc x]
  congr 2
  ring

theorem continuous_qA : Continuous (qA : AF F → mixedEmbedding.mixedSpace F) := by
  refine continuous_of_continuousAt_zero (qA (F := F)).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  have h : Continuous fun a : AF F => ∑ v, ‖a.1 v‖ :=
    continuous_finset_sum _ fun v _ => ((continuous_apply v).comp continuous_fst).norm
  refine squeeze_zero (fun _ => norm_nonneg _) norm_qA_le (h.tendsto' 0 0 ?_)
  exact Finset.sum_eq_zero fun v _ => norm_zero

theorem continuous_archW : Continuous (archW (F := F) (κ := κ)) :=
  (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp continuous_fst)).prodMk
    (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp continuous_snd))

theorem continuousAt_schr_zero (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (hl : l ∈ (adeleClass F).adm κ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Tendsto (fun w => l (schr ψ w Φ)) (𝓝 0) (𝓝 (l Φ)) := by
  induction hΦ using Submodule.span_induction with
  | zero =>
    have : ∀ w : (κ → AF F) × (κ → AF F), schr ψ w 0 = 0 := fun w => map_zero (schrL ψ w)
    simp only [this]
    exact tendsto_const_nhds
  | add a b _ _ ha hb =>
    have : ∀ w : (κ → AF F) × (κ → AF F), schr ψ w (a + b) = schr ψ w a + schr ψ w b := fun w => map_add (schrL ψ w) a b
    simp only [this, map_add]
    exact ha.add hb
  | smul c a _ ha =>
    have : ∀ w : (κ → AF F) × (κ → AF F), schr ψ w (c • a) = c • schr ψ w a := fun w => map_smul (schrL ψ w) c a
    simp only [this, map_smul]
    exact ha.const_smul c
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    have hΦ : pureA F f g ∈ schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
    obtain ⟨T, hT⟩ := hl g hg
    let ε : AF F := mk 1 0
    have hε : ε * ε = ε := Prod.ext (mul_one _) (mul_zero _)
    let s : (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F) := fun w => ε • w
    let u : (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F) := fun w => w - ε • w
    have hs : Continuous s := continuous_const_smul ε
    have hu : Continuous u := continuous_id.sub hs
    have hs0 : s 0 = 0 := smul_zero _
    have hu0 : u 0 = 0 := by simp [u]
    have hev := (hu.tendsto' 0 0 hu0).eventually (GlobalTheory.XTermFinParts.eventually_schr_eq hψ hΦ)
    let c : (κ → AF F) × (κ → AF F) → ℂ := fun w =>
      ψ (⅟(2 : AF F) * ((s w).1 ⬝ᵥ (u w).2 + (u w).1 ⬝ᵥ (s w).2) - (s w).1 ⬝ᵥ (u w).2)
    have hc : Continuous c := hψ.1.comp ((continuous_const.mul ((hs.fst.dotProduct hu.snd).add
      (hu.fst.dotProduct hs.snd))).sub (hs.fst.dotProduct hu.snd))
    have hc0 : c 0 = 1 := by simp [c, hs0, hu0]
    obtain ⟨q, M, -, hq⟩ := tame_archOp (F := F) (κ := κ) ((normSeminorm ℂ ℂ).comp T.toLinearMap) T.continuous.norm
    have h1 : Tendsto (fun w => T (archOp (archW (s w)) f)) (𝓝 0) (𝓝 (T f)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hn : Continuous fun w => ‖archW (s w)‖ * (1 + ‖archW (s w)‖) ^ M * q f :=
        ((continuous_archW.comp hs).norm.mul ((continuous_const.add (continuous_archW.comp hs).norm).pow M)).mul
          continuous_const
      refine squeeze_zero (fun _ => norm_nonneg _) (fun w => ?_) (hn.tendsto' 0 0 ?_)
      · rw [← map_sub]
        exact hq (archW (s w)) f
      · have : archW (0 : (κ → AF F) × (κ → AF F)) = 0 := Prod.ext (funext fun _ => map_zero qA) (funext fun _ => map_zero qA)
        simp only [hs0, this, norm_zero, zero_mul]
    have h2 := (hc.tendsto' 0 1 hc0).smul h1
    rw [one_smul, ← hT] at h2
    refine h2.congr' (hev.mono fun w hw => ?_)
    have h3 : schr ψ (u w) (pureA F f g) = pureA F f g := hw (by
      change ε • (w - ε • w) = 0
      rw [smul_sub, smul_smul, hε, sub_self])
    have h4 : w = s w + u w := (add_sub_cancel _ _).symm
    beta_reduce
    conv_rhs => rw [h4, schr_add, h3, map_smul, schr_pureA ψ hψ, finOp_arch, hT]

theorem continuous_schr (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (hl : l ∈ (adeleClass F).adm κ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Continuous fun w => l (schr ψ w Φ) := by
  refine continuous_iff_continuousAt.2 fun s => ?_
  have h1 := continuousAt_schr_zero ψ hψ (GlobalTheory.ConeTermCont.schrLin_comp_mem_adm ψ hψ s l hl) hΦ
  let c : (κ → AF F) × (κ → AF F) → ℂ := fun u => ψ (⅟(2 : AF F) * (s.1 ⬝ᵥ u.2 + u.1 ⬝ᵥ s.2) - s.1 ⬝ᵥ u.2)
  have hc : Continuous c := hψ.1.comp ((continuous_const.mul ((continuous_const.dotProduct continuous_snd).add
      (continuous_fst.dotProduct continuous_const))).sub (continuous_const.dotProduct continuous_snd))
  have h2 := ((hc.tendsto' 0 1 (by simp [c])).smul h1).comp ((continuous_sub_right s).tendsto' s 0 (sub_self s))
  rw [one_smul] at h2
  refine h2.congr fun w => ?_
  conv_rhs => rw [← add_sub_cancel s w, schr_add, map_smul]
  rfl

theorem proj_mem_adm (y : κ → AF F) : (LinearMap.proj y : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (y i).2) • (BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ),
    fun f => mul_comm _ _⟩

end Sch

section Bound

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.DiffDecay GlobalTheory.XTermDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def onePt : SInf F PEmpty :=
  (HasCompactSupport.of_compactSpace (fun _ : PEmpty → mixedEmbedding.mixedSpace F => (1 : ℂ))).toSchwartzMap contDiff_const

theorem weak_decay {ι T : Type} [Fintype ι] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (S U : ι → (κ → AF F) × (κ → AF F)) (hSU : ∀ i j, (S j).1 ⬝ᵥ (U i).2 - (U i).1 ⬝ᵥ (S j).2 = if i = j then 1 else 0)
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ (adeleClass F).adm κ)
    (hinv : ∀ i (a : AF F), ∀ Φ ∈ schA F κ, l (schr ψ (a • U i) Φ) = l Φ)
    (Ψ : T → (κ → AF F) → ℂ) (hΨ : ∀ t, Ψ t ∈ schA F κ) (hb : ∀ l ∈ (adeleClass F).adm κ, ∃ C : ℝ, ∀ t, ‖l (Ψ t)‖ ≤ C)
    {Ω : Set (ι → Af F)} (hΩ : IsCompact Ω) (N : ℕ) :
    ∃ C : ℝ, ∀ t (x : ι → AF F), (fun i => (x i).2) ∈ Ω →
      ‖l (schr ψ (∑ i, x i • S i) (Ψ t))‖ ≤ C * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖) ^ (-(N : ℝ)) := by
  obtain ⟨m, g, f, hg, hdec, hf⟩ := exists_decomp Ψ hΨ hb
  choose C hC using fun j => slice_decay ψ hψ S U hSU (l.smulRight (coeL (onePt (F := F))))
    (fun g hg => by
      obtain ⟨T, hT⟩ := hl g hg
      refine ⟨T.smulRight onePt, fun f => ?_⟩
      rw [LinearMap.smulRight_apply, hT]
      rfl)
    (fun i a Φ hΦ => by rw [LinearMap.smulRight_apply, LinearMap.smulRight_apply, hinv i a Φ hΦ])
    (hg j) (f j) (hf j) hΩ (SchwartzMap.seminorm ℂ 0 0) ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (0, 0)) N
  refine ⟨∑ j, C j, fun t x hx => ?_⟩
  rw [hdec t, Finset.sum_mul]
  change ‖l (schrL ψ _ _)‖ ≤ _
  rw [map_sum, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  obtain ⟨f₁, h1, h2⟩ := hC j t x hx
  refine le_trans ?_ ((SchwartzMap.norm_le_seminorm ℂ f₁ 0).trans h2)
  rw [h1]
  exact le_of_eq (congrArg norm (mul_one _).symm)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem tsum_enorm_le {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    {χX χW : Chr F E} {om : Rep σ X W} (hom : M.IsWeil ψ χX χW om) {K : Set (UA σ X.J)} (hK : IsCompact K) (h : UA σ W.J)
    {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] (κ → AF F) → ℂ)
    (hmaps : ∀ Ψ ∈ schA F _, e Ψ ∈ schA F κ) (hadm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ e ∈ (adeleClass F).adm _)
    {ι : Type} [Fintype ι] (S U : ι → Matrix (Fin n) (Fin d) (AE F E))
    (hSU : ∀ i j, symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (S j) (U i) = if i = j then 1 else 0)
    (hinv : ∀ i (a : AF F), ∀ Ψ ∈ schA F _, e (M.co.rho ψ (a • U i) Ψ) = e Ψ) :
    ∃ Ω : Set (ι → Af F), IsCompact Ω ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ k ∈ K, ∀ x : ι → AF F,
      ∑' ξ : κ → F, ‖e (M.co.rho ψ (∑ i, x i • S i) (om (k, h) Φ)) (fun i => algebraMap F (AF F) (ξ i))‖ₑ ≤
        ENNReal.ofReal C * Ω.indicator
          (fun _ => ENNReal.ofReal ((1 + ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖) ^ (-(N : ℝ)))) (fun i => (x i).2) := by
  have hw : IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hom
  have hΨ : ∀ k, om (k, h) Φ ∈ schA F _ := fun k => hw.isUSplitting.pres (k, h) Φ hΦ
  have hO := fun i => GlobalTheory.XTermSupp.rho_om_fixed M ψ hψ.1 hom hK h Φ hΦ (U i)
  obtain ⟨V, hV, hVm⟩ := GlobalTheory.ScalarAnnih.exists_compact_annihilator_finiteAdeles_traceChar F ψ hψ.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hψ) _
    (Filter.eventually_all.2 hO)
  have hΩ : IsCompact (Set.pi Set.univ fun _ : ι => V) := isCompact_univ_pi fun _ => hV
  have hSU' : ∀ i j, (M.co.e (S j)).1 ⬝ᵥ (M.co.e (U i)).2 - (M.co.e (U i)).1 ⬝ᵥ (M.co.e (S j)).2 =
      if i = j then 1 else 0 := fun i j => by rw [← M.co.form, hSU]
  have hrho : ∀ x : ι → AF F, M.co.rho ψ (∑ i, x i • S i) = schr ψ (∑ i, x i • M.co.e (S i)) := fun x => by
    simp only [Darboux.rho, map_sum, map_smul]
  refine ⟨_, hΩ, fun N => ?_⟩
  let r : (ι → AF F) → ℝ := fun x => 1 + ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖
  have hr : ∀ x, 0 < r x := fun x => by positivity
  let T := {p : K × (ι → AF F) // (fun i => (p.2 i).2) ∈ Set.pi Set.univ fun _ : ι => V}
  have hmem : ∀ k (x : ι → AF F), e (M.co.rho ψ (∑ i, x i • S i) (om (k, h) Φ)) ∈ schA F κ := fun k x =>
    hmaps _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ _ (hΨ k))
  obtain ⟨C, hC⟩ := tsum_norm_le_of_weak
    (fun t : T => ((r t.1.2 ^ N : ℝ) : ℂ) • e (M.co.rho ψ (∑ i, t.1.2 i • S i) (om (t.1.1.1, h) Φ)))
    (fun t => Submodule.smul_mem _ _ (hmem _ _)) fun l hl => by
      obtain ⟨C, hC⟩ := weak_decay ψ hψ (fun i => M.co.e (S i)) (fun i => M.co.e (U i)) hSU' (l ∘ₗ e) (hadm l hl)
        (fun i a Ψ hΨ => by
          have := hinv i a Ψ hΨ
          rw [Darboux.rho, map_smul] at this
          exact congrArg l this)
        (fun k : K => om (k.1, h) Φ) (fun k => hΨ k.1) (fun l hl => by
          have hc := (hw.2.2 l hl Φ hΦ).comp
            (continuous_id.prodMk continuous_const : Continuous fun g : UA σ X.J => (g, h))
          obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
          exact ⟨C, fun k => hC k.1 k.2⟩) hΩ N
      refine ⟨C, fun t => ?_⟩
      have h1 := hC t.1.1 t.1.2 t.2
      have h2 := hr t.1.2
      rw [Real.rpow_neg h2.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos h2 _)] at h1
      rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_pos h2 _).le, mul_comm, hrho]
      exact h1
  refine ⟨C, fun k hk x => ?_⟩
  by_cases hx : (fun i => (x i).2) ∈ Set.pi Set.univ fun _ : ι => V
  · have h1 := hC ⟨(⟨k, hk⟩, x), hx⟩
    have h2 := hr x
    simp only [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_pos h2 _).le, tsum_mul_left] at h1
    rw [Set.indicator_of_mem hx, mul_comm, ← ENNReal.ofReal_mul (Real.rpow_nonneg h2.le _)]
    simp only [← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (summable_norm_of_mem_schA F (hmem k x))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.rpow_neg h2.le, Real.rpow_natCast, le_inv_mul_iff₀ (pow_pos h2 _)]
    exact h1
  · have h0 : e (M.co.rho ψ (∑ i, x i • S i) (om (k, h) Φ)) = 0 := by
      by_contra hne
      refine hx fun i _ => hVm _ fun a ha => ?_
      have h1 := congrArg e (GlobalTheory.XTermSupp.rho_comm M.co ψ (∑ j, x j • S j) (pairA F 0 a • U i) (om (k, h) Φ))
      have hω : symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (∑ j, x j • S j) (pairA F 0 a • U i) =
          pairA F 0 a * x i := by
        have : ∀ j, (x j • M.co.e (S j)).1 ⬝ᵥ (pairA F 0 a • M.co.e (U i)).2 -
            (pairA F 0 a • M.co.e (U i)).1 ⬝ᵥ (x j • M.co.e (S j)).2 = if i = j then pairA F 0 a * x j else 0 := fun j => by
          simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
          have := hSU' i j
          split_ifs at this ⊢
          · linear_combination (pairA F 0 a * x j) * this
          · linear_combination (pairA F 0 a * x j) * this
        rw [M.co.form]
        simp only [map_sum, map_smul]
        rw [Prod.fst_sum, Prod.snd_sum, sum_dotProduct, dotProduct_sum, ← Finset.sum_sub_distrib]
        simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [ha i k hk, map_smul, hinv _ _ _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ _ (hΨ k)), hω] at h1
      have h2 : pairA F 0 a * x i = pairA F 0 (a * (x i).2) := Prod.ext (zero_mul _) rfl
      rw [h2] at h1
      exact smul_left_injective ℂ hne (h1.symm.trans (one_smul ℂ _).symm)
    simp only [h0, Pi.zero_apply, enorm_zero, tsum_zero]
    exact zero_le

end Bound

theorem metrizable_of_compact (K : Type) [TopologicalSpace K] [CompactSpace K] [T2Space K] [SecondCountableTopology K] :
    TopologicalSpace.MetrizableSpace K := inferInstance

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem idele_top : IsTopologicalGroup (AE F E)ˣ ∧ LocallyCompactSpace (AE F E)ˣ ∧ SecondCountableTopology (AE F E)ˣ ∧
    T2Space (AE F E)ˣ := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact ⟨inferInstance, Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology, inferInstance⟩

theorem trace_inclR (x : E) :
    Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) x) = algebraMap F (AF F) (Algebra.trace F E x) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  change Algebra.trace (AF F) (AE F E) ((1 : AF F) ⊗ₜ[F] x) = _
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem form_herm (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (x y : Fin n → E) : form σ J y x = σ (form σ J x y) := by
  simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, GlobalTheory.XTermSupp.invol h, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_dual (hcm : IsCMExt F E σ) {n d : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E}
    {x y : Fin n → E} {x' y' : Fin d → E} (h : form σ JX y x = 1) (h' : form σ JW x' y' = 1) :
    ∃ t : Fin (Module.finrank F E) → E, ∀ i j, symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)
      (inclR (F := F) (AF F) (σ (Module.finBasis F E j)) • Matrix.vecMulVec (incV F y) (incV F x'))
      (inclR (F := F) (AF F) (t i) • Matrix.vecMulVec (incV F x) (incV F y')) = if i = j then 1 else 0 := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext (GlobalTheory.XTermSupp.invol hcm)) (AlgHom.ext (GlobalTheory.XTermSupp.invol hcm))
  refine ⟨fun i => -(Module.finBasis F E).traceDual i, fun i j => ?_⟩
  rw [symp, GlobalTheory.XTermSupp.hTens_vv, GlobalTheory.XTermSupp.form_inc, GlobalTheory.XTermSupp.form_inc, h, h', hc, map_one, mul_one, mul_one,
    ← map_mul, ← map_mul, neg_one_mul, ← map_neg, ← map_neg, mul_neg, neg_neg, trace_inclR]
  have := Algebra.trace_eq_of_algEquiv s (Module.finBasis F E j * (Module.finBasis F E).traceDual i)
  change Algebra.trace F E (σ _) = _ at this
  rw [this, Module.Basis.trace_mul_traceDual]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

theorem cA_eq_sum (z : AE F E) :
    cA σ z = ∑ i, GlobalTheory.XTermMaj.crd F E z i • inclR (F := F) (AF F) (σ (Module.finBasis F E i)) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun z, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.TensorProduct.basis_apply]
  rfl

theorem lintegral_maj_lt_top (μ : Measure (AE F E)ˣ) [μ.IsHaarMeasure] {s : ℝ} (hs : 1 < s)
    {U : Set (Fin (Module.finrank F E) → Af F)} (hU : IsCompact U) : ∃ N : ℕ,
      ∫⁻ l, GlobalTheory.XTermMaj.maj F E N U (l : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ s) ∂μ < ⊤ := by
  obtain ⟨N, k, L, C, hk, hb⟩ := GlobalTheory.TateConv.bound F E hs hU
  exact ⟨N, lt_of_le_of_lt (lintegral_mono hb) (GlobalTheory.TateConv.lintegral_bound_lt_top F E μ hs hk L C)⟩

end Main

theorem thetaSum_integral : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h h₁,
        ∀ g, thetaSum F (fun y => ∫ k, ∫ l, om₁' (g, h₁) (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) y * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) ∂μ ∂μK) =
          ∫ k, ∫ l, theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) g h₁ * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) ∂μ ∂μK := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ hΦ h h₁ g
  have hψ := hT.base.std
  have hKeq : K = GlobalTheory.StabHaar.stabK (σ := σ) B G.V' :=
    Subgroup.ext fun g => (hK g).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B G.V' g).symm
  have hKc : IsCompact (K : Set (UA σ G.V'.J)) := by
    have hX := hT.geo.hV'
    obtain ⟨C, hCc, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B (b + 2) G.V' _ _ hT.base hX
    rw [hKeq]
    exact hCc.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B G.V' (GlobalTheory.T.isClosed_adelic_lattice_closure F E (b + 2) G.V' hX.lat)) hsub
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  obtain ⟨u1, u2, u3, u4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (b + 2) G.V'.J
  obtain ⟨v1, v2, v3, v4⟩ := idele_top (F := F) (E := E)
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : T2Space K := inferInstance
  haveI : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : TopologicalSpace.MetrizableSpace K := metrizable_of_compact K
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (b + 2) → Fin (a + (b + 2)) → AE F E))
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om' := hT.weil'
  have hw₁ : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G₁.V'.J) (incM F G₁.W.J) G₁.M'.co X.α (X.α / X.β) om₁' :=
    hT₁.weil'
  have hΦA : Φ ∈ schA F _ := GlobalTheory.ConeTermCont.polData_le B G.M' hT.geo.hM' hΦ.1
  have hadm : ∀ l ∈ (adeleClass F).adm (Fin b × Fin (a + b)), l ∘ₗ (om₁' (g, h₁) ∘ₗ e) ∈ (adeleClass F).adm _ := fun l hl =>
    GlobalTheory.EvAdm.comp_mem_adm F E σ B _ _ _ _ G.V' G.W G₁.V' G₁.W G.M' G₁.M' H.ι H'.ι _ e hT.geo.hM' hT₁.geo.hM' he _
      (hw₁.isUSplitting.adm (g, h₁) l hl)
  obtain ⟨t, ht⟩ := exists_dual (x := H.x) (y := H.y) hT.base.cm
    (by rw [form_herm hT.base.cm hT.geo.hV'.herm, hC.hH.xy, map_one]) hC.hH'.xy
  obtain ⟨Ω, hΩ, hN⟩ := tsum_enorm_le G.M' B.ψ hψ hT.weil' hKc h hΦA (om₁' (g, h₁) ∘ₗ e)
    (fun Ψ hΨ => hw₁.isUSplitting.pres (g, h₁) _ (he.maps Ψ hΨ)) hadm
    (fun j => inclR (F := F) (AF F) (σ (Module.finBasis F E j)) • Matrix.vecMulVec (incV F H.y) (incV F H'.x))
    (fun i => inclR (F := F) (AF F) (t i) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
    (fun i j => by convert ht i j) fun i c Ψ hΨ =>
      congrArg (om₁' (g, h₁)) (he.inv _ (Or.inl ⟨c • inclR (F := F) (AF F) (t i) • incV F H'.y, by
        rw [Matrix.vecMulVec_smul, Matrix.vecMulVec_smul]⟩) Ψ hΨ)
  set z : ℕ := (a - (b + 2)) / 2 + 1 with hz
  have hz1 : (1 : ℝ) < z := by
    have := hT.geo.eBig
    exact_mod_cast (show 1 < z by omega)
  obtain ⟨N, hI⟩ := lintegral_maj_lt_top μ hz1 hΩ
  obtain ⟨C, hCb⟩ := hN N
  have hS : ∀ l : (AE F E)ˣ, shiftB σ H H' l = ∑ i, GlobalTheory.XTermMaj.crd F E (l : AE F E) i •
      inclR (F := F) (AF F) (σ (Module.finBasis F E i)) • Matrix.vecMulVec (incV F H.y) (incV F H'.x) := fun l => by
    simp only [← smul_assoc, ← Finset.sum_smul]
    rw [shiftB, cA_eq_sum]
  have hsh : Continuous fun l : (AE F E)ˣ => G.M'.co.e (shiftB σ H H' l) :=
    (IsModuleTopology.continuous_of_linearMap G.M'.co.e.toLinearMap).comp
      (((IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap).comp Units.continuous_val).smul continuous_const)
  have hν : Continuous fun l : (AE F E)ˣ => (X.ν l : ℂ) :=
    continuous_subtype_val.comp (hT.chars.heckeα.1.div' hT.chars.heckeβ.1)
  have hab : Continuous fun l : (AE F E)ˣ => ((absE F E l : ℝ) : ℂ) ^ z :=
    (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow z
  simp only [theta, thetaSum, ← tsum_mul_right]
  refine tsum_integral_integral μK μ (fun (ξ : Fin b × Fin (a + b) → F) (k : K) (l : (AE F E)ˣ) =>
      om₁' (g, h₁) (e (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ))) (fun i => algebraMap F (AF F) (ξ i)) *
        (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) (fun ξ => ?_)
    (fun l => ENNReal.ofReal C * (GlobalTheory.XTermMaj.maj F E N Ω (l : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ (z : ℝ))))
    (fun k l => ?_) ?_
  · have hl := hadm _ (proj_mem_adm fun i => algebraMap F (AF F) (ξ i))
    refine measurable_uncurry_of_continuous_of_measurable (fun l => ?_) fun k => ?_
    · refine (Continuous.mul ?_ continuous_const).mul continuous_const
      exact (hw.2.2 _ (GlobalTheory.ConeTermCont.schrLin_comp_mem_adm B.ψ hψ (G.M'.co.e (shiftB σ H H' l)) _ hl) Φ hΦA).comp
        (continuous_subtype_val.prodMk continuous_const)
    · refine ((Continuous.mul ?_ hν).mul hab).measurable
      exact (continuous_schr B.ψ hψ hl (hw.isUSplitting.pres (k.1, h) Φ hΦA)).comp hsh
  · have h1 := hCb k.1 k.2 (GlobalTheory.XTermMaj.crd F E (l : AE F E))
    rw [← hS] at h1
    have h2 : ‖(X.ν l : ℂ)‖ₑ = 1 := by rw [← ofReal_norm_eq_enorm, Circle.norm_coe, ENNReal.ofReal_one]
    have h3 : ‖((absE F E l : ℝ) : ℂ) ^ z‖ₑ = ENNReal.ofReal ((absE F E l : ℝ) ^ (z : ℝ)) := by
      rw [← ofReal_norm_eq_enorm, norm_pow, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _), Real.rpow_natCast]
    simp only [enorm_mul, h2, h3, mul_one]
    rw [ENNReal.tsum_mul_right, ← mul_assoc]
    exact mul_le_mul_left h1 _
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI

end GlobalTheory.ThetaConeSwap

end
