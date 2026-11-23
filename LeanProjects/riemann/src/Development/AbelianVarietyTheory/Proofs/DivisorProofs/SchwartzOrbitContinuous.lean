import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

namespace GlobalTheory.ThKSoCont

variable {F : Type} [Field F] [NumberField F]

def mkA (a : mixedEmbedding.mixedSpace F) (b : Af F) : AF F :=
  (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a) b : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

theorem evI_mkA (a : mixedEmbedding.mixedSpace F) (b : Af F) : evI F (mkA a b) = a := by
  simp [evI, mkA]

theorem pureA_add {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (a b : (κ → Af F) → ℂ) :
    pureA F f (a + b) = pureA F f a + pureA F f b := by
  funext x; simp [pureA, mul_add]

theorem pureA_smul {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (c : ℂ) (a : (κ → Af F) → ℂ) :
    pureA F f (c • a) = c • pureA F f a := by
  funext x; simp [pureA]; ring

theorem pureA_zero {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : pureA F f (0 : (κ → Af F) → ℂ) = 0 := by
  funext x; simp [pureA]

theorem pureA_mkA {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (a : (κ → Af F) → ℂ)
    (y : κ → mixedEmbedding.mixedSpace F) (z : κ → Af F) : pureA F f a (fun i => mkA (y i) (z i)) = f y * a z := by
  simp only [pureA]
  congr 1
  congr 1
  funext i
  exact evI_mkA (y i) (z i)

theorem thetaSum_finset_sum {κ ι : Type} [Fintype κ] (s : Finset ι) (Φ : ι → (κ → AF F) → ℂ)
    (h : ∀ i ∈ s, Φ i ∈ schA F κ) : thetaSum F (∑ i ∈ s, Φ i) = ∑ i ∈ s, thetaSum F (Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [thetaSum]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      thetaSum_add F (h a (Finset.mem_insert_self a s)) (Submodule.sum_mem _ fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

open scoped Classical in

theorem soCont (hP : KP) : SoCont := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair m φ f u hconv hSo hSoLim h
  have hB := GlobalTheory.T.theta_basic_properties hP.base F E σ B n d X W M χX χW om r s r' s' hPair
  have hU := soDecayUnif hP F E σ B n d X W M χX χW om r s r' s' hPair
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
    hPair.weil.isUSplitting.pres
  haveI := hPair.good.haar
  have hfin : M.μ M.dom < ⊤ := GlobalTheory.UnitaryVol.measure_fundDom_lt_top hP.siegelSetUnitary hPair.base.cm
    (GlobalTheory.UnitaryVol.isHermND_map (GlobalTheory.SiegelSet.sigma_sigma hPair.base.cm) hPair.herm) hPair.good.dom
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩

  let So := M.So B.ψ B.τ₁
  let T' : Submodule ℂ ((Fin n × Fin d → Af F) → ℂ) :=
    { carrier := {a | ∀ g : SInf F (Fin n × Fin d), pureA F g a ∈ So}
      add_mem' := fun ha hb g => by rw [pureA_add]; exact So.add_mem (ha g) (hb g)
      zero_mem' := fun g => by rw [pureA_zero]; exact So.zero_mem
      smul_mem' := fun c a ha g => by rw [pureA_smul]; exact So.smul_mem c (ha g) }
  let T := SB (Fin n × Fin d → Af F) ⊓ T'

  have hslice : ∀ Φ ∈ So, ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      (fun z : Fin n × Fin d → Af F => Φ (fun i => mkA (y i) (z i))) ∈ T' := by
    intro Φ hΦ y
    induction hΦ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨g, ψ, h1, h2, h3, rfl⟩ := hΦ
      let a : (Fin n × Fin d → Af F) → ℂ := fun z => ∏ᶠ v, ψ v fun i => evFin F v (mkA 0 (z i))
      have e1 : (fun z : Fin n × Fin d → Af F => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g ψ (fun i => mkA (y i) (z i))) = g y • a := by
        funext z
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, a]
        congr 1
        congr 1
        funext i
        exact evI_mkA (y i) (z i)
      have e2 : ∀ g' : SInf F (Fin n × Fin d), pureA F g' a = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' ψ := fun g' => by
        funext x
        rfl
      rw [e1]
      refine T'.smul_mem _ fun g' => ?_
      rw [e2]
      exact Submodule.subset_span ⟨g', ψ, h1, h2, h3, rfl⟩
    | zero =>
      have e0 : (fun z : Fin n × Fin d → Af F => (0 : (Fin n × Fin d → AF F) → ℂ) (fun i => mkA (y i) (z i))) = 0 := rfl
      rw [e0]
      exact T'.zero_mem
    | add Φ Ψ _ _ hΦ hΨ => exact T'.add_mem hΦ hΨ
    | smul c Φ _ hΦ => exact T'.smul_mem c hΦ

  obtain ⟨C, hC⟩ := Submodule.exists_isCompl T
  have hdec : ∀ j, ∃ t ∈ T, ∃ c ∈ C, t + c = φ j := fun j =>
    Submodule.mem_sup.1 (hC.sup_eq_top ▸ Submodule.mem_top)
  choose t htT c hcC htc using hdec
  have hcSB : ∀ j, c j ∈ SB (Fin n × Fin d → Af F) := fun j => by
    have : c j = φ j - t j := by rw [← htc j]; abel
    rw [this]; exact Submodule.sub_mem _ (hconv j).1 (htT j).1

  have hred : ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ So →
      ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (t j) := by
    intro w hw
    have e : ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (t j) + ∑ j, pureA F (w j) (c j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [← pureA_add, htc j]
    have hΨ : ∑ j, pureA F (w j) (c j) ∈ So := by
      have : ∑ j, pureA F (w j) (c j) = ∑ j, pureA F (w j) (φ j) - ∑ j, pureA F (w j) (t j) := by
        rw [e]; abel
      rw [this]
      exact So.sub_mem hw (So.sum_mem fun j _ => (htT j).2 (w j))
    have h0 : ∀ y, ∑ j, w j y • c j = 0 := by
      intro y
      have h1 : ∑ j, w j y • c j ∈ T := by
        refine ⟨SB _ |>.sum_mem fun j _ => (SB _).smul_mem _ (hcSB j), ?_⟩
        have := hslice _ hΨ y
        have e' : (fun z : Fin n × Fin d → Af F => (∑ j, pureA F (w j) (c j)) (fun i => mkA (y i) (z i))) =
            ∑ j, w j y • c j := by
          funext z
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pureA_mkA]
        rwa [e'] at this
      have h2 : ∑ j, w j y • c j ∈ C := C.sum_mem fun j _ => C.smul_mem _ (hcC j)
      have := hC.inf_eq_bot ▸ (Submodule.mem_inf.2 ⟨h1, h2⟩)
      exact (Submodule.mem_bot ℂ).1 this
    rw [e, add_eq_left]
    funext x
    have := congrFun (h0 fun i => evI F (x i)) (fun i => (x i).2)
    simpa [pureA, Finset.sum_apply, evI] using this

  have hmem : ∀ (a : (Fin n × Fin d → Af F) → ℂ), a ∈ SB (Fin n × Fin d → Af F) → ∀ g : SInf F (Fin n × Fin d),
      pureA F g a ∈ schA F (Fin n × Fin d) := fun a ha g => Submodule.subset_span ⟨g, a, ha, rfl⟩
  have hmeas : ∀ Φ ∈ schA F (Fin n × Fin d),
      AEStronglyMeasurable (fun x => theta om Φ x h) (M.μ.restrict M.dom) := by
    intro Φ hΦ
    haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
    exact ((hB.1 Φ hΦ).1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hbd : ∀ a ∈ T, ∃ (C0 : ℝ) (k0 : ℕ), 0 ≤ C0 ∧ ∀ (g : SInf F (Fin n × Fin d)) x,
      ‖theta om (pureA F g a) x h‖ ≤ C0 * semK (Fin n × Fin d) k0 g * (ht h : ℝ) ^ k0 := by
    intro a ha
    obtain ⟨C0, k0, hC0⟩ := hU a ha.1 ha.2 0
    refine ⟨max C0 0, k0, le_max_right _ _, fun g x => ?_⟩
    have := hC0 g x h
    rw [pow_zero, mul_one] at this
    refine this.trans ?_
    gcongr
    exact le_max_left _ _
  have hint : ∀ a ∈ T, ∀ g : SInf F (Fin n × Fin d),
      Integrable (fun x => theta om (pureA F g a) x h) (M.μ.restrict M.dom) := by
    intro a ha g
    obtain ⟨C0, k0, -, hC0⟩ := hbd a ha
    exact Integrable.mono' (integrable_const (C0 * semK (Fin n × Fin d) k0 g * (ht h : ℝ) ^ k0))
      (hmeas _ (hmem a ha.1 g)) (ae_of_all _ fun x => hC0 g x)
  have hcont : ∀ a ∈ T, ∀ (v : ℕ → SInf F (Fin n × Fin d)) (g0 : SInf F (Fin n × Fin d)), Tendsto v atTop (𝓝 g0) →
      Tendsto (fun k => M.I om (pureA F (v k) a) h) atTop (𝓝 (M.I om (pureA F g0 a) h)) := by
    intro a ha v g0 hv
    obtain ⟨C0, k0, hC0p, hC0⟩ := hbd a ha
    have hsem : ∀ᶠ k in atTop, semK (Fin n × Fin d) k0 (v k) ≤ semK (Fin n × Fin d) k0 g0 + 1 := by
      have h1 := ((schwartz_withSeminorms ℂ _ ℂ).tendsto_nhds' v g0).1 hv
        (Finset.Iic (k0, k0)) 1 one_pos
      filter_upwards [h1] with k hk
      calc semK (Fin n × Fin d) k0 (v k) = semK (Fin n × Fin d) k0 ((v k - g0) + g0) := by rw [sub_add_cancel]
        _ ≤ semK (Fin n × Fin d) k0 (v k - g0) + semK (Fin n × Fin d) k0 g0 := map_add_le_add _ _ _
        _ ≤ semK (Fin n × Fin d) k0 g0 + 1 := by
          have : semK (Fin n × Fin d) k0 (v k - g0) < 1 := hk
          linarith
    simp only [Model.I]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ => C0 * (semK (Fin n × Fin d) k0 g0 + 1) * (ht h : ℝ) ^ k0)
      (Eventually.of_forall fun k => hmeas _ (hmem a ha.1 (v k))) ?_ (integrable_const _) ?_
    · filter_upwards [hsem] with k hk
      refine ae_of_all _ fun x => (hC0 (v k) x).trans ?_
      gcongr
    · exact ae_of_all _ fun x => ((hB.2 a ha.1 x h).tendsto g0).comp hv

  have hI : ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ So →
      M.I om (∑ j, pureA F (w j) (φ j)) h = ∑ j, M.I om (pureA F (w j) (t j)) h := by
    intro w hw
    rw [hred w hw]
    simp only [Model.I]
    rw [← integral_finset_sum _ fun j _ => hint (t j) (htT j) (w j)]
    congr 1
    funext x
    simp only [theta]
    rw [map_sum]
    exact thetaSum_finset_sum _ _ fun j _ => hpres _ _ (hmem _ (htT j).1 (w j))
  rw [hI f hSoLim]
  refine Tendsto.congr (fun k => (hI (u k) (hSo k)).symm) ?_
  exact tendsto_finset_sum _ fun j _ => hcont (t j) (htT j) (fun k => u k j) (f j) (hconv j).2

end GlobalTheory.ThKSoCont
