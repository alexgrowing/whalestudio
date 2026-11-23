import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEvaluationStabilizerVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteParts

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeExch

open scoped Classical in

theorem admissible_integral_exchange {F : Type} [Field F] [NumberField F] {κ T : Type} [Fintype κ] [MeasurableSpace T] (μ : Measure T) {m : ℕ}
    (φ : Fin m → (κ → Af F) → ℂ) (hφ : ∀ j, φ j ∈ SB _) (f : Fin m → T → SInf F κ)
    (hm : ∀ j y, AEStronglyMeasurable (fun t => f j t y) μ)
    (hb : ∀ j k n, ∃ b : T → ℝ, Integrable b μ ∧ ∀ t, SchwartzMap.seminorm ℂ k n (f j t) ≤ b t)
    (D : T → (κ → AF F) → ℂ) (hD : ∀ t, D t = ∑ j, pureA F (f j t) (φ j)) :
    (fun y => ∫ t, D t y ∂μ) ∈ schA F κ ∧ ∀ l ∈ (adeleClass F).adm κ,
      Integrable (fun t => l (D t)) μ ∧ l (fun y => ∫ t, D t y ∂μ) = ∫ t, l (D t) ∂μ := by
  choose g hg hL using fun j => GlobalTheory.SchwartzPettis.exists_integral (f j) (hm j) (hb j)
  have hi : ∀ j y, Integrable (fun t => f j t y) μ := fun j y =>
    (hL j ((BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ))).1
  have e : (fun y => ∫ t, D t y ∂μ) = ∑ j, pureA F (g j) (φ j) := by
    funext y
    simp only [hD, Finset.sum_apply, pureA]
    rw [integral_finset_sum _ fun j _ => (hi j _).mul_const _]
    exact Finset.sum_congr rfl fun j _ => by rw [integral_mul_const, hg]
  rw [e]
  refine ⟨Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨g j, φ j, hφ j, rfl⟩, fun l hl => ?_⟩
  choose L hLl using fun j => hl (φ j) (hφ j)
  simp only [hD, map_sum, hLl]
  refine ⟨integrable_finset_sum _ fun j _ => (hL j _).1, ?_⟩
  rw [integral_finset_sum _ fun j _ => (hL j _).1]
  exact Finset.sum_congr rfl fun j _ => (hL j _).2

open scoped Classical in

theorem proj_mem_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (y : κ → AF F) :
    (LinearMap.proj y : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := fun g _ =>
  ⟨g (fun i => (y i).2) • (BoundedContinuousFunction.evalCLM ℂ fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ), fun f => mul_comm _ _⟩

theorem aesm_slice {A C Y : Type} [MeasurableSpace A] [MeasurableSpace C] [MeasurableSpace Y] [TopologicalSpace Y]
    [FirstCountableTopology Y] (μ : Measure A) (ν : Measure C) (ρ : Measure Y) [SFinite μ] [SFinite ν] [SFinite ρ]
    [ρ.IsOpenPosMeasure] (D : A × C → Y → ℂ) (hc : ∀ t, Continuous (D t))
    (hm : AEStronglyMeasurable (fun p : A × (C × Y) => D (p.1, p.2.1) p.2.2) (μ.prod (ν.prod ρ))) (y : Y) :
    AEStronglyMeasurable (fun t => D t y) (μ.prod ν) := by
  have h1 : AEStronglyMeasurable (fun p : (A × C) × Y => D p.1 p.2) ((μ.prod ν).prod ρ) :=
    hm.comp_measurePreserving (measurePreserving_prodAssoc μ ν ρ)
  have h2 : ∀ᵐ y ∂ρ, AEStronglyMeasurable (fun t => D t y) (μ.prod ν) := h1.prodMk_right
  obtain ⟨u, hu, hy⟩ := mem_closure_iff_seq_limit.1 (Measure.dense_of_ae h2 y)
  exact aestronglyMeasurable_of_tendsto_ae atTop hu (Eventually.of_forall fun t => ((hc t).tendsto y).comp hy)

theorem sfinite_of_finite {A : Type} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ] : SFinite μ := inferInstance

theorem sfinite_of_haar {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [MeasurableSpace A] (μ : Measure A) [μ.IsHaarMeasure] : SFinite μ := inferInstance

theorem exists_integrable_maj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (μ : Measure (AE F E)ˣ) [μ.IsHaarMeasure] {z : ℕ} (hz : 2 ≤ z) {U : Set (Fin (Module.finrank F E) → Af F)}
    (hU : IsCompact U) : ∃ N : ℕ,
      Integrable (fun l : (AE F E)ˣ => (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal * (absE F E l : ℝ) ^ z) μ := by
  have hs : (1 : ℝ) < z := by exact_mod_cast hz
  obtain ⟨N, k, L, C, hk, hb⟩ := GlobalTheory.TateConv.bound F E hs hU
  refine ⟨N, ?_⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : T2Space (Af F) := (Topology.IsEmbedding.of_comp (f := fun x : Af F => ((0, x) : AF F)) (by fun_prop) continuous_snd
    Topology.IsEmbedding.id).t2Space
  have hc : Continuous fun l : (AE F E)ˣ => GlobalTheory.XTermMaj.crd F E (l : AE F E) :=
    (IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun.toLinearMap).comp Units.continuous_val
  have hm : Measurable fun l : (AE F E)ˣ => GlobalTheory.XTermMaj.maj F E N U (l : AE F E) := by
    refine Measurable.indicator (s := {l : (AE F E)ˣ | (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U})
      (f := fun l : (AE F E)ˣ => ENNReal.ofReal
        ((1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)))) ?_ ?_
    · refine (Continuous.measurable ?_).pow_const _ |>.ennreal_ofReal
      exact continuous_const.add (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun v _ =>
        ((continuous_apply v).comp (continuous_fst.comp ((continuous_apply i).comp hc))).norm)
    · exact (hU.isClosed.preimage (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp hc))).measurableSet
  have ha : Continuous fun l : (AE F E)ˣ => (absE F E l : ℝ) := NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE
  refine ⟨(hm.ennreal_toReal.mul (ha.pow z).measurable).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun l => le_trans ?_ (hb l)) (GlobalTheory.TateConv.lintegral_bound_lt_top F E μ hs hk L C)
  rw [Real.enorm_of_nonneg (by positivity), ENNReal.ofReal_mul ENNReal.toReal_nonneg, Real.rpow_natCast]
  gcongr
  exact ENNReal.ofReal_toReal_le

theorem cone_adm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Ψ ∈ schA F (Fin b × Fin (b + a')) ∧
      ∀ L ∈ (adeleClass F).adm (Fin b × Fin (b + a')),
        Integrable (fun t : K × (AE F E)ˣ => L (e (G.M.co.rho B.ψ (shiftA H H' t.2) (om (t.1.1, 1) Ψ))) * (X.ν t.2 : ℂ) *
          ((absE F E t.2 : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) (μK.prod μ) ∧
        L (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Ψ) =
          ∫ k, ∫ l, L (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ))) * (X.ν l : ℂ) *
            ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ ∂μK := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Ψ hΨ
  classical
  have hKeq : K = GlobalTheory.StabHaar.stabK (σ := σ) B G.V :=
    Subgroup.ext fun g => (hK g).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B G.V g).symm
  have hKc : IsCompact (K : Set (UA σ G.V.J)) := by
    have hX := hT.geo.hV
    obtain ⟨C, hCc, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B (b + 2) G.V _ _ hT.base hX
    rw [hKeq]
    exact hCc.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B G.V (GlobalTheory.T.isClosed_adelic_lattice_closure F E (b + 2) G.V hX.lat)) hsub
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  haveI : IsFiniteMeasure μK := ⟨isCompact_univ.measure_lt_top⟩
  obtain ⟨v1, v2, v3, v4⟩ := GlobalTheory.IwInt.ideleTop (F := F) (E := E)
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI := sfinite_of_finite μK
  haveI := sfinite_of_haar μ
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  letI : MeasurableSpace (Fin b × Fin (b + a') → AF F) := borel _
  haveI : BorelSpace (Fin b × Fin (b + a') → AF F) := ⟨rfl⟩
  have hz : 2 ≤ (b + 2 - a') / 2 := by have := hT.geo.eBig; omega
  have hS := IsUWeilPair.isUSplitting hT.weil
  set z := (b + 2 - a') / 2 with hzdef
  let D₀ : K × (AE F E)ˣ → Fn F b (b + a') := fun t => e (G.M.co.rho B.ψ (shiftA H H' t.2) (om (t.1.1, 1) Ψ))
  let w : K × (AE F E)ˣ → ℂ := fun t => (X.ν t.2 : ℂ) * ((absE F E t.2 : ℝ) : ℂ) ^ z
  have hD₀ : ∀ t, D₀ t ∈ schA F (Fin b × Fin (b + a')) := fun t =>
    he.maps _ (GlobalTheory.HeisSchA.rho_mem_schA _ _ hT.base.std _ _ (hS.pres _ _ hΨ))
  have hmeas : ∀ y, AEStronglyMeasurable (fun t => (w t • D₀ t) y) (μK.prod μ) := by
    refine aesm_slice μK μ Measure.addHaar (fun t => w t • D₀ t)
      (fun t => (GlobalTheory.ThKOp.continuous_of_mem_schA (hD₀ t)).const_smul (w t)) ?_
    refine (GlobalTheory.T.config_a_evaluation_stabilizer_vanishing hKP F E σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ Measure.addHaar
      inferInstance).congr (Eventually.of_forall fun p => ?_)
    simp only [D₀, w, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨m, c, φ, hφ, hfin⟩ := GlobalTheory.ConeData.finite_parts hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' hT Ψ hΨ 1
  obtain ⟨U, hU, hsupp⟩ := GlobalTheory.ConeData.finsupp hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' hT Ψ hΨ 1
  have hdec := GlobalTheory.ConeData.arch_decay hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' hT Ψ hΨ 1 U hU
  obtain ⟨N, hN⟩ := exists_integrable_maj F E μ hz hU
  have hsl : ∀ j (t : K × (AE F E)ˣ), ∃ f : SInf F (Fin b × Fin (b + a')),
      ∀ y, f y = D₀ t fun q => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y q), c j q) := fun j t => by
    by_cases hl : (fun i => (GlobalTheory.XTermMaj.crd F E (t.2 : AE F E) i).2) ∈ U
    · obtain ⟨C, hCb⟩ := hdec (c j) 0 ∅
      obtain ⟨f, hf, -⟩ := hCb t.1.1 t.1.2 t.2 hl
      exact ⟨f, hf⟩
    · exact ⟨0, fun y => (congrFun (hsupp t.1.1 t.1.2 t.2 hl) _).symm⟩
  choose f hf using hsl
  have hb : ∀ j k n, ∃ β : K × (AE F E)ˣ → ℝ, Integrable β (μK.prod μ) ∧
      ∀ t, SchwartzMap.seminorm ℂ k n (w t • f j t) ≤ β t := fun j k n => by
    obtain ⟨C, hCb⟩ := hdec (c j) N {(k, n)}
    refine ⟨fun t => C * ((GlobalTheory.XTermMaj.maj F E N U (t.2 : AE F E)).toReal * (absE F E t.2 : ℝ) ^ z),
      (hN.const_mul C).comp_snd μK, fun t => ?_⟩
    have hw : ‖w t‖ = (absE F E t.2 : ℝ) ^ z := by
      simp only [w, norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq]
    beta_reduce
    rw [map_smul_eq_mul, hw, mul_comm, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    by_cases hl : (fun i => (GlobalTheory.XTermMaj.crd F E (t.2 : AE F E) i).2) ∈ U
    · obtain ⟨f', hf', hle⟩ := hCb t.1.1 t.1.2 t.2 hl
      rw [show f j t = f' from SchwartzMap.ext fun y => (hf j t y).trans (hf' y).symm, GlobalTheory.XTermMaj.maj,
        Set.indicator_of_mem hl, ENNReal.toReal_ofReal (Real.rpow_nonneg (by positivity) _)]
      rwa [Finset.sup_singleton] at hle
    · rw [show f j t = 0 from SchwartzMap.ext fun y => (hf j t y).trans (congrFun (hsupp t.1.1 t.1.2 t.2 hl) _),
        GlobalTheory.XTermMaj.maj, Set.indicator_of_notMem hl, map_zero, ENNReal.toReal_zero, mul_zero]
  have key := admissible_integral_exchange (μK.prod μ) φ hφ (fun j t => w t • f j t)
    (fun j y => (hmeas _).congr (Eventually.of_forall fun t => congrArg (w t * ·) (hf j t y).symm)) hb
    (fun t => w t • D₀ t) (fun t => by
      funext y
      rw [Pi.smul_apply, smul_eq_mul, show D₀ t y = _ from hfin t.1.1 t.1.2 t.2 y, Finset.mul_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [pureA, SchwartzMap.smul_apply, smul_eq_mul, hf, RingEquiv.symm_apply_apply, mul_assoc]
      rfl)
  have hcone : cone B G.M om e K μK μ (shiftA H H') X.ν z Ψ = fun y => ∫ t, (w t • D₀ t) y ∂(μK.prod μ) := by
    funext y
    refine Eq.trans ?_ (integral_prod _ (key.2 _ (proj_mem_adm y)).1).symm
    refine integral_congr_ae (Eventually.of_forall fun k => integral_congr_ae (Eventually.of_forall fun l => ?_))
    simp only [D₀, w, LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hcone]
  refine ⟨key.1, fun L hL => ?_⟩
  obtain ⟨h1, h2⟩ := key.2 L hL
  have h3 : ∀ t, L (w t • D₀ t) = L (D₀ t) * (X.ν t.2 : ℂ) * ((absE F E t.2 : ℝ) : ℂ) ^ z := fun t => by
    rw [map_smul, smul_eq_mul, mul_comm, mul_assoc]
  simp only [h3] at h1
  refine ⟨h1, h2.trans ?_⟩
  simp only [h3]
  exact integral_prod _ h1

theorem weilOp_cone : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ x : UA σ G₁.V.J × UA σ G₁.W.J,
      om₁ x (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Ψ) =
        fun y => ∫ k, ∫ l, om₁ x (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ))) y * (X.ν l : ℂ) *
          ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ ∂μK := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Ψ hΨ x
  funext y
  exact ((cone_adm hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Ψ hΨ).2 _
    ((IsUWeilPair.isUSplitting hT₁.weil).adm x _ (proj_mem_adm y))).2

theorem weilOp_cone_ae : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ x : UA σ G₁.V.J × UA σ G₁.W.J,
      ∀ μY : @Measure (Fin b × Fin (b + a') → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μY →
      om₁ x (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Ψ) =ᵐ[μY] (fun y => ∫ k, ∫ l, om₁ x (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ))) y * (X.ν l : ℂ) *
          ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ ∂μK) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Ψ hΨ x μY _
  rw [weilOp_cone hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Ψ hΨ x]

end GlobalTheory.ConeExch

end
