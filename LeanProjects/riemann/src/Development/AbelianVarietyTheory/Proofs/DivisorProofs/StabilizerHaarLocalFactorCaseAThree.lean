import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop

noncomputable section

namespace GlobalTheory.ConeSliceDecay

section Tate

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (AF Af Ainf)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE)
open scoped GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GroundTheory.Global GroundTheory.Global.IdeleGroup

attribute [local instance] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.topTens

private theorem exists_integrable_majorant (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (μ : Measure (AE F E)ˣ) [μ.IsHaarMeasure] {z : ℕ} (hz : 1 < z) {U : Set (Fin (Module.finrank F E) → Af F)} (hU : IsCompact U) :
    ∃ (N : ℕ) (T : (AE F E)ˣ → ℝ), Integrable T μ ∧ (∀ l, 0 ≤ T l) ∧ ∀ l : (AE F E)ˣ,
      (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U →
      (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) * (absE F E l : ℝ) ^ z ≤ T l := by
  have hs : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  obtain ⟨N, k, L, C, hk, hb⟩ := GlobalTheory.TateConv.bound F E hs hU
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : (μ.map (GlobalTheory.TateConv.idl F E)).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ (GlobalTheory.TateConv.idl F E)
  have h1 := ((integrable_zetaBound hs hk L).const_mul C).smul_measure_nnreal
    (c := Measure.haarScalarFactor (μ.map (GlobalTheory.TateConv.idl F E)) (ideleMeasure E))
  rw [← Measure.isMulLeftInvariant_eq_smul] at h1
  have h2 := (integrable_map_equiv (GlobalTheory.TateConv.idl F E).toHomeomorph.toMeasurableEquiv _).mp h1
  refine ⟨N, _, h2.abs, fun l => abs_nonneg _, fun l hl => ?_⟩
  have h3 := hb l
  rw [GlobalTheory.XTermMaj.maj, Set.indicator_of_mem hl, ← ENNReal.ofReal_mul (by positivity), Real.rpow_natCast] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).mp (h3.trans (ENNReal.ofReal_le_ofReal (le_abs_self _)))

end Tate

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

section Decay

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.DiffDecay GlobalTheory.XTermDecay

private theorem arch_decay_schA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ h, ∀ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U → ∀ (c : Fin b × Fin (b + a') → Af F) (N : ℕ) (s : Finset (ℕ × ℕ)),
      ∃ C : ℝ, ∀ k ∈ K, ∀ l : (AE F E)ˣ, (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U →
        ∃ f : SInf F (Fin b × Fin (b + a')), (∀ y, f y = e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, h) Φ)) (fun q => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y q), c q))) ∧
          (s.sup (schwartzSeminormFamily ℂ _ ℂ)) f ≤ C * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦA h U hU c N s
  have hKeq : K = GlobalTheory.StabHaar.stabK (σ := σ) B G.V :=
    Subgroup.ext fun g => (hK g).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B G.V g).symm
  have hKc : IsCompact (K : Set (UA σ G.V.J)) := by
    have hX := hT.geo.hV
    obtain ⟨C, hCc, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B (b + 2) G.V _ _ hT.base hX
    rw [hKeq]
    exact hCc.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B G.V (GlobalTheory.T.isClosed_adelic_lattice_closure F E (b + 2) G.V hX.lat)) hsub
  have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hT.weil
  obtain ⟨m, g, f, hg, hdec, hf⟩ := exists_decomp (fun k : K => om (k.1, h) Φ)
    (fun k => hw.isUSplitting.pres (k.1, h) Φ hΦA) fun l hl => by
      have hc := (hw.2.2 l hl Φ hΦA).comp
        (continuous_id.prodMk continuous_const : Continuous fun g : UA σ G.V.J => (g, h))
      obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hc.continuousOn
      exact ⟨C, fun k => hC k.1 k.2⟩
  obtain ⟨t, ht⟩ := GlobalTheory.T.symplectic_trace_basis_exists F E σ _ _ G.V.J G.W.J H.x H.y H'.x H'.y hC.hH.xy (by
    rw [form_swap hT.base.cm hT.geo.hW.skew, hC.hH'.xy, map_one])
  let S := fun j => G.M.co.e (inclR (F := F) (AF F) (Module.finBasis F E j) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
  let U' := fun i => G.M.co.e (Matrix.vecMulVec (inclR (F := F) (AF F) (t i) • incV F H.y) (incV F H'.x))
  have hp : Continuous ⇑(Finset.sup s (schwartzSeminormFamily ℂ (Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F) ℂ)) :=
    Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm i
  choose C hCb using fun j => slice_decay B.ψ hT.base.std S U' (fun i j => by rw [← G.M.co.form]; convert ht i j)
    (sliceL c ∘ₗ e) (exists_slice_clm hT.geo.hM he c) (fun i a Ψ hΨ => by
      have := he.inv (Matrix.vecMulVec (a • inclR (F := F) (AF F) (t i) • incV F H.y) (incV F H'.x)) (Or.inl ⟨_, rfl⟩) Ψ hΨ
      rw [Matrix.smul_vecMulVec, Darboux.rho, map_smul] at this
      exact congrArg (sliceL c) this) (hg j) (f j) (hf j) hU _ hp N
  refine ⟨∑ j, C j, fun k hk l hl => ?_⟩
  choose f₁ hf₁ hb₁ using fun j => hCb j ⟨k, hk⟩ (GlobalTheory.XTermMaj.crd F E (l : AE F E)) hl
  have hS : G.M.co.e (shiftA H H' l) = ∑ i, GlobalTheory.XTermMaj.crd F E (l : AE F E) i • S i := by
    simp only [S, ← map_smul, ← map_sum, ← smul_assoc, ← Finset.sum_smul]
    congr 2
    rw [shiftA]
    congr 1
    refine ((Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun (l : AE F E)).symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  refine ⟨∑ j, f₁ j, fun y => ?_, ?_⟩
  · have h1 := hdec ⟨k, hk⟩
    simp only at h1
    rw [h1, Darboux.rho, hS]
    change coeL (∑ j, f₁ j) y = (sliceL c ∘ₗ e) (schrL B.ψ _ _) y
    rw [map_sum, map_sum, map_sum]
    exact congrFun (Finset.sum_congr rfl fun j _ => hf₁ j) y
  · rw [Finset.sum_mul]
    exact (Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _).trans (Finset.sum_le_sum fun j _ => hb₁ j)

end Decay

section Support

open GlobalTheory.XTermSupp

private theorem finsupp_schA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ h, ∃ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U ∧
      ∀ k ∈ K, ∀ l : (AE F E)ˣ, (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∉ U → e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, h) Φ)) = 0 := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ' h
  have hstd := hT.base.std
  obtain ⟨C, hCc, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B (b + 2) G.V _ _ hT.base hT.geo.hV
  choose c hc using trace_mul_dual (F := F) (E := E)
  have hO := fun i => rho_om_fixed G.M B.ψ hstd.1 hT.weil hCc h Φ hΦ'
    (inclR (F := F) (AF F) (σ (c i)) • Matrix.vecMulVec (incV F H.y) (incV F H'.x))
  obtain ⟨U, hU, hUm⟩ := GlobalTheory.ScalarAnnih.exists_compact_annihilator_finiteAdeles_traceChar F B.ψ hstd.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hstd) _
    (Filter.eventually_all.2 hO)
  refine ⟨Set.pi Set.univ fun _ => U, isCompact_univ_pi fun _ => hU, fun k hk l hl => ?_⟩
  by_contra hne
  refine hl fun i _ => hUm _ fun a ha => ?_
  have hfix := ha i k (hsub ((hK k).1 hk))
  have hΨ : om (k, h) Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := (IsUWeilPair.isUSplitting hT.weil).pres _ _ hΦ'
  have h1 := congrArg e (rho_comm G.M.co B.ψ (shiftA H H' l) (pairA F 0 a • inclR (F := F) (AF F) (σ (c i)) •
    Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (om (k, h) Φ))
  rw [hfix, map_smul, he.inv _ (Or.inl ⟨pairA F 0 a • inclR (F := F) (AF F) (σ (c i)) • incV F H.y, by
      rw [Matrix.smul_vecMulVec, Matrix.smul_vecMulVec]⟩) _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hstd _ _ hΨ),
    symp_shiftA hT.base.cm hT.geo.hW.skew H H' hC.hH.xy hC.hH'.xy, hc] at h1
  have h2 : pairA F 0 a * GlobalTheory.XTermMaj.crd F E (l : AE F E) i = pairA F 0 (a * (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) :=
    Prod.ext (zero_mul _) rfl
  rw [h2] at h1
  exact (smul_left_injective ℂ hne (h1.symm.trans (one_smul ℂ _).symm))

end Support

private theorem translate_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (a : V) (c : ℂ) (n m : ℕ) (t : V) :
    ‖t‖ ^ n * ‖iteratedFDeriv ℝ m (fun s => f (s + a) * c) t‖ ≤
      (1 + ‖a‖) ^ n * 2 ^ n * ((Finset.Iic (n, m)).sup (schwartzSeminormFamily ℂ V ℂ)) f * ‖c‖ := by
  have h1 : (fun s => f (s + a) * c) = fun s => (c • (f : V → ℂ)) (s + a) := by
    funext s
    simp [mul_comm]
  rw [h1, iteratedFDeriv_comp_add_right, iteratedFDeriv_const_smul_apply (f.smooth m).contDiffAt, norm_smul]
  have h2 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (n, m)) (k := n) (n := m) le_rfl le_rfl f (t + a)
  have h3 : ‖t‖ ≤ (1 + ‖a‖) * (1 + ‖t + a‖) := by
    have : ‖t‖ ≤ ‖t + a‖ + ‖a‖ := by simpa using norm_sub_le (t + a) a
    nlinarith [norm_nonneg a, norm_nonneg (t + a), mul_nonneg (norm_nonneg a) (norm_nonneg (t + a))]
  calc ‖t‖ ^ n * (‖c‖ * ‖iteratedFDeriv ℝ m f (t + a)‖)
      ≤ ((1 + ‖a‖) * (1 + ‖t + a‖)) ^ n * (‖c‖ * ‖iteratedFDeriv ℝ m f (t + a)‖) := by gcongr
    _ = (1 + ‖a‖) ^ n * ((1 + ‖t + a‖) ^ n * ‖iteratedFDeriv ℝ m f (t + a)‖) * ‖c‖ := by rw [mul_pow]; ring
    _ ≤ (1 + ‖a‖) ^ n * (2 ^ n * ((Finset.Iic (n, m)).sup (schwartzSeminormFamily ℂ V ℂ)) f) * ‖c‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) (norm_nonneg c)
    _ = _ := by ring

private theorem slice_dominated : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ x : Fin b × Fin (b + a') → AF F,
      ∀ n m : ℕ, ∃ Bd : K → (AE F E)ˣ → ℝ, (∀ k, Integrable (Bd k) μ) ∧ Integrable (fun k => ∫ l, Bd k l ∂μ) μK ∧
        ∀ k l t, ‖t‖ ^ n * ‖iteratedFDeriv ℝ m (fun s => (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) (x + GlobalTheory.ThetaTransform.embR s) * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2))) t‖ ≤ Bd k l := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT _ Ψ hΨ x n m
  have hz : 1 < (b + 2 - a') / 2 := by
    have h1 := hT.geo.eBig
    omega
  obtain ⟨K', -, -, hK', hKc, -, -⟩ := GlobalTheory.StabHaar.stabEx hKP.base F E σ B (b + 2) G.V _ _ hT.base hT.geo.hV
  obtain rfl : K' = K := Subgroup.ext fun g => (hK' g).trans (hK g).symm
  haveI : CompactSpace K' := isCompact_iff_compactSpace.mp hKc
  obtain ⟨U, hU, hU0⟩ := finsupp_schA F E σ B b a' G G₁ H H' hC K' hK e he X om om' hT Ψ hΨ 1
  obtain ⟨N, T, hTi, hT0, hTb⟩ := exists_integrable_majorant F E μ hz hU
  obtain ⟨C, hCb⟩ := arch_decay_schA F E σ B b a' G G₁ H H' hC K' hK e he X om om' hT Ψ hΨ 1 U hU (fun q => (x q).2) N
    (Finset.Iic (n, m))
  let a : Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F := fun q => InfiniteAdeleRing.ringEquiv_mixedSpace F (x q).1
  refine ⟨fun _ l => (1 + ‖a‖) ^ n * 2 ^ n * |C| * T l, fun _ => hTi.const_mul _, integrable_const _, fun k l t => ?_⟩
  by_cases hl : (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U
  · obtain ⟨f, hf, hfb⟩ := hCb k.1 k.2 l hl
    have h1 : (fun s => (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) (x + GlobalTheory.ThetaTransform.embR s) * (X.ν l : ℂ) *
        ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2))) =
        fun s => f (s + a) * ((X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) := by
      funext s
      rw [hf, mul_assoc]
      refine congrArg (· * _) (congrArg _ (funext fun q => ?_))
      refine Prod.ext ?_ (add_zero _)
      show (x q).1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (s q) =
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (s q + InfiniteAdeleRing.ringEquiv_mixedSpace F (x q).1)
      rw [map_add, RingEquiv.symm_apply_apply, add_comm]
    rw [h1]
    refine (translate_le f a _ n m t).trans ?_
    rw [norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    have h2 := hTb l hl
    have h0 : 0 ≤ (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    have h3 := hfb.trans (mul_le_mul_of_nonneg_right (le_abs_self C) h0)
    calc _ ≤ (1 + ‖a‖) ^ n * 2 ^ n * (|C| * (1 + ∑ i, ∑ v : InfinitePlace F,
            ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ))) * (absE F E l : ℝ) ^ ((b + 2 - a') / 2) := by
          gcongr
      _ = (1 + ‖a‖) ^ n * 2 ^ n * |C| * ((1 + ∑ i, ∑ v : InfinitePlace F,
            ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) * (absE F E l : ℝ) ^ ((b + 2 - a') / 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  · rw [hU0 k.1 k.2 l hl]
    simp only [Pi.zero_apply, zero_mul, iteratedFDeriv_fun_zero, norm_zero, mul_zero]
    exact mul_nonneg (by positivity) (hT0 l)

end GlobalTheory.ConeSliceDecay

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

theorem _root_.GlobalTheory.T.stabilizer_haar_local_factor_case_a_three : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ x : Fin b × Fin (b + a') → AF F,
      ∀ n m : ℕ, ∃ Bd : K → (AE F E)ˣ → ℝ, (∀ k, Integrable (Bd k) μ) ∧ Integrable (fun k => ∫ l, Bd k l ∂μ) μK ∧
        ∀ k l t, ‖t‖ ^ n * ‖iteratedFDeriv ℝ m (fun s => (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) (x + GlobalTheory.ThetaTransform.embR s) * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2))) t‖ ≤ Bd k l :=
  GlobalTheory.ConeSliceDecay.slice_dominated

end
