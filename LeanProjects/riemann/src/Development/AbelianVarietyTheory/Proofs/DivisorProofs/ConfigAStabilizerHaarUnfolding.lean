import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarEigenTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerHaarEigenStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ConePure

section Abstract

open scoped SchwartzMap

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {T : Type} [MeasurableSpace T]
  {μ : Measure T}

theorem exists_integral_le (f : T → 𝓢(V, ℂ)) (hm : ∀ y, AEStronglyMeasurable (fun t => f t y) μ) (b : ℕ → ℕ → T → ℝ)
    (hbi : ∀ k n, Integrable (b k n) μ) (hb : ∀ k n t, SchwartzMap.seminorm ℂ k n (f t) ≤ b k n t) :
    ∃ g : 𝓢(V, ℂ), (∀ y, g y = ∫ t, f t y ∂μ) ∧ ∀ k n, SchwartzMap.seminorm ℂ k n g ≤ ∫ t, b k n t ∂μ := by
  obtain ⟨g, hg, -⟩ := GlobalTheory.SchwartzPettis.exists_integral f hm fun k n => ⟨_, hbi k n, hb k n⟩
  refine ⟨g, hg, fun k n => SchwartzMap.seminorm_le_bound ℂ k n g
    (integral_nonneg fun t => (apply_nonneg _ _).trans (hb k n t)) fun x => ?_⟩
  rw [show (g : V → ℂ) = fun y => ∫ t, f t y ∂μ from funext hg,
    (GlobalTheory.SchwartzPettis.iter_integral f hm (fun n => ⟨_, hbi 0 n, hb 0 n⟩) n).2.1]
  calc _ = ‖∫ t, ‖x‖ ^ k • iteratedFDeriv ℝ n (f t) x ∂μ‖ := by rw [integral_smul, norm_smul, norm_pow, norm_norm]
    _ ≤ _ := norm_integral_le_of_norm_le (hbi k n) (Eventually.of_forall fun t => by
      rw [norm_smul, norm_pow, norm_norm]
      exact (SchwartzMap.le_seminorm ℂ k n (f t) x).trans (hb k n t))

theorem exists_iter {S : Type} [MeasurableSpace S] {ν : Measure S} [IsFiniteMeasure ν] (f : S → T → 𝓢(V, ℂ))
    (hm : ∀ s y, AEStronglyMeasurable (fun t => f s t y) μ)
    (hm' : ∀ y, AEStronglyMeasurable (fun s => ∫ t, f s t y ∂μ) ν)
    (hb : ∀ k n, ∃ b : T → ℝ, Integrable b μ ∧ ∀ s t, SchwartzMap.seminorm ℂ k n (f s t) ≤ b t) :
    ∃ g : 𝓢(V, ℂ), ∀ y, g y = ∫ s, ∫ t, f s t y ∂μ ∂ν := by
  choose b hbi hb using hb
  choose g hg hgb using fun s => exists_integral_le (f s) (hm s) b hbi fun k n => hb k n s
  obtain ⟨h, hh, -⟩ := GlobalTheory.SchwartzPettis.exists_integral (μ := ν) g (fun y => by simpa only [hg] using hm' y)
    fun k n => ⟨_, integrable_const _, fun s => hgb s k n⟩
  exact ⟨h, fun y => by simp only [hh, hg]⟩

end Abstract

attribute [-instance] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.measAF in
open GroundTheory.Global GroundTheory.Global.IdeleGroup GlobalTheory.TateConv in

theorem exists_majorant (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (μ : Measure (AE F E)ˣ) [μ.IsHaarMeasure] {s : ℝ} (hs : 1 < s) {U : Set (Fin (Module.finrank F E) → Af F)}
    (hU : IsCompact U) : ∃ (N : ℕ) (m : (AE F E)ˣ → ℝ), Integrable m μ ∧ (∀ l, 0 ≤ m l) ∧ ∀ l : (AE F E)ˣ,
      (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U →
      (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) *
        (absE F E l : ℝ) ^ s ≤ m l := by
  obtain ⟨N, k, L, C, hk, hb⟩ := GlobalTheory.TateConv.bound F E hs hU
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : (μ.map (idl F E)).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ (idl F E)
  have h1 := ((integrable_zetaBound hs hk L).const_mul C).abs
  have h2 := h1.smul_measure_nnreal (c := Measure.haarScalarFactor (μ.map (idl F E)) (ideleMeasure E))
  rw [← Measure.isMulLeftInvariant_eq_smul] at h2
  refine ⟨N, _, (integrable_map_equiv (idl F E).toHomeomorph.toMeasurableEquiv _).1 h2, fun l => abs_nonneg _,
    fun l hl => ?_⟩
  have h3 := hb l
  rw [GlobalTheory.XTermMaj.maj, Set.indicator_of_mem hl, ← ENNReal.ofReal_mul (by positivity)] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).1 (h3.trans (ENNReal.ofReal_le_ofReal (le_abs_self _)))

theorem cone_mem : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Φ ∈ schA F (Fin b × Fin (b + a')) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Φ hΦ
  have hKeq : K = GlobalTheory.StabHaar.stabK (σ := σ) B G.V :=
    Subgroup.ext fun g => (hK g).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B G.V g).symm
  have hKc : IsCompact (K : Set (UA σ G.V.J)) := by
    have hX := hT.geo.hV
    obtain ⟨C, hCc, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B (b + 2) G.V _ _ hT.base hX
    rw [hKeq]
    exact hCc.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B G.V (GlobalTheory.T.isClosed_adelic_lattice_closure F E (b + 2) G.V hX.lat)) hsub
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  haveI : IsFiniteMeasure μK := ⟨isCompact_univ.measure_lt_top⟩
  have hz : 1 < (b + 2 - a') / 2 := by have := hT.geo.eBig; have := hC.ep; omega
  have hi₁ := fun (k : K) => GlobalTheory.T.config_a_haar_eigen_triple hKP F E σ B b a' G G₁ H H' hC μ hμ e he X om om' om₁ om₁' hT hT₁ _
    ((IsUWeilPair.isUSplitting hT.weil).pres (k.1, 1) Φ hΦ)
  have hi₂ := GlobalTheory.T.config_a_stabilizer_haar_eigen hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Φ hΦ
  obtain ⟨U, hU, hU0⟩ := GlobalTheory.ConeData.finsupp hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ 1
  obtain ⟨m, c, φ, hφ, hsum⟩ := GlobalTheory.ConeData.finite_parts hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ 1
  have hdec := GlobalTheory.ConeData.arch_decay hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ 1 U hU
  generalize (b + 2 - a') / 2 = z at hz hi₁ hi₂ ⊢
  obtain ⟨N, M, hM, hM0, hMb⟩ := exists_majorant F E μ (s := z) (by exact_mod_cast hz) hU
  have slice : ∀ c₀ : Fin b × Fin (b + a') → Af F, ∃ g : SInf F (Fin b × Fin (b + a')), ∀ y,
      g y = cone B G.M om e K μK μ (shiftA H H') X.ν z Φ
        (fun q => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y q), c₀ q)) := by
    intro c₀
    have hex : ∀ (k : K) (l : (AE F E)ˣ), ∃ f : SInf F (Fin b × Fin (b + a')), ∀ y,
        f y = e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Φ))
          (fun q => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y q), c₀ q)) := by
      intro k l
      by_cases hl : (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U
      · obtain ⟨C, hC⟩ := hdec c₀ 0 ∅
        obtain ⟨f, hf, -⟩ := hC k.1 k.2 l hl
        exact ⟨f, hf⟩
      · exact ⟨0, fun y => by rw [hU0 k.1 k.2 l hl]; rfl⟩
    choose f hf using hex
    have hval : ∀ k l y, (((X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) • f k l) y =
        e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Φ))
          (fun q => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y q), c₀ q)) * (X.ν l : ℂ) *
          ((absE F E l : ℝ) : ℂ) ^ z := fun k l y => by
      rw [SchwartzMap.smul_apply, hf, smul_eq_mul]
      ring
    obtain ⟨g, hg⟩ := exists_iter (μ := μ) (ν := μK) (fun k l => ((X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) • f k l)
      (fun k y => by simpa only [hval] using (hi₁ k _).1) (fun y => by simpa only [hval] using (hi₂ _).1) (fun p n => by
        obtain ⟨C, hC⟩ := hdec c₀ N {(p, n)}
        refine ⟨fun l => |C| * M l, hM.const_mul _, fun k l => ?_⟩
        rw [map_smul_eq_mul, norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg
          (NNReal.coe_nonneg _), ← Real.rpow_natCast]
        by_cases hl : (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U
        · obtain ⟨f', hf', hb⟩ := hC k.1 k.2 l hl
          rw [show f' = f k l from SchwartzMap.ext fun y => (hf' y).trans (hf k l y).symm, Finset.sup_singleton] at hb
          have h1 := hMb l hl
          have h2 : 0 ≤ (absE F E l : ℝ) ^ (z : ℝ) := by positivity
          have h3 : 0 ≤ (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) := by
            positivity
          refine (mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right (le_abs_self C) h3)) h2).trans ?_
          rw [mul_left_comm, mul_comm (_ ^ _)]
          exact mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
        · rw [show f k l = 0 from SchwartzMap.ext fun y => by rw [hf, hU0 k.1 k.2 l hl]; rfl, map_zero, mul_zero]
          exact mul_nonneg (abs_nonneg C) (hM0 l))
    exact ⟨g, fun y => by simp only [hg, hval, cone]⟩
  choose g hg using slice
  have key : cone B G.M om e K μK μ (shiftA H H') X.ν z Φ = ∑ j, pureA F (g (c j)) (φ j) := by
    funext x
    rw [Finset.sum_apply]
    simp only [pureA, hg, RingEquiv.symm_apply_apply, cone, ← integral_mul_const]
    rw [← integral_finset_sum _ fun j _ => by
      simpa only [← integral_mul_const] using (hi₂ fun q => ((x q).1, c j q)).mul_const (φ j fun q => (x q).2)]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    beta_reduce
    rw [← integral_finset_sum _ fun j _ => (hi₁ k fun q => ((x q).1, c j q)).mul_const (φ j fun q => (x q).2)]
    refine integral_congr_ae (Eventually.of_forall fun l => ?_)
    beta_reduce
    rw [hsum k.1 k.2 l x, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨g (c j), φ j, hφ j, rfl⟩

theorem cone_pure_mem : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (f : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ),
      (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) →
      cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (pure f φ) ∈ schA F (Fin b × Fin (b + a')) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ f φ hφ hv
  exact cone_mem hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ _
    (GlobalTheory.TensUniq.pure_mem_schA f φ hφ ((hv.and hT.geo.hM.std).mono fun v h => h.1.trans h.2))

end GlobalTheory.ConePure

end
