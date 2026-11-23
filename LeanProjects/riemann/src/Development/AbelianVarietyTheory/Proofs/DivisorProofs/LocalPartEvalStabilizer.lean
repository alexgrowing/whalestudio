import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCompactLocalSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriplePairLocalPartCaseAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleAbsPowerIntegrable
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LemF

theorem coneFin_finite_comb : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, GlobalTheory.ThK.LemF.IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ∃ (N : ℕ) (g : Fin N → (Fin b × Fin (b + a') → Fv F v) → ℂ) (c : Fin N → ℂ), (∀ i, g i ∈ SB (Fin b × Fin (b + a') → Fv F v)) ∧
        ∀ (L : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin b × Fin (b + a') → Fv F v) → ℂ)) (y : Fin b × Fin (b + a') → Fv F v),
          ∫ k, ∫ l, L (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l.1))) (locOp v (om (k.1, 1)) φ))) y *
            (X.ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ ∂μK = ∑ i, c i * L (g i) y := by
  intro hPr F E _ _ _ _ _ σ B b a' G G₁ H H' hCfg e he ei ev hloc K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ φ hφ
  classical
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  have hz1 : 1 ≤ (b + 2 - a') / 2 := by have := hT.geo.eBig; omega
  set w : idelesAt E (evFin F v) → ℂ := fun l => (X.ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2) with hw
  have hν : Continuous (X.ν : (AE F E)ˣ → Circle) := by
    have h := hT.chars.heckeα.1.div' hT.chars.heckeβ.1
    convert h using 1
    funext x
    exact MonoidHom.div_apply _ _ x
  have hwc : Continuous w := by
    have h1 : Continuous fun l : idelesAt E (evFin F v) => ((X.ν l.1 : Circle) : ℂ) := by
      have : Continuous (fun z : Circle => (z : ℂ)) := by fun_prop
      exact this.comp (hν.comp continuous_subtype_val)
    have h2 : Continuous fun l : idelesAt E (evFin F v) => ((absE F E l.1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp continuous_subtype_val))
    exact h1.mul (h2.pow _)
  have hwint : ∀ C : Set (Fv F v ⊗[F] E), IsCompact C →
      IntegrableOn w {l | ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ C} μ := by
    intro C hC
    refine Integrable.mono' (GlobalTheory.LocTateInt.integrableOn_absE_pow F E v μ hμ C hC _ hz1) hwc.aestronglyMeasurable (ae_of_all _ fun l => ?_)
    rw [hw]
    simp only [norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq, le_refl]
  have hu : Continuous fun l : idelesAt E (evFin F v) => ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) :=
    Units.continuous_val.comp ((GlobalTheory.Doubling.continuous_unitFin v).comp continuous_subtype_val)
  have hinner : ∀ ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ∃ (s : Finset ((Fin b × Fin (b + a') → Fv F v) → ℂ)) (c : ((Fin b × Fin (b + a') → Fv F v) → ℂ) → ℂ),
        (∀ g ∈ s, g ∈ SB (Fin b × Fin (b + a') → Fv F v)) ∧
        ∀ (L : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin b × Fin (b + a') → Fv F v) → ℂ)) (y : Fin b × Fin (b + a') → Fv F v),
          ∫ l, L (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l.1))) ψ)) y * w l ∂μ = ∑ g ∈ s, c g * L g y := by
    intro ψ hψ
    obtain ⟨Gh, hGc, ⟨C, hC, hout⟩, hGl⟩ := GlobalTheory.T.triple_pair_local_part_case_a hPr F E σ B b a' G G₁ H H' hCfg e he ei ev hloc X om om' om₁ om₁' hT hT₁ v ψ hψ
    have hGu : IsLocallyConstant fun l : idelesAt E (evFin F v) =>
        Gh ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := hGc.comp_continuous hu
    haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
    have hfin : (Set.range fun x : C => Gh x).Finite := (hGc.comp_continuous continuous_subtype_val).range_finite
    let s := (hfin.toFinset.erase 0).filter (fun g => g ∈ SB (Fin b × Fin (b + a') → Fv F v))
    let A : ((Fin b × Fin (b + a') → Fv F v) → ℂ) → Set (idelesAt E (evFin F v)) := fun g =>
      {l | Gh ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) = g}
    have hAm : ∀ g, MeasurableSet (A g) := fun g => (hGu.isOpen_fiber g).measurableSet
    have hs0 : ∀ g ∈ s, g ≠ 0 := fun g hg => (Finset.mem_erase.1 (Finset.mem_filter.1 hg).1).1
    have hAC : ∀ g ∈ s, A g ⊆ {l | ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ C} := by
      intro g hg l hl
      by_contra hn
      exact hs0 g hg ((show Gh _ = g from hl).symm.trans (hout _ hn))
    refine ⟨s, fun g => ∫ l in A g, w l ∂μ, fun g hg => (Finset.mem_filter.1 hg).2, fun L y => ?_⟩
    have hpt : ∀ l : idelesAt E (evFin F v), L (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l.1))) ψ)) y * w l =
        ∑ g ∈ s, (A g).indicator (fun l => L g y * w l) l := by
      intro l
      have hSBx : ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l.1))) ψ) ∈ SB (Fin b × Fin (b + a') → Fv F v) := by
        rw [← (hloc.2.1 v).2]
        exact Submodule.mem_map_of_mem (locOp_mem v _ ψ)
      rw [hGl l.1 l.2] at hSBx ⊢
      by_cases h0 : Gh ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) = 0
      · rw [h0, map_zero, Pi.zero_apply, zero_mul]
        refine (Finset.sum_eq_zero fun g hg => Set.indicator_of_notMem ?_ _).symm
        intro hl
        exact hs0 g hg ((show Gh _ = g from hl).symm.trans h0)
      · have hxs : Gh ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ s := by
          refine Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨h0, hfin.mem_toFinset.2 ?_⟩, hSBx⟩
          by_cases hm : ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ C
          · exact ⟨⟨_, hm⟩, rfl⟩
          · exact absurd (hout _ hm) h0
        rw [Finset.sum_eq_single_of_mem _ hxs (fun g _ hgx => Set.indicator_of_notMem (s := A g)
          (fun hl => hgx (show Gh _ = g from hl).symm) _), Set.indicator_of_mem (s := A _) (show l ∈ A _ from rfl)]
    have hI : ∀ g ∈ s, Integrable ((A g).indicator fun l => L g y * w l) μ := fun g hg =>
      IntegrableOn.integrable_indicator (((hwint C hC).mono_set (hAC g hg)).const_mul (L g y)) (hAm g)
    rw [integral_congr_ae (ae_of_all _ hpt), integral_finset_sum s hI]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [integral_indicator (hAm g), integral_const_mul, mul_comm]
  choose! s c hsSB hint using hinner
  obtain ⟨hKc, hFk⟩ := GlobalTheory.KFin.kFinite hPr F E σ B (b + 2) a' G X om om' hT K hK v φ hφ
  haveI : CompactSpace (KAt K (evFin F v)) := isCompact_iff_compactSpace.mp hKc
  haveI := hμK
  haveI : IsFiniteMeasure μK := CompactSpace.isFiniteMeasure
  have hSfin := hFk.range_finite
  let S := hSfin.toFinset
  let Bk : ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) → Set (KAt K (evFin F v)) := fun ψ =>
    {k | locOp v (om (k.1, 1)) φ = ψ}
  have hBm : ∀ ψ, MeasurableSet (Bk ψ) := fun ψ => (hFk.isOpen_fiber ψ).measurableSet
  have hSSB : ∀ ψ ∈ S, ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) := by
    intro ψ hψ
    obtain ⟨k, rfl⟩ := hSfin.mem_toFinset.1 hψ
    exact locOp_mem v _ φ
  let T := S.sigma s
  refine ⟨T.card, fun i => (T.equivFin.symm i).1.2,
    fun i => μK.real (Bk (T.equivFin.symm i).1.1) * c (T.equivFin.symm i).1.1 (T.equivFin.symm i).1.2, fun i => ?_, fun L y => ?_⟩
  · have h := (T.equivFin.symm i).2
    rw [Finset.mem_sigma] at h
    exact hsSB _ (hSSB _ h.1) _ h.2
  · have hpt : ∀ k : KAt K (evFin F v), ∫ l, L (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l.1))) (locOp v (om (k.1, 1)) φ))) y *
          (X.ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ =
        ∑ ψ ∈ S, (Bk ψ).indicator (fun _ => ∑ g ∈ s ψ, c ψ g * L g y) k := by
      intro k
      have hk : locOp v (om (k.1, 1)) φ ∈ S := hSfin.mem_toFinset.2 ⟨k, rfl⟩
      rw [Finset.sum_eq_single_of_mem _ hk
        (fun ψ _ hne => Set.indicator_of_notMem (s := Bk ψ) (fun h => hne (show locOp v (om (k.1, 1)) φ = ψ from h).symm) _),
        Set.indicator_of_mem (s := Bk _) (show k ∈ Bk _ from rfl)]
      refine (integral_congr_ae (ae_of_all _ fun l => ?_)).trans (hint _ (locOp_mem v _ φ) L y)
      simp only [hw]
      ring
    rw [integral_congr_ae (ae_of_all _ hpt), integral_finset_sum S (fun ψ _ => (integrable_const _).indicator (hBm ψ))]
    simp only [integral_indicator_const _ (hBm _), smul_eq_mul]
    rw [show (∑ i : Fin T.card, μK.real (Bk (T.equivFin.symm i).1.1) * c (T.equivFin.symm i).1.1 (T.equivFin.symm i).1.2 *
        L (T.equivFin.symm i).1.2 y) = ∑ x ∈ T, μK.real (Bk x.1) * c x.1 x.2 * L x.2 y from by
      rw [← Finset.sum_coe_sort T]
      exact Equiv.sum_comp T.equivFin.symm (fun x : T => μK.real (Bk x.1.1) * c x.1.1 x.1.2 * L x.1.2 y)]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [Complex.real_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by dsimp only; ring

end GlobalTheory.ThK.LemF

end
