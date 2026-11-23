import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCompactLocalSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriplePairLocalPartCaseAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleAbsPowerIntegrableStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeInteg

theorem integrable_cone_integrand : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ∀ l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
        Integrable (fun p : KAt K (evFin F v) × idelesAt E (evFin F v) =>
          l (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' p.2.1))) (locOp v (om (p.1.1, 1)) φ))) *
            (X.ν p.2.1 : ℂ) * ((absE F E p.2.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) (μK.prod μ) := by
  intro hPr F E _ _ _ _ _ σ B b a' G G₁ H H' hCfg e he ei ev hloc K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ φ hφ L
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
    refine Integrable.mono' (GlobalTheory.T.idele_abs_power_integrable F E v μ hμ C hC _ hz1) hwc.aestronglyMeasurable (ae_of_all _ fun l => ?_)
    rw [hw]
    simp only [norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq, le_refl]
  have hu : Continuous fun l : idelesAt E (evFin F v) => ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) :=
    Units.continuous_val.comp ((GlobalTheory.Doubling.continuous_unitFin v).comp continuous_subtype_val)
  have hinner : ∀ ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      Integrable (fun l : idelesAt E (evFin F v) =>
        L (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l.1))) ψ)) * w l) μ := by
    intro ψ hψ
    obtain ⟨Gh, hGc, ⟨C, hC, hout⟩, hGl⟩ := GlobalTheory.T.triple_pair_local_part_case_a hPr F E σ B b a' G G₁ H H' hCfg e he ei ev hloc X om om' om₁ om₁' hT hT₁ v ψ hψ
    have hGu : IsLocallyConstant fun l : idelesAt E (evFin F v) =>
        Gh ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := hGc.comp_continuous hu
    haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
    have hfin : (Set.range fun x : C => Gh x).Finite := (hGc.comp_continuous continuous_subtype_val).range_finite
    let s := hfin.toFinset.erase 0
    let A : ((Fin b × Fin (b + a') → Fv F v) → ℂ) → Set (idelesAt E (evFin F v)) := fun g =>
      {l | Gh ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) = g}
    have hAm : ∀ g, MeasurableSet (A g) := fun g => (hGu.isOpen_fiber g).measurableSet
    have hs0 : ∀ g ∈ s, g ≠ 0 := fun g hg => (Finset.mem_erase.1 hg).1
    have hAC : ∀ g ∈ s, A g ⊆ {l | ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ C} := by
      intro g hg l hl
      by_contra hn
      exact hs0 g hg ((show Gh _ = g from hl).symm.trans (hout _ hn))
    have hpt : ∀ l : idelesAt E (evFin F v), L (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l.1))) ψ)) * w l =
        ∑ g ∈ s, (A g).indicator (fun l => L g * w l) l := by
      intro l
      rw [hGl l.1 l.2]
      by_cases h0 : Gh ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) = 0
      · rw [h0, map_zero, zero_mul]
        refine (Finset.sum_eq_zero fun g hg => Set.indicator_of_notMem ?_ _).symm
        intro hl
        exact hs0 g hg ((show Gh _ = g from hl).symm.trans h0)
      · have hxs : Gh ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ s := by
          refine Finset.mem_erase.2 ⟨h0, hfin.mem_toFinset.2 ?_⟩
          by_cases hm : ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ C
          · exact ⟨⟨_, hm⟩, rfl⟩
          · exact absurd (hout _ hm) h0
        rw [Finset.sum_eq_single_of_mem _ hxs (fun g _ hgx => Set.indicator_of_notMem (s := A g)
          (fun hl => hgx (show Gh _ = g from hl).symm) _), Set.indicator_of_mem (s := A _) (show l ∈ A _ from rfl)]
    have hI : ∀ g ∈ s, Integrable ((A g).indicator fun l => L g * w l) μ := fun g hg =>
      IntegrableOn.integrable_indicator (((hwint C hC).mono_set (hAC g hg)).const_mul (L g)) (hAm g)
    exact (integrable_finsetSum s hI).congr (ae_of_all _ fun l => (hpt l).symm)
  obtain ⟨hKc, hFk⟩ := GlobalTheory.T.stabilizer_compact_local_schwartz hPr F E σ B (b + 2) a' G X om om' hT K hK v φ hφ
  haveI : CompactSpace (KAt K (evFin F v)) := isCompact_iff_compactSpace.mp hKc
  haveI := hμK
  haveI := hμ
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
  have hI : ∀ ψ ∈ S, Integrable (fun p : KAt K (evFin F v) × idelesAt E (evFin F v) =>
      (Bk ψ).indicator (fun _ => (1 : ℂ)) p.1 *
        (L (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' p.2.1))) ψ)) * w p.2)) (μK.prod μ) := fun ψ hψ =>
    Integrable.mul_prod ((integrable_const (1 : ℂ)).indicator (hBm ψ)) (hinner ψ (hSSB ψ hψ))
  refine (integrable_finsetSum S hI).congr (ae_of_all _ fun p => ?_)
  have hk : locOp v (om (p.1.1, 1)) φ ∈ S := hSfin.mem_toFinset.2 ⟨p.1, rfl⟩
  dsimp only
  rw [Finset.sum_eq_single_of_mem _ hk (fun ψ _ hne => by
      rw [Set.indicator_of_notMem (s := Bk ψ) (fun h => hne (show locOp v (om (p.1.1, 1)) φ = ψ from h).symm), zero_mul]),
    Set.indicator_of_mem (s := Bk _) (show p.1 ∈ Bk _ from rfl)]
  simp only [hw]
  ring

end GlobalTheory.ConeInteg

end
