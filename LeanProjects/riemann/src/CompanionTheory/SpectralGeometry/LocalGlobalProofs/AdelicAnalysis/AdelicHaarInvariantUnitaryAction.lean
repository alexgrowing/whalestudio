import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceGramDetNeZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MapMulVecEqOfTransposeMulMulEq
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdeleRingStableRangeOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HaarInv

def tupEquiv {K A : Type} [AddCommGroup K] [TopologicalSpace K] [AddCommGroup A] [TopologicalSpace A]
    {M d : ℕ} (Φ : K ≃ₜ (Fin d → A)) (hadd : ∀ x y, Φ (x + y) = Φ x + Φ y) :
    (Fin 1 → Fin M → K) ≃ₜ+ (Fin M × Fin d → A) where
  toFun X p := Φ (X 0 p.1) p.2
  invFun Y _ i := Φ.symm fun k => Y (i, k)
  left_inv X := by
    funext a i
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    simp
  right_inv Y := by
    funext p
    simp
  map_add' X Y := by
    funext p
    simp [hadd]
  continuous_toFun := by
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.2).comp
      (Φ.continuous.comp ((continuous_apply p.1).comp (continuous_apply 0)))
  continuous_invFun := by
    refine continuous_pi fun _ => continuous_pi fun i => ?_
    exact Φ.symm.continuous.comp (continuous_pi fun k => continuous_apply (i, k))

theorem map_eq_of_conj {V W : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] (e : V ≃ₜ W) (μ : Measure V)
    (T : V → V) (G : W → W) (hG : Measurable G) (hc : ∀ x, e (T x) = G (e x))
    (hinv : (μ.map e).map G = μ.map e) : μ.map T = μ := by
  have he : Measurable e := e.continuous.measurable
  have hes : Measurable e.symm := e.symm.continuous.measurable
  have hT : T = e.symm ∘ G ∘ e := by
    funext x
    simp [← hc x]
  calc μ.map T = ((μ.map e).map G).map e.symm := by
        rw [Measure.map_map hG he, Measure.map_map hes (hG.comp he), hT]
    _ = (μ.map e).map e.symm := by rw [hinv]
    _ = μ := by
        rw [Measure.map_map hes he]
        simp

end GlobalTheory.CompanionTheory.SW.HaarInv

open GlobalTheory.CompanionTheory.SW.HaarInv in
theorem GlobalTheory.CompanionTheory.SW.HaarInv.actW_map_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure → ∀ h : HA (AF F) σ J, μ.map (actW (AF F) σ J h) = μ := by
  intro F E _ _ _ _ _ σ hσ M J hJ μ _ h
  obtain ⟨⟨i3, i4, i5⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  letI : MeasurableSpace (AF F) := borel (AF F)
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨iR, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)
  haveI := hBor 1 M
  let b := Module.finBasis F E
  obtain ⟨B, -, hBdet, hB⟩ := GlobalTheory.CompanionTheory.SW.CoordMat.coord_orthogonal F E σ hσ M J hJ _ b
  obtain ⟨g, hg, hconj⟩ := hB (AF F) h
  let Φ := GlobalTheory.CompanionTheory.SW.TopK.coordHomeo (AF F) b
  have hadd : ∀ x y, Φ (x + y) = Φ x + Φ y := fun x y => by
    funext k
    simp [Φ, GlobalTheory.CompanionTheory.SW.TopK.coordHomeo]
  let e := tupEquiv (M := M) Φ hadd
  have hcomm : ∀ X, e.toHomeomorph (actW (AF F) σ J h X) = (fun x => g *ᵥ x) (e.toHomeomorph X) := by
    intro X
    have := hconj X
    funext p
    have hp := congrFun this p
    simpa [e, tupEquiv, Φ, GlobalTheory.CompanionTheory.SW.TopK.coordHomeo] using hp
  have hdet : IsUnit (B.map (algebraMap F (AF F))).det := by
    have : (B.map (algebraMap F (AF F))).det = algebraMap F (AF F) B.det := by
      rw [RingHom.map_det]
      rfl
    rw [this]
    exact (Ne.isUnit hBdet).map _
  haveI : (μ.map e.toHomeomorph).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hinv : (μ.map e.toHomeomorph).map (fun x => g *ᵥ x) = μ.map e.toHomeomorph :=
    GlobalTheory.CompanionTheory.Adelic.OrthHaar.map_mulVec_eq_of_transpose_mul_mul_eq (AF F) (GlobalTheory.CompanionTheory.AdeleStableRange.adeleRing_stableRange_one F) _ (μ.map e.toHomeomorph) (B.map (algebraMap F (AF F))) g hdet hg
  exact map_eq_of_conj e.toHomeomorph μ (actW (AF F) σ J h) (fun x => g *ᵥ x)
    (continuous_const.matrix_mulVec continuous_id).measurable hcomm hinv
