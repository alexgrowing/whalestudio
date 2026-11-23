import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarScalingByRealIdele
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Flow

theorem map_eq_of_conj {G H : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [MeasurableSpace H] [BorelSpace H] (e : G ≃+ H) (he : Continuous e) (hs : Continuous e.symm)
    (L : G → G) (L' : H → H) (hL' : Continuous L') (hc : ∀ X, e (L X) = L' (e X)) (c : ℝ≥0∞)
    (hH : ∀ ν : Measure H, ν.IsAddHaarMeasure → ν.map L' = c • ν)
    (μ : Measure G) [μ.IsAddHaarMeasure] : μ.map L = c • μ := by
  have hL : Continuous L := by
    have : L = fun X => e.symm (L' (e X)) := by
      funext X; rw [← hc, AddEquiv.symm_apply_apply]
    rw [this]
    exact hs.comp (hL'.comp he)
  have hν := hH (μ.map e) (e.isAddHaarMeasure_map μ he hs)
  have h1 : (μ.map L).map e = (c • μ).map e := by
    rw [Measure.map_map he.measurable hL.measurable, Measure.map_smul, ← hν,
      Measure.map_map hL'.measurable he.measurable]
    congr 1
    funext X
    exact hc X
  have h2 : ((μ.map L).map e).map e.symm = ((c • μ).map e).map e.symm := by rw [h1]
  rw [Measure.map_map hs.measurable he.measurable, Measure.map_map hs.measurable he.measurable] at h2
  have hid : (e.symm ∘ e : G → G) = id := by funext X; simp
  rwa [hid, Measure.map_id, Measure.map_id] at h2

section Coord

variable {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]

def coordEquiv {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    (Fin n → Fin M → A ⊗[F] E) ≃+ (Fin n × Fin M × Fin d → A) where
  toFun X p := (Algebra.TensorProduct.basis A b).repr (X p.1 p.2.1) p.2.2
  invFun Y a i := (Algebra.TensorProduct.basis A b).equivFun.symm (fun k => Y (a, i, k))
  left_inv X := by
    funext a i
    have := (Algebra.TensorProduct.basis A b).equivFun.symm_apply_apply (X a i)
    simpa using this
  right_inv Y := by
    funext ⟨a, i, k⟩
    have := (Algebra.TensorProduct.basis A b).equivFun.apply_symm_apply (fun k => Y (a, i, k))
    exact congrFun this k
  map_add' X Y := by
    funext p
    simp

theorem coordEquiv_smul {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) (a : A)
    (X : Fin n → Fin M → A ⊗[F] E) :
    coordEquiv b n M ((a ⊗ₜ[F] (1 : E)) • X) = fun p => a * coordEquiv b n M X p := by
  funext p
  have h : (a ⊗ₜ[F] (1 : E)) * X p.1 p.2.1 = a • X p.1 p.2.1 := by
    rw [Algebra.smul_def]; rfl
  simp [coordEquiv, h]

end Coord

theorem modulus_flow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (n M : ℕ) (μ : Measure (Fin n → Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure → ∀ x : ℝ, μ.map (fun X => ((τ (Multiplicative.ofAdd (x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X) = ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * n * M * x))) • μ := by
  intro F E _ _ _ _ _ σ hcm τ hτ n M μ hμ x
  obtain ⟨⟨hAlc, hAsc, hAt2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hAlc
  haveI := hAsc
  haveI := hAt2
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨hTR, -, -, -, -, -, hHom, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  haveI := hTR
  haveI := hBor n M
  have hd : Module.finrank F E = 2 := hcm.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hd
  obtain ⟨-, θ, hθ, hτx⟩ := hτ
  have hh := hHom 2 b
  let hm := hh.homeomorph
  have he : Continuous (coordEquiv (A := AF F) b n M) := by
    refine continuous_pi fun p => ?_
    have h1 : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E => X p.1 p.2.1 :=
      (continuous_apply p.2.1).comp (continuous_apply p.1)
    exact (continuous_apply p.2.2).comp (hh.continuous.comp h1)
  have hs : Continuous (coordEquiv (A := AF F) b n M).symm := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    have h1 : Continuous fun Y : Fin n × Fin M × Fin 2 → AF F => fun k => Y (a, i, k) :=
      continuous_pi fun k => continuous_apply _
    have h2 : (fun Y : Fin n × Fin M × Fin 2 → AF F => (coordEquiv (A := AF F) b n M).symm Y a i) =
        fun Y => hm.symm (fun k => Y (a, i, k)) := by
      funext Y
      apply hm.injective
      rw [Homeomorph.apply_symm_apply]
      funext k
      have := (Algebra.TensorProduct.basis (AF F) b).equivFun.apply_symm_apply (fun k => Y (a, i, k))
      exact congrFun this k
    rw [h2]
    exact hm.symm.continuous.comp h1
  have ht : 0 < Real.exp x := Real.exp_pos x
  refine map_eq_of_conj (coordEquiv (A := AF F) b n M) he hs _
    (fun y p => (show AF F from (θ (Real.exp x), 1)) * y p) ?_ ?_ _ ?_ μ
  · exact continuous_pi fun p => continuous_const.mul (continuous_apply p)
  · intro X
    rw [hτx x]
    exact coordEquiv_smul b n M _ X
  · intro ν hν
    have := GlobalTheory.CompanionTheory.AdelicFlow.map_scalar F hcm.1 θ hθ (Fin n × Fin M × Fin 2) ν (Real.exp x) ht
    rw [this]
    congr 2
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    simp only [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring

end GlobalTheory.CompanionTheory.SW.Flow
