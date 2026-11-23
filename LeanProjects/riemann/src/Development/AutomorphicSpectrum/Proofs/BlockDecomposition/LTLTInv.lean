import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerToL

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp

section LeftTranslation

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem LT_coeFn (x : G n) (u : Lp V 2 μ) :
    (LT μ x u : G n → V) =ᵐ[μ] fun g => u (x⁻¹ * g) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_mul_left μ x⁻¹)

theorem LT_LT_inv (x : G n) (u : Lp V 2 μ) : LT μ x (LT μ x⁻¹ u) = u := by
  apply Lp.ext
  have h1 := LT_coeFn μ x (LT μ x⁻¹ u)
  have h2 := LT_coeFn μ x⁻¹ u
  have h3 := (measurePreserving_mul_left μ x⁻¹).quasiMeasurePreserving.ae_eq_comp h2
  filter_upwards [h1, h3] with g e1 e3
  rw [e1]
  have e3' : (LT μ x⁻¹ u : G n → V) (x⁻¹ * g) = u (x⁻¹⁻¹ * (x⁻¹ * g)) := e3
  rw [e3']
  simp

theorem LT_inner (x : G n) (u v : Lp V 2 μ) : ⟪LT μ x u, LT μ x v⟫_ℂ = ⟪u, v⟫_ℂ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun g : G n => x⁻¹ * g)
    (measurePreserving_mul_left μ x⁻¹)).inner_map_map u v

theorem LT_facts (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) :
    (LT μ x : Lp V 2 μ →L[ℂ] Lp V 2 μ) * LT μ x⁻¹ = 1 ∧
    (∀ u v : Lp V 2 μ, ⟪LT μ x u, v⟫_ℂ = ⟪u, LT μ x⁻¹ v⟫_ℂ) ∧
    ∀ f : Mat n → V, MemLp (fun y : G n => f y.val) 2 μ → LT μ x (toL μ f) = toL μ (transl x f) := by
  refine ⟨?_, fun u v => ?_, fun f hf => ?_⟩
  · ext1 u
    exact LT_LT_inv μ x u
  · conv_lhs => rw [← LT_LT_inv μ x v]
    exact LT_inner μ x u _
  · have hfun : (fun y : G n => transl x f y.val) = (fun y : G n => f y.val) ∘ fun g : G n => x⁻¹ * g := by
      funext y
      simp [transl, Units.val_mul]
    have hm : MemLp (fun y : G n => transl x f y.val) 2 μ := by
      rw [hfun]
      exact hf.comp_measurePreserving (measurePreserving_mul_left μ x⁻¹)
    apply Lp.ext
    have h1 := LT_coeFn μ x (toL μ f)
    have h2 : (toL μ f : G n → V) =ᵐ[μ] fun g => f g.val := toL_coe hf
    have h3 := (measurePreserving_mul_left μ x⁻¹).quasiMeasurePreserving.ae_eq_comp h2
    have h4 : (toL μ (transl x f) : G n → V) =ᵐ[μ] fun g => transl x f g.val := toL_coe hm
    filter_upwards [h1, h3, h4] with g e1 e3 e4
    rw [e1, e4]
    have e3' : (toL μ f : G n → V) (x⁻¹ * g) = f (x⁻¹ * g).val := e3
    rw [e3']
    simp [transl, Units.val_mul]

end LeftTranslation

end GlobalTheory.CompanionTheory.WaveCp
