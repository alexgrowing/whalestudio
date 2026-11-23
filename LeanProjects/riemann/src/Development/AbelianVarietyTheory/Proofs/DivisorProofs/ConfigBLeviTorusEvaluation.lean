import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleEvaluationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairPlaneDescentStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.EvLawB

theorem incM_one_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem mul_vecMulVec_eq {R : Type} [CommRing R] {k l p : ℕ} (A : Matrix (Fin k) (Fin l) R) (y : Fin l → R) (w : Fin p → R) :
    A * Matrix.vecMulVec y w = Matrix.vecMulVec (A *ᵥ y) w := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

end GlobalTheory.ThK.EvLawB

open GlobalTheory.ThK.EvLawB in

theorem GlobalTheory.ThK.evLaw_isoB : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (t : (AE F E)ˣ) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J), IsLevi H' t h₁ m → ∀ u ∈ unip σ G.W H',
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      e' (om' (1, u * m) Ψ) = ((X.α t : ℂ) * (((absE F E t : ℝ) ^ ((b : ℝ) / 2) : ℝ) : ℂ)) • om₁' (1, h₁) (e' Ψ) := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' cfg e' hev X om om' om₁ om₁' T T₁ t h₁ m hL u hu Ψ hΨ
  have P' := GlobalTheory.ThK.Inhab.pairV' T
  have P₁' := GlobalTheory.ThK.Inhab.pairV' T₁

  obtain ⟨Mb, hMb⟩ := GlobalTheory.T.exists_good_schrodinger_model F E σ B T.base b (a + (b + 2)) G₁.V' G.W _ _ _ _ T₁.geo.hV' T.geo.hW
  obtain ⟨omb, hwb⟩ := GlobalTheory.WeilExGen.exists_isWeil hP F E σ B T.base b (a + (b + 2)) G₁.V' G.W _ _ _ _ T₁.geo.hV' T.geo.hW Mb hMb
    X.α (X.α / X.β) P'.hX P'.hW T₁.chars.resα P'.resW
  have Pb : IsPair B Mb X.α (X.α / X.β) omb G₁.q (b - G₁.q) _ _ :=
    ⟨T.base, T₁.geo.hV', T.geo.hW, hMb, P'.hX, P'.hW, T₁.chars.resα, P'.resW, hwb⟩

  obtain ⟨⟨e₁, he₁⟩, law₁⟩ := GlobalTheory.T.adapted_plane_first_variable hP F E σ B (b + 2) (a + (b + 2)) G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ P'
    b G₁.V' H 0 (b + 1) Mb omb _ _ cfg.hH Pb
  obtain ⟨e₂, he₂⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hP).1 F E σ B b (a + (b + 2)) G₁.V' G.W Mb X.α (X.α / X.β) omb _ _ _ _ Pb
    (a + b) G₁.V' G₁.W H' a (a + b + 1) G₁.M' rfl cfg.hH' T₁.geo.hM').1

  have mapsC : ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), (e₂ ∘ₗ e₁) Φ ∈ schA F (Fin b × Fin (a + b)) :=
    fun Φ hΦ => he₂.maps _ (he₁.maps Φ hΦ)
  have heisC : ∀ z, ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      (e₂ ∘ₗ e₁) (G.M'.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = G₁.M'.co.rho B.ψ z ((e₂ ∘ₗ e₁) Φ) := by
    intro z Φ hΦ
    have h1 := he₁.Heisenberg₂ (z * (incM F H'.ι)ᵀ) Φ hΦ
    have h2 := he₂.Heisenberg₂ z (e₁ Φ) (he₁.maps Φ hΦ)
    rw [incM_one_eq, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc] at h1
    rw [incM_one_eq, Matrix.one_mul] at h2
    simp only [LinearMap.comp_apply]
    rw [h1, h2]
  have invC : ∀ u ∈ isoB H H', ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      (e₂ ∘ₗ e₁) (G.M'.co.rho B.ψ u Φ) = (e₂ ∘ₗ e₁) Φ := by
    intro u hu Φ hΦ
    simp only [LinearMap.comp_apply]
    rcases hu with hu | ⟨y, rfl⟩
    · rw [he₁.inv u hu Φ hΦ]
    · have h1 := he₁.Heisenberg₂ (Matrix.vecMulVec y (incV F H'.x)) Φ hΦ
      rw [incM_one_eq, Matrix.transpose_one, Matrix.mul_one, mul_vecMulVec_eq] at h1
      rw [h1, he₂.inv _ ⟨y, rfl⟩ _ (he₁.maps Φ hΦ)]
  have locC : ∃ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
      (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
        (e₂ ∘ₗ e₁) (pure f φ) = pure (ei f) fun v => ev v (φ v) := by
    obtain ⟨ei₁, ev₁, -, hv₁, hp₁⟩ := he₁.loc
    obtain ⟨ei₂, ev₂, -, hv₂, hp₂⟩ := he₂.loc
    refine ⟨ei₂.comp ei₁, fun v => ev₂ v ∘ₗ ev₁ v, fun v => ⟨?_, ?_⟩, ?_⟩
    · simp only [LinearMap.comp_apply]
      rw [(hv₁ v).1, (hv₂ v).1]
    · rw [Submodule.map_comp, (hv₁ v).2, (hv₂ v).2]
    · intro f φ hφ hcof
      have hφ₁ : ∀ v, ev₁ v (φ v) ∈ SB _ := fun v => (hv₁ v).2 ▸ Submodule.mem_map_of_mem (hφ v)
      have hcof₁ : ∀ᶠ v in cofinite, ev₁ v (φ v) = Mb.vac v := hcof.mono fun v hv => by rw [hv, (hv₁ v).1]
      simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      rw [hp₁ f φ hφ hcof, hp₂ _ _ hφ₁ hcof₁]
  obtain ⟨c, hc⟩ := GlobalTheory.T.config_b_triple_evaluation_compatible hP F E σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ e' hev (e₂ ∘ₗ e₁)
    mapsC heisC invC locC
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.weil_pair_plane_descent hP F E σ B (b + 2) (a + (b + 2)) b (a + b) G.V' G.W G₁.V' G₁.W G.M'
    X.α (X.α / X.β) om' _ _ _ _ P' H H' 0 (b + 1) a (a + b + 1) Mb omb _ _ G₁.M' cfg.hH cfg.hH' Pb T₁.geo.hM' e₁ e₂ he₁ he₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne
    have := hc Φ₀ hΦ₀
    rw [zero_smul, LinearMap.comp_apply] at this
    exact this
  have hpres : om' (1, u * m) Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) := (T.weil'.isUSplitting).pres _ _ hΨ
  have hLX : IsLevi (W₁ := G₁.V') H 1 (1 : UA σ G₁.V'.J) (1 : UA σ G.V'.J) := by
    refine ⟨?_, ?_, ?_⟩
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _)
      simp
  have key : e₂ (e₁ (om' (1, u * m) Ψ)) = ((X.α t : ℂ) * (((absE F E t : ℝ) ^ ((b : ℝ) / 2) : ℝ) : ℂ)) •
      om₁' (1, h₁) (e₂ (e₁ Ψ)) := by
    have h1 := law₁ e₁ he₁ (u * m) 1 1 1 hLX 1 (Subgroup.one_mem _) Ψ hΨ
    have h2 := GlobalTheory.T.adapted_plane_second_variable hP F E σ B b (a + (b + 2)) G₁.V' G.W Mb X.α (X.α / X.β) omb _ _ _ _ Pb (a + b) G₁.W H'
      a (a + b + 1) G₁.M' om₁' _ _ cfg.hH' P₁' e₂ he₂ 1 t h₁ m hL u hu (e₁ Ψ) (he₁.maps Ψ hΨ)
    simp only [one_mul, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] at h1
    rw [h1, h2]
  calc e' (om' (1, u * m) Ψ) = c⁻¹ • (c • e' (om' (1, u * m) Ψ)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = c⁻¹ • (((X.α t : ℂ) * (((absE F E t : ℝ) ^ ((b : ℝ) / 2) : ℝ) : ℂ)) • om₁' (1, h₁) (c • e' Ψ)) := by
        rw [← hc _ hpres, ← hc _ hΨ]
        simp only [LinearMap.comp_apply]
        rw [key]
    _ = _ := by rw [map_smul, smul_comm _ c, smul_smul, inv_mul_cancel₀ hc0, one_smul]
