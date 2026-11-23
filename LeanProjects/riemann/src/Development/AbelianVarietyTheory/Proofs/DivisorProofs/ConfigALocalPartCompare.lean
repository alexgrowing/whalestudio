import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentModelsStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ShiftInfA

theorem lawS : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (l : (AE F E)ˣ) (m : UA σ G.V.J), IsLevi (W₁ := G₁.V) H l 1 m →
      ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
        e (om (m, 1) Ψ) = (((X.ν l : ℂ))⁻¹ * (((absE F E l : ℝ) ^ (((b + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ)) • e Ψ := by
  intro hP F E _ _ _ _ _ σ B b a' G G₁ H H' cfg e hev X om om' om₁ om₁' T T₁ l m hL Ψ hΨ
  have P := Inhab.pairV T
  have P₁ := Inhab.pairV T₁

  obtain ⟨Ma, hMa⟩ := GlobalTheory.ModelEx.model_exists F E σ B P.base (b + 2) (b + a') G.V G₁.W _ _ _ _ P.herm P₁.skew
  obtain ⟨oma, hwa⟩ := GlobalTheory.WeilExGen.exists_isWeil hP F E σ B P.base (b + 2) (b + a') G.V G₁.W _ _ _ _ P.herm P₁.skew Ma hMa
    X.β (X.β / X.α) P.hX P.hW P.resX P₁.resW
  have Pa : IsPair B Ma X.β (X.β / X.α) oma (b + 2 - G.p) G.p (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q) :=
    ⟨P.base, P.herm, P₁.skew, hMa, P.hX, P.hW, P.resX, P₁.resW, hwa⟩

  obtain ⟨e₁, he₁⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hP).1 F E σ B (b + 2) (b + 2 + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P
    (b + a') G.V G₁.W H' 0 (b + 1) Ma rfl cfg.hH' hMa).1
  obtain ⟨⟨e₂, he₂⟩, law₂⟩ := GlobalTheory.T.adapted_plane_first_variable hP F E σ B (b + 2) (b + a') G.V G₁.W Ma X.β (X.β / X.α) oma _ _ _ _ Pa
    b G₁.V H 0 (b + 1) G₁.M om₁ _ _ cfg.hH P₁
  have h1 : incM F (1 : Matrix (Fin (b + 2)) (Fin (b + 2)) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin (b + a')) (Fin (b + a')) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have heisC : ∀ (z : Matrix (Fin b) (Fin (b + a')) (AE F E)), ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      (e₂ ∘ₗ e₁) (G.M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = G₁.M.co.rho B.ψ z ((e₂ ∘ₗ e₁) Φ) := by
    intro z Φ hΦ
    have k1 := he₁.Heisenberg₂ (incM F H.ι * z) Φ hΦ
    have k2 := he₂.Heisenberg₂ z (e₁ Φ) (he₁.maps Φ hΦ)
    rw [h1, Matrix.one_mul] at k1
    rw [h1', Matrix.transpose_one, Matrix.mul_one] at k2
    simp only [LinearMap.comp_apply]
    rw [k1, k2]
  have invC : ∀ u ∈ isoA H H', ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      (e₂ ∘ₗ e₁) (G.M.co.rho B.ψ u Φ) = (e₂ ∘ₗ e₁) Φ := by
    intro u hu Φ hΦ
    simp only [LinearMap.comp_apply]
    rcases hu with hu | ⟨z, rfl⟩
    · rw [he₁.inv u hu Φ hΦ]
    · have k1 := he₁.Heisenberg₂ (Matrix.vecMulVec (incV F H.x) z) Φ hΦ
      have hvm : Matrix.vecMulVec (incV F H.x) z * (incM F H'.ι)ᵀ = Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z) := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [h1, Matrix.one_mul, hvm] at k1
      rw [k1, he₂.inv _ ⟨z, rfl⟩ _ (he₁.maps Φ hΦ)]
  obtain ⟨c, hc⟩ := GlobalTheory.T.pair_double_descent hP F E σ B (b + 2) (b + 2 + a') b (b + a') G.V G.W G₁.V G₁.W G.M X.β (X.β / X.α) om
    _ _ _ _ P H H' 0 (b + 1) 0 (b + 1) G₁.M cfg.hH cfg.hH' T₁.geo.hM e hev (e₂ ∘ₗ e₁) heisC invC
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.pair_double_descent_models hP F E σ B (b + 2) (b + 2 + a') b (b + a') G.V G.W G₁.V G₁.W G.M X.β (X.β / X.α) om
    _ _ _ _ P H H' 0 (b + 1) 0 (b + 1) Ma oma _ _ G₁.M cfg.hH cfg.hH' Pa T₁.geo.hM e₁ e₂ he₁ he₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne
    have := hc Φ₀ hΦ₀
    rw [zero_smul, LinearMap.comp_apply] at this
    exact this
  have hLW : IsLevi (W₁ := G₁.W) H' 1 (1 : UA σ G₁.W.J) (1 : UA σ G.W.J) := by
    refine ⟨?_, ?_, ?_⟩
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _)
      simp

  have law₁ : ∀ (g : UA σ G.V.J) Ψ, Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) → e₁ (om (g, 1) Ψ) = oma (g, 1) (e₁ Ψ) := by
    intro g Ψ hΨ
    have k := GlobalTheory.T.adapted_plane_second_variable hP F E σ B (b + 2) (b + 2 + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P (b + a') G₁.W H'
      0 (b + 1) Ma oma _ _ cfg.hH' Pa e₁ he₁ g 1 1 1 hLW 1 (Subgroup.one_mem _) Ψ hΨ
    simpa only [one_mul, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] using k
  have hpres : om (m, 1) Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := (T.weil.isUSplitting).pres _ _ hΨ
  have k2 := law₂ e₂ he₂ 1 l 1 m hL 1 (Subgroup.one_mem _) (e₁ Ψ) (he₁.maps Ψ hΨ)
  rw [one_mul, show om₁ (1, 1) = 1 from map_one om₁, Module.End.one_apply] at k2
  have hν : ((X.β / X.α) l : ℂ) = (X.ν l : ℂ)⁻¹ := by
    simp [Chars.ν, MonoidHom.div_apply, Circle.coe_div, inv_div]
  rw [hν] at k2
  apply smul_right_injective _ hc0
  show c • e (om (m, 1) Ψ) = c • _ • e Ψ
  rw [smul_comm c, ← hc _ hpres, ← hc _ hΨ, LinearMap.comp_apply, LinearMap.comp_apply, law₁ m Ψ hΨ, k2]

theorem evShift_levi : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (l : (AE F E)ˣ) (m : UA σ G.V.J), l ∈ idelesAt E (evI F) → IsLevi (W₁ := G₁.V) H l 1 m → m ∈ UAt σ G.V (evI F) →
      ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
        ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' 1))) (locOpInf (om (m, 1)) f)) =
          (((X.ν l : ℂ))⁻¹ * (((absE F E l : ℝ) ^ (((b + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ)) •
            ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l⁻¹))) f) := by
  intro hP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he ei ev hloc X om om' om₁ om₁' hT hT₁ l m _ hLevi hm f
  have hψ : IsStd B.ψ := hT.base.std
  have hcm : IsCMExt F E σ := hT.base.cm
  have hW := hT.weil
  have hS := IsUWeilPair.isUSplitting hW
  have hM : G.M.IsGood B.ψ := hT.geo.hM
  have hM₁ : G₁.M.IsGood B.ψ := hT₁.geo.hM
  obtain ⟨_, hloc0, hpure⟩ := hloc
  have hex : ∀ v : Pl F, ∃ p : (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ, p ∈ SB _ ∧
      ev v p = Set.indicator {x : Fin b × Fin (b + a') → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      (G₁.M.vac v = Set.indicator {x : Fin b × Fin (b + a') → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
        p = G.M.vac v) := by
    intro v
    by_cases h : G₁.M.vac v = Set.indicator {x : Fin b × Fin (b + a') → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
    · exact ⟨G.M.vac v, (hM.vac v).1, by rw [← h]; exact (hloc0 v).1, fun _ => rfl⟩
    · have hmem : Set.indicator {x : Fin b × Fin (b + a') → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∈
          (SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v)).map (ev v) := by
        rw [(hloc0 v).2]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hmem
      exact ⟨p, hp, hpe, fun h' => absurd h' h⟩
  choose φ hφSB hφev hφvac using hex
  have hcof : ∀ᶠ v in cofinite, φ v = G.M.vac v := by
    filter_upwards [hM₁.std] with v hv
    exact hφvac v hv
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x : Fin (b + 2) × Fin (b + 2 + a') → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hcof, hM.std] with v h1 h2
    rw [h1, h2]
  have hevφ : (fun v => ev v (φ v)) =
      fun v => Set.indicator {x : Fin b × Fin (b + a') → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    funext hφev
  have hRest : ∀ g : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
      Rest (evI F) (⇑g) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) :=
    fun g => GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφSB hstd
  have he' : ∀ g : SInf F (Fin (b + 2) × Fin (b + 2 + a')), e (pure g φ) = pure (ei g) (fun v =>
      Set.indicator {x : Fin b × Fin (b + a') → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) := by
    intro g; rw [hpure g φ hφSB hcof, hevφ]

  have hrho : ∀ (u : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E)) (g : SInf F (Fin (b + 2) × Fin (b + 2 + a'))),
      G.M.co.rho B.ψ (partInf F u) (pure g φ) = pure (locOpInf (G.M.co.rho B.ψ (partInf F u)) g) φ :=
    fun u g => (locOpInf_rho G.M.co hψ u g).1 _ (hRest g)
  have hom : om (m, 1) (pure f φ) = pure (locOpInf (om (m, 1)) f) φ :=
    acts_locOpInf (GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ (b + 2) (b + 2 + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om
      hcm hψ hW m hm f) _ (hRest f)

  have hact : actAB (cA σ) ((m, 1) : UA σ G.V.J × UA σ G.W.J) (partInf F (shiftA H H' l⁻¹)) =
      partInf F (shiftA H H' 1) := by
    have hm1 : mat (1 : UA σ G.W.J) = 1 := rfl
    have hx := hLevi.1
    change mat m * (realAd F 1 • ((l⁻¹ : (AE F E)ˣ).1 • Matrix.vecMulVec (incV F H.x) (incV F H'.y))) * (mat (1 : UA σ G.W.J))ᵀ =
      realAd F 1 • ((1 : (AE F E)ˣ).1 • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
    rw [hm1, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_vecMulVec, hx,
      Matrix.smul_vecMulVec, smul_smul (l⁻¹ : (AE F E)ˣ).1, Units.inv_mul, Units.val_one]
  have hΦ : pure f φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := (hRest f).2
  have hglob : e (G.M.co.rho B.ψ (partInf F (shiftA H H' 1)) (om (m, 1) (pure f φ))) =
      (((X.ν l : ℂ))⁻¹ * (((absE F E l : ℝ) ^ (((b + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ)) •
        e (G.M.co.rho B.ψ (partInf F (shiftA H H' l⁻¹)) (pure f φ)) := by
    have h1 := hS.impl (m, 1) (partInf F (shiftA H H' l⁻¹)) (pure f φ) hΦ
    rw [hact] at h1
    rw [← h1]
    exact lawS hP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ l m hLevi _
      (GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ _ hΦ)
  rw [hom, hrho, hrho, he', he'] at hglob
  refine GlobalTheory.ThK.EvUniqInf.eq_of_pure_std _ _ (hglob.trans ?_)
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.map_smul, SchwartzMap.smul_apply]
  ring

end GlobalTheory.ShiftInfA
