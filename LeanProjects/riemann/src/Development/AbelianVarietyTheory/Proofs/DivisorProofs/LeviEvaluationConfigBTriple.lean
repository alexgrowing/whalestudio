import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedPlaneIsPairStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem GlobalTheory.ThK.levi_evaluation_triple : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ (t : (AE F E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := G₁.W) H' t 1 m → ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (1, m) Ψ) = ((X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)) • e₂ Ψ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev t m hL Ψ hΨ
  obtain ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩ := G₁
  have eV : V₁ = G.V := cfg.eV
  subst eV
  have ep : p₁ = G.p := cfg.ep
  subst ep
  have P := (Check.isPair_of_isTriple T).1
  have P₁ := (Check.isPair_of_isTriple T₁).1
  obtain ⟨hEZ, -⟩ := GlobalTheory.T.theta_evaluation_zero_cone hKP.base
  obtain ⟨⟨e₀, he₀⟩, -⟩ := hEZ F E σ B a (a + (b + 2)) G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P (a + b) G.V W₁ H' a
    (a + b + 1) M₁ rfl cfg.hH' T₁.geo.hM
  have hpres : ∀ x, ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), om x Ψ ∈ schA F (Fin a × Fin (a + (b + 2))) :=
    fun x Ψ hΨ => (T.weil.isUSplitting).pres x Ψ hΨ
  have key := GlobalTheory.T.adapted_plane_second_variable hKP.base F E σ B a (a + (b + 2)) G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P (a + b) W₁ H' a
    (a + b + 1) M₁ om₁ _ _ cfg.hH' P₁ e₀ he₀ 1 t 1 m hL 1 (Subgroup.one_mem _) Ψ hΨ
  rw [one_mul] at key
  have h11 : om₁ (1, 1) (e₀ Ψ) = e₀ Ψ := by
    first
    | rw [Prod.mk_one_one, map_one, Module.End.one_apply]
    | exact congrArg (fun f => f (e₀ Ψ)) (map_one om₁)
    | simp
  rw [h11] at key
  have hsub : om (1, m) Ψ - ((X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)) • Ψ ∈ schA F (Fin a × Fin (a + (b + 2))) :=
    Submodule.sub_mem _ (hpres _ _ hΨ) (Submodule.smul_mem _ _ hΨ)
  have hz := GlobalTheory.T.pair_adapted_plane_is_pair hKP F E σ B a (a + (b + 2)) G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P (a + b) W₁ H' a (a + b + 1) M₁ om₁ _ _
    cfg.hH' P₁ e₀ he₀ n₁ (a + b) X₁ W₁ M₂ H₀.ι H'.ι (isoA H₀ H') e₂ hM₂ Set.subset_union_left hev _ hsub
    (by rw [map_sub, map_smul, key, sub_self])
  rw [map_sub, map_smul, sub_eq_zero] at hz
  exact hz
