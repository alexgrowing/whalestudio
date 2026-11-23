import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdaptedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneAutomorphicFunctionTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalTranslatesDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFunctionMaximalCompactTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleFiniteDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFunctionTwistBoundedStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

noncomputable section
namespace GlobalTheory.ThKCtFin

theorem leviElt_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} {i₀ i₁ : ℕ}
    (hA : H'.IsAdapted σ B G.W W₁ i₀ i₁) (t s : (AE F E)ˣ) :
    leviElt σ G.W W₁ H' (t * s) = leviElt σ G.W W₁ H' t * leviElt σ G.W W₁ H' s := by
  have ex := fun t => GlobalTheory.T.exists_levi_element_adapted F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA t
  obtain ⟨t1, t2, t3⟩ := isLevi_leviElt (ex t)
  obtain ⟨s1, s2, s3⟩ := isLevi_leviElt (ex s)
  have hm : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g g' : UA σ J), mat (g * g') = mat g * mat g' := fun _ _ => rfl
  refine GlobalTheory.T.levi_element_unique F E σ B _ _ _ G.W hT.geo.hW d₁ W₁ H' i₀ i₁ hA (t * s) _ _ (isLevi_leviElt (ex (t * s))) ⟨?_, ?_, ?_⟩
  · rw [hm, ← Matrix.mulVec_mulVec, s1, Matrix.mulVec_smul, t1, smul_smul, Units.val_mul, mul_comm]
  · rw [hm, ← Matrix.mulVec_mulVec, s2, Matrix.mulVec_smul, t2, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [hm, Matrix.mul_assoc, s3, ← Matrix.mul_assoc, t3, Matrix.mul_assoc, ← hm, mul_one]

theorem ctFinDim : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ f : UA σ G.W.J → ℂ, (∃ K, IsMaxCpt σ (c • G.W.J.map σ) K ∧ IsAut σ (c • G.W.J.map σ) K (fun x => f ((toGAd hσ G.W.J hc).symm x))) → ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun s : (AE F E)ˣ => fun t => ctLevi σ G.W W₁ H' μ 𝓕 f h (t * s))) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA hσ c hc hcs f hf μ 𝓕 h1 h2 h3 h
  have htr : ∀ b t, ctLevi σ G.W W₁ H' μ 𝓕 f h (b * t) = ctLevi σ G.W W₁ H' μ 𝓕 f (leviElt σ G.W W₁ H' b * h) t := by
    intro b t
    rw [ctLevi_apply, ctLevi_apply, mul_comm b t, leviElt_mul hT hA, mul_assoc]
  obtain ⟨U, hUo, hU⟩ := GlobalTheory.T.automorphic_function_maximal_compact_twist F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA hσ c hc hcs f hf μ 𝓕 h1 h2 h3 h
  obtain ⟨C, hC⟩ := GlobalTheory.T.idele_finite_decomposition F E U hUo
  refine GlobalTheory.T.finite_dimensional_translates_decomposition (AE F E)ˣ (ctLevi σ G.W W₁ H' μ 𝓕 f h)
    (Set.range (Units.map (inclR (F := F) (AF F)).toMonoidHom)) {u | u ∈ U ∧ u ∈ idelesFin F E} (idelesInf F E) C
    ?_ ?_ ?_ ?_
  · rintro _ ⟨γ, rfl⟩ t
    exact GlobalTheory.T.adapted_plane_automorphic_function_twist hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA hσ c hc hcs f hf μ 𝓕 h1 h2 h3 h γ t
  · rintro u ⟨hu, hu'⟩ t
    exact hU u hu hu' t
  · intro t
    obtain ⟨γ, c, hcC, a, ha, u, hu, hu', e⟩ := hC t
    exact ⟨_, ⟨γ, rfl⟩, c, hcC, a, ha, u, ⟨hu, hu'⟩, e⟩
  · intro b
    have e : (fun a : idelesInf F E => fun a' : idelesInf F E => ctLevi σ G.W W₁ H' μ 𝓕 f h (b * a' * a)) =
        fun a : idelesInf F E => fun a' : idelesInf F E =>
          ctLevi σ G.W W₁ H' μ 𝓕 f (leviElt σ G.W W₁ H' b * h) ((a' : (AE F E)ˣ) * a) := by
      funext a a'
      rw [mul_assoc, htr]
    rw [e]
    exact GlobalTheory.T.automorphic_function_twist_bounded hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA hσ c hc hcs f hf μ 𝓕 h1 h2 h3 _

end GlobalTheory.ThKCtFin
