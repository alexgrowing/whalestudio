import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicThetaAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicRestrictedTensorStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK

theorem integral_smul_datum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (c : ℂ) (Φ : (Fin n × Fin d → AF F) → ℂ) :
    M.I om (c • Φ) = c • M.I om Φ := by
  funext h
  simp only [Model.I, theta, map_smul, thetaSum, Pi.smul_apply, smul_eq_mul]
  simp_rw [tsum_mul_left]
  rw [integral_const_mul]

theorem exists_so_integral_ne_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.q = 0 → ∀ Φ' ∈ PolData B G.M', G.M'.I om' Φ' ≠ 0 →
    ∃ Φ'' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, G.M'.I om' Φ'' ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT hq Φ' hΦ' hI
  classical
  suffices key : ∀ Φ ∈ PolData B G.M', ∃ Φ'' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, G.M'.I om' Φ'' = G.M'.I om' Φ by
    obtain ⟨Φ'', h1, h2⟩ := key Φ' hΦ'
    exact ⟨Φ'', h1, h2 ▸ hI⟩
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hφ, hcof, rfl⟩ := hx
    have hgood : X.Good B.v₁ := hT.chars.good
    have hnr := GlobalTheory.T.character_at_uniformizer_not_root_of_unity F E σ B a a' G X om om' hT B.v₁ hgood
    obtain ⟨φ₀, hφ₀, hd⟩ := GlobalTheory.T.schwartz_bruhat_local_approximation hKP.base F E σ B a a' G X om om' hT B.v₁ hgood hnr B.τ₁ (φ B.v₁) (hφ B.v₁)
    have hSB : ∀ v, Function.update φ B.v₁ φ₀ v ∈ SB _ := by
      intro v
      by_cases hv : v = B.v₁
      · subst hv; simpa using hφ₀.1
      · simpa [Function.update_of_ne hv] using hφ v
    have hcof' : ∀ᶠ v in cofinite, Function.update φ B.v₁ φ₀ v = G.M'.vac v := by
      filter_upwards [hcof, (Set.finite_singleton B.v₁).compl_mem_cofinite] with v hv hv'
      rw [Function.update_of_ne (by simpa using hv')]
      exact hv
    refine ⟨pure f (Function.update φ B.v₁ φ₀), ⟨?_, ?_⟩,
      GlobalTheory.T.anisotropic_restricted_tensor hKP F E σ B a a' G X om om' hT hq f φ (Function.update φ B.v₁ φ₀) hf hφ hcof
        (by simpa using hφ₀.1) (fun v hv => Function.update_of_ne hv _ _) (by simpa using hd)⟩
    · exact Submodule.subset_span ⟨f, hf, Function.update φ B.v₁ φ₀, hSB, hcof', rfl⟩
    · exact Submodule.subset_span ⟨f, Function.update φ B.v₁ φ₀, hSB, hcof', by simpa using hφ₀, rfl⟩
  | zero => exact ⟨0, zero_mem _, rfl⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨Φx, hx', ex⟩ := ihx
    obtain ⟨Φy, hy', ey⟩ := ihy
    refine ⟨Φx + Φy, add_mem hx' hy', ?_⟩
    rw [GlobalTheory.T.anisotropic_theta_additive hKP F E σ B a a' G X om om' hT hq _ hx'.1 _ hy'.1, GlobalTheory.T.anisotropic_theta_additive hKP F E σ B a a' G X om om' hT hq _ hx _ hy, ex, ey]
  | smul c x hx ih =>
    obtain ⟨Φx, hx', ex⟩ := ih
    exact ⟨c • Φx, Submodule.smul_mem _ c hx', by rw [integral_smul_datum, integral_smul_datum, ex]⟩

end GlobalTheory.ThK
