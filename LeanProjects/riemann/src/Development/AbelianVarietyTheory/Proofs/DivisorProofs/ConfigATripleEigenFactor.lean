import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSkewCmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroThetaPureTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTripleSeesawConfigurationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleTransferAlongConfigAThirdStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

noncomputable section

namespace GlobalTheory.ConeA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem I_smul {a a' : ℕ} {G : Geo σ a a'} (om : Rep σ G.V G.W) (c : ℂ) (Ψ : (Fin a × Fin (a + a') → AF F) → ℂ)
    (h : UA σ G.W.J) : G.M.I om (c • Ψ) h = c * G.M.I om Ψ h := by
  simp only [Model.I, theta, map_smul, thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]
  exact integral_const_mul c _

theorem coneA_nonZero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → (∃ Φ₁ ∈ PolData B G₁.M, G₁.M.I om₁ Φ₁ ≠ 0) →
    ∃ Φ ∈ PolData B G.M, ∃ (h : UA σ G.W.J) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J), IsLevi (W₁ := G₁.W) H' 1 h₁ m ∧
      G₁.M.I om₁ (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (om (1, h) Φ)) h₁ ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he K μK μ hK hμK hμ hΦ₁
  obtain ⟨f₁, -, φ₁, hSB₁, hcof₁, h₁, hne₁⟩ := GlobalTheory.T.nonzero_theta_pure_tensor hKP F E σ B b a' G₁ X om₁ om₁' hT₁ hΦ₁
  have hfin : {v | ¬ φ₁ v = G₁.M.vac v}.Finite := Filter.eventually_cofinite.1 hcof₁
  set T : Finset (Pl F) := X.T ∪ hfin.toFinset with hTdef
  have hXT : X.T ⊆ T := Finset.subset_union_left
  have hvac₁ : ∀ v ∉ T, φ₁ v = G₁.M.vac v := fun v hv => by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hc))
  obtain ⟨ei, ev, hei, hev, hloc⟩ := he.loc
  have hcpt : IsCompact (K : Set (UA σ G.V.J)) := GlobalTheory.T.stabilizer_compact hKP F E σ B (b + 2) G.V _ _ K hT.base hT.geo.hV hK
  obtain ⟨κ, hκ, hcone⟩ := GlobalTheory.T.theta_triple_seesaw_configuration hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he ei ev hei hev hloc
    K μK μ hK hμK hμ
    (existsUnique_isNormK hcpt (evI F)).choose (exists_haar_idelesAt E (evI F)).choose
    (fun v => (existsUnique_isNormK hcpt (evFin F v)).choose) (fun v => (existsUnique_isNormE E v).choose)
    (existsUnique_isNormK hcpt (evI F)).choose_spec.1 (exists_haar_idelesAt E (evI F)).choose_spec
    (fun v => (existsUnique_isNormK hcpt (evFin F v)).choose_spec.1) (fun v => (existsUnique_isNormE E v).choose_spec.1) T hXT
  obtain ⟨f, hf, φ, hSB, hvac, hne⟩ := GlobalTheory.T.triple_transfer_along_config_a_third hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he ei ev hei hev
    hloc K hK
    (existsUnique_isNormK hcpt (evI F)).choose (exists_haar_idelesAt E (evI F)).choose
    (fun v => (existsUnique_isNormK hcpt (evFin F v)).choose) (fun v => (existsUnique_isNormE E v).choose)
    (existsUnique_isNormK hcpt (evI F)).choose_spec.1 (exists_haar_idelesAt E (evI F)).choose_spec
    (fun v => (existsUnique_isNormK hcpt (evFin F v)).choose_spec.1) (fun v => (existsUnique_isNormE E v).choose_spec.1) T hXT
    f₁ φ₁ h₁ hSB₁ hvac₁ hne₁
  have hcofT : ∀ᶠ v in cofinite, φ v = G.M.vac v :=
    Filter.eventually_cofinite.2 ((T.finite_toSet).subset fun v hv => by
      by_contra hc
      exact hv (hvac v hc))
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_levi_element_skew_cm F E σ B _ _ G.W G₁.W H' 0 (b + 1) _ _ hT.base.cm hT.geo.hW hC.hH' h₁
  refine ⟨pure f φ, Submodule.subset_span ⟨f, hf, φ, hSB, hcofT, rfl⟩, 1, h₁, m, hm, ?_⟩
  have h11 : om (1, 1) = 1 := map_one om
  rw [h11, Module.End.one_apply, hcone f hf φ hSB hvac, I_smul]
  exact mul_ne_zero hκ hne

end GlobalTheory.ConeA

end
