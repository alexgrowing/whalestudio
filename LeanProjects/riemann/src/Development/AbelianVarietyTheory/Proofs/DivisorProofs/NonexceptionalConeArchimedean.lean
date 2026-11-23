import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealConstA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroThetaPureTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictedTensorRepresentativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleTransferAlongConfigASecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawIdentityConfigAFourthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEvaluationIsoCaseAStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.RealA
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.RealA.NeCone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_norm_ne {n : ℕ} {X : Spc F E n} {K : Subgroup (UA σ X.J)} (hK : IsCompact (K : Set (UA σ X.J)))
    (μ : Measure (KAt K (evI F))) (hμ : μ.IsHaarMeasure) :
    ∃ (μ₀ : Measure (KAt K (evI F))) (c : ℝ), c ≠ 0 ∧ IsNormK K (evI F) μ₀ ∧
      ∀ g : KAt K (evI F) → ℂ, ∫ k, g k ∂μ = c • ∫ k, g k ∂μ₀ := by
  haveI : CompactSpace (KAt K (evI F)) := isCompact_iff_compactSpace.1 (isCompact_KAt hK _)
  have h0 : μ Set.univ ≠ 0 := (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
  have h1 : μ Set.univ ≠ ⊤ := isCompact_univ.measure_lt_top.ne
  refine ⟨(μ Set.univ)⁻¹ • μ, (μ Set.univ).toReal, ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩,
    ⟨Measure.IsHaarMeasure.smul μ (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0), ?_⟩, fun g => ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 h1]
  · rw [integral_smul_measure, smul_smul, ← ENNReal.toReal_mul, ENNReal.mul_inv_cancel h0 h1, ENNReal.toReal_one,
      one_smul]

open Classical in

theorem neConeA_holds : GlobalTheory.ThK.KP → GlobalTheory.FunPr.Hypotheses₂ → NeConeA := by
  intro hKP hPr F E _ _ _ _ _ σ B b a' G G₁ H H' hC R R₁ e he ei ev hloc K hK μK μ hμK hμ X om om' Rf om₁ om₁' Rf₁ hM hM₁
  have hT := hM.triple
  have hT₁ := hM₁.triple
  have hcpt : IsCompact (K : Set (UA σ G.V.J)) :=
    GlobalTheory.StabCpt.isCompact_of_isStab hKP F E σ B (b + 2) G.V _ _ K hT.base hT.geo.hV hK
  obtain ⟨μ₀, c, hc0, hμ₀, hc⟩ := exists_norm_ne hcpt μK hμK
  obtain ⟨L, hL⟩ := GlobalTheory.T.seesaw_identity_config_a_fourth hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he ei ev hloc.1 hloc.2.1
    hloc.2.2 K hK μ₀ μ hμ₀ hμ
  have hL₀ : ∀ f, coneInf B G.M om ei K μ₀ μ (shiftA H H') X.ν ((b + 2 - a') / 2) f = L f := fun f => coneInf_eq (hL f)
  have hLc : ∀ f, coneA B G H H' om ei K μK μ X.ν f = (c : ℂ) • L f := fun f => by
    unfold coneA
    refine coneInf_eq (funext fun y => ?_)
    change (c : ℂ) • L f y = _
    rw [hL f]
    simp only [coneInfFun]
    rw [hc, Complex.coe_smul]
  have hLpol : ∀ f ∈ G.M.Pol B.ψ B.emb, L f ∈ G₁.M.Pol B.ψ B.emb := fun f hf => by
    choose μKf hμKf using fun v : Pl F => (existsUnique_isNormK hcpt (evFin F v)).exists
    choose μf hμf using fun v : Pl F => (existsUnique_isNormE E v).exists
    obtain ⟨g, hg, hgp⟩ := GlobalTheory.T.local_evaluation_iso_case_a F E σ hPr B b a' G G₁ H H' hC e he ei ev hloc K hK μKf hμKf μf hμf μ₀ hμ₀ μ hμ
      X om om' hT hT₁.geo.hM f
    rw [← hL₀, coneInf_eq hg]
    exact hgp hf
  obtain ⟨f₁, -, φ₁, hSB₁, hcof₁, h₁, hne₁⟩ := GlobalTheory.T.nonzero_theta_pure_tensor hKP F E σ B b a' G₁ X om₁ om₁' hT₁
    (GlobalTheory.T.theta_nonvanishing hKP F E σ B b a' G₁ X om₁ om₁' hT₁).1
  obtain ⟨l, hl, hinv⟩ := GlobalTheory.T.exists_restricted_tensor_representative hKP F E σ B b a' G₁ X om₁ om₁' hT₁ φ₁ h₁ hSB₁ hcof₁
  have hl0 : l ≠ 0 := fun h0 => hne₁ (by rw [← hl, h0]; rfl)
  obtain ⟨f, hf, hlf⟩ := GlobalTheory.T.triple_transfer_along_config_a_second hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he ei ev hloc.1 hloc.2.1
    hloc.2.2 K hK μ₀ μ hμ₀ hμ l hl0 hinv
  refine ⟨f, hf, fun h0 => hlf ?_⟩
  rw [hL₀]
  have hp : R₁.p (L f) = 0 := by
    rw [hLc, map_smul] at h0
    exact (smul_eq_zero.1 h0).resolve_left (by exact_mod_cast hc0)
  have hfin : {v | ¬ φ₁ v = G₁.M.vac v}.Finite := Filter.eventually_cofinite.1 hcof₁
  have hvac₁ : ∀ v ∉ X.T ∪ hfin.toFinset, φ₁ v = G₁.M.vac v := fun v hv => by
    by_contra hc'
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hc'))
  have hI : G₁.M.I om₁ (pure (L f) φ₁) = 0 := by
    refine (GlobalTheory.T.theta_factorization hKP F E σ B b a' G₁ X om₁ om₁' R₁ Rf₁ hM₁).1 _
      ⟨X.T ∪ hfin.toFinset, Finset.subset_union_left, 1, 0, fun _ => L f, fun _ => φ₁, Fin.elim0, Fin.elim0,
        fun _ => ⟨hLpol f hf, hSB₁, hvac₁⟩, fun j => j.elim0, by simp, by simp, ?_⟩
    simp [hp]
  rw [hl, hI]
  rfl

end GlobalTheory.ThK.RealA.NeCone

end

example : GlobalTheory.ThK.KP → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.RealA.NeConeA := GlobalTheory.ThK.RealA.NeCone.neConeA_holds
