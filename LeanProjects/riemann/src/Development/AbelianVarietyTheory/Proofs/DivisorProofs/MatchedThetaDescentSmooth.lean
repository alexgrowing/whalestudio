import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDataLocalIdentityInfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedRepLocalFactorFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedRepLocalFactorSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedRepLocalFactorThirdStatement

noncomputable section

namespace GlobalTheory.ThKAdm

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem finiteDimensional_span_thetaIntegrals : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (L : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)), GlobalTheory.ThKAdm.IsLevel G.W L → ∀ (m : ℕ) (τ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J → (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))), GlobalTheory.ThKAdm.IsKRep B τ → FiniteDimensional ℂ (Submodule.span ℂ (G.M'.I om' '' {Ψ | Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) ∧ (∀ l ∈ L, om' (1, l) Ψ = Ψ) ∧ GlobalTheory.ThKAdm.HasTypes B om' τ Ψ})) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM L hL m τ hτ
  obtain ⟨I, g, e, hg, hT⟩ := GlobalTheory.T.matched_data_local_identity_inf hKP F E σ B a a' G X om om' R Rf hM L hL
  obtain ⟨N, c, hc⟩ := GlobalTheory.T.matched_rep_local_factor_second hKP F E σ B a a' G X om om' R Rf hM L hL I g e hg hT
  obtain ⟨hU, hK⟩ := GlobalTheory.T.modelI_mem_range_kinf_equivariant_map hKP F E σ B a a' G X om om' R Rf hM L hL m τ hτ I g e hg hT
  have hfin := hKP.automorphicFormsFiniteUnitary I g hg N c (EuclideanSpace ℂ (Fin m)) _ hU
  let Φ : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J → ℂ) →ₗ[ℂ] (I.GA → ℂ) := LinearMap.funLeft ℂ ℂ e
  have hinj : Function.Injective Φ := LinearMap.funLeft_injective_of_surjective _ _ _ hT.surj
  set P := Submodule.span ℂ (G.M'.I om' '' {Ψ | Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) ∧
    (∀ l ∈ L, om' (1, l) Ψ = Ψ) ∧ GlobalTheory.ThKAdm.HasTypes B om' τ Ψ}) with hP
  have hle : P.map Φ ≤ Submodule.span ℂ {f : I.GA → ℂ | GlobalTheory.Dec.IsSmoothMG I g f ∧
      (∀ v m x, (GlobalTheory.Dec.zOp I v m)^[N v m] f x = ∑ i, c v m i * (GlobalTheory.Dec.zOp I v m)^[i.val] f x) ∧
      ∃ T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] (I.GA → ℂ), (∀ (k : GlobalTheory.Dec.Kinf I) w x,
        T (τ (e (fun v => (k v : Formalism.REAL.UJ (I.ε v)), 1)) w) x = T w (x * (fun v => (k v : Formalism.REAL.UJ (I.ε v)), 1))) ∧
        f ∈ LinearMap.range T} := by
    rw [hP, Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨Ψ, hΨ, rfl⟩, rfl⟩
    exact ⟨GlobalTheory.T.matched_rep_local_factor_first hKP F E σ B a a' G X om om' R Rf hM L hL I g e hg hT Ψ hΨ.1 hΨ.2.1, hc Ψ hΨ.1,
      hK Ψ hΨ.1 hΨ.2.2⟩
  haveI : FiniteDimensional ℂ (P.map Φ) := by haveI := hfin; exact Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective Φ hinj P).symm

end GlobalTheory.ThKAdm

end
