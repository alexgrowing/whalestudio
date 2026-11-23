import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergLineDerivativeFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchSchwartzDerivativeHeisenbergLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TracePairingNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussVacuumNondegenerateGaussianDualPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSubmoduleEqTopOfGaussianMemDerivStableStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolDense

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem mem_pol_of_isGauss (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {f₀ : SInf F (Fin n × Fin d)} (h : M.IsGauss ψ τ f₀) : f₀ ∈ M.Pol ψ τ :=
  Submodule.mem_sInf.2 fun _ hN => hN.1 f₀ h

theorem mem_pol_of_actsD (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ)
    (h : ActsD (evI F) (M.heisLine ψ u) f f₁) : f₁ ∈ M.Pol ψ τ :=
  Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h

open scoped Classical in

theorem pol_stable (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (v a : Fin n × Fin d → mixedEmbedding.mixedSpace F) {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ)
    (h₁ : ∀ y, f₁ y = fderiv ℝ (⇑f) y v - 2 * Real.pi * Complex.I * (GlobalTheory.ArchUniq.trP F (Fin n × Fin d) y a : ℂ) * f y) :
    f₁ ∈ M.Pol ψ τ := by
  obtain ⟨u, hu, hD⟩ := GlobalTheory.HeisDerivArch.exists_heisLine_actsD_eq M ψ hψ (v, a)
  obtain ⟨D, hDa⟩ := GlobalTheory.HeisDeriv.exists_actsD_heisLine M ψ hψ u hu
  have e : D f = f₁ := by
    refine SchwartzMap.ext fun y => ?_
    rw [hD f (D f) (hDa f) y, h₁ y]
  exact e ▸ mem_pol_of_actsD M ψ τ hu hf (hDa f)

open scoped Classical in

theorem pol_dense : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → Dense (M.Pol B.ψ B.emb : Set (SInf F (Fin n × Fin d))) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨g, hg, Q, c, hc, hQ, hgQ⟩ := GlobalTheory.T.exists_gaussVacuum_nondegenerate_gaussian_dualPair F E σ B n d X W M χX χW om r s r' s' hP
  refine GlobalTheory.T.schwartzSubmodule_eq_top_of_gaussian_mem_derivStable _ _ g Q c hc hQ hgQ (mem_pol_of_isGauss M B.ψ B.emb hg) ?_ ?_
  · intro v f f₁ hf h₁
    refine pol_stable M B.ψ hψ B.emb v 0 hf fun y => ?_
    rw [h₁ y]
    simp [GlobalTheory.ArchUniq.trP]
  · intro ℓ f f₁ hf h₁
    have hnd := GlobalTheory.ArchSch.mixedTracePairing_nondegenerate F (Fin n × Fin d)
    obtain ⟨a, ha⟩ : ∃ a, ∀ y, GlobalTheory.ArchUniq.trP F (Fin n × Fin d) y a = ℓ y := by
      let e := (GlobalTheory.ArchSch.trP F (Fin n × Fin d)).flip.toDual hnd.flip
      refine ⟨e.symm ℓ.toLinearMap, fun y => ?_⟩
      calc GlobalTheory.ArchUniq.trP F (Fin n × Fin d) y (e.symm ℓ.toLinearMap) = e (e.symm ℓ.toLinearMap) y := by
            simp only [e, LinearMap.BilinForm.toDual_def]; rfl
        _ = ℓ y := by rw [e.apply_symm_apply]; rfl
    have hmem : (-(2 * Real.pi * Complex.I)) • f₁ ∈ M.Pol B.ψ B.emb := by
      refine pol_stable M B.ψ hψ B.emb 0 a hf fun y => ?_
      simp [h₁ y, ha y]
      ring
    have hne : (-(2 * Real.pi * Complex.I)) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := (M.Pol B.ψ B.emb).smul_mem (-(2 * Real.pi * Complex.I))⁻¹ hmem
    rwa [inv_smul_smul₀ hne] at this

end GlobalTheory.PolDense
