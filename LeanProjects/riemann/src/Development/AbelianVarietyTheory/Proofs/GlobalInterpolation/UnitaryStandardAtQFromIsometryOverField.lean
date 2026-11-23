import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinearEquivDescendsOfPreservesImageStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryFourfoldLatticePreservesRationalVectorsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourfoldLatticeIsometryDenominatorCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InverseIsometryFourfoldLatticeDenominatorCoprimeStatement

noncomputable section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.KapIsom

theorem form_u (D : D7) (L : PeriodPair) (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
    (hu : Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))
    (x y : Fin 4 × D.what₂.Tau → ℂ) :
    ∑ w, u x w * (starRingEnd ℂ) (u y w) = ∑ w, x w * (starRingEnd ℂ) (y w) := by
  have h := hu x y
  change Formalism.L2.Th1.H.matH (hOne L _) (u x) (u y) = Formalism.L2.Th1.H.matH (hOne L _) x y at h
  rw [matH_hOne, matH_hOne] at h
  have hA : ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Formalism.L2.Th1.F.areaPos L).ne'
  exact (div_left_inj' hA).1 h

theorem main : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ∃ γ : IsoK D, γ.AtP q ∧ LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) = D.host.φ₀ ((γ.detRel B.γ₀ : D.host.K) : D.host.E) := by
  intro D cc δ B hcc hδ q _ hq2 hsplit hqc ι u hu h1 h2 h3
  obtain ⟨G, hG, hdet⟩ := GlobalTheory.T.exists_linearEquiv_descends_det_of_preserves_image (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) u
    (GlobalTheory.T.unitary_fourfoldLattice_preserves_rationalVectors D cc δ B hcc u h1)
  have hG' : ∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E))
      = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E) := fun v => hG v
  let γ : IsoK D :=
    { g := B.γ₀.g.trans G
      isom := by
        intro x y
        apply D.host.φ₀.injective
        have e1 := form_u D B.L u hu (fun w => D.host.φ₀ ((B.γ₀.g x w : D.host.K) : D.host.E))
          (fun w => D.host.φ₀ ((B.γ₀.g y w : D.host.K) : D.host.E))
        rw [hG', hG'] at e1
        rw [← B.γ₀.isom x y, map_sum, map_sum]
        simp only [map_mul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.emb_conj]
        exact e1 }
  refine ⟨γ, ⟨fun x hx => GlobalTheory.T.fourfoldLattice_isometry_denominator_coprime D cc δ B hcc q hqc u h1 h2 G hG' x hx,
    fun v hv => GlobalTheory.T.inverseIsometry_fourfoldLattice_denominator_coprime_alt D cc δ B hcc hδ q hqc u hu h1 h2 h3 G hG' v hv⟩, ?_⟩
  have hd : γ.detRel B.γ₀ = LinearMap.det (G : (Fin 4 × D.what₂.Tau → D.host.K) →ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)) := by
    have e : (B.γ₀.g.symm.trans γ.g) = G := by
      apply LinearEquiv.ext; intro v
      show G (B.γ₀.g (B.γ₀.g.symm v)) = G v
      rw [LinearEquiv.apply_symm_apply]
    unfold IsoK.detRel
    rw [e]
  rw [hdet, hd]
  rfl

end GlobalTheory.KapIsom
