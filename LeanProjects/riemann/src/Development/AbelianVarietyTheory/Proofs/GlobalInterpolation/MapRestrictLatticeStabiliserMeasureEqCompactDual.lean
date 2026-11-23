import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport

noncomputable section

namespace GlobalTheory.VolStabImage

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

theorem map_restrict_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), M = P + Q → ∀ (J : Matrix (Fin M) (Fin M) E), J.det ≠ 0 → ∀ (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ), (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∀ (L : Set (Fin M → E)), MeasurableSet (stab σ J L : Set (HA (AF F) σ J)) → ∀ (cd : CDHaar) (μ : Measure (HA (AF F) σ J)), (∀ B : I → Set (UpqT P Q), (∀ ρ, MeasurableSet (B ρ)) → μ {h | StabHat F L (finMat σ J h) ∧ ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat σ J (θ ρ) h} = ∏ ρ, cd.cd P Q (B ρ)) → (∃ N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ, (∀ ρ, N ρ * A ρ = 1) ∧ ∀ ρ, A ρ * N ρ = 1) ∧ ∃ ψ : HA (AF F) σ J →* (I → UpqT P Q), Continuous ψ ∧ (∀ h ρ, UpqT.mat (ψ h ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) ∧ (μ.restrict (stab σ J L)).map ψ = Measure.pi fun _ => cd.cd P Q := by
  intro F E _ _ _ _ _ σ hcm I _ τ θ hθ M P Q hM J hJ A hA L hL cd μ hμ
  have hd : ∀ ρ, IsUnit (J.map (τ ρ)).det := fun ρ => by
    have : (J.map (τ ρ)).det = τ ρ J.det := ((τ ρ).map_det J).symm
    rw [this]
    exact ((map_ne_zero (τ ρ)).2 hJ).isUnit
  let N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ := fun ρ => (J.map (τ ρ))⁻¹ * ((A ρ)ᴴ * Formalism.UG.Jpq P Q)
  have hl : ∀ ρ, N ρ * A ρ = 1 := fun ρ => by
    change (J.map (τ ρ))⁻¹ * ((A ρ)ᴴ * Formalism.UG.Jpq P Q) * A ρ = 1
    rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul _ (hd ρ)]
  have e : Fin M ≃ (Fin P ⊕ Fin Q) := Fintype.equivOfCardEq (by simpa using hM)
  have hr : ∀ ρ, A ρ * N ρ = 1 := fun ρ => (Matrix.mul_eq_one_comm_of_equiv e).1 (hl ρ)
  refine ⟨⟨N, hl, hr⟩, ?_⟩
  choose ψ hψ hψm using fun ρ => GlobalTheory.VolPairExists.exists_hom _ (continuous_infMat J (hθ ρ))
    (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul σ J (θ ρ)) (infMat_unitary J hcm (hθ ρ)) (hA ρ) (hl ρ) (hr ρ)
  have hψA : ∀ h ρ, UpqT.mat (ψ ρ h) * A ρ = A ρ * infMat σ J (θ ρ) h := fun h ρ => by
    rw [hψm, Matrix.mul_assoc, hl, Matrix.mul_one]
  have hc : Continuous (MonoidHom.pi ψ) := continuous_pi hψ
  refine ⟨MonoidHom.pi ψ, hc, hψA, ?_⟩
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have : LocallyCompactSpace (UpqT P Q) :=
    (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (UpqT P Q) :=
    (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
  have := cd.haar P Q
  refine (Measure.pi_eq fun B hB => ?_).symm
  have hm : MeasurableSet (Set.univ.pi B) := MeasurableSet.univ_pi hB
  rw [Measure.map_apply hc.measurable hm, Measure.restrict_apply (hc.measurable hm), ← hμ B hB]
  congr 1
  ext h
  refine and_comm.trans (and_congr Iff.rfl ?_)
  rw [Set.mem_preimage, Set.mem_univ_pi]
  refine forall_congr' fun ρ => ⟨fun hb => ⟨_, hb, hψA h ρ⟩, ?_⟩
  rintro ⟨b, hb, hbA⟩
  have : b = ψ ρ h := GlobalTheory.VolPairExists.mat_injective (by
    rw [hψm, ← hbA, Matrix.mul_assoc, hr, Matrix.mul_one])
  subst this
  exact hb

end GlobalTheory.VolStabImage
