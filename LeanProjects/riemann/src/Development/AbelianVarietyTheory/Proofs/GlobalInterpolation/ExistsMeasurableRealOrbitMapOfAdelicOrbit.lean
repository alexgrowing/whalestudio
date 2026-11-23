import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.RealOrbitMap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_homeomorph (h : IsCMExt F E σ) {I : Type} [Fintype I] {τ : I → (E →+* ℂ)} (hτ : IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) :
    ∃ Φ : (Ainf F ⊗[F] E) ≃ₜ (I → ℂ), ∀ z ρ, Φ z ρ = θ ρ z := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  obtain ⟨e₀⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : LocallyCompactSpace (Ainf F ⊗[F] E) := e₀.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e₀.secondCountableTopology
  have hb := infEmb_bijective h hτ hθ
  let Θ : Ainf F ⊗[F] E →+ (I → ℂ) := (Pi.ringHom θ).toAddMonoidHom
  have hΘ : Continuous Θ := continuous_pi fun ρ => infEmb_continuous (hθ ρ)
  have ho : IsOpenMap Θ := AddMonoidHom.isOpenMap_of_sigmaCompact Θ hb.2 hΘ
  exact ⟨(Equiv.ofBijective Θ hb).toHomeomorphOfContinuousOpen hΘ ho, fun _ _ => rfl⟩

theorem mat_inv_mul {P Q : ℕ} (t : UpqT P Q) : UpqT.mat t⁻¹ * UpqT.mat t = 1 :=
  Units.inv_mul (show Formalism.UG.Upq P Q from t).1

theorem theta_projInf {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) :
    (fun i => θ (projInf (h • ratTup (F := F) (AF F) x) 0 i)) = infMat σ J θ h *ᵥ fun i => τ (x 0 i) := by
  funext i
  let p : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have e := RingHom.map_mulVec (θ.comp p) (HA.mat (AF F) σ J h).1 (ratTup (F := F) (AF F) x 0) i
  refine e.trans ?_
  have e2 : (θ.comp p) ∘ ratTup (F := F) (AF F) x 0 = fun i => τ (x 0 i) := by
    funext j
    rw [← hθ.1]
    show θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (1 ⊗ₜ x 0 j)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  rw [e2]
  rfl

theorem realOrbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)), IsCMFam τ → ∀ (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ) (J : Matrix (Fin M) (Fin M) E) (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ), (∀ ρ, N ρ * A ρ = 1) → (∀ ρ, A ρ * N ρ = 1) → ∀ x : Fin 1 → Fin M → E, AllSome (fun pt : (I → UpqT P Q) → (Fin 1 → Fin M → Ainf F ⊗[F] E) => ∀ g ρ, infCoord (θ ρ) (A ρ) (pt g) = UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) fun pt => Measurable pt ∧ (∀ g g', (∀ ρ, UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i)) = UpqT.mat (g' ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) → pt g = pt g') ∧ ∀ (h : HA (AF F) σ J) (t : I → UpqT P Q), (∀ ρ, UpqT.mat (t ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) → pt t = projInf (h⁻¹ • ratTup (F := F) (AF F) x) := by
  intro F E _ _ _ _ _ σ hcm I _ τ hτ θ hθ M P Q J A N hl hr x
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph hcm hτ hθ
  let v : (I → UpqT P Q) → I → Fin P ⊕ Fin Q → ℂ := fun g ρ => UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))
  have key : ∀ (Y : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : I → Fin P ⊕ Fin Q → ℂ),
      (∀ ρ, infCoord (θ ρ) (A ρ) Y = w ρ) ↔ Y = fun _ i => Φ.symm fun ρ => (N ρ *ᵥ w ρ) i := by
    intro Y w
    constructor
    · intro hY
      funext a i
      obtain rfl : a = 0 := Subsingleton.elim _ _
      apply Φ.injective
      rw [Φ.apply_symm_apply]
      funext ρ
      rw [hΦ, ← hY ρ, infCoord, Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
    · rintro rfl ρ
      have : (fun i => θ ρ (Φ.symm fun ρ => (N ρ *ᵥ w ρ) i)) = N ρ *ᵥ w ρ := by
        funext i
        rw [← hΦ, Φ.apply_symm_apply]
      rw [infCoord, this, Matrix.mulVec_mulVec, hr, Matrix.one_mulVec]
  refine ⟨⟨fun g _ i => Φ.symm fun ρ => (N ρ *ᵥ v g ρ) i, fun g => (key _ (v g)).2 rfl⟩, fun pt hpt => ?_⟩
  have hpt' : ∀ g, pt g = fun _ i => Φ.symm fun ρ => (N ρ *ᵥ v g ρ) i := fun g => (key _ (v g)).1 (hpt g)
  refine ⟨?_, fun g g' hg => ?_, fun h t ht => ?_⟩
  · haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
    haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
    haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
    haveI : SecondCountableTopology (UpqT P Q) :=
      (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
    rw [show pt = _ from funext hpt']
    refine measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun i => Continuous.measurable ?_
    refine Φ.symm.continuous.comp (continuous_pi fun ρ => (continuous_apply i).comp (f := fun a => N ρ *ᵥ v a ρ) ?_)
    exact continuous_const.matrix_mulVec
      ((GlobalTheory.VolPairExists.continuous_mat.comp (continuous_apply ρ).inv).matrix_mulVec continuous_const)
  · rw [hpt', hpt', show v g = v g' from funext hg]
  · rw [hpt']
    refine ((key _ (v t)).1 fun ρ => ?_).symm
    have e : A ρ * infMat σ J (θ ρ) h⁻¹ = UpqT.mat (t ρ)⁻¹ * A ρ := by
      calc A ρ * infMat σ J (θ ρ) h⁻¹
          = UpqT.mat (t ρ)⁻¹ * (UpqT.mat (t ρ) * A ρ) * infMat σ J (θ ρ) h⁻¹ := by
            rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
        _ = UpqT.mat (t ρ)⁻¹ * A ρ := by
            rw [ht, Matrix.mul_assoc, Matrix.mul_assoc, ← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul, mul_inv_cancel,
              Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_one, Matrix.mul_one]
    rw [infCoord, theta_projInf (hθ ρ), Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]

end GlobalTheory.RealOrbitMap
