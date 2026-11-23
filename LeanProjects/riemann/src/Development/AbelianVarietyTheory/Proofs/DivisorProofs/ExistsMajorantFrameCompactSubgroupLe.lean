import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPosDefHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPosDefSimultaneousNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Matrix
noncomputable section

namespace GlobalTheory.CptMajorant

theorem exists_frame_le_majCpt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ K : Subgroup (GAd σ J), K ≤ infPts σ J → IsCompact (K : Set (GAd σ J)) →
    ∃ c : (∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)),
      (∀ w, ∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) ∧ K ≤ majCpt σ J c := by
  intro F E _ _ _ _ _ σ h n J hJ K hKinf hK
  have key : ∀ w : InfinitePlace F, ∃ c : GL (Fin n) (w.Completion ⊗[F] E),
      (∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) c.1 * JR w.Completion J * c.1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) ∧ ∀ k ∈ K, projArch σ J w k ∈ stabArch σ J w c := by
    intro w
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    let e := RingEquiv.ofBijective _ (infEmb_bijective h τ)
    have : IsTopologicalRing (w.Completion ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
    let φ : GAd σ J →* GL (Fin n) ℂ :=
      (Units.map (infEmb τ).mapMatrix.toMonoidHom).comp ((matHom _ σ J).comp (projArch σ J w))
    have hφv : ∀ x, (φ x).1 = (matHom _ σ J (projArch σ J w x)).1.map (infEmb τ) := fun x => rfl
    have hcv : Continuous fun x : GAd σ J => (φ x).1 := by
      simp only [hφv]
      exact (Units.continuous_val.comp ((isEmbedding_matHom _ σ J).continuous.comp
        (continuous_projArch σ J w))).matrix_map (GlobalTheory.Orb.continuous_infEmb τ)
    have hφ : Continuous φ := Units.continuous_iff.2 ⟨hcv, by
      simp only [← map_inv]; exact hcv.comp continuous_inv⟩
    obtain ⟨P, hPh, hPpos, hPinv⟩ := GlobalTheory.T.exists_posDef_hermitian_invariant_of_isCompact (K.map φ) (by rw [Subgroup.coe_map]; exact hK.image hφ)
    have hG : (J.map τ.1).IsHermitian := by
      ext i j
      exact (h.2.2.2 τ.1 _).symm.trans (congrArg _ (hJ.1 i j))
    have hd : (J.map τ.1).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero _).2 hJ.2
    obtain ⟨ε, Q, hQ, hQu⟩ := GlobalTheory.T.hermitian_posDef_simultaneous_normal_form hG hd hPh hPpos
    have h1 : (Formalism.UG.bc e.symm.toRingHom Q).1.map (infEmb τ) = Q.1 := Matrix.ext fun i j => e.apply_symm_apply _
    have h1' : ((Formalism.UG.bc e.symm.toRingHom Q)⁻¹).1.map (infEmb τ) = (Q⁻¹).1 :=
      Matrix.ext fun i j => e.apply_symm_apply _
    have h2 : (JR w.Completion J).map (infEmb τ) = J.map τ.1 := by ext r s; simp [JR, inclR]
    refine ⟨Formalism.UG.bc e.symm.toRingHom Q, ⟨ε, Matrix.map_injective e.injective ?_⟩, fun k hk => ?_⟩
    · change Matrix.map _ (infEmb τ) = Matrix.map _ (infEmb τ)
      rw [Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR h, h1, h2, hQ, Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      split_ifs <;> simp
    · rw [mem_stabArch]
      change Formalism.UG.cT _ _ * 1 * _ = 1
      refine Matrix.map_injective e.injective ?_
      change Matrix.map _ (infEmb τ) = Matrix.map _ (infEmb τ)
      have hu := hQu (φ k).1 (hPinv _ ⟨k, hk, rfl⟩) (by
        have : Formalism.UG.cT (sigR _ σ) (matHom _ σ J (projArch σ J w k)).1 * JR w.Completion J *
          (matHom _ σ J (projArch σ J w k)).1 = JR w.Completion J := (projArch σ J w k).2
        have := congrArg (fun A => A.map (infEmb τ)) this
        simpa only [Matrix.map_mul, Frames.map_cT_sigR h, h2, hφv] using this)
      simpa only [Matrix.mul_one, Matrix.map_mul, Frames.map_cT_sigR h, Units.val_mul, h1, h1', hφv,
        Matrix.map_one _ (map_zero _) (map_one _)] using hu
  choose c hc hKc using key
  exact ⟨c, hc, fun k hk => mem_majCpt.2 ⟨hKinf hk, fun w => hKc w k hk⟩⟩

end GlobalTheory.CptMajorant
