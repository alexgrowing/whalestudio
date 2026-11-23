import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
open scoped TensorProduct Matrix
open NumberField Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.ArchFrameConj

open GlobalTheory.MaxCptConj GlobalTheory.UAut

theorem exists_frame_mem_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ K' : Subgroup (GAd σ J), GlobalTheory.UAut.IsMaxCpt σ J K' →
      ∀ (k : GAd σ J) (w : InfinitePlace F) (τ : EmbOver E w), ∃ (C : GL (Fin n) ℂ) (ε : Fin n → Bool),
        C.1ᴴ * J.map τ.1 * C.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
        ∀ y : GArch σ J w, ((C⁻¹).1 * GlobalTheory.Orb.archMat σ J τ y * C.1)ᴴ * ((C⁻¹).1 * GlobalTheory.Orb.archMat σ J τ y * C.1) = 1 →
          k⁻¹ * embArch σ J w y * k ∈ K' := by
  intro F E _ _ _ _ _ σ h n J hJ K' hK k w τ
  choose c ε hc using Frames.exists_arch_frame h hJ
  obtain ⟨a, -, e⟩ := exists_conj_majCpt h (fun w => ⟨ε w, hc w⟩) hK
  obtain ⟨b, hb⟩ : ∃ b : GAd σ J, b = a * k⁻¹ := ⟨_, rfl⟩
  set m : GL (Fin n) (w.Completion ⊗[F] E) := matHom _ σ J (projArch σ J w b) with hm
  set C' : GL (Fin n) (w.Completion ⊗[F] E) := m⁻¹ * c w with hC'
  have inj := Matrix.map_injective (m := Fin n) (n := Fin n) (infEmb_bijective h τ).1
  have one : (1 : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)).map (infEmb τ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hC : ∀ x : GL (Fin n) (w.Completion ⊗[F] E), (Formalism.UG.bc (infEmb τ) x).1 = x.1.map (infEmb τ) := fun x => rfl
  have hJR : (JR w.Completion J).map (infEmb τ) = J.map τ.1 := by ext r s; simp [JR, inclR]
  have hmU : Formalism.UG.cT (sigR _ σ) (m⁻¹).1 * JR w.Completion J * (m⁻¹).1 = JR w.Completion J := by
    have := ((projArch σ J w b)⁻¹).2
    rw [hm, ← map_inv]
    exact this
  have hC'J : Formalism.UG.cT (sigR _ σ) C'.1 * JR w.Completion J * C'.1 =
      Matrix.diagonal fun i => if ε w i then 1 else -1 := by
    rw [← hc w, hC', Units.val_mul, Formalism.UG.cT_mul]
    calc _ = Formalism.UG.cT (sigR _ σ) (c w).1 * (Formalism.UG.cT (sigR _ σ) (m⁻¹).1 * JR w.Completion J * (m⁻¹).1) * (c w).1 := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hmU]
  refine ⟨Formalism.UG.bc (infEmb τ) C', ε w, ?_, fun y hy => ?_⟩
  · rw [hC, ← hJR, ← Frames.map_cT_sigR h, ← Matrix.map_mul, ← Matrix.map_mul, hC'J, Matrix.diagonal_map (map_zero _)]
    congr 1; funext i; split_ifs <;> simp
  · rw [e, show a * (k⁻¹ * embArch σ J w y * k) * a⁻¹ = b * embArch σ J w y * b⁻¹ by rw [hb]; group, mem_majCpt]
    refine ⟨?_, fun u => ?_⟩
    · rw [mem_infPts]; simp [map_mul, map_inv]
    rcases eq_or_ne u w with rfl | hu
    · rw [map_mul, map_mul, map_inv, projArch_embArch_self, mem_stabArch]
      have hX : (c u)⁻¹ * matHom _ σ J (projArch σ J u b * y * (projArch σ J u b)⁻¹) * c u = C'⁻¹ * matHom _ σ J y * C' := by
        rw [hC', map_mul, map_mul, map_inv, ← hm]; group
      rw [hX]
      change Formalism.UG.cT _ (C'⁻¹ * matHom _ σ J y * C').1 * 1 * (C'⁻¹ * matHom _ σ J y * C').1 = 1
      refine inj ?_
      simp only [mul_one, Matrix.map_mul, Frames.map_cT_sigR h, Units.val_mul, one]
      have hCi : ((Formalism.UG.bc (infEmb τ) C')⁻¹).1 = (C'⁻¹).1.map (infEmb τ) := by rw [← map_inv]; rfl
      simpa only [hCi, hC, GlobalTheory.Orb.archMat_apply, Matrix.map_mul] using hy
    · rw [map_mul, map_mul, map_inv, projArch_embArch_ne σ J hu, mul_one, mul_inv_cancel]
      exact one_mem _

end GlobalTheory.ArchFrameConj
