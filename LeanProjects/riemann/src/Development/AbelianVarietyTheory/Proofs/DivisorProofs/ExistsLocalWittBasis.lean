import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInverseExtendsToGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalEntriesUpperStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbSlotDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixActionColumnSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicColumnStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicColumnsLocalGLExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CMColumnLocalGLStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLocalGLExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixDiagonalColumnActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitIdeleAbsUniformizerStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.LeviBlockFrame

theorem exists_frame_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v), ∃ B : GL (Fin n) (Fv F v),
      (∀ (S : Finset (Fin r)), (∀ k ∈ S, ∀ i ≤ k, i ∈ S) → ∀ i ∈ S, ∀ (hi : i.val + 1 ≤ n),
        ∀ g ∈ GlobalTheory.SmGL.unipRad (Fv F v) (blockIndex hi), ∃ x : GLoc σ J v,
          IsCompAt σ J t B g x ∧ emb σ J v x ∈ GlobalTheory.StdPar.unip σ J Xf S) ∧
      (∀ (i : Fin r) (hi : i.val + 1 ≤ n) (ϖ : (Fv F v)ˣ), ∃ (x : GLoc σ J v) (e : (AF F ⊗[F] E)ˣ),
        IsCompAt σ J t B (GlobalTheory.SmGL.leviEmb (Fv F v) (blockIndex hi) (blockScalar₂ (Fv F v) n i ϖ)) x ∧
        GlobalTheory.LeviBlockRealization.IsBlockCentre σ J Xf Yf i e (emb σ J v x) ∧ (GlobalTheory.Doubling.absE F E e : ℝ) = nabs (Fv F v) ϖ) := by
  intro F E _ _ _ _ _ σ hcm n J hJ r Xf Yf hW v t
  have cTmul : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B' : Matrix (Fin b) (Fin c) E),
      Formalism.UG.cT (σ : E →+* E) (A * B') = Formalism.UG.cT (σ : E →+* E) B' * Formalism.UG.cT (σ : E →+* E) A := fun A B' => by
    simp [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have cTJ : Formalism.UG.cT (σ : E →+* E) J = J := Matrix.ext fun a b => hJ.1 a b
  have cTcT : Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) Xf) = Xf := Matrix.ext fun a b => by
    simp [Formalism.UG.cT, GlobalTheory.AdelicU.cm_conj_conj hcm]
  have hLX : Formalism.UG.cT (σ : E →+* E) Yf * J * Xf = 1 := by
    have h := congrArg (Formalism.UG.cT (σ : E →+* E)) hW.xy
    rw [cTmul, cTmul, cTJ, cTcT, ← Matrix.mul_assoc] at h
    rw [h]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, Matrix.one_apply, hab, Ne.symm hab]
  obtain ⟨hrn, C, hC⟩ := GlobalTheory.T.left_inverse_extends_to_GL E n r Xf (Formalism.UG.cT (σ : E →+* E) Yf * J) hLX
  let B : GL (Fin n) (Fv F v) := Matrix.GeneralLinearGroup.map (t : E →+* Fv F v) C
  have hB : ∀ (j : Fin r) (k : Fin n), (k : ℕ) = j →
      (∀ a, B.1 a k = t (Xf a j)) ∧ ∀ a, (B⁻¹).1 k a = t ((Formalism.UG.cT (σ : E →+* E) Yf * J) j a) := by
    intro j k hk
    refine ⟨fun a => ?_, fun a => ?_⟩
    · show t (C.1 a k) = _
      rw [(hC j k hk).1 a]
    · rw [← map_inv]
      show t ((C⁻¹).1 k a) = _
      rw [(hC j k hk).2 a]
  have hcomp : ∀ x : E, compFin F E v (inclR (F := F) (AF F) x) = inclR (F := F) (Fv F v) x := fun x => by
    change Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] x) = (1 : Fv F v) ⊗ₜ[F] x
    simp
  have compat : ∀ (g : GL (Fin n) (Fv F v)),
      IsCompAt σ J t B g ((splitEquiv hcm hJ t).symm (B * g * B⁻¹)) := fun g => by
    unfold IsCompAt
    rw [← splitEquiv_val hcm hJ t]
    exact congrArg Units.val ((splitEquiv hcm hJ t).apply_symm_apply _)
  refine ⟨B, ?_, ?_⟩
  · intro S hS i hiS hi g hg
    have key : ∀ g' : GL (Fin n) (Fv F v), g' ∈ GlobalTheory.SmGL.unipRad (Fv F v) (blockIndex hi) →
        (∀ j : Fin r, (matHom _ σ J (emb σ J v ((splitEquiv hcm hJ t).symm (B * g' * B⁻¹)))).1 *ᵥ (adMat F Xf)ᵀ j -
          (adMat F Xf)ᵀ j ∈ GlobalTheory.StdPar.colSpan F Xf {l | l < j ∧ l ≤ i}) ∧
        ∀ y ∈ GlobalTheory.StdPar.colPerp σ J Xf {l | l ≤ i},
          (matHom _ σ J (emb σ J v ((splitEquiv hcm hJ t).symm (B * g' * B⁻¹)))).1 *ᵥ y - y ∈
            GlobalTheory.StdPar.colSpan F Xf {l | l ≤ i} := by
      intro g' hg'
      have hent := GlobalTheory.T.unipotent_radical_entries_upper (Fv F v) n i hi g' hg'
      refine ⟨fun j => GlobalTheory.T.local_matrix_action_column_span F E σ n J r Xf v _ _ _ ?_, fun y hy => GlobalTheory.T.local_matrix_action_column_span F E σ n J r Xf v _ _ _ ?_⟩
      · have e : (fun a => compFin F E v ((adMat F Xf)ᵀ j a)) = fun a => inclR (F := F) (Fv F v) (Xf a j) :=
          funext fun a => hcomp _
        rw [e]
        exact GlobalTheory.T.isotropic_columns_local_GL_extension F E σ n J hJ r Xf hW.xx hrn v t hcm B (fun j k hk => (hB j k hk).1) i g' hent j
      · refine GlobalTheory.T.CM_column_local_GL_stabilizer F E σ n J hJ r Xf hrn v t hcm B (fun j k hk => (hB j k hk).1) i g' hent _ fun l hl => ?_
        have h1 : (adMat F (Formalism.UG.cT (σ : E →+* E) Xf * J) *ᵥ y) l = 0 := by
          have := Submodule.mem_iInf _ |>.1 hy l
          exact (Submodule.mem_iInf _ |>.1 this hl)
        have h2 := congrArg (compFin F E v) h1
        rw [map_zero, RingHom.map_mulVec] at h2
        have e : (Formalism.UG.cT (σ : E →+* E) Xf * J).map (inclR (F := F) (Fv F v)) =
            (adMat F (Formalism.UG.cT (σ : E →+* E) Xf * J)).map (compFin F E v) := by
          ext a b
          simp only [Matrix.map_apply, hcomp]
        rw [e]
        exact h2
    refine ⟨(splitEquiv hcm hJ t).symm (B * g * B⁻¹), compat g, ?_⟩
    refine GlobalTheory.T.standard_parabolic_column_stable F E σ n J r Xf S hS i hiS _ fun h' hh' => ?_
    rcases hh' with rfl | hh'
    · exact key g hg
    · rw [Set.mem_singleton_iff] at hh'
      subst hh'
      have e : (emb σ J v ((splitEquiv hcm hJ t).symm (B * g * B⁻¹)))⁻¹ =
          emb σ J v ((splitEquiv hcm hJ t).symm (B * g⁻¹ * B⁻¹)) := by
        rw [← map_inv, ← map_inv]
        congr 2
        group
      rw [e]
      exact key g⁻¹ (inv_mem hg)
  · intro i hi ϖ
    let e : (Fv F v ⊗[F] E)ˣ :=
      ⟨(splitAlgEquiv hcm t).symm ((ϖ : Fv F v), 1), (splitAlgEquiv hcm t).symm (((ϖ⁻¹ : (Fv F v)ˣ) : Fv F v), 1),
        by rw [← map_mul]; simp, by rw [← map_mul]; simp⟩
    have he1 : splitProj t (e : Fv F v ⊗[F] E) = ϖ := splitProj_symm hcm t _
    have he2 : splitProj (t.comp σ) (e : Fv F v ⊗[F] E) = 1 := splitProj_comp_symm hcm t _
    have hk : ((⟨i, by omega⟩ : Fin n) : ℕ) = i := rfl
    have hD := GlobalTheory.T.leviEmb_position_diagonal (Fv F v) n i hi ϖ
    refine ⟨(splitEquiv hcm hJ t).symm (B * GlobalTheory.SmGL.leviEmb (Fv F v) (blockIndex hi) (blockScalar₂ (Fv F v) n i ϖ) * B⁻¹),
      GlobalTheory.Doubling.ideleAt F E v e, compat _, ?_, GlobalTheory.T.split_idele_abs_uniformizer F E σ hcm v t ϖ e he1 he2⟩
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.wittFrame_local_GL_extension F E σ hcm n J hJ r Xf Yf hW v t B hB i _ hk (ϖ : Fv F v) _ hD e he1 he2
    exact GlobalTheory.T.local_matrix_diagonal_column_action F E σ n J r Xf Yf v _ e i h1 h2 h3

end GlobalTheory.LeviBlockFrame
