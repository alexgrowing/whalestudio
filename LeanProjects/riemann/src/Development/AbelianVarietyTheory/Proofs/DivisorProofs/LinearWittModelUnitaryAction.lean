import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactConjugateExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactIntertwinesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryIntertwinesStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.KSplit.om_linW_split : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) (locMat t b g) (locMat t c h) (ι φ) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v t b c ι hι g hg h hh φ hφ φ₁ hφ₁ hA
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.theta_action_exists hP F E σ B n d X W M χX χW om r s r' s' hp v
  have oneX : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by
    show u • (mat (1 : UA σ X.J) - 1) = 0
    simp [mat]
  have oneW : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := fun u _ => by
    show u • (mat (1 : UA σ W.J) - 1) = 0
    simp [mat]
  have hspl := hp.weil.isUSplitting
  obtain ⟨φ', ⟨hφ', hA'⟩, -⟩ := hex 1 oneX h hh φ hφ
  obtain ⟨φ'', ⟨hφ'', hA''⟩, -⟩ := hex g hg 1 oneW φ' hφ'
  have hcomp : Acts (evFin F v) (om (g, h)) φ φ'' := by
    intro R hR
    have e : om (g, h) = om (g, 1) * om (1, h) := by rw [← map_mul]; simp
    have hR' : Rest (evFin F v) φ' R := ⟨hR.1, by rw [← hA' R hR]; exact hspl.pres (1, h) _ hR.2⟩
    rw [e, Module.End.mul_apply, hA' R hR, hA'' R hR']
  have e1 : φ₁ = φ'' := (hex g hg h hh φ hφ).unique ⟨hφ₁, hA⟩ ⟨hφ'', hcomp⟩
  obtain ⟨κW, hW⟩ := GlobalTheory.T.linear_model_unitary_conjugate hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι
  obtain ⟨κX, hX⟩ := GlobalTheory.T.linear_model_compact_conjugate_exists hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι
  have sW := GlobalTheory.T.linear_model_compact_intertwines hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι κW hW h hh
  have sX := GlobalTheory.T.linear_model_unitary_intertwines hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι κX hX g hg
  rw [e1, hX g hg φ' hφ' φ'' hφ'' hA'', hW h hh φ hφ φ' hφ' hA', sW, sX]
  funext Y
  simp only [GlobalTheory.SplitFlip.omA, Pi.smul_apply, smul_eq_mul, Fintype.card_fin, MonoidHom.inv_apply,
    Units.val_inv_eq_inv_val, inv_inv, Matrix.mul_assoc]
  ring
