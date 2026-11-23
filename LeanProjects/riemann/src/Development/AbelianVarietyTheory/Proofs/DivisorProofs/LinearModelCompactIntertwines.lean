import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSplittingPairIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelDoubleSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingIwasawaDecompositionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.DblScal in
theorem GlobalTheory.DblScal.scalW_main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ h ∈ UAt σ W (evFin F v), κ h = (chrW χX t (GlobalTheory.SplitFlip.gdet (locMat t c h)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (locMat t c h)) (-(n : ℂ) / 2) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c ι hι κ hκ h hh
  obtain ⟨⟨-, dd, omd, hdc, hws, hbox⟩, -, -⟩ := hP.weil
  have hspl := hws.2.1
  have hloc := GlobalTheory.T.double_splitting_pair_identity hPr F E σ B n d X W M χX χW om r s r' s' hP dd omd hspl v
  obtain ⟨ιd, hιd, hprod⟩ := GlobalTheory.T.linear_model_double_splitting hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c ι hι dd hdc
  obtain ⟨cd, hcd⟩ := GlobalTheory.T.double_scaling_local_identity hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hspl hloc ιd hιd
  obtain ⟨χd, hχd⟩ := GlobalTheory.T.double_scaling_local_equivariance hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hspl hloc ιd hιd cd hcd
  obtain ⟨gd, hgd⟩ := exists_diag_one h
  have hgdAt : gd ∈ UDAt σ W.J (evFin F v) := by
    intro u hu
    change u • (((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) - 1) = 0
    have h1 : u • (mat h - 1) = 0 := hh u hu
    rw [hgd, fromBlocks_sub_one, Matrix.fromBlocks_smul, h1]
    simp
  have e1 : κ h = cd gd := GlobalTheory.T.linear_model_compact_equivariance hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c ι hι κ hκ dd omd hdc hspl
    (fun g gd' hg φ₁ hφ₁ φ₂ hφ₂ => hbox g gd' hg φ₁ hφ₁ φ₂ hφ₂) hloc ιd hιd hprod cd hcd h hh gd hgd
  obtain ⟨p, hpAt, hp⟩ := GlobalTheory.T.double_scaling_iwasawa_decomposition F E σ B n d X W M χX χW om r s r' s' hP v t c (fixDiag (locMat t c h))
  have e5 := GlobalTheory.T.double_scaling_local_vanishing hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hdc hws hloc ιd hιd cd hcd p hpAt
    ⟨1, by rw [hp]; exact fixDiag_diag _⟩
  rw [hp, gdet_fixDiag] at e5
  have f1 : cd gd = χd (GlobalTheory.SplitFlip.gdet (locMat t c h)) := by rw [hχd gd hgdAt, gdet_locMatD_diag t c h gd hgd]
  have f2 : cd p = χd (GlobalTheory.SplitFlip.gdet (locMat t c h)) := by rw [hχd p hpAt, hp, gdet_fixDiag]
  rw [e1, f1, ← f2]
  exact e5
