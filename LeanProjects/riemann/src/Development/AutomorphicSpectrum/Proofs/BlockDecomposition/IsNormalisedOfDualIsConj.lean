import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.ArchBaseChangeOfHyp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.LocalComponentGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsThetaPull
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointLocalComponentMemLocalUn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLinearCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeL2InnerProduct

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.OneExDatum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev sConj (x : HeightOneSpectrum (𝓞 E)) :
    GL (Fin n) ((GlobalTheory.ThetaSatake.cw x).adicCompletion E) →* GL (Fin n) (x.adicCompletion E) :=
  GeneralLinearGroup.map (n := Fin n) (conjLoc (IsCMField.complexConj E).toRingEquiv x)

theorem exists_equiv_of_dualIsConj {π : CuspSub E n} (hd : GlobalTheory.ContraPair.DualIsConj π) (x : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin n) ((GlobalTheory.ThetaSatake.cw x).adicCompletion E)))
    (τ : SmIrr (GL (Fin n) (x.adicCompletion E))) (hσ : π.IsLocComp (GlobalTheory.ThetaSatake.cw x) σ)
    (ha : IsAdmissible σ.ρ) (hτ : π.IsLocComp x τ) :
    ∃ T : σ.V ≃ₗ[ℂ] τ.V, ∀ g v, τ.ρ (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc x) n g) (T v) = T (σ.ρ g v) := by
  obtain ⟨B, -, hB, hfinB, -, -⟩ := hd
  obtain ⟨f, f0, hf⟩ := hτ
  have hs : Continuous (sConj (n := n) x) :=
    Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec _ x).1)
  let τ' : SmIrr (GL (Fin n) ((GlobalTheory.ThetaSatake.cw x).adicCompletion E)) :=
    { V := τ.V, ρ := MonoidHom.comp τ.ρ (sConj x), smooth := fun v => (τ.smooth v).preimage hs
      irred := GlobalTheory.ConjPairLoc.irred_comp _ _ (GlobalTheory.ConjPairLoc.map_conjLoc_surjective x) τ.irred }
  have hσ' := ((cuspSub_iff π).2.1 _ σ).2 hσ
  let β : π.V →ₗ[ℂ] τ.V →ₗ[ℂ] ℂ := B.compl₂ f
  have hβ : β ≠ 0 := fun h => f0 (LinearMap.ext fun v =>
    hB (f v) fun φ => LinearMap.congr_fun (LinearMap.congr_fun h φ) v)
  obtain ⟨F, hF⟩ := GlobalTheory.LocDual.exists_comp_ne_zero π.V π.stable π.irred _ σ hσ' β hβ
  let P : σ.V →ₗ[ℂ] τ.V →ₗ[ℂ] ℂ := β ∘ₗ F.1.codRestrict π.V F.2.1
  have hP : ∀ g u v, P (σ.ρ g u) (τ'.ρ g v) = P u v := fun g u v => by
    have e1 : F.1.codRestrict π.V F.2.1 (σ.ρ g u) =
        π.op (.fin (locGL E n _ g)) (F.1.codRestrict π.V F.2.1 u) := Subtype.ext (F.2.2 g u)
    have e2 : f (τ'.ρ g v) = π.op (GlobalTheory.ContraPair.conjOp (.fin (locGL E n _ g))) (f v) := by
      change f (τ.ρ (sConj x g) v) = π.op (.fin (GeneralLinearGroup.map _ (locGL E n _ g))) (f v)
      rw [GlobalTheory.ConjPairLoc.conjFin_locGL, hf, CuspSub.locRep_eq]
    change B (F.1.codRestrict π.V F.2.1 (σ.ρ g u)) (f (τ'.ρ g v)) = B (F.1.codRestrict π.V F.2.1 u) (f v)
    rw [e1, e2, hfinB]
  have hirr : (GlobalTheory.SmGL.contra σ.ρ).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis _ n) ha σ.irred
  let e₁ := (GlobalTheory.InvPairing.pairMap σ.ρ τ'.smooth P hP).ofBijective
    (GlobalTheory.InvPairing.pairMap_bijective σ.ρ τ'.smooth P hP hF τ'.irred hirr)
  obtain ⟨e₂⟩ := GlobalTheory.GelfandKazhdan.equiv_contra _ n σ.V σ.ρ ha σ.irred
  let e : σ.V ≃ₗ[ℂ] τ.V := (e₂.trans e₁.symm).toLinearEquiv
  have he : ∀ g v, e (σ.ρ g v) = τ.ρ (sConj x (invT n _ g)) (e v) := fun g v => by
    have h := GlobalTheory.ConjPairLoc.equiv_apply (e₂.trans e₁.symm) (invT n _ g) v
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose n _ (invT n _ g) = g := Units.ext (Matrix.transpose_transpose _)
    rw [MonoidHom.comp_apply, h1] at h
    exact h
  refine ⟨e, fun g v => ?_⟩
  rw [he]
  congr 2
  exact Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)

theorem eq_cw_of_conjPl {w u : HeightOneSpectrum (𝓞 E)} (h : ConjPl w u) : u = GlobalTheory.ThetaSatake.cw w := by
  obtain ⟨h1, h2⟩ := h
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u w).1 h1.symm with e | e
  · subst e
    rcases h2 with h2 | h2
    · exact absurd rfl h2
    · exact (GlobalTheory.BCT.LocMem.conjSrc_eq_of_not_split _ h2).symm
  · exact eq_conjSrc e

end GlobalTheory.CompanionTheory.OneExDatum

end
