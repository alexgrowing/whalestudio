import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.HOfMain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilMeasdictHOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDict
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.MeasD
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Rat
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {η : E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
theorem mem_ratHerm_k {S : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n} :
    S ∈ MeasP.ratHerm F E σ d.n ↔ ∃ M : Matrix (Fin d.n) (Fin d.n) E, incM F M = (S.1 : Mx F E d.n d.n) := by
  simp only [MeasP.ratHerm, AddSubgroup.mem_comap, AddMonoidHom.mem_range]
  rfl
def ratE_k (hne : η ≠ 0)
    (hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ))
    (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    MeasP.ratHerm F E σ d.n ≃ nF σ d.Y d.b where
  toFun S := ⟨(_root_.PositivityTheory.SiegelWeilFormula.MeasD.hEq_k hOf hne hof herm).symm S.1, by
    rw [mem_nF_iff]
    obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.MeasD.mem_ratHerm_k.1 S.2
    refine ⟨-(η • Mᵀ), ?_⟩
    show -(inclR (F := F) (AF F) η • ((S.1).1 : Mx F E d.n d.n)ᵀ) = _
    rw [← hM]
    ext a b
    simp [incM, Matrix.map_apply, map_mul, map_neg]⟩
  invFun γ := ⟨_root_.PositivityTheory.SiegelWeilFormula.MeasD.hEq_k hOf hne hof herm γ.1, by
    rw [_root_.PositivityTheory.SiegelWeilFormula.MeasD.mem_ratHerm_k]
    obtain ⟨T, hT⟩ := (mem_nF_iff γ.1).1 γ.2
    refine ⟨-(η⁻¹ • Tᵀ), ?_⟩
    show _ = ((hOf γ.1).1 : Mx F E d.n d.n)
    rw [_root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof, hT]
    ext a b
    simp [incM, Matrix.map_apply, map_mul, map_neg]⟩
  left_inv S := Subtype.ext ((_root_.PositivityTheory.SiegelWeilFormula.MeasD.hEq_k hOf hne hof herm).apply_symm_apply S.1)
  right_inv γ := Subtype.ext ((_root_.PositivityTheory.SiegelWeilFormula.MeasD.hEq_k hOf hne hof herm).symm_apply_apply γ.1)
end Rat
theorem meas_hOf_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hR : _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g)
    {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) :
    MeasurableEmbedding hOf ∧ (lam.map hOf).IsAddHaarMeasure ∧
      IsAddFundamentalDomain (MeasP.ratHerm F E σ d.n) (hOf '' 𝓖) (lam.map hOf) ∧ lam.map hOf (hOf '' 𝓖) = 1 := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨-, -, -, hbo⟩ := nA_top hσ d.ok.frame
  haveI := hbo
  haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) := ⟨rfl⟩
  obtain ⟨-, hlam, hfd, h1⟩ := hc
  haveI := hlam
  let e := _root_.PositivityTheory.SiegelWeilFormula.MeasD.hEq_k hOf hR.ne hR.hof hR.herm
  let eM := e.toHomeomorph.toMeasurableEquiv
  have hemb : MeasurableEmbedding hOf := eM.measurableEmbedding
  refine ⟨hemb, ?_, ?_, ?_⟩
  · exact e.toAddEquiv.isAddHaarMeasure_map lam e.continuous e.symm.continuous
  · refine hfd.image_of_equiv eM.toEquiv (eM.measurePreserving_symm lam).quasiMeasurePreserving
      (_root_.PositivityTheory.SiegelWeilFormula.MeasD.ratE_k hR.ne hR.hof hR.herm) ?_
    intro S β
    show e (e.symm S.1 + β) = S.1 + e β
    rw [map_add, ContinuousAddEquiv.apply_symm_apply]
  · rw [hemb.map_apply, Set.preimage_image_eq _ hemb.injective, h1]
end PositivityTheory.SiegelWeilFormula.MeasD
end
end
