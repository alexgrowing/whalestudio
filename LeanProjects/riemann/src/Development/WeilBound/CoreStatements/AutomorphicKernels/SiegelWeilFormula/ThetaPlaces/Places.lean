import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.RelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def archimedeanEmbeddingTensor (B : Base F E) (w : InfinitePlace F) : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ :=
  (infEmb (B.emb w)).comp (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)).toRingHom

theorem thW_eq (B : Base F E) (w : InfinitePlace F) (z : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E) :
    thW B w z = starRingEnd ℂ (archimedeanEmbeddingTensor B w z) := rfl

theorem archimedean_embedding_tmul (B : Base F E) (w : InfinitePlace F) (a : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (x : E) :
    archimedeanEmbeddingTensor B w (a ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding w (a w) * (B.emb w).1 x := rfl

theorem thW_th' (B : Base F E) (w : InfinitePlace F) (y : AE F E) :
    thW B w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (B.emb w) y) := by
  have h : Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = compInf F E w y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  show starRingEnd ℂ (infEmb (B.emb w) (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y))) = _
  rw [h]
  rfl

theorem archimedean_embedding_family (B : Base F E) :
    Formalism.IndefR.DatumF.IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) (archimedeanEmbeddingTensor B) := by
  intro w
  refine ⟨fun x => ?_, ?_⟩
  · rw [archimedean_embedding_tmul]
    show InfinitePlace.Completion.extensionEmbedding w 1 * (B.emb w).1 x = (B.emb w).1 x
    rw [map_one, one_mul]
  · have : (fun a : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F => archimedeanEmbeddingTensor B w (a ⊗ₜ[F] (1 : E))) =
        fun a => InfinitePlace.Completion.extensionEmbedding w (a w) := by
      funext a; rw [archimedean_embedding_tmul, map_one, mul_one]
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

theorem thW_infEmb (B : Base F E) (w : InfinitePlace F) :
    Formalism.MainNotions.StandardLattice.IsInfEmb (ComplexEmbedding.conjugate (B.emb w).1) (thW B w) := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [thW_eq, (archimedean_embedding_family B w).1 x]
    rfl
  · exact Complex.continuous_conj.comp (archimedean_embedding_family B w).2

theorem isCMFam_conj (B : Base F E) (h : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) :
    GlobalTheory.Mem.Vol.IsCMFam (fun w : InfinitePlace F => ComplexEmbedding.conjugate (B.emb w).1) := by
  have hT := GlobalTheory.BotLValue.isCMType_embOver h B.emb
  have cc : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := fun φ => star_star φ
  beta_reduce at hT
  constructor
  · intro i j e
    simp only [InfinitePlace.mk_conjugate_eq] at e
    obtain ⟨k, -, hk⟩ := hT (B.emb i).1
    have hi := hk i (Or.inl rfl)
    have hj : j = k := by
      refine hk j ?_
      rcases InfinitePlace.mk_eq_iff.1 e with e' | e'
      · exact Or.inl e'
      · right
        show (B.emb i).1 = ComplexEmbedding.conjugate (B.emb j).1
        rw [← e', cc]
    rw [hi, hj]
  · intro φ
    obtain ⟨k, hk, -⟩ := hT φ.embedding
    beta_reduce at hk
    refine ⟨k, ?_⟩
    simp only [InfinitePlace.mk_conjugate_eq]
    rcases hk with e | e
    · rw [← e, InfinitePlace.mk_embedding]
    · rw [show (B.emb k).1 = ComplexEmbedding.conjugate φ.embedding by
          rw [e, cc],
        InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

theorem isPlaces_thW' (B : Base F E) (hB : B.IsGood σ) : Gen.IsPlaces σ B.ψ (thW B) (fun _ => -1) := by
  have : IsTotallyReal F := hB.cm.1
  refine ⟨fun w => GlobalTheory.Mem.VolExists.infEmb_continuous (thW_infEmb B w),
    GlobalTheory.Mem.VolExists.infEmb_bijective hB.cm (isCMFam_conj B hB.cm) (fun w => thW_infEmb B w),
    fun w z => GlobalTheory.Mem.VolExists.infEmb_sigR hB.cm (thW_infEmb B w) z, fun _ => by norm_num, fun x => ?_⟩
  have hs := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).2.2 (archimedeanEmbeddingTensor B) (archimedean_embedding_family B) x
  have hs' : B.ψ ((x, 0) : AF F) = _ := hs
  change B.ψ ((x, 0) : AF F) = _
  rw [hs']
  congr 1
  have hr : ∀ w, starRingEnd ℂ (archimedeanEmbeddingTensor B w (x ⊗ₜ[F] (1 : E))) = archimedeanEmbeddingTensor B w (x ⊗ₜ[F] (1 : E)) := fun w => by
    rw [archimedean_embedding_tmul, map_one, mul_one, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w),
      Complex.conj_ofReal]
  simp only [thW_eq, hr]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

end PositivityTheory.SiegelWeilFormula.ThetaDictR

end
