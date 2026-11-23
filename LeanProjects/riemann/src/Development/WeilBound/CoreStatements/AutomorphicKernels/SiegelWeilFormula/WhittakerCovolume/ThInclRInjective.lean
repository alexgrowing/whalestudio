import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem th_inclR_injective : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem th_incM_injective {m n : Type} : Function.Injective (incM F : Matrix m n E → Matrix m n (AE F E)) :=
  fun _ _ h => Matrix.map_injective th_inclR_injective h

theorem th_inclR_eq (x : E) : HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) x = inclR (F := F) (E := E) (AF F) x := rfl

theorem th_sigR_eq (x : AE F E) : HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ x = cA σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem th_JR (d : SD σ) (η : E) :
    HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (Jd d η) = inclR (F := F) (E := E) (AF F) η • (incM F d.A.J)ᵀ := by
  ext i j
  simp [HeckeCharacterZeroLocus.SiegelWeilU.JR, Jd, incM, th_inclR_eq, Matrix.transpose_apply, map_mul]

theorem th_mem_iff (d : SD σ) {η : E} (hη : η ≠ 0) (g : GL (Fin d.m) (AE F E)) :
    g ∈ UG (cA σ) (incM F d.A.J) ↔ g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (Jd d η) := by
  have hc : IsUnit (inclR (F := F) (E := E) (AF F) η) := (Ne.isUnit hη).map _
  have hm : (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) =
      (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ) := by
    ext i j; exact th_sigR_eq _
  show (g : Matrix (Fin d.m) (Fin d.m) (AE F E))ᵀ * incM F d.A.J * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ) =
      incM F d.A.J ↔ HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) (g : Matrix (Fin d.m) (Fin d.m) (AE F E)) *
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (Jd d η) * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)) = HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (Jd d η)
  rw [th_JR, HeckeCharacterZeroLocus.SiegelWeilU.cT, hm]
  set L := (g : Matrix (Fin d.m) (Fin d.m) (AE F E))ᵀ * incM F d.A.J * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ)
  have hL : ((g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ))ᵀ *
      (inclR (F := F) (E := E) (AF F) η • (incM F d.A.J)ᵀ) * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)) =
      inclR (F := F) (E := E) (AF F) η • Lᵀ := by
    simp only [L, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [hL]
  constructor
  · intro h; rw [h]
  · intro h
    have h2 := congrArg (fun M => (hc.unit⁻¹ : (AE F E)ˣ) • M) h
    simp only [Units.smul_def, smul_smul] at h2
    have h3 : ((hc.unit⁻¹ : (AE F E)ˣ) : AE F E) * inclR (F := F) (E := E) (AF F) η = 1 := by
      exact hc.val_inv_mul
    rw [h3, one_smul, one_smul] at h2
    have := congrArg Matrix.transpose h2
    simpa using this

def thE (d : SD σ) {η : E} (hη : η ≠ 0) : UA σ d.A.J ≃* HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ (Jd d η) :=
  MulEquiv.subgroupCongr (Subgroup.ext (th_mem_iff d hη))

theorem thE_cont (d : SD σ) {η : E} (hη : η ≠ 0) : Continuous (thE d hη) :=
  continuous_subtype_val.subtype_mk _

theorem thE_symm_cont (d : SD σ) {η : E} (hη : η ≠ 0) : Continuous (thE d hη).symm :=
  continuous_subtype_val.subtype_mk _

theorem th_haar_map {G H : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [Group H]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [hμ : μ.IsHaarMeasure] (e : G ≃* H)
    (he : Continuous e) (hs : Continuous e.symm) : (μ.map e).IsHaarMeasure := by
  let f : G ≃ᵐ H := (Homeomorph.mk e.toEquiv he hs).toMeasurableEquiv
  have hf : ∀ x, f x = e x := fun _ => rfl
  have hfe : μ.map e = μ.map f := rfl
  have hne : μ ≠ 0 := by
    intro h0
    have := (isOpen_univ : IsOpen (Set.univ : Set G)).measure_ne_zero μ Set.univ_nonempty
    rw [h0] at this; exact this rfl
  have hmeas : ∀ g : G, AEMeasurable (fun x => g * x) μ := by
    intro g
    by_contra hn
    have := Measure.map_of_not_aemeasurable hn
    rw [map_mul_left_eq_self μ g] at this
    exact hne this
  rw [hfe]
  refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro K hK
    rw [MeasurableEquiv.map_apply]
    have : f ⁻¹' K = e.symm '' K := by
      ext x; simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx; exact ⟨e x, by rw [← hf]; exact hx, e.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩; rw [hf, e.apply_symm_apply]; exact hy
    rw [this]
    exact (hK.image hs).measure_lt_top
  · intro h
    have hg : AEMeasurable (fun x => e.symm h * x) μ := hmeas _
    have hcomp : (fun y => h * y) ∘ f = f ∘ (fun x => e.symm h * x) := by
      funext x; simp only [Function.comp, hf, map_mul, MulEquiv.apply_symm_apply]
    have hh : AEMeasurable (fun y => h * y) (μ.map f) := by
      rw [aemeasurable_map_equiv_iff, hcomp]
      exact f.measurable.comp_aemeasurable hg
    ext S hS
    rw [Measure.map_apply_of_aemeasurable hh hS, MeasurableEquiv.map_apply, MeasurableEquiv.map_apply]
    have hpre : f ⁻¹' ((fun y => h * y) ⁻¹' S) = (fun x => e.symm h * x) ⁻¹' (f ⁻¹' S) := by
      rw [← Set.preimage_comp, ← Set.preimage_comp, hcomp]
    rw [hpre, ← Measure.map_apply_of_aemeasurable hg (f.measurableSet_preimage.mpr hS),
      map_mul_left_eq_self μ]
  · intro U hU hne'
    rw [MeasurableEquiv.map_apply]
    exact (hU.preimage he).measure_ne_zero μ (hne'.preimage f.surjective)

end PositivityTheory.SiegelWeilFormula.KWhit

end
