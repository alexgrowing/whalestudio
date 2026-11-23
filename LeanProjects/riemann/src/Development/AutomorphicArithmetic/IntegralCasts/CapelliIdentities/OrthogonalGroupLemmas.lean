import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ClosureSpanCoefficients

theorem UpperTheory.Reformulated.B.OrthogonalGroupLemmas.aux1 :
    ∀ (F : Type) [inst : Field F] [inst_1 : NumberField F] {a b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F},
      a ∈
          {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F |
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a = (0 : NumberField.mixedEmbedding.mixedSpace F) ∧
              ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
                (GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) a ∈
                  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v} →
        b ∈
            {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F |
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a = (0 : NumberField.mixedEmbedding.mixedSpace F) ∧
                ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
                  (GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) a ∈
                    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v} →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (a + b) = (0 : NumberField.mixedEmbedding.mixedSpace F) ∧
            ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
              (GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (a + b) ∈
                IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v := by
  intro F _ _ a b ha hb
  refine ⟨?_, fun v => ?_⟩
  · have h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (a + b) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F b :=
      map_add (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
    rw [h, ha.1, hb.1, add_zero]
  · rw [map_add]
    exact add_mem (ha.2 v) (hb.2 v)

theorem UpperTheory.Reformulated.B.OrthogonalGroupLemmas.aux2 :
    ∀ (F : Type) [inst : Field F] [inst_1 : NumberField F],
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) = (0 : NumberField.mixedEmbedding.mixedSpace F) ∧
        ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
          (GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ∈
            IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v := by
  intro F _ _
  refine ⟨map_zero (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F), fun v => ?_⟩
  rw [map_zero]
  exact zero_mem _

theorem UpperTheory.Reformulated.B.OrthogonalGroupLemmas.aux3 :
    ∀ (F : Type) [inst : Field F] [inst_1 : NumberField F] {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F},
      a ∈
          {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F |
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a = (0 : NumberField.mixedEmbedding.mixedSpace F) ∧
              ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
                (GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) a ∈
                  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v} →
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (-a) = (0 : NumberField.mixedEmbedding.mixedSpace F) ∧
          ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
            (GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (-a) ∈
              IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v := by
  intro F _ _ a ha
  refine ⟨?_, fun v => ?_⟩
  · have h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (-a) = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a :=
      map_neg (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1
    rw [h, ha.1, neg_zero]
  · rw [map_neg]
    exact neg_mem (ha.2 v)

noncomputable def UpperTheory.Reformulated.B.OrthogonalGroupLemmas.Oh :
    (F : Type) → [inst : Field F] → [inst_1 : NumberField F] → AddSubgroup (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) :=
    fun (F : Type) [inst : Field F] [inst_1 : NumberField F] ↦
      {
        carrier :=
          {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F |
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a = (0 : NumberField.mixedEmbedding.mixedSpace F) ∧
              ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
                (GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) a ∈
                  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v},
        add_mem' := @UpperTheory.Reformulated.B.OrthogonalGroupLemmas.aux1 F inst inst_1, zero_mem' := UpperTheory.Reformulated.B.OrthogonalGroupLemmas.aux2 F,
        neg_mem' := @UpperTheory.Reformulated.B.OrthogonalGroupLemmas.aux3 F inst inst_1 : AddSubgroup (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) }

theorem UpperTheory.Reformulated.B.OrthogonalGroupLemmas.lat_gen :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E]
      {n : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n},
      Submodule.IsLattice E Y.L →
        ∃ (m : ℕ) (x : Fin m → ↥Y.L),
          Submodule.span ℤ (Set.range x) = ⊤ ∧
            ∀ (z : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E),
              z ∈ GlobalTheory.ThK.latHat Y ↔
                ∃ (a : Fin m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F),
                  (∀ (i : Fin m), a i ∈ UpperTheory.Reformulated.B.OrthogonalGroupLemmas.Oh F) ∧ ∑ i : Fin m, a i • GlobalTheory.ThK.incV F (↑(x i) : Fin n → E) = z := by
  intro F E _ _ _ _ _ n Y hL
  have h1 : Module.Finite (NumberField.RingOfIntegers E) Y.L := Module.Finite.iff_fg.2 hL.fg
  have h2 : Module.Finite ℤ Y.L := Module.Finite.trans (NumberField.RingOfIntegers E) Y.L
  obtain ⟨m, x, hx⟩ := Module.Finite.exists_fin (R := ℤ) (M := Y.L)
  refine ⟨m, x, hx, fun z => ?_⟩
  let f : Y.L →+ (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :=
    { toFun := fun l => GlobalTheory.ThK.incV F (l : Fin n → E)
      map_zero' := funext fun _ => map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F))
      map_add' := fun a b => funext fun i =>
        map_add (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) (a.1 i) (b.1 i) }
  have hs : GlobalTheory.ThK.latHat Y = AddSubgroup.closure
      {z | ∃ a ∈ UpperTheory.Reformulated.B.OrthogonalGroupLemmas.Oh F, ∃ l : Y.L, z = a • f l} := by
    unfold GlobalTheory.ThK.latHat
    congr 1
    ext w
    constructor
    · rintro ⟨a, h0, hv, y, hy, rfl⟩
      exact ⟨a, ⟨h0, hv⟩, ⟨y, hy⟩, rfl⟩
    · rintro ⟨a, ⟨h0, hv⟩, y, rfl⟩
      exact ⟨a, h0, hv, y.1, y.2, rfl⟩
  rw [hs]
  exact UpperTheory.closure_span_coefficients (UpperTheory.Reformulated.B.OrthogonalGroupLemmas.Oh F) f x hx z
