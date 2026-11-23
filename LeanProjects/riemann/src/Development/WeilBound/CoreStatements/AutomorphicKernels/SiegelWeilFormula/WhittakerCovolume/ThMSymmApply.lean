import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThInclRInjective

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

instance th_borelUA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

instance th_borelHA {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ J) := ⟨rfl⟩

def thM (d : SD σ) {η : E} (hη : η ≠ 0) : UA σ d.A.J ≃ᵐ HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ (Jd d η) :=
  (Homeomorph.mk (thE d hη).toEquiv (thE_cont d hη) (thE_symm_cont d hη)).toMeasurableEquiv

theorem th_sigR_incl (x : E) :
    HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ (inclR (F := F) (E := E) (AF F) x) = inclR (F := F) (E := E) (AF F) (σ x) := by
  simp [HeckeCharacterZeroLocus.SiegelWeilU.sigR, inclR, Algebra.TensorProduct.map_tmul]

theorem th_cT_map {M : ℕ} (γ : Matrix (Fin M) (Fin M) E) :
    (HeckeCharacterZeroLocus.SiegelWeilU.cT (σ : E →+* E) γ).map (inclR (F := F) (E := E) (AF F)) =
      HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) (γ.map (inclR (F := F) (E := E) (AF F))) := by
  ext i j
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.cT, Matrix.map_apply, Matrix.transpose_apply]
  exact (th_sigR_incl _).symm

def thE' (d : SD σ) {η : E} (hη : η ≠ 0) (g : UA σ d.A.J) : HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (Jd d η) := thE d hη g

theorem th_rat_iff (d : SD σ) {η : E} (hη : η ≠ 0) (g : UA σ d.A.J) :
    g ∈ ratU σ d.A.J ↔ thE' d hη g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HFinIn (AF F) σ (Jd d η) := by
  rw [ratU, Subgroup.mem_subgroupOf, MonoidHom.mem_range, HeckeCharacterZeroLocus.SiegelWeilU.HFinIn, Subgroup.mem_subgroupOf,
    HeckeCharacterZeroLocus.SiegelWeilU.HFin, Subgroup.mem_map]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_, hγ⟩
    have hg : (g.1 : GL (Fin d.m) (AE F E)) ∈ HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (Jd d η) := (th_mem_iff d hη g.1).1 g.2
    rw [← hγ] at hg
    change HeckeCharacterZeroLocus.SiegelWeilU.cT (σ : E →+* E) (γ : Matrix (Fin d.m) (Fin d.m) E) * Jd d η * (γ : Matrix (Fin d.m) (Fin d.m) E) =
      Jd d η
    apply Matrix.map_injective (th_inclR_injective (F := F) (E := E))
    change HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) ((γ : Matrix (Fin d.m) (Fin d.m) E).map (inclR (F := F) (E := E) (AF F))) *
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (Jd d η) * (γ : Matrix (Fin d.m) (Fin d.m) E).map (inclR (F := F) (E := E) (AF F)) =
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (Jd d η) at hg
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, th_cT_map]
    exact hg
  · rintro ⟨γ, -, hγ⟩
    exact ⟨γ, hγ⟩

def thR (d : SD σ) {η : E} (hη : η ≠ 0) : HeckeCharacterZeroLocus.SiegelWeilU.HFinIn (AF F) σ (Jd d η) ≃ ratU σ d.A.J where
  toFun h := ⟨(thE d hη).symm h.1, (th_rat_iff d hη _).2
    (by have e1 : thE' d hη ((thE d hη).symm h.1) = h.1 := (thE d hη).apply_symm_apply h.1
        rw [e1]; exact h.2)⟩
  invFun g := ⟨thE' d hη g.1, (th_rat_iff d hη _).1 g.2⟩
  left_inv h := Subtype.ext ((thE d hη).apply_symm_apply h.1)
  right_inv g := Subtype.ext ((thE d hη).symm_apply_apply g.1)

theorem th_haar (d : SD σ) {η : E} (hη : η ≠ 0) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH F E σ d.m (Jd d η) (d.μ.map (thM d hη)) := by
  have := d.ok.haar
  exact th_haar_map d.μ (thE d hη) (thE_cont d hη) (thE_symm_cont d hη)

theorem th_fd (d : SD σ) {η : E} (hη : η ≠ 0) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsFDH F E σ d.m (Jd d η) (d.μ.map (thM d hη)) (thM d hη '' d.D) := by
  refine d.ok.dom.image_of_equiv (thM d hη).toEquiv ⟨(thM d hη).symm.measurable, ?_⟩ (thR d hη) ?_
  · change Measure.map (thM d hη).symm (Measure.map (thM d hη) d.μ) ≪ d.μ
    rw [MeasurableEquiv.map_symm_map]
  · intro h x
    rfl

end PositivityTheory.SiegelWeilFormula.KWhit

end
