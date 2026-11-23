import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RealCoord

open InfinitePlace InfinitePlace.Completion

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def rho (w : InfinitePlace F) : F →+* ℝ := embedding_of_isReal (IsTotallyReal.isReal w)

def coord : Ainf F ≃+* (InfinitePlace F → ℝ) :=
  RingEquiv.piCongrRight (R := fun w : InfinitePlace F => w.Completion) (S := fun _ => ℝ)
    (fun w => ringEquivRealOfIsReal (IsTotallyReal.isReal w))

theorem coord_apply (y : Ainf F) (w : InfinitePlace F) :
    coord F y w = ringEquivRealOfIsReal (IsTotallyReal.isReal w) (y w) := rfl

def coordHomeo : Ainf F ≃ₜ (InfinitePlace F → ℝ) :=
  Homeomorph.piCongrRight (Y₁ := fun w : InfinitePlace F => w.Completion) (Y₂ := fun _ => ℝ)
    (fun w => (isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).toHomeomorph)

theorem coordHomeo_coe : ⇑(coordHomeo F) = ⇑(coord F) := rfl

theorem isHomeomorph_coord : IsHomeomorph (coord F) := (coordHomeo F).isHomeomorph

theorem abs_coord (y : Ainf F) (w : InfinitePlace F) : |coord F y w| = ‖y w‖ := by
  have h := (isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).isometry.norm_map_of_map_zero
    (map_zero (ringEquivRealOfIsReal (IsTotallyReal.isReal w))) (y w)
  exact h

theorem rho_coe (w : InfinitePlace F) (x : F) : ((rho F w x : ℝ) : ℂ) = w.embedding x :=
  embedding_of_isReal_apply _ _

theorem coord_algebraMap (x : F) (w : InfinitePlace F) :
    coord F (algebraMap F (Ainf F) x) w = rho F w x := by
  have h : ((coord F (algebraMap F (Ainf F) x) w : ℝ) : ℂ) = ((rho F w x : ℝ) : ℂ) := by
    rw [rho_coe, coord_apply, InfiniteAdeleRing.algebraMap_apply, ringEquivRealOfIsReal_apply,
      extensionEmbeddingOfIsReal_apply]
    exact extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)
  exact Complex.ofReal_injective h

instance : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
  ⟨fun w => not_isReal_iff_isComplex.mpr w.2 (IsTotallyReal.isReal w.1)⟩

def toMixed (y : InfinitePlace F → ℝ) : mixedEmbedding.mixedSpace F :=
  (fun w => y w.1, 0)

theorem toMixed_add (y z : InfinitePlace F → ℝ) : toMixed F (y + z) = toMixed F y + toMixed F z := by
  refine Prod.ext rfl ?_
  simp [toMixed]

theorem toMixed_injective : Function.Injective (toMixed F) := by
  intro y z h
  funext w
  exact congrFun (congrArg Prod.fst h) ⟨w, IsTotallyReal.isReal w⟩

theorem toMixed_coord_algebraMap (x : F) :
    toMixed F (coord F (algebraMap F (Ainf F) x)) = mixedEmbedding F x := by
  refine Prod.ext ?_ (Subsingleton.elim _ _)
  funext w
  rw [mixedEmbedding.mixedEmbedding_apply_isReal]
  exact coord_algebraMap F x w.1

open scoped Classical in
theorem measurePreserving_toMixed : MeasurePreserving (toMixed F) volume volume := by
  let f : {w : InfinitePlace F // w.IsReal} ≃ InfinitePlace F :=
    Equiv.subtypeUnivEquiv IsTotallyReal.isReal
  have h1 := (volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace F => ℝ) f).symm
  have h2 : MeasurePreserving (fun y : InfinitePlace F → ℝ => fun w : {w : InfinitePlace F // w.IsReal} => y w.1)
      volume volume := by
    convert h1 using 1
    funext y w
    rfl
  refine ⟨?_, ?_⟩
  · exact h2.measurable.prodMk measurable_const
  · have hm : Measurable (fun x : {w : InfinitePlace F // w.IsReal} → ℝ =>
        (x, (0 : {w : InfinitePlace F // w.IsComplex} → ℂ))) := by fun_prop
    rw [Measure.volume_eq_prod, volume_pi (α := fun _ : {w : InfinitePlace F // w.IsComplex} => ℂ),
      Measure.pi_of_empty _ (0 : {w : InfinitePlace F // w.IsComplex} → ℂ), Measure.prod_dirac, ← h2.map_eq,
      Measure.map_map hm h2.measurable]
    rfl

theorem coord_measurable : Measurable (coord F) := by
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  exact (isHomeomorph_coord F).continuous.measurable

open scoped Classical in
theorem map_coord_eq (lam : Measure (Ainf F)) (hl : IsStdInf lam) :
    lam.map (coord F) = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) := by
  obtain ⟨hH, D, hD, hD1⟩ := hl
  haveI := hH
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : (lam.map (coord F)).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map lam (coord F).toAddEquiv (isHomeomorph_coord F).continuous
      (coordHomeo F).symm.continuous
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, lam.map (coord F) = c • (volume : Measure (InfinitePlace F → ℝ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  set P := ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) with hP
  have hmp := measurePreserving_toMixed F
  have hPm : MeasurableSet P := ZSpan.fundamentalDomain_measurableSet _
  set Λ := mixedEmbedding.integerLattice F with hΛdef
  set Γ : AddSubgroup (Ainf F) :=
    ((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom.range with hΓ
  let Ψ : Ainf F → mixedEmbedding.mixedSpace F := fun y => toMixed F (coord F y)
  have hΨadd : ∀ x y, Ψ (x + y) = Ψ x + Ψ y := fun x y => by
    simp only [Ψ, map_add, toMixed_add]
  have hΨinj : Function.Injective Ψ := (toMixed_injective F).comp (coord F).injective
  have hΨalg : ∀ a : 𝓞 F, Ψ (algebraMap F (Ainf F) (algebraMap (𝓞 F) F a)) =
      mixedEmbedding F (algebraMap (𝓞 F) F a) := fun a => toMixed_coord_algebraMap F _
  have hΛmem : ∀ g : Λ, ∃ a : 𝓞 F, (g : mixedEmbedding.mixedSpace F) =
      mixedEmbedding F (algebraMap (𝓞 F) F a) := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  have hΛmem' : ∀ a : 𝓞 F, mixedEmbedding F (algebraMap (𝓞 F) F a) ∈ Λ :=
    fun a => ⟨a, rfl⟩
  choose a ha using hΛmem
  let m : Λ → Γ := fun g => ⟨algebraMap F (Ainf F) (algebraMap (𝓞 F) F (a g)), ⟨a g, rfl⟩⟩
  have hmΨ : ∀ g : Λ, Ψ (m g : Ainf F) = g := fun g => by
    rw [ha g]; exact hΨalg _
  have hmbij : Function.Bijective m := by
    refine ⟨fun g g' h => ?_, ?_⟩
    · apply Subtype.ext
      rw [← hmΨ g, ← hmΨ g', h]
    · rintro ⟨_, b, rfl⟩
      refine ⟨⟨_, hΛmem' b⟩, Subtype.ext (hΨinj ?_)⟩
      rw [hmΨ]
      exact (hΨalg b).symm
  have hq : Measure.QuasiMeasurePreserving Ψ lam volume := by
    refine hmp.quasiMeasurePreserving.comp ⟨coord_measurable F, ?_⟩
    rw [hc]
    intro s hs
    simp [hs]
  have hFD : IsAddFundamentalDomain Γ (Ψ ⁻¹' P) lam :=
    (mixedEmbedding.fundamentalDomain_integerLattice F).preimage_of_equiv hq hmbij (fun g x => by
      change Ψ ((m g : Ainf F) + x) = (g : mixedEmbedding.mixedSpace F) + Ψ x
      rw [hΨadd, hmΨ])
  haveI : Countable Γ := hmbij.surjective.countable
  have h1 : lam (Ψ ⁻¹' P) = 1 := by
    rw [← hD1]
    exact hFD.measure_eq hD
  have hQm : MeasurableSet (toMixed F ⁻¹' P) := hmp.measurable hPm
  have h2 : (c : ℝ≥0∞) * volume (toMixed F ⁻¹' P) = 1 := by
    have := Measure.map_apply (μ := lam) (coord_measurable F) hQm
    rw [hc] at this
    have e : Ψ ⁻¹' P = coord F ⁻¹' (toMixed F ⁻¹' P) := rfl
    rw [← h1, e]
    simpa using this
  have h3 : volume (toMixed F ⁻¹' P) = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
    rw [hmp.measure_preimage hPm.nullMeasurableSet, hP, mixedEmbedding.volume_fundamentalDomain_latticeBasis,
      IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, one_mul,
      ← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  have hd : 0 < Real.sqrt |(discr F : ℝ)| := by
    have : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
    positivity
  rw [h3] at h2
  have h4 : (c : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hd]
    exact ENNReal.eq_inv_of_mul_eq_one_left h2
  rw [hc, ← h4]
  rfl

end GlobalTheory.CompanionTheory.SW.RealCoord

open GlobalTheory.CompanionTheory.SW.RealCoord in
theorem GlobalTheory.CompanionTheory.SW.real_iso : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∃ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) ∧ IsHomeomorph e ∧ (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) ∧ (∀ y w, |e y w| = ‖y w‖) ∧ ∀ lam : Measure (Ainf F), IsStdInf lam → lam.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) := by
  intro F _ _ hF
  haveI := hF
  exact ⟨rho F, coord F, rho_coe F, isHomeomorph_coord F, coord_algebraMap F, abs_coord F, map_coord_eq F⟩
