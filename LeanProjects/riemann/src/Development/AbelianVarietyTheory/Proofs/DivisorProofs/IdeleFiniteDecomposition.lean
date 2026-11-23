import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousSymmFinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesInf
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

noncomputable section
namespace GlobalTheory.ThKCtFin

theorem finiteIdele_classes (E : Type) [Field E] [NumberField E] (U : Subgroup (FiniteAdeleRing (𝓞 E) E)ˣ)
    (hU : IsOpen (U : Set (FiniteAdeleRing (𝓞 E) E)ˣ)) :
    ∃ C : Finset (FiniteAdeleRing (𝓞 E) E)ˣ, ∀ a : (FiniteAdeleRing (𝓞 E) E)ˣ, ∃ f : Eˣ, ∃ c ∈ C, ∃ u ∈ U,
      a = Units.map (algebraMap E (FiniteAdeleRing (𝓞 E) E) : E →* FiniteAdeleRing (𝓞 E) E) f * c * u := by
  classical
  obtain ⟨C, hC⟩ := PIW.ClassFinD.idele_class_finite E
  have hO : IsCompact ((PIW.ClassFinD.Ohat E).toSubmonoid : Set (FiniteAdeleRing (𝓞 E) E)) :=
    (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties E).1
  haveI : T2Space (FiniteAdeleRing (𝓞 E) E) := inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  have hK := Submonoid.units_isCompact hO
  obtain ⟨D, -, hD⟩ := hK.elim_nhds_subcover (fun d => {y | d⁻¹ * y ∈ U})
    (fun d _ => (hU.preimage (continuous_const.mul continuous_id)).mem_nhds (by
      show d⁻¹ * d ∈ U
      rw [inv_mul_cancel]; exact U.one_mem))
  refine ⟨Finset.image₂ (· * ·) C D, fun a => ?_⟩
  obtain ⟨f, c, hc, e, he, he', rfl⟩ := hC a
  have heK : e ∈ ((PIW.ClassFinD.Ohat E).toSubmonoid.units : Set (FiniteAdeleRing (𝓞 E) E)ˣ) := ⟨he, he'⟩
  obtain ⟨d, hd, hde⟩ := Set.mem_iUnion₂.1 (hD heK)
  refine ⟨f, c * d, Finset.mem_image₂_of_mem hc hd, d⁻¹ * e, hde, ?_⟩
  group

theorem idele_classes_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (U : Subgroup (AE F E)ˣ), IsOpen (U : Set (AE F E)ˣ) → ∃ C : Finset (AE F E)ˣ, ∀ t : (AE F E)ˣ, ∃ γ : Eˣ, ∃ c ∈ C, ∃ a ∈ idelesInf F E, ∃ u ∈ U, u ∈ idelesFin F E ∧ t = Units.map (inclR (F := F) (AF F)).toMonoidHom γ * c * a * u := by
  intro F E _ _ _ _ _ U hU
  classical
  letI t2 : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  letI t3 : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  obtain ⟨e, he, -, hec⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  obtain ⟨ι, hι1, hι2, -⟩ := GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E
  have hιc := GlobalTheory.AdeleBaseChange.continuous_symm_finite F E ι hι2
  have he1 : ∀ (a : AdeleRing (𝓞 F) F) (x : E), (e (a ⊗ₜ[F] x)).1 = a.1 ⊗ₜ[F] x :=
    fun a x => (he _).1.trans (Algebra.TensorProduct.map_tmul _ _ _ _)
  have he2 : ∀ (a : AdeleRing (𝓞 F) F) (x : E), (e (a ⊗ₜ[F] x)).2 = a.2 ⊗ₜ[F] x :=
    fun a x => (he _).2.trans (Algebra.TensorProduct.map_tmul _ _ _ _)
  let Φ : AE F E ≃+* ((InfiniteAdeleRing F ⊗[F] E) × FiniteAdeleRing (𝓞 E) E) :=
    e.trans (RingEquiv.prodCongr (RingEquiv.refl _) ι)
  have hΦ : ∀ z, Φ z = ((e z).1, ι (e z).2) := fun z => rfl
  let mf : FiniteAdeleRing (𝓞 E) E →* AE F E := Φ.symm.toRingHom.toMonoidHom.comp (MonoidHom.inr _ _)
  let mi : (InfiniteAdeleRing F ⊗[F] E) →* AE F E := Φ.symm.toRingHom.toMonoidHom.comp (MonoidHom.inl _ _)
  have hmf : ∀ y, Φ (mf y) = (1, y) := fun y => Φ.apply_symm_apply _
  have hmi : ∀ y, Φ (mi y) = (y, 1) := fun y => Φ.apply_symm_apply _
  have hmfc : Continuous mf := by
    have : (mf : _ → _) = fun w => e.symm (1, ι.symm w) := rfl
    rw [this]
    exact hec.comp (continuous_const.prodMk hιc)
  have hsm : ∀ (a : AF F) (z : AE F E), Φ (a • z) = (a.1 ⊗ₜ[F] (1 : E), ι (a.2 ⊗ₜ[F] (1 : E))) * Φ z := by
    intro a z
    rw [Algebra.smul_def, map_mul]
    congr 1
    rw [hΦ, ← he1, ← he2]
    rfl
  obtain ⟨C, hC⟩ := finiteIdele_classes E (U.comap (Units.map mf)) (hU.preimage (Continuous.units_map _ hmfc))
  refine ⟨C.image (Units.map mf), fun t => ?_⟩
  let p1 : AE F E →* (InfiniteAdeleRing F ⊗[F] E) := (MonoidHom.fst _ _).comp Φ.toRingHom.toMonoidHom
  let p2 : AE F E →* FiniteAdeleRing (𝓞 E) E := (MonoidHom.snd _ _).comp Φ.toRingHom.toMonoidHom
  obtain ⟨f, c, hc, u, hu, ht⟩ := hC (Units.map p2 t)
  set g : (AE F E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom f with hg
  refine ⟨f, Units.map mf c, Finset.mem_image_of_mem _ hc, Units.map mi (Units.map p1 (g⁻¹ * t)), ?_,
    Units.map mf u, hu, ?_, ?_⟩
  · intro a ha
    have ha1 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (ha.trans (map_zero _).symm)
    apply Φ.injective
    rw [hsm, map_sub, map_one, map_zero, Units.coe_map, hmi, ha1]
    ext <;> simp
  · intro a ha
    have ha2 : a.2 = 0 := ha
    apply Φ.injective
    rw [hsm, map_sub, map_one, map_zero, Units.coe_map, hmf, ha2]
    ext <;> simp
  · rw [← hg, mul_assoc, mul_assoc, ← inv_mul_eq_iff_eq_mul]
    have hg2 : Units.map p2 g = Units.map (algebraMap E (FiniteAdeleRing (𝓞 E) E) : E →* FiniteAdeleRing (𝓞 E) E) f := by
      apply Units.ext
      change ι (e ((1 : AF F) ⊗ₜ[F] (f : E))).2 = _
      rw [he2]
      exact hι1 f
    have h2 : Units.map p2 (g⁻¹ * t) = c * u := by
      rw [map_mul, map_inv, hg2, ht]; group
    have h2' : (Φ ((g⁻¹ * t : (AE F E)ˣ) : AE F E)).2 = (c : FiniteAdeleRing (𝓞 E) E) * u := congrArg Units.val h2
    apply Units.ext
    apply Φ.injective
    rw [Units.val_mul (Units.map mf c), Units.val_mul (Units.map mi _), map_mul, map_mul, Units.coe_map, Units.coe_map,
      Units.coe_map (f := mf), hmf, hmf, hmi]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, one_mul, mul_one]
      rfl
    · simp only [Prod.snd_mul, one_mul]
      exact h2'

end GlobalTheory.ThKCtFin
