import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import GroundTheory.AutomorphicForms.HermitianExistenceLocal
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements

namespace CompanionTheory.SWFin

open NumberField GroundTheory.Automorphic Module MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped TensorProduct NumberField.AdeleRing

theorem allSome_of {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ]
    (h : ∀ (μ : Measure G) [μ.IsHaarMeasure], ∃ D : Set G, IsFundamentalDomain Γ D μ ∧ μ D < ⊤) :
    AllSome (fun μ : Measure G => μ.IsHaarMeasure) fun μ =>
      AllSome (fun D : Set G => IsFundamentalDomain Γ D μ) fun D => μ D < ⊤ := by
  refine ⟨⟨Measure.haar, inferInstance⟩, fun μ hμ => ?_⟩
  obtain ⟨D, hD, hfin⟩ := h μ
  exact ⟨⟨D, hD⟩, fun D' hD' => (hD'.measure_eq hD).trans_lt hfin⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

theorem HR_eq {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (R : Type) [CommRing R] [Algebra F R] :
    HR R (conj F E).toAlgHom J = unitaryPoints F E J R := by
  have : sigR R (conj F E).toAlgHom = conjBase F E R := by
    refine RingHom.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  ext g
  show cT (sigR R (conj F E).toAlgHom) _ * _ * _ = _ ↔ _
  rw [this]
  rfl

theorem HFin_eq {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    (HFin 𝔸[F] (conj F E).toAlgHom J).subgroupOf (unitaryPoints F E J 𝔸[F]) = (unitaryDiagonal F J).range := by
  have key : ∀ x : unitaryPoints F E J F,
      ((unitaryDiagonal F J x : unitaryPoints F E J 𝔸[F]) : GL (Fin M) (𝔸[F] ⊗[F] E)) =
        bc (inclR 𝔸[F]) (unitaryPointsRationalEquiv F E J x : GL (Fin M) E) := by
    intro x
    refine Units.ext (Matrix.ext fun i j => ?_)
    show tensorMap E (Algebra.ofId F 𝔸[F]) ((x : GL (Fin M) (F ⊗[F] E)) i j) =
      inclR 𝔸[F] (Algebra.TensorProduct.lid F E ((x : GL (Fin M) (F ⊗[F] E)) i j))
    generalize (x : GL (Fin M) (F ⊗[F] E)) i j = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r e =>
      rw [tensorMap_tmul, Algebra.TensorProduct.lid_tmul]
      show algebraMap F 𝔸[F] r ⊗ₜ[F] e = (1 : 𝔸[F]) ⊗ₜ[F] (r • e)
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  ext g
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨γ, hγ, e⟩
    refine ⟨(unitaryPointsRationalEquiv F E J).symm ⟨γ, hγ⟩, Subtype.ext ?_⟩
    rw [key, MulEquiv.apply_symm_apply]
    exact e
  · rintro ⟨x, rfl⟩
    exact ⟨_, (unitaryPointsRationalEquiv F E J x).2, (key x).symm⟩

theorem finite_volume_unitary_adelic {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsUnit J.det)
    (h : ∀ (μ : Measure (unitaryPoints F E J 𝔸[F])) [μ.IsHaarMeasure],
      ∃ D : Set (unitaryPoints F E J 𝔸[F]), IsFundamentalDomain (unitaryDiagonal F J).range D μ ∧ μ D < ⊤)
    (S : Subgroup (GL (Fin M) (𝔸[F] ⊗[F] E))) (hS : S = unitaryPoints F E J 𝔸[F]) :
    letI : MeasurableSpace S := borel S
    AllSome (fun μ : Measure S => μ.IsHaarMeasure) fun μ =>
      AllSome (fun D : Set S => IsFundamentalDomain ((HFin 𝔸[F] (conj F E).toAlgHom J).subgroupOf S) D μ)
        fun D => μ D < ⊤ := by
  subst hS
  rw [HFin_eq]
  have := locallyCompactSpace_unitaryPoints_adele (K := F) J hJ
  have : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.countable_iff.2 inferInstance
  have : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  have : Countable (GL (Fin M) E) :=
    (Units.val_injective.countable : Countable (Matrix (Fin M) (Fin M) E)ˣ)
  have : Countable (unitaryPoints F E J F) := (unitaryPointsRationalEquiv F E J).toEquiv.countable_iff.2 inferInstance
  have : Countable (unitaryDiagonal F J).range := (MonoidHom.rangeRestrict_surjective _).countable
  exact allSome_of _ h

theorem finVol_of (hC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E] (M : ℕ)
      (h : HermitianForm F E (Fin M → E)), AdelicCovolumeFinite.Statement h (Pi.basisFun E (Fin M)))
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) : FinVol F E σ M J := by
  obtain ⟨hF, hE, h2, hc⟩ := hσ
  have : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (embedding_conj τ x).symm)
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  have hH : IsHermitianFor (conjHom F E) J := Matrix.ext fun i j => hJ.1 i j
  have h := hC F E M (HermitianForm.ofGram J hH hu)
  have hr : ∀ (h : HermitianForm F E (Fin M → E)) (v : Basis (Fin M) E (Fin M → E)),
      (hermitianDiagonal h v).range = (unitaryDiagonal F (gram h.toSesq v)).range := by
    intro h v
    rw [hermitianDiagonal, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (unitaryPointsRationalEquivHermitian F E h v).symm.surjective, ← MonoidHom.range_eq_map]
  unfold AdelicCovolumeFinite.Statement at h
  rw [hr] at h
  have hg := gram_ofGram J hH hu
  generalize gram (HermitianForm.ofGram J hH hu).toSesq (Pi.basisFun E (Fin M)) = J' at h hg
  subst hg
  exact finite_volume_unitary_adelic J' hu h _ (HR_eq J' _)

end CompanionTheory.SWFin
