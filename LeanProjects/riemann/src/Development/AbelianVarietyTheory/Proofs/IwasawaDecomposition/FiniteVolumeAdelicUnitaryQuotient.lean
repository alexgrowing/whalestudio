import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpenStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeLatticeStabiliserUnitaryRealPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct Pointwise

namespace GlobalTheory.Mem.VolFin

theorem measure_lt_top_of_cover {G A B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B] [SecondCountableTopology B]
    [MeasurableSpace B] [BorelSpace B]
    (e : G ≃ₜ* A × B) (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure]
    (S : Finset B) (K : Set B) (hK : IsCompact K) (Ω : B → Set A)
    (hΩ : ∀ s, (Measure.haar : Measure A) (Ω s) < ⊤)
    (hcov : ∀ g : G, ∃ γ : Γ, ∃ s ∈ S, (e (γ • g)).1 ∈ Ω s ∧ (e (γ • g)).2 ∈ s • K)
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) : μ 𝓕 < ⊤ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have h1 : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  have h2 := Measure.isMulLeftInvariant_eq_smul (μ.map e)
    ((Measure.haar : Measure A).prod (Measure.haar : Measure B))
  have hle : μ 𝓕 ≤ μ (⋃ s ∈ S, e ⁻¹' (Ω s ×ˢ (s • K))) := by
    refine GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers h𝓕 (.of_forall fun g => ?_)
    obtain ⟨γ, s, hs, h⟩ := hcov g
    exact ⟨γ, Set.mem_biUnion hs h⟩
  refine hle.trans_lt ((measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top.2 fun s _ => ?_))
  refine (Measure.le_map_apply (map_continuous e).measurable.aemeasurable _).trans_lt ?_
  rw [h2, Measure.smul_apply, Measure.prod_prod]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top (hΩ s) (hK.smul s).measure_lt_top)

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (x : E) :
    sigR R σ (inclR (F := F) R x) = inclR (F := F) R (σ x) := by
  simp [sigR, inclR]

noncomputable def ratPt (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Formalism.UG.UJ (σ : E →+* E) J →* HA R σ J where
  toFun γ := (⟨Formalism.UG.bc (inclR (F := F) R) γ.1, by
    have := congrArg (fun N => N.map (inclR (F := F) R)) (show Formalism.UG.cT _ _ * _ * _ = _ from γ.2)
    simp only [Matrix.map_mul] at this
    change Formalism.UG.cT _ _ * _ * _ = _
    refine Eq.trans ?_ this
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ rfl) rfl
    ext i j
    exact sigR_inclR R σ _⟩ : HR R σ J)
  map_one' := Subtype.ext (map_one (Formalism.UG.bc (inclR (F := F) R)))
  map_mul' a b := Subtype.ext (map_mul (Formalism.UG.bc (inclR (F := F) R)) _ _)

theorem topGroup_HA [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    IsTopologicalGroup (HA R σ J) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  exact inferInstanceAs (IsTopologicalGroup (HR R σ J))

theorem countable_HFinIn [Countable E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Countable (HFinIn R σ J) := by
  haveI : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  haveI : Countable (GL (Fin M) E) := Units.val_injective.countable
  refine Function.Surjective.countable
    (f := fun γ : Formalism.UG.UJ (σ : E →+* E) J => (⟨ratPt R σ J γ, γ.1, γ.2, rfl⟩ : HFinIn R σ J)) ?_
  rintro ⟨g, γ, hγ, h⟩
  exact ⟨⟨γ, hγ⟩, Subtype.ext (Subtype.ext h)⟩

variable [NumberField F]

theorem mulVec_fv {M : ℕ} (m : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    (m.map (inclR (F := F) (Af F))).mulVec (GlobalTheory.AdLat.fv F x) = GlobalTheory.AdLat.fv F (m.mulVec x) := by
  ext i
  exact (RingHom.map_mulVec (inclR (F := F) (Af F)) m x i).symm

theorem mulVec_mem_hat_of_rat {M : ℕ} (m : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E))
    (h : ∀ x ∈ Λ, m.mulVec x ∈ Λ) {z : Fin M → Af F ⊗[F] E} (hz : z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E))) :
    (m.map (inclR (F := F) (Af F))).mulVec z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E)) := by
  refine GlobalTheory.AdLat.Translate.mulVec_mem_hat (fun x hx => ?_) hz
  rw [SetLike.mem_coe, GlobalTheory.AdLat.Translate.mem_pre, mulVec_fv]
  exact GlobalTheory.AdLat.Translate.fv_mem_hat (h x hx)

theorem stabHat_conj {M : ℕ} (δ : GL (Fin M) E) (L Λ : Submodule (𝓞 E) (Fin M → E))
    (s : GL (Fin M) (Af F ⊗[F] E))
    (hΛ : (GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E)) : Set (Fin M → Af F ⊗[F] E)) =
      (s : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec '' (GlobalTheory.AdLat.hat F (L : Set (Fin M → E))))
    (h : ∀ x, x ∈ Λ ↔ (δ : Matrix (Fin M) (Fin M) E).mulVec x ∈ Λ) :
    StabHat F (L : Set (Fin M → E))
      ((s⁻¹ * Formalism.UG.bc (inclR (F := F) (Af F)) δ * s : GL (Fin M) (Af F ⊗[F] E)) :
        Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) := by
  have him : ∀ y, y ∈ latHat F E (L : Set (Fin M → E)) ↔
      (s : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E)) := by
    intro y
    rw [← SetLike.mem_coe (p := GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E))), hΛ]
    constructor
    · exact fun hy => ⟨y, hy, rfl⟩
    · rintro ⟨u, hu, huy⟩
      have := congrArg ((s⁻¹ : GL (Fin M) (Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec huy
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.one_mulVec] at this
      exact this ▸ hu
  intro y
  rw [him, him, Matrix.mulVec_mulVec y, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
    Units.val_mul, ← Matrix.mulVec_mulVec]
  refine ⟨mulVec_mem_hat_of_rat _ Λ fun x hx => (h x).1 hx, fun hz => ?_⟩
  have := mulVec_mem_hat_of_rat ((δ⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Λ (fun x hx => by
    rw [h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact hx) hz
  change ((Formalism.UG.bc (inclR (F := F) (Af F)) δ⁻¹ : GL (Fin M) (Af F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec _ ∈ _ at this
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
    Matrix.one_mulVec] at this

end Rat

theorem finVol : FiniteVolume₂ := by
  intro F E _ _ _ _ _ σ hCM M J hJ μ hμ 𝓕 h𝓕
  classical
  haveI := topGroup_HA (AF F) σ J
  haveI := topGroup_HA (Ainf F) σ J
  haveI := topGroup_HA (Af F) σ J
  haveI : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  haveI : BorelSpace (HA (Ainf F) σ J) := ⟨rfl⟩
  haveI : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field F
  obtain ⟨_, _, -⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Ainf F) σ M J
  obtain ⟨_, _, -⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Af F) σ M J
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  haveI : Countable Γ := countable_HFinIn (AF F) σ J
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split F E σ M J
  have herat : ∀ γ, e (ratPt (AF F) σ J γ) = (ratPt (Ainf F) σ J γ, ratPt (Af F) σ J γ) := by
    intro γ
    refine Prod.ext (Subtype.ext (Units.ext ((he _).2.trans ?_))) (Subtype.ext (Units.ext ((he _).1.trans ?_)))
    · ext i j
      change Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (inclR (F := F) (AF F) _) = inclR (F := F) (Ainf F) _
      simp [inclR]
    · ext i j
      change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (inclR (F := F) (AF F) _) = inclR (F := F) (Af F) _
      simp [inclR]
  let b := Pi.basisFun E (Fin M)
  let L : Submodule (𝓞 E) (Fin M → E) := Submodule.span (𝓞 E) (Set.range b)
  have hL : L.FG := Submodule.fg_span (Set.finite_range b)
  have hLs : Submodule.span E (L : Set (Fin M → E)) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_mono Submodule.subset_span
  obtain ⟨K, hK, hKo, hKc⟩ := GlobalTheory.T.completedLattice_stabilizer_compact_open F E σ M J L hL hLs
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_classSet_hermitianUnitary_openLevel F E σ hCM M J hJ K hKo
  choose Λ _ hΛ1 hΛ2 hΛ3 using fun s : HA (Af F) σ J =>
    GlobalTheory.AdLat.exists_lattice_latOf F E M L (HA.mat (Af F) σ J s) hL hLs
  choose Ω _ hΩ1 hΩ2 using fun s : HA (Af F) σ J =>
    GlobalTheory.T.finite_covolume_latticeStabiliser_unitaryRealPoints F E σ hCM M J hJ (Λ s) (hΛ1 s) (hΛ2 s) Measure.haar inferInstance
  refine measure_lt_top_of_cover e Γ μ S K hKc Ω hΩ1 (fun g => ?_) 𝓕 h𝓕
  obtain ⟨⟨γ', γ, hγ, hγγ⟩, s, hs, k, hk, hg⟩ := hS (e g).2
  have hg2 : (e g).2 = ratPt (Af F) σ J ⟨γ, hγ⟩ * (s * k) := by
    rw [hg]
    exact congrArg (· * (s * k)) (Subtype.ext hγγ.symm : (γ' : HA (Af F) σ J) = ratPt (Af F) σ J ⟨γ, hγ⟩)
  obtain ⟨δ, hδ, hδΛ, w, hw, hwe⟩ := hΩ2 s ((ratPt (Ainf F) σ J ⟨γ, hγ⟩)⁻¹ * (e g).1)
  have hw1 : (ratPt (Ainf F) σ J ⟨γ, hγ⟩)⁻¹ * (e g).1 = ratPt (Ainf F) σ J ⟨δ, hδ⟩ * w := Subtype.ext hwe
  have hkδ : s⁻¹ * ratPt (Af F) σ J ⟨δ, hδ⟩ * s ∈ K :=
    (hK _).2 (stabHat_conj δ L (Λ s) (HA.mat (Af F) σ J s) (hΛ3 s) hδΛ)
  let η : Formalism.UG.UJ (σ : E →+* E) J := (⟨δ, hδ⟩ : Formalism.UG.UJ (σ : E →+* E) J)⁻¹ * (⟨γ, hγ⟩ : Formalism.UG.UJ (σ : E →+* E) J)⁻¹
  refine ⟨⟨ratPt (AF F) σ J η, η.1, η.2, rfl⟩, s, hs, ?_, ?_⟩
  · change (e (ratPt (AF F) σ J η * g)).1 ∈ _
    rw [map_mul, herat, Prod.fst_mul, map_mul, map_inv, map_inv, mul_assoc, hw1, inv_mul_cancel_left]
    exact hw
  · change (e (ratPt (AF F) σ J η * g)).2 ∈ _
    rw [map_mul, herat, Prod.snd_mul]
    dsimp only
    rw [map_mul, map_inv, map_inv, mul_assoc, hg2, inv_mul_cancel_left]
    refine ⟨_, K.mul_mem (K.inv_mem hkδ) hk, ?_⟩
    simp only [smul_eq_mul]
    group

end GlobalTheory.Mem.VolFin
