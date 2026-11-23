import Mathlib
import GroundTheory.GlobalFields.CompletionAtPlace.Galois
import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
import GroundTheory.GlobalFields.IdeleGroups.LocalNormGroups
import GroundTheory.GlobalFields.IdeleGroups.LocalNormsEverywhere
import GroundTheory.LocalFields.LocalReciprocityUniversal

namespace GroundTheory.Global

open IsDedekindDomain NumberField SemiLocal
open scoped Pointwise

noncomputable section

section Range

variable {F E Ω : Type*} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra F Ω]

def equivFieldRange (i : E →ₐ[F] Ω) : E ≃ₐ[F] i.fieldRange :=
  AlgEquiv.ofInjectiveField i

@[simp]
theorem coe_equivFieldRange (i : E →ₐ[F] Ω) (y : E) :
    ((equivFieldRange i y : i.fieldRange) : Ω) = i y :=
  rfl

end Range

section NormResidue

variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [CharZero k] (M : Type*) [Field M] [Algebra k M] [FiniteDimensional k M]

def residueEmbedding : M →ₐ[k] AlgebraicClosure k :=
  IsAlgClosed.lift

def residueImage : IntermediateField k (AlgebraicClosure k) :=
  (residueEmbedding k M).fieldRange

def residueImageEquiv : M ≃ₐ[k] residueImage k M :=
  AlgEquiv.ofInjectiveField (residueEmbedding k M)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
@[simp]
theorem coe_residueImageEquiv (y : M) :
    ((residueImageEquiv k M y : residueImage k M) : AlgebraicClosure k) = residueEmbedding k M y :=
  rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem residueEmbedding_residueImageEquiv_symm (z : residueImage k M) :
    residueEmbedding k M ((residueImageEquiv k M).symm z) = z := by
  rw [← coe_residueImageEquiv, AlgEquiv.apply_symm_apply]

instance : FiniteDimensional k (residueImage k M) :=
  LinearEquiv.finiteDimensional (residueImageEquiv k M).toLinearEquiv

instance [IsGalois k M] : IsGalois k (residueImage k M) :=
  IsGalois.of_algEquiv (residueImageEquiv k M)

instance [IsMulCommutative (M ≃ₐ[k] M)] :
    IsMulCommutative (residueImage k M ≃ₐ[k] residueImage k M) :=
  ⟨⟨fun a b ↦ (AlgEquiv.autCongr (residueImageEquiv k M)).symm.injective (by
    rw [map_mul, map_mul]
    exact mul_comm' _ _)⟩⟩

variable [IsGalois k M] [IsMulCommutative (M ≃ₐ[k] M)]

def normResidueSymbol : kˣ →* (M ≃ₐ[k] M) :=
  (AlgEquiv.autCongr (residueImageEquiv k M).symm).toMonoidHom.comp
    ((LocalField.abelianRestrict (residueImage k M)).comp
      (LocalField.localReciprocityLimit k (AlgebraicClosure k)))

variable {k M}

theorem normResidueSymbol_apply (x : kˣ) (y : M) :
    normResidueSymbol k M x y = (residueImageEquiv k M).symm
      (LocalField.abelianRestrict (residueImage k M)
        (LocalField.localReciprocityLimit k (AlgebraicClosure k) x) (residueImageEquiv k M y)) :=
  rfl

theorem exists_mk_eq_localReciprocityLimit (x : kˣ) :
    ∃ τ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      (τ : TopologicalAbelianization (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) =
        LocalField.localReciprocityLimit k (AlgebraicClosure k) x :=
  QuotientGroup.mk_surjective _

theorem residueEmbedding_normResidueSymbol {x : kˣ}
    {τ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k}
    (hτ : (τ : TopologicalAbelianization (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) =
      LocalField.localReciprocityLimit k (AlgebraicClosure k) x) (y : M) :
    residueEmbedding k M (normResidueSymbol k M x y) = τ (residueEmbedding k M y) := by
  rw [normResidueSymbol_apply, ← hτ, LocalField.abelianRestrict_mk,
    residueEmbedding_residueImageEquiv_symm]
  exact AlgEquiv.restrictNormal_commutes τ (residueImage k M) (residueImageEquiv k M y)

theorem normResidueSymbol_spec (i : M →ₐ[k] AlgebraicClosure k) {x : kˣ}
    {τ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k}
    (hτ : (τ : TopologicalAbelianization (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) =
      LocalField.localReciprocityLimit k (AlgebraicClosure k) x) (y : M) :
    i (normResidueSymbol k M x y) = τ (i y) := by
  set χ : residueImage k M ≃ₐ[k] i.fieldRange :=
    (residueImageEquiv k M).symm.trans
      (equivFieldRange i) with hχ
  set ρ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k := χ.liftNormal (AlgebraicClosure k) with hρ
  have hρi : ∀ z : M, ρ (residueEmbedding k M z) = i z := fun z ↦
    (χ.liftNormal_commutes (AlgebraicClosure k) (residueImageEquiv k M z)).trans (by
      rw [hχ, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
      rfl)
  have hτ' : ((ρ⁻¹ * τ * ρ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
      TopologicalAbelianization (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) =
        LocalField.localReciprocityLimit k (AlgebraicClosure k) x := by
    rw [← hτ, QuotientGroup.mk_mul, QuotientGroup.mk_mul, mul_comm, ← mul_assoc,
      QuotientGroup.mk_inv, mul_inv_cancel, one_mul]
  have h := residueEmbedding_normResidueSymbol hτ' y
  rw [← hρi, ← hρi, h]
  simp [AlgEquiv.mul_apply]

theorem ker_normResidueSymbol :
    (normResidueSymbol k M).ker = (LocalField.normUnits k M).range := by
  have hN : (LocalField.normUnits k (residueImage k M)).range =
      (LocalField.normUnits k M).range := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨Units.map (residueImageEquiv k M).symm.toRingEquiv.toMonoidHom z, Units.ext ?_⟩
      simp only [LocalField.coe_normUnits, Units.coe_map]
      exact Algebra.norm_eq_of_algEquiv (residueImageEquiv k M).symm (z : residueImage k M)
    · rintro ⟨z, rfl⟩
      refine ⟨Units.map (residueImageEquiv k M).toRingEquiv.toMonoidHom z, Units.ext ?_⟩
      simp only [LocalField.coe_normUnits, Units.coe_map]
      exact Algebra.norm_eq_of_algEquiv (residueImageEquiv k M) (z : M)
  ext x
  rw [MonoidHom.mem_ker, ← hN]
  change (AlgEquiv.autCongr (residueImageEquiv k M).symm)
    (LocalField.abelianRestrict (residueImage k M)
      (LocalField.localReciprocityLimit k (AlgebraicClosure k) x)) = 1 ↔ _
  rw [LocalField.abelianRestrict_localReciprocityLimit, map_eq_one_iff _ (MulEquiv.injective _),
    map_eq_one_iff _ (MulEquiv.injective _), QuotientGroup.eq_one_iff]

end NormResidue

theorem continuous_monoidHom_of_isOpen_ker {G D : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group D] [TopologicalSpace D] [DiscreteTopology D] (f : G →* D)
    (hf : IsOpen (f.ker : Set G)) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, map_one, nhds_discrete D, Filter.tendsto_pure]
  exact Filter.mem_of_superset (hf.mem_nhds f.ker.one_mem) fun x hx ↦ hx

section Finite

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))

instance isMulCommutative_gal_adicCompletion [IsMulCommutative (L ≃ₐ[K] L)] (w : PlacesOver L v) :
    IsMulCommutative (w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :=
  ⟨⟨fun a b ↦ (decompositionMulEquiv v w.1).symm.injective (by
    rw [map_mul, map_mul]
    exact Subtype.ext (by simp only [Subgroup.coe_mul]; exact mul_comm' _ _))⟩⟩

variable [IsMulCommutative (L ≃ₐ[K] L)]

def symbolAt (w : PlacesOver L v) : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
  (MulAction.stabilizer (L ≃ₐ[K] L) w.1.asIdeal).subtype.comp
    ((decompositionMulEquiv v w.1).symm.toMonoidHom.comp
      (normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L)))

theorem symbolAt_mem_stabilizer (w : PlacesOver L v) (x : (v.adicCompletion K)ˣ) :
    symbolAt L v w x ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.1.asIdeal :=
  ((decompositionMulEquiv v w.1).symm _).2

theorem algebraMap_symbolAt_apply (w : PlacesOver L v) (x : (v.adicCompletion K)ˣ) (l : L) :
    algebraMap L (w.1.adicCompletion L) (symbolAt L v w x l) =
      normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x
        (algebraMap L (w.1.adicCompletion L) l) := by
  have h : decompositionToLocal v w.1 ((decompositionMulEquiv v w.1).symm
      (normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x)) =
        normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x :=
    (decompositionMulEquiv v w.1).apply_symm_apply _
  conv_rhs => rw [← h]
  rw [decompositionToLocal_algebraMap]
  rfl

theorem symbolAt_eq (w w' : PlacesOver L v) : symbolAt L v w = symbolAt L v w' := by
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (L ≃ₐ[K] L) w w'
  have h' : w'.1 = σ • w.1 := by rw [← hσ]; rfl
  set s := galEquiv v σ w.1 w'.1 h' with hs_def
  ext x l
  obtain ⟨τ, hτ⟩ := exists_mk_eq_localReciprocityLimit (k := v.adicCompletion K) x
  set a := normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x with ha
  set a' := normResidueSymbol (v.adicCompletion K) (w'.1.adicCompletion L) x with ha'
  have hs : ∀ y, a' (s y) = s (a y) := fun y ↦ by
    apply (residueEmbedding (v.adicCompletion K) (w'.1.adicCompletion L)).toRingHom.injective
    have h2 : residueEmbedding _ _ (s (a y)) = τ (residueEmbedding _ _ (s y)) :=
      normResidueSymbol_spec
        ((residueEmbedding (v.adicCompletion K) (w'.1.adicCompletion L)).comp s.toAlgHom) hτ y
    change residueEmbedding _ _ (a' (s y)) = residueEmbedding _ _ (s (a y))
    rw [ha', residueEmbedding_normResidueSymbol hτ, h2]
  set d := symbolAt L v w x with hd_def
  have hd : σ (d (σ⁻¹ l)) = d l := by
    have := congrArg (fun g : L ≃ₐ[K] L ↦ g l)
      (show σ * d * σ⁻¹ = d by rw [mul_comm' σ d, mul_inv_cancel_right])
    simpa only [AlgEquiv.mul_apply] using this
  apply (algebraMap L (w'.1.adicCompletion L)).injective
  calc algebraMap L (w'.1.adicCompletion L) (d l)
      = algebraMap L (w'.1.adicCompletion L) (σ (d (σ⁻¹ l))) := by rw [hd]
    _ = s (algebraMap L (w.1.adicCompletion L) (d (σ⁻¹ l))) :=
        (galEquiv_algebraMap v σ w.1 w'.1 h' _).symm
    _ = s (a (algebraMap L (w.1.adicCompletion L) (σ⁻¹ l))) := by
        rw [hd_def, algebraMap_symbolAt_apply]
    _ = a' (s (algebraMap L (w.1.adicCompletion L) (σ⁻¹ l))) := (hs _).symm
    _ = a' (algebraMap L (w'.1.adicCompletion L) (σ (σ⁻¹ l))) := by
        rw [hs_def, galEquiv_algebraMap]
    _ = a' (algebraMap L (w'.1.adicCompletion L) l) := by
        rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    _ = algebraMap L (w'.1.adicCompletion L) (symbolAt L v w' x l) :=
        (algebraMap_symbolAt_apply L v w' x l).symm

def localSymbol : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
  symbolAt L v (nonempty_placesOver L v).some

theorem localSymbol_eq_symbolAt (w : PlacesOver L v) : localSymbol L v = symbolAt L v w :=
  symbolAt_eq L v _ w

theorem localSymbol_mem_stabilizer (w : PlacesOver L v) (x : (v.adicCompletion K)ˣ) :
    localSymbol L v x ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.1.asIdeal := by
  rw [localSymbol_eq_symbolAt L v w]
  exact symbolAt_mem_stabilizer L v w x

theorem algebraMap_localSymbol_apply (w : PlacesOver L v) (x : (v.adicCompletion K)ˣ) (l : L) :
    algebraMap L (w.1.adicCompletion L) (localSymbol L v x l) =
      normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x
        (algebraMap L (w.1.adicCompletion L) l) := by
  rw [localSymbol_eq_symbolAt L v w]
  exact algebraMap_symbolAt_apply L v w x l

theorem ker_localSymbol (w : PlacesOver L v) :
    (localSymbol L v).ker =
      (LocalField.normUnits (v.adicCompletion K) (w.1.adicCompletion L)).range := by
  rw [localSymbol_eq_symbolAt L v w, ← ker_normResidueSymbol]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  change (((decompositionMulEquiv v w.1).symm
    (normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x)) : L ≃ₐ[K] L) = 1 ↔ _
  rw [OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff]

theorem units_le_ker_localSymbol (w : PlacesOver L v)
    (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (localSymbol L v).ker := by
  intro u hu
  rw [ker_localSymbol L v w]
  obtain ⟨y, -, hyu⟩ := IdeleNorm.exists_norm_eq_of_ramificationIdx_eq_one v w.1 he hu
  exact ⟨y, Units.ext hyu⟩

theorem eventually_units_le_ker_localSymbol :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (localSymbol L v).ker := by
  filter_upwards [IdeleNorm.eventually_forall_placesOver K
    (IdeleNorm.eventually_ramificationIdx_eq_one K L)] with v hv
  obtain ⟨w⟩ := nonempty_placesOver L v
  exact units_le_ker_localSymbol L v w (hv w)

theorem continuous_localSymbol : Continuous (localSymbol L v) := by
  obtain ⟨w⟩ := nonempty_placesOver L v
  refine continuous_monoidHom_of_isOpen_ker _ ?_
  rw [ker_localSymbol L v w]
  exact LocalField.isOpen_range_normUnits _ _

theorem range_finiteLocalNorm_le_ker_localSymbol :
    (IdeleNorm.finiteLocalNorm L v).range ≤ (localSymbol L v).ker := by
  rintro _ ⟨y, rfl⟩
  change ∏ w, Units.map (Algebra.norm (v.adicCompletion K) :
    w.1.adicCompletion L →* v.adicCompletion K) (y w) ∈ _
  exact Subgroup.prod_mem _ fun w _ ↦ by
    rw [ker_localSymbol L v w]
    exact ⟨y w, rfl⟩

end Finite

end

end GroundTheory.Global
