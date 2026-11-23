import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedAlgebraicOfLimitOfFixedElementsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseNumberFieldOfContinuousCompletionEquivStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsNormPlaceLeOfFrobeniusStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilTransport

theorem conj_nhds : ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] [Algebra.IsAlgebraic E Ω] (E' Ω' : Type)
    [Field E'] [Field Ω'] [Algebra E' Ω'] (φ : Ω ≃+* Ω') (U' : Set (G E' Ω')), U' ∈ nhds (1 : G E' Ω') →
    ∃ U : Set (G E Ω), IsOpen U ∧ (1 : G E Ω) ∈ U ∧
      ∀ σ ∈ U, ∀ σ' : G E' Ω', (∀ z, φ (σ z) = σ' (φ z)) → σ' ∈ U' := by
  intro E Ω _ _ _ _ E' Ω' _ _ _ φ U' hU'
  obtain ⟨L', hL'fin, hL'⟩ := (krullTopology_mem_nhds_one_iff E' Ω' U').mp hU'
  let b := Module.finBasis E' L'
  let S : Set Ω := Set.range fun i => φ.symm (b i : Ω')
  let L : IntermediateField E Ω := IntermediateField.adjoin E S
  haveI : Finite S := (Set.finite_range _).to_subtype
  haveI : FiniteDimensional E L := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  refine ⟨L.fixingSubgroup, L.fixingSubgroup_isOpen, L.fixingSubgroup.one_mem, ?_⟩
  intro σ hσ σ' hrel
  apply hL'
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  have hb : ∀ i, σ' (b i : Ω') = b i := by
    intro i
    have h1 : φ.symm (b i : Ω') ∈ L := IntermediateField.subset_adjoin E S ⟨i, rfl⟩
    have h2 := (IntermediateField.mem_fixingSubgroup_iff L σ).mp hσ _ h1
    have h3 := hrel (φ.symm (b i : Ω'))
    rw [h2, RingEquiv.apply_symm_apply] at h3
    exact h3.symm
  intro x hx
  have e := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
  simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at e
  rw [← e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hb]

section Transfer

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω']
  {A' : ValuationSubring Ω'} {φ : Ω ≃+* Ω'}

def conj (φ : Ω ≃+* Ω') (σ : Ω ≃+* Ω) : Ω' ≃+* Ω' := (φ.symm.trans σ).trans φ

@[simp] theorem conj_apply (φ : Ω ≃+* Ω') (σ : Ω ≃+* Ω) (y : Ω') : conj φ σ y = φ (σ (φ.symm y)) := rfl

def conjAlg (φ : Ω ≃+* Ω') (σ : G E Ω)
    (hσ : ∀ y : E', conj φ σ.toRingEquiv (algebraMap E' Ω' y) = algebraMap E' Ω' y) : G E' Ω' :=
  AlgEquiv.ofRingEquiv hσ

@[simp] theorem conjAlg_apply (φ : Ω ≃+* Ω') (σ : G E Ω)
    (hσ : ∀ y : E', conj φ σ.toRingEquiv (algebraMap E' Ω' y) = algebraMap E' Ω' y) (y : Ω') :
    conjAlg φ σ hσ y = φ (σ (φ.symm y)) := rfl

theorem val_le_one_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) (z : Ω) :
    A'.valuation (φ z) ≤ 1 ↔ A.valuation z ≤ 1 := by
  rw [A'.valuation_le_one_iff, A.valuation_le_one_iff, hm]

theorem val_lt_one_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) (z : Ω) :
    A'.valuation (φ z) < 1 ↔ A.valuation z < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ φ.injective]

omit [NumberField E'] in
theorem mem_Dec_iff' {K F : Type} [Field K] [Field F] [NumberField F] [Algebra F K] (B : ValuationSubring K)
    (τ : G F K) : τ ∈ Dec (F := F) B ↔ ∀ x, τ x ∈ B ↔ x ∈ B := by
  refine ⟨fun h x => apply_mem_iff_of_mem_Dec h x, fun h => mem_Dec.mpr ?_⟩
  ext x
  have := h ((τ⁻¹ : G F K) x)
  rw [mul_inv_apply] at this
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  exact this.symm

theorem mem_Dec_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) {σ : G E Ω} {σ' : G E' Ω'}
    (hrel : ∀ z, φ (σ z) = σ' (φ z)) : σ' ∈ Dec (F := E') A' ↔ σ ∈ Dec (F := E) A := by
  rw [mem_Dec_iff', mem_Dec_iff']
  constructor
  · intro h x; rw [← hm, hrel, h, hm]
  · intro h x; obtain ⟨z, rfl⟩ := φ.surjective x; rw [← hrel, hm, hm, h]

theorem actsAs_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) {σ : G E Ω} {σ' : G E' Ω'}
    (hrel : ∀ z, φ (σ z) = σ' (φ z)) (q a b : ℕ) : ActsAs A' q σ' a b ↔ ActsAs A q σ a b := by
  unfold ActsAs
  rw [mem_Dec_iff hm hrel]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h x hx
    have := h (φ x) ((val_le_one_iff hm x).mpr hx)
    rwa [← hrel, ← map_pow φ, ← map_pow φ, ← map_sub φ, val_lt_one_iff hm] at this
  · intro h x hx
    obtain ⟨z, rfl⟩ := φ.surjective x
    rw [val_le_one_iff hm] at hx
    rw [← hrel, ← map_pow φ, ← map_pow φ, ← map_sub φ, val_lt_one_iff hm]
    exact h z hx

end Transfer

section Smooth

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

theorem smooth_comp (φ : Ω ≃+* Ω') (e : Weil h →* Weil h')
    (he : ∀ (σ : Weil h) z, φ ((σ : G E Ω) z) = (e σ : G E' Ω') (φ z)) (hdeg : ∀ σ, deg (e σ) = deg σ)
    {M : Type} [Monoid M] (f : Weil h' →* M) (hf : IsSmooth f) : IsSmooth (f.comp e) := by
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  obtain ⟨O', hO', hpre⟩ := isOpen_induced_iff.mp hf
  have h1 : (1 : G E' Ω') ∈ O' := by
    have : (1 : Ine (F := E') A') ∈ Subtype.val ⁻¹' O' := by rw [hpre]; simp
    exact this
  obtain ⟨U, hU, hU1, hUO⟩ := conj_nhds E Ω E' Ω' φ O' (hO'.mem_nhds h1)
  refine IsSmooth.of_open (U := Subtype.val ⁻¹' U) (hU.preimage continuous_subtype_val) hU1 ?_
  intro τ hτ
  have hmem : ((e (ineIncl h τ) : Weil h') : G E' Ω') ∈ Ine (F := E') A' := by
    rw [← deg_eq_zero_iff, hdeg, deg_ineIncl]
  have hO : (⟨_, hmem⟩ : Ine (F := E') A') ∈ Subtype.val ⁻¹' O' := hUO τ hτ _ (he (ineIncl h τ))
  rw [hpre] at hO
  have e1 : ineIncl h' ⟨_, hmem⟩ = e (ineIncl h τ) := Subtype.ext rfl
  rw [Set.mem_setOf_eq, e1] at hO
  exact hO

end Smooth

open GlobalTheory.LocLanglands in
theorem weil_equiv : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∃ c : Weil h ≃* Weil h', (∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ') ∧ (∀ σ, deg (c σ) = deg σ) ∧ normV w' = normV w ∧ ∀ (M : Type) [Monoid M] (f : Weil h' →* M), GlobalTheory.WeilDeligne.IsSmooth f ↔ GlobalTheory.WeilDeligne.IsSmooth (f.comp c.toMonoidHom) := by
  intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j i hP
  haveI : CharZero Ω' := (RingHom.charZero_iff (algebraMap E' Ω').injective).mp inferInstance
  haveI : Algebra.IsAlgebraic E' Ω' := IsAlgClosure.isAlgebraic
  have fixE : ∀ σ : G E Ω, σ ∈ Dec (F := E) A →
      ∀ y : E', conj φ σ.toRingEquiv (algebraMap E' Ω' y) = algebraMap E' Ω' y := by
    intro σ hσ y
    refine GlobalTheory.T.fixed_algebraic_of_limit_of_fixed_elements Ω' A' (conj φ σ.toRingEquiv) ?_ _ ?_ ?_
    · intro z
      rw [conj_apply, hP.mem, AlgEquiv.coe_ringEquiv, apply_mem_iff_of_mem_Dec hσ]
      conv_rhs => rw [← φ.apply_symm_apply z]
      rw [hP.mem]
    · exact (IsIntegral.map (algebraMap E' Ω').toRatAlgHom
        (Algebra.IsIntegral.isIntegral (R := ℚ) y)).isAlgebraic
    · intro δ hδ
      obtain ⟨x, hx⟩ := GlobalTheory.T.dense_numberField_of_continuous_completion_equiv E w E' Ω' A' w' h' j i hP.cont hP.loc y δ hδ
      refine ⟨algebraMap E' Ω' (j x), ?_, hx⟩
      rw [conj_apply, ← hP.ext, RingEquiv.symm_apply_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  have fixE' : ∀ σ' : G E' Ω', ∀ x : E,
      conj φ.symm σ'.toRingEquiv (algebraMap E Ω x) = algebraMap E Ω x := by
    intro σ' x
    rw [conj_apply, RingEquiv.symm_symm, hP.ext, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, ← hP.ext,
      RingEquiv.symm_apply_apply]
  have hrelC : ∀ (σ : G E Ω) (hσ : ∀ y : E', conj φ σ.toRingEquiv (algebraMap E' Ω' y) = algebraMap E' Ω' y) z,
      φ (σ z) = conjAlg φ σ hσ (φ z) := by
    intro σ hσ z; rw [conjAlg_apply, RingEquiv.symm_apply_apply]
  have hrelC' : ∀ (σ' : G E' Ω') z, φ (conjAlg φ.symm σ' (fixE' σ') z) = σ' (φ z) := by
    intro σ' z; rw [conjAlg_apply, RingEquiv.symm_symm, RingEquiv.apply_symm_apply]
  have q_eq : normV w' = normV w := by
    apply le_antisymm
    · obtain ⟨σ, hσ⟩ := exists_isFrob h
      have hrel := hrelC σ (fixE σ hσ.1)
      refine GlobalTheory.T.absNorm_place_le_of_frobenius E' Ω' A' w' h' (normV w) (one_lt_normV w) (conjAlg φ σ (fixE σ hσ.1)) ?_
      rw [← actsAs_one_iff, actsAs_iff hP.mem hrel, actsAs_one_iff]; exact hσ
    · obtain ⟨τ', hτ'⟩ := exists_isFrob h'
      have hrel := hrelC' τ'
      refine GlobalTheory.T.absNorm_place_le_of_frobenius E Ω A w h (normV w') (one_lt_normV w') (conjAlg φ.symm τ' (fixE' τ')) ?_
      rw [← actsAs_one_iff, ← actsAs_iff hP.mem hrel, actsAs_one_iff]; exact hτ'
  have memW : ∀ σ : Weil h, conjAlg φ (σ : G E Ω) (fixE σ (Weil_le_Dec h σ.2)) ∈ Weil h' := by
    intro σ
    obtain ⟨a, b, hab⟩ := σ.2
    refine ⟨a, b, ?_⟩
    rw [q_eq, actsAs_iff hP.mem (hrelC _ _)]; exact hab
  have memW' : ∀ σ' : Weil h', conjAlg φ.symm (σ' : G E' Ω') (fixE' σ') ∈ Weil h := by
    intro σ'
    obtain ⟨a, b, hab⟩ := σ'.2
    refine ⟨a, b, ?_⟩
    rw [← q_eq, ← actsAs_iff hP.mem (hrelC' _)]; exact hab
  let c : Weil h ≃* Weil h' :=
    { toFun := fun σ => ⟨_, memW σ⟩
      invFun := fun σ' => ⟨_, memW' σ'⟩
      left_inv := fun σ => by ext z; simp
      right_inv := fun σ' => by ext z; simp
      map_mul' := fun σ τ => by ext z; simp }
  have hc : ∀ σ y, ((c σ : Weil h') : G E' Ω') y = φ ((σ : G E Ω) (φ.symm y)) := fun _ _ => rfl
  have hcs : ∀ σ' y, ((c.symm σ' : Weil h) : G E Ω) y = φ.symm ((σ' : G E' Ω') (φ y)) := fun _ _ => rfl
  have hrel : ∀ (σ : Weil h) z, φ ((σ : G E Ω) z) = ((c σ : Weil h') : G E' Ω') (φ z) := by
    intro σ z; rw [hc, RingEquiv.symm_apply_apply]
  have hdeg : ∀ σ, deg (c σ) = deg σ := by
    intro σ
    obtain ⟨a, b, hab⟩ := σ.2
    rw [deg_eq hab, deg_eq (σ := c σ) (a := a) (b := b) (by rw [q_eq, actsAs_iff hP.mem (hrel σ)]; exact hab)]
  refine ⟨c, ?_, hdeg, q_eq, ?_⟩
  · intro σ σ'
    constructor
    · intro hr
      ext y
      obtain ⟨z, rfl⟩ := φ.surjective y
      rw [← hrel]
      exact hr z
    · rintro rfl z
      exact hrel σ z
  · intro M _ f
    constructor
    · exact smooth_comp φ c.toMonoidHom hrel hdeg f
    · intro hf
      have hrel' : ∀ (σ' : Weil h') z, φ.symm ((σ' : G E' Ω') z) = ((c.symm σ' : Weil h) : G E Ω) (φ.symm z) := by
        intro σ' z; rw [hcs, RingEquiv.apply_symm_apply]
      have hdeg' : ∀ σ', deg (c.symm σ') = deg σ' := by
        intro σ'; rw [← hdeg, MulEquiv.apply_symm_apply]
      have := smooth_comp φ.symm c.symm.toMonoidHom hrel' hdeg' (f.comp c.toMonoidHom) hf
      convert this using 1
      ext σ'
      simp

end GlobalTheory.WeilTransport
