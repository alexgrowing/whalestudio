import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitting
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.EtQuot
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

section star
variable {L : Type} [CommRing L] [StarRing L]

def quotStarRing (J : Ideal L) (hJ : ∀ a ∈ J, star a ∈ J) : StarRing (L ⧸ J) where
  star := Ideal.Quotient.lift J ((Ideal.Quotient.mk J).comp (starRingEnd L))
    (fun a ha => by
      simp only [RingHom.comp_apply, starRingEnd_apply]; exact Ideal.Quotient.eq_zero_iff_mem.2 (hJ a ha))
  star_involutive x := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp
  star_mul x y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp [← map_mul, mul_comm]
  star_add x y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp [← map_add]

end star

variable (A : Et F E) (e : A.K)

abbrev QK := A.K ⧸ Ideal.span {e}

abbrev QL := A.L ⧸ (Ideal.span {e}).map (algebraMap A.K A.L)

instance twQ : IsScalarTower F (QK A e) (QL A e) := IsScalarTower.of_algebraMap_eq fun x => by
  rw [IsScalarTower.algebraMap_apply F A.K (QK A e)]
  simp only [Ideal.Quotient.algebraMap_eq, RingHom.comp_apply, Ideal.Quotient.algebraMap_quotient_map_quotient]
  show Ideal.Quotient.mk _ (algebraMap F A.L x) = _
  rw [IsScalarTower.algebraMap_apply F A.K A.L]

theorem star_mem (a : A.L) (ha : a ∈ (Ideal.span {e}).map (algebraMap A.K A.L)) :
    star a ∈ (Ideal.span {e}).map (algebraMap A.K A.L) := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at ha ⊢
  obtain ⟨c, rfl⟩ := ha
  exact ⟨star c, by rw [star_mul, A.star_K, mul_comm]⟩

def eq0 : TensorProduct A.K (QK A e) A.L ≃ₗ[A.K] QL A e :=
  (TensorProduct.comm A.K (QK A e) A.L).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A.L (Ideal.span {e})).symm.toLinearEquiv.restrictScalars A.K)

theorem etaleQuotientTensorLinearEquiv_one_tmul (x : A.L) : eq0 A e (1 ⊗ₜ x) = Ideal.Quotient.mk _ x := by
  simp only [eq0, LinearEquiv.trans_apply, TensorProduct.comm_tmul, LinearEquiv.restrictScalars_apply,
    AlgEquiv.toLinearEquiv_apply]
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {e})), Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul,
    one_smul]
  rfl

theorem isBaseChange_quot : IsBaseChange (QK A e) (IsScalarTower.toAlgHom A.K A.L (QL A e)).toLinearMap :=
  IsBaseChange.of_equiv ((eq0 A e).extendScalarsOfSurjective Ideal.Quotient.mk_surjective) fun x => by
    simpa using etaleQuotientTensorLinearEquiv_one_tmul A e x

theorem push_quot : Algebra.IsPushout F E (QK A e) (QL A e) := by
  have h2 : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap :=
    (Algebra.isPushout_iff F A.K E A.L).1 A.push.symm
  have h5 := h2.comp (isBaseChange_quot A e)
  refine Algebra.IsPushout.symm ((Algebra.isPushout_iff F (QK A e) E (QL A e)).2 ?_)
  have hm : (IsScalarTower.toAlgHom F E (QL A e)).toLinearMap =
      (IsScalarTower.toAlgHom A.K A.L (QL A e)).toLinearMap.restrictScalars F ∘ₗ
        (IsScalarTower.toAlgHom F E A.L).toLinearMap := by
    ext y; rfl
  rw [hm]; exact h5

end GlobalTheory.JR.EtQuot

namespace GlobalTheory.JR.EtQuot
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable (A : Et F E) (e : A.K)

theorem isReduced_quot (he : IsIdempotentElem e) : IsReduced (QK A e) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, hn⟩ := hx
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hn
  obtain ⟨c, hc⟩ := hn
  have h1 : IsNilpotent (y * (1 - e)) := ⟨n + 1, by
    rw [mul_pow, he.one_sub.pow_succ_eq, pow_succ, ← hc]
    linear_combination (-(c * y)) * he.eq⟩
  have h2 := IsReduced.eq_zero _ h1
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨y, by linear_combination -h2⟩

def quotEt (he : IsIdempotentElem e) : Et F E :=
  letI tK : TopologicalSpace (QK A e) := moduleTopology F _
  haveI mtK : IsModuleTopology F (QK A e) := ⟨rfl⟩
  letI tL : TopologicalSpace (QL A e) := moduleTopology F _
  haveI mtL : IsModuleTopology F (QL A e) := ⟨rfl⟩
  letI mK : MeasurableSpace (QK A e) := borel _
  letI mL : MeasurableSpace (QL A e) := borel _
  letI sL : StarRing (QL A e) := quotStarRing _ (star_mem A e)
  { K := QK A e
    L := QL A e
    redK := isReduced_quot A e he
    trK := IsModuleTopology.isTopologicalRing F _
    lcK := (IsModuleTopology.isOpenQuotientMap_of_surjective (R := F) (A := A.K)
      (φ := (Ideal.Quotient.mkₐ F (Ideal.span {e})).toLinearMap) (Ideal.Quotient.mkₐ_surjective F _)).locallyCompactSpace
    bK := ⟨rfl⟩
    bL := ⟨rfl⟩
    push := push_quot A e
    star_K := fun x => by
      obtain ⟨k, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
      show Ideal.Quotient.mk _ (star _) = _
      rw [A.star_K]
    star_E := fun y => by
      show Ideal.Quotient.mk _ (star (algebraMap E A.L y)) = Ideal.Quotient.mk _ (algebraMap E A.L (star y))
      rw [A.star_E] }

theorem exists_idem (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] [Nontrivial K] (hf : ¬ IsField K) :
    ∃ e : K, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  classical
  obtain ⟨m₁, hm₁⟩ := Ideal.exists_maximal K
  have hex : ∃ m₂ : Ideal K, m₂.IsMaximal ∧ m₂ ≠ m₁ := by
    by_contra h
    push_neg at h
    haveI : IsLocalRing K := IsLocalRing.of_unique_max_ideal ⟨m₁, hm₁, fun y hy => h y hy⟩
    exact hf (IsArtinianRing.isField_of_isReduced_of_isLocalRing K)
  obtain ⟨m₂, hm₂, hne⟩ := hex
  let i : MaximalSpectrum K := ⟨m₁, hm₁⟩
  let j : MaximalSpectrum K := ⟨m₂, hm₂⟩
  have hij : j ≠ i := fun h => hne (congrArg MaximalSpectrum.asIdeal h)
  haveI : i.asIdeal.IsMaximal := hm₁
  haveI : j.asIdeal.IsMaximal := hm₂
  let φ := IsArtinianRing.equivPi K
  refine ⟨φ.symm (Pi.single i 1), ?_, ?_, ?_⟩
  · unfold IsIdempotentElem
    rw [← map_mul, ← Pi.single_mul, mul_one]
  · intro h
    have := congrArg φ h
    simp at this
  · intro h
    have := congrFun (congrArg φ h) j
    simp [Pi.single_apply, hij] at this

end GlobalTheory.JR.EtQuot

namespace GlobalTheory.JR.EtQuot

theorem idem_eq_one_of_isUnit {K : Type} [CommRing K] {e : K} (he : IsIdempotentElem e) (hu : IsUnit e) : e = 1 := by
  obtain ⟨u, rfl⟩ := hu
  calc (u : K) = u * u * ↑u⁻¹ := by simp
    _ = u * ↑u⁻¹ := by rw [he.eq]
    _ = 1 := by simp

theorem nontrivial_quot {K : Type} [CommRing K] {e : K} (he : IsIdempotentElem e) (h1 : e ≠ 1) :
    Nontrivial (K ⧸ Ideal.span {e}) :=
  Ideal.Quotient.nontrivial_iff.2 (fun h => h1 (idem_eq_one_of_isUnit he (Ideal.span_singleton_eq_top.1 h)))

theorem exists_splitting : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), Nontrivial A.K → ¬ IsField A.K →
    ∃ (A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L),
      IsSplitting A A₁ A₂ eK eL ∧ Module.finrank F A₁.K < Module.finrank F A.K ∧
        Module.finrank F A₂.K < Module.finrank F A.K := by
  intro F E _ _ _ _ _ A hnt hf
  haveI : IsArtinianRing A.K := IsArtinianRing.of_finite F A.K
  obtain ⟨e, he, h0, h1⟩ := exists_idem A.K hf
  let A₁ := quotEt A e he
  let A₂ := quotEt A (1 - e) he.one_sub
  let eK : A.K ≃ₐ[F] A₁.K × A₂.K :=
    AlgEquiv.prodQuotientOfIsIdempotentElem F he he.one_sub (by ring) he.mul_one_sub_self
  let e' := algebraMap A.K A.L e
  have he' : IsIdempotentElem e' := he.map _
  have hJ1 : (Ideal.span {e}).map (algebraMap A.K A.L) = Ideal.span {e'} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hJ2 : (Ideal.span {1 - e}).map (algebraMap A.K A.L) = Ideal.span {1 - e'} := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]
  let eL : A.L ≃ₐ[F] A₁.L × A₂.L :=
    (AlgEquiv.prodQuotientOfIsIdempotentElem F he' he'.one_sub (by ring) he'.mul_one_sub_self).trans
      (AlgEquiv.prodCongr (Ideal.quotientEquivAlgOfEq F hJ1.symm) (Ideal.quotientEquivAlgOfEq F hJ2.symm))
  have hsum : Module.finrank F A.K = Module.finrank F A₁.K + Module.finrank F A₂.K := by
    rw [eK.toLinearEquiv.finrank_eq, Module.finrank_prod]
  haveI : Nontrivial A₁.K := nontrivial_quot he h1
  haveI : Nontrivial A₂.K := nontrivial_quot he.one_sub (fun h => h0 (by linear_combination -h))
  have p1 : 0 < Module.finrank F A₁.K := Module.finrank_pos
  have p2 : 0 < Module.finrank F A₂.K := Module.finrank_pos
  refine ⟨A₁, A₂, eK, eL, ⟨fun k => ?_, fun y => ?_, fun y => ?_⟩, by omega, by omega⟩
  · refine Prod.ext ?_ ?_
    · show Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ (algebraMap A.K A.L k)) =
        algebraMap (QK A e) (QL A e) (Ideal.Quotient.mk _ k)
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.Quotient.algebraMap_quotient_map_quotient]
    · show Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ (algebraMap A.K A.L k)) =
        algebraMap (QK A (1 - e)) (QL A (1 - e)) (Ideal.Quotient.mk _ k)
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.Quotient.algebraMap_quotient_map_quotient]
  · refine Prod.ext ?_ ?_
    · show Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ (algebraMap E A.L y)) =
        Ideal.Quotient.mk _ (algebraMap E A.L y)
      rw [Ideal.quotientEquivAlgOfEq_mk]
    · show Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ (algebraMap E A.L y)) =
        Ideal.Quotient.mk _ (algebraMap E A.L y)
      rw [Ideal.quotientEquivAlgOfEq_mk]
  · refine Prod.ext ?_ ?_
    · show Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ (star y)) =
        (quotStarRing _ (star_mem A e)).star (Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ y))
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientEquivAlgOfEq_mk]
      rfl
    · show Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ (star y)) =
        (quotStarRing _ (star_mem A (1 - e))).star (Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ y))
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientEquivAlgOfEq_mk]
      rfl

end GlobalTheory.JR.EtQuot
