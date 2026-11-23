import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

noncomputable section

namespace LocMassOrdSF

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory
  NumberField IsDedekindDomain Topology Matrix
open scoped TensorProduct

section FvTop

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem secondCountable_Fv : SecondCountableTopology (Fv F v) := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : TopologicalSpace.SeparableSpace (Fv F v) :=
    ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
      IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
  exact UniformSpace.secondCountable_of_separable (Fv F v)

theorem locallyCompact_Fv : LocallyCompactSpace (Fv F v) :=
  (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _))

theorem isOpen_units_Fv : IsOpen {r : Fv F v | IsUnit r} := by
  simp only [isUnit_iff_ne_zero]
  exact isOpen_ne

end FvTop

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem isModTop_tens : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

attribute [local instance] isModTop_tens

theorem isTopRing_tens : IsTopologicalRing (R ⊗[F] E) :=
  IsModuleTopology.isTopologicalRing R _

attribute [local instance] isTopRing_tens

theorem exists_homeomorph_tens :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (R ⊗[F] E ≃ₜ (ι → R)) := by
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  exact ⟨Fin (Module.finrank F E), inferInstance,
    ⟨{ toEquiv := e.toEquiv
       continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
       continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩⟩

theorem lc_tens [LocallyCompactSpace R] [T2Space R] : LocallyCompactSpace (R ⊗[F] E) := by
  obtain ⟨ι, hι, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isClosedEmbedding.locallyCompactSpace

theorem t2_tensor_product [T2Space R] : T2Space (R ⊗[F] E) := by
  obtain ⟨ι, hι, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isEmbedding.t2Space

theorem sc_tens [SecondCountableTopology R] : SecondCountableTopology (R ⊗[F] E) := by
  obtain ⟨ι, hι, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isInducing.secondCountableTopology

end Tens

section Free

def LIP (R : Type) [CommRing R] : Prop :=
  ∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (W : Matrix m n R),
    (∀ c, W *ᵥ c = 0 → c = 0) → ∃ P : Matrix n m R, P * W = 1

theorem lip_field (K : Type) [Field K] : LIP K := by
  intro m n _ _ _ _ W hW
  have hker : LinearMap.ker (Matrix.mulVecLin W) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    exact hW c hc
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin W) hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 : LinearMap.toMatrix' (g ∘ₗ Matrix.mulVecLin W) = 1 := by
    rw [hg, LinearMap.toMatrix'_id]
  rwa [LinearMap.toMatrix'_comp,
    show LinearMap.toMatrix' (Matrix.mulVecLin W) = W from LinearMap.toMatrix'_toLin' W] at h1

theorem inj_of_isUnit {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (W : Matrix m n R) (P : Matrix n m R) (hP : IsUnit (P * W).det)
    (c : n → R) (hc : W *ᵥ c = 0) : c = 0 := by
  have h1 : (P * W) *ᵥ c = 0 := by
    rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hP
  calc c = ((↑u⁻¹ : Matrix n n R) * (P * W)) *ᵥ c := by
        rw [← hu, Units.inv_mul, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) (k : Fin d) : R :=
  (Algebra.TensorProduct.basis R b).repr y k

def wMat (R : Type) [CommRing R] [Algebra F R] {a M : ℕ} (X : Fin a → Fin M → R ⊗[F] E) :
    Matrix (Fin M × Fin d) (Fin a × Fin d) R :=
  fun p q => crd b R (((1 : R) ⊗ₜ[F] b q.2) * X q.1 p.1) p.2

theorem wMat_mulVec (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) (c : Fin a × Fin d → R) (j : Fin M) (l : Fin d) :
    (wMat b R X *ᵥ c) (j, l) =
      crd b R (∑ i, (∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) * X i j) l := by
  simp only [Matrix.mulVec, dotProduct, wMat, crd, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem wMat_mulVec_eq_zero (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) (c : Fin a × Fin d → R) :
    wMat b R X *ᵥ c = 0 ↔ ∀ j, ∑ i, (∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) * X i j = 0 := by
  constructor
  · intro h j
    apply (Algebra.TensorProduct.basis R b).repr.injective
    ext l
    have h1 := congrFun h (j, l)
    rw [wMat_mulVec] at h1
    simpa [crd] using h1
  · intro h
    funext q
    obtain ⟨j, l⟩ := q
    rw [wMat_mulVec, h j]
    simp [crd]

theorem linIndep_iff (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) :
    LinearIndependent (R ⊗[F] E) X ↔ ∀ c, wMat b R X *ᵥ c = 0 → c = 0 := by
  classical
  let B := Algebra.TensorProduct.basis R b
  have hBk : ∀ k, B k = (1 : R) ⊗ₜ[F] b k := fun k => Algebra.TensorProduct.basis_apply b k
  have hsum : ∀ g : Fin a → R ⊗[F] E, (∑ i, g i • X i = 0) ↔ ∀ j, ∑ i, g i * X i j = 0 := by
    intro g
    constructor
    · intro h j
      have h1 := congrFun h j
      simpa [Finset.sum_apply] using h1
    · intro h
      funext j
      simpa [Finset.sum_apply] using h j
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hli c hc
    rw [wMat_mulVec_eq_zero] at hc
    have h0 := hli (fun i => ∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) ((hsum _).mpr hc)
    funext q
    obtain ⟨i, k⟩ := q
    have h0' : (∑ k, c (i, k) • B k) = 0 := by
      have h3 := h0 i
      simpa [hBk] using h3
    have h2 : ⇑(B.repr (∑ k, c (i, k) • B k)) = fun k => c (i, k) := B.repr_sum_self _
    rw [h0', map_zero] at h2
    simpa using (congrFun h2 k).symm
  · intro h g hg i
    let c : Fin a × Fin d → R := fun q => B.repr (g q.1) q.2
    have hg' : ∀ i, (∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) = g i := by
      intro i
      simp only [c, ← hBk]
      exact B.sum_repr (g i)
    have hc : wMat b R X *ᵥ c = 0 := by
      rw [wMat_mulVec_eq_zero]
      intro j
      simp only [hg']
      exact (hsum g).mp hg j
    have h0 := h c hc
    apply B.repr.injective
    ext k
    have h4 := congrFun h0 (i, k)
    simpa [c] using h4

variable [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
  [IsTopologicalRing R]

attribute [local instance] isModTop_tens isTopRing_tens

theorem continuous_crd (k : Fin d) : Continuous (fun y : R ⊗[F] E => crd b R y k) :=
  IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis R b).coord k)

theorem continuous_wMat {a M : ℕ} :
    Continuous (fun X : Fin a → Fin M → R ⊗[F] E => wMat b R X) := by
  refine continuous_matrix fun p q => ?_
  exact (continuous_crd b R p.2).comp
    (continuous_const.mul ((continuous_apply p.1).comp (continuous_apply q.1)))

include b in
theorem isOpen_linIndep (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R) {a M : ℕ} :
    IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  have e : {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} =
      ⋃ P : Matrix (Fin a × Fin d) (Fin M × Fin d) R,
        (fun X => (P * wMat b R X).det) ⁻¹' {r | IsUnit r} := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
    rw [linIndep_iff b]
    constructor
    · intro h
      obtain ⟨P, hP⟩ := hL _ _ _ h
      exact ⟨P, by rw [hP, Matrix.det_one]; exact isUnit_one⟩
    · rintro ⟨P, hP⟩ c hc
      exact inj_of_isUnit _ P hP c hc
  rw [e]
  exact isOpen_iUnion fun P =>
    hU.preimage ((continuous_const.matrix_mul (continuous_wMat b R)).matrix_det)

end Free

section Fib

theorem sfinite_of_fib {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [OpensMeasurableSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {f : V → Y} {ι : X → Y}
    {U : Set V} (hU : IsOpen U) {ν : Measure X} {fib : X → Measure V}
    (h : IsFibreFamily μ f ι U ν Set.univ fib) (b : X) : SFinite (fib b) := by
  classical
  obtain ⟨hconc, -, hint⟩ := h
  have hsub : Uᶜ ⊆ (f ⁻¹' {ι b} ∩ U)ᶜ := fun x hx hx' => hx hx'.2
  have hnull : fib b Uᶜ = 0 := measure_mono_null hsub (hconc b)
  have hK : ∀ K : Set V, IsCompact K → K ⊆ U → fib b K < ⊤ := by
    intro K hKc hKU
    obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hKc hU hKU
    obtain ⟨g, hg1, hg0, hgc, -⟩ := exists_continuous_one_zero_of_isCompact hKc
      isOpen_interior.isClosed_compl (Set.disjoint_compl_right_iff_subset.mpr hKL)
    have hsupp : Function.support g ⊆ interior L := by
      intro x hx
      by_contra hn
      exact hx (by simpa using hg0 hn)
    have hts : tsupport g ⊆ U :=
      (closure_minimal (hsupp.trans interior_subset) hLc.isClosed).trans hLU
    have hI := (hint g g.continuous hgc hts).1 b (Set.mem_univ b)
    have hle := hI.measure_norm_ge_lt_top (ε := 1) one_pos
    refine lt_of_le_of_lt (measure_mono ?_) hle
    intro x hx
    show (1 : ℝ) ≤ ‖g x‖
    rw [hg1 hx]
    simp
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  let K : ℕ → Set V := fun n => Subtype.val '' compactCovering U n
  have hKc : ∀ n, IsCompact (K n) := fun n =>
    (isCompact_compactCovering U n).image continuous_subtype_val
  have hKU : ∀ n, K n ⊆ U := by
    intro n y hy
    obtain ⟨x, -, rfl⟩ := hy
    exact x.2
  have hcov : ∀ x ∈ U, ∃ n, x ∈ K n := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_mem_compactCovering (⟨x, hx⟩ : U)
    exact ⟨n, ⟨x, hx⟩, hn, rfl⟩
  have hfin : ∀ n, fib b (K n ∪ Uᶜ) < ⊤ := fun n =>
    (measure_union_le _ _).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hK _ (hKc n) (hKU n), by rw [hnull]; exact ENNReal.zero_lt_top⟩)
  haveI : SigmaFinite (fib b) := ⟨⟨{
    set := fun n => K n ∪ Uᶜ
    set_mem := fun _ => Set.mem_univ _
    finite := hfin
    spanning := by
      refine Set.eq_univ_of_forall fun x => ?_
      by_cases hx : x ∈ U
      · obtain ⟨n, hn⟩ := hcov x hx
        exact Set.mem_iUnion.mpr ⟨n, Or.inl hn⟩
      · exact Set.mem_iUnion.mpr ⟨0, Or.inr hx⟩ }⟩⟩
  infer_instance

end Fib

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finDim_FE : FiniteDimensional F E := by
  first
  | infer_instance
  | exact Module.Finite.of_restrictScalars_finite ℚ F E

theorem isOpen_indep (v : HeightOneSpectrum (𝓞 F)) (n a : ℕ) :
    IsOpen (IndepV (E := E) (n := n) v a) := by
  haveI : FiniteDimensional F E := finDim_FE
  exact isOpen_linIndep (Module.finBasis F E) (Fv F v) (isOpen_units_Fv v) (lip_field _)

end Main

theorem orbit_measure_sFinite : LocMassOrdW.OmSF := by
  intro F E _ _ _ _ _ σ n J ψ v _ a T
  unfold Formalism.L2.SG.LocVol.omAt
  split_ifs with hT
  · unfold Formalism.L2.SG.LocVol.omFam
    split_ifs with hfib
    · haveI : FiniteDimensional F E := finDim_FE
      haveI : LocallyCompactSpace (Fv F v) := locallyCompact_Fv v
      haveI : SecondCountableTopology (Fv F v) := secondCountable_Fv v
      haveI : LocallyCompactSpace (Fv F v ⊗[F] E) := lc_tens (Fv F v)
      haveI : T2Space (Fv F v ⊗[F] E) := t2_tensor_product (Fv F v)
      haveI : SecondCountableTopology (Fv F v ⊗[F] E) := sc_tens (Fv F v)
      haveI : OpensMeasurableSpace (TupV (E := E) v n a) := by
        first
        | exact ⟨le_rfl⟩
        | (haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩; infer_instance)
      exact sfinite_of_fib (isOpen_indep v n a) hfib.choose_spec ⟨T, hT⟩
    · infer_instance
  · infer_instance

theorem self_dual_measure_sFinite : LocMassOrdW.SdESF := by
  intro F E _ _ _ _ _ σ n J ψ v _ r
  unfold Formalism.L2.SG.LocVol.sdE
  split_ifs with h
  · haveI : FiniteDimensional F E := finDim_FE
    haveI : LocallyCompactSpace (Fv F v) := locallyCompact_Fv v
    haveI : SecondCountableTopology (Fv F v) := secondCountable_Fv v
    haveI : LocallyCompactSpace (Fv F v ⊗[F] E) := lc_tens (Fv F v)
    haveI : T2Space (Fv F v ⊗[F] E) := t2_tensor_product (Fv F v)
    haveI : SecondCountableTopology (Fv F v ⊗[F] E) := sc_tens (Fv F v)
    haveI := h.choose_spec.1
    infer_instance
  · infer_instance

end LocMassOrdSF
