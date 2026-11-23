import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace GlobalTheory.UnitU

variable {D : D7} {ρ : ℕ}

def uniSet (D : D7) (ρ : ℕ) : Set (Matrix (Fin ρ) (Fin ρ) (AE D)) :=
  {M | ∀ i j : Fin ρ, (j < i → M i j = 0) ∧ M i i = 1}

private theorem t2_lemma (D : D7) : T2Space (AE D) := by
  haveI : T2Space (Fin 1 → Fin 1 → AE D) := (lattice_Mx D 1 1).2.2.2.1
  exact T2Space.of_injective_continuous (f := fun a : AE D => (fun _ _ => a : Mx D 1 1))
    (fun a b h => congrFun (congrFun h 0) 0) (continuous_pi fun _ => continuous_pi fun _ => continuous_id)

theorem isClosed_uniSet (D : D7) (ρ : ℕ) : IsClosed (uniSet D ρ) := by
  haveI : T2Space (AE D) := t2_lemma D
  have h1 : ∀ i j : Fin ρ, IsClosed {M : Matrix (Fin ρ) (Fin ρ) (AE D) | j < i → M i j = 0} := by
    intro i j
    by_cases h : j < i
    · have hc : Continuous fun M : Matrix (Fin ρ) (Fin ρ) (AE D) => M i j := continuous_id.matrix_elem i j
      simpa only [h, true_implies] using isClosed_eq hc continuous_const
    · simp only [h, false_implies, Set.setOf_true]
      exact isClosed_univ
  have h2 : ∀ i : Fin ρ, IsClosed {M : Matrix (Fin ρ) (Fin ρ) (AE D) | M i i = 1} := fun i =>
    isClosed_eq (show Continuous fun M : Matrix (Fin ρ) (Fin ρ) (AE D) => M i i from
      continuous_id.matrix_elem i i) continuous_const
  have e : uniSet D ρ = ⋂ i, ⋂ j, ({M : Matrix (Fin ρ) (Fin ρ) (AE D) | j < i → M i j = 0} ∩ {M | M i i = 1}) := by
    ext M
    simp only [uniSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [e]
  exact isClosed_iInter fun i => isClosed_iInter fun j => (h1 i j).inter (h2 i)

theorem det_of_mem {M : Matrix (Fin ρ) (Fin ρ) (AE D)} (hM : M ∈ uniSet D ρ) : M.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => (hM i j).1 h)]
  exact Finset.prod_eq_one fun i _ => (hM i i).2

def toUnit (M : Matrix (Fin ρ) (Fin ρ) (AE D)) (hM : M ∈ uniSet D ρ) : GL (Fin ρ) (AE D) :=
  ⟨M, M.adjugate, by rw [Matrix.mul_adjugate, det_of_mem hM, one_smul],
    by rw [Matrix.adjugate_mul, det_of_mem hM, one_smul]⟩

theorem mem_UX_iff (u : GL (Fin ρ) (AE D)) : u ∈ UX D ρ ↔ (u : Matrix (Fin ρ) (Fin ρ) (AE D)) ∈ uniSet D ρ :=
  ⟨fun h => h, fun h => h⟩

theorem inv_eq_adjugate (u : UX D ρ) :
    (u⁻¹).1.1 = u.1.1.adjugate := by
  have hu : (u.1.1 : Matrix (Fin ρ) (Fin ρ) (AE D)) ∈ uniSet D ρ := (mem_UX_iff u.1).1 u.2
  have h1 : u.1.1 * u.1.1.adjugate = 1 := by rw [Matrix.mul_adjugate, det_of_mem hu, one_smul]
  have h2 : (u⁻¹).1.1 * u.1.1 = 1 := by rw [Subgroup.coe_inv, Units.inv_mul]
  calc (u⁻¹).1.1 = (u⁻¹).1.1 * (u.1.1 * u.1.1.adjugate) := by rw [h1, Matrix.mul_one]
    _ = ((u⁻¹).1.1 * u.1.1) * u.1.1.adjugate := (Matrix.mul_assoc _ _ _).symm
    _ = u.1.1.adjugate := by rw [h2, Matrix.one_mul]

theorem isClosedEmbedding_val (D : D7) (ρ : ℕ) :
    Topology.IsClosedEmbedding (fun u : UX D ρ => u.1.1) := by
  have hc : Continuous (fun u : UX D ρ => u.1.1) := Units.continuous_val.comp continuous_subtype_val
  have hg : Continuous (fun M : Matrix (Fin ρ) (Fin ρ) (AE D) => (M, MulOpposite.op M.adjugate)) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_adjugate)
  have hind : Topology.IsInducing (fun u : UX D ρ => u.1.1) := by
    refine Topology.IsInducing.of_comp hc hg ?_
    have e : ((fun M : Matrix (Fin ρ) (Fin ρ) (AE D) => (M, MulOpposite.op M.adjugate)) ∘
        fun u : UX D ρ => u.1.1) = Units.embedProduct _ ∘ (Subtype.val : UX D ρ → GL (Fin ρ) (AE D)) := by
      funext u
      simp only [Function.comp_apply, Units.embedProduct_apply]
      rw [← inv_eq_adjugate u]
      rfl
    rw [e]
    exact Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  refine ⟨⟨hind, fun a b h => Subtype.ext (Units.ext h)⟩, ?_⟩
  have hr : Set.range (fun u : UX D ρ => u.1.1) = uniSet D ρ := by
    ext M
    constructor
    · rintro ⟨u, rfl⟩
      exact (mem_UX_iff u.1).1 u.2
    · intro hM
      exact ⟨⟨toUnit M hM, (mem_UX_iff _).2 hM⟩, rfl⟩
  rw [hr]
  exact isClosed_uniSet D ρ

end GlobalTheory.UnitU

namespace GlobalTheory.UnitU

variable {D : D7} {ρ : ℕ}

theorem topology (D : D7) (ρ : ℕ) :
    LocallyCompactSpace (UX D ρ) ∧ SecondCountableTopology (UX D ρ) ∧ T2Space (UX D ρ) := by
  obtain ⟨-, hlc, hsc, ht2, -⟩ := lattice_Mx D ρ ρ
  haveI : LocallyCompactSpace (Matrix (Fin ρ) (Fin ρ) (AE D)) := hlc
  haveI : SecondCountableTopology (Matrix (Fin ρ) (Fin ρ) (AE D)) := hsc
  haveI : T2Space (Matrix (Fin ρ) (Fin ρ) (AE D)) := ht2
  have he := isClosedEmbedding_val D ρ
  exact ⟨he.locallyCompactSpace, he.isInducing.secondCountableTopology, he.isEmbedding.t2Space⟩

theorem rational (D : D7) (ρ : ℕ) : Countable (UXQ D ρ) ∧ DiscreteTopology (UXQ D ρ) := by
  obtain ⟨-, -, hsc, -, hd, -⟩ := lattice_Mx D ρ ρ
  let f : UXQ D ρ → ratMx D ρ ρ := fun u => ⟨u.1.1.1, u.2.1⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (Subtype.ext (Units.ext (congrArg Subtype.val h)))
  have hc : Continuous f :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  haveI : SecondCountableTopology (Mx D ρ ρ) := hsc
  haveI : DiscreteTopology (ratMx D ρ ρ) := hd
  haveI : Countable (ratMx D ρ ρ) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact ⟨hf.countable, DiscreteTopology.of_continuous_injective hc hf⟩

noncomputable def row (u : Matrix (Fin ρ) (Fin ρ) (AE D)) (pick : AE D → D.host.E) (i : Fin ρ) (j : Fin ρ) : D.host.E :=
  if j < i then 0 else if j = i then 1 else
    pick (∑ l : Fin ρ, if h : l < j then incA D (row u pick i l) * u l j else 0)
termination_by j.val
decreasing_by exact h

theorem row_eq (u : Matrix (Fin ρ) (Fin ρ) (AE D)) (pick : AE D → D.host.E) (i j : Fin ρ) :
    row u pick i j = if j < i then 0 else if j = i then 1 else
      pick (∑ l : Fin ρ, if l < j then incA D (row u pick i l) * u l j else 0) := by
  rw [row]
  simp only [dite_eq_ite]

theorem mul_apply_of_uni (δ : Matrix (Fin ρ) (Fin ρ) D.host.E) {u : Matrix (Fin ρ) (Fin ρ) (AE D)} (hu : u ∈ uniSet D ρ)
    (i j : Fin ρ) : (rat δ * u) i j = incA D (δ i j) + ∑ l : Fin ρ, if l < j then incA D (δ i l) * u l j else 0 := by
  rw [Matrix.mul_apply]
  have key : ∀ l : Fin ρ, rat δ i l * u l j =
      (if l = j then incA D (δ i j) else 0) + (if l < j then incA D (δ i l) * u l j else 0) := by
    intro l
    rcases lt_trichotomy l j with h | rfl | h
    · simp [h, h.ne, rat]
    · simp [(hu l l).2, rat]
    · simp [not_lt.2 h.le, h.ne', (hu l j).1 h, rat]
  rw [Finset.sum_congr rfl (fun l _ => key l), Finset.sum_add_distrib]
  simp

theorem reduce : ∀ (D : D7) (ρ : ℕ), ∃ C : Set (AE D), IsCompact C ∧ ∀ u : UX D ρ, ∃ γ ∈ UXQ D ρ, ∀ i j : Fin ρ, i < j → (γ⁻¹ * u).1.1 i j ∈ C := by
  intro D ρ
  obtain ⟨-, -, -, -, -, K, hK, hKx⟩ := lattice_Mx D 1 1
  have hcK : Continuous fun M : Mx D 1 1 => M 0 0 := continuous_id.matrix_elem 0 0
  refine ⟨(fun M : Mx D 1 1 => M 0 0) '' K, hK.image hcK, ?_⟩
  have hex : ∀ x : AE D, ∃ e : D.host.E, incA D e + x ∈ (fun M : Mx D 1 1 => M 0 0) '' K := by
    intro x
    obtain ⟨γ, hγ, hγK⟩ := hKx (fun _ _ => x)
    obtain ⟨g, rfl⟩ := mem_ratMx.1 hγ
    exact ⟨g 0 0, _, hγK, rfl⟩
  choose pick hpick using hex
  intro u
  have hu : u.1.1 ∈ uniSet D ρ := (mem_UX_iff u.1).1 u.2
  let δ : Matrix (Fin ρ) (Fin ρ) D.host.E := Matrix.of (row u.1.1 pick)
  have hδ : ∀ i j, δ i j = row u.1.1 pick i j := fun _ _ => rfl
  have hδu : ∀ i j : Fin ρ, (j < i → δ i j = 0) ∧ δ i i = 1 := by
    intro i j
    refine ⟨fun h => ?_, ?_⟩
    · rw [hδ, row_eq]
      simp [h]
    · rw [hδ, row_eq]
      simp
  have hr : rat δ ∈ uniSet D ρ := by
    intro i j
    refine ⟨fun h => ?_, ?_⟩
    · simp [rat, (hδu i j).1 h]
    · simp [rat, (hδu i i).2]
  let w : UX D ρ := ⟨toUnit (rat δ) hr, (mem_UX_iff _).2 hr⟩
  have hw : w.1.1 = rat δ := rfl
  have hadj : (rat δ).adjugate = rat δ.adjugate := (RingHom.map_adjugate (incA D) δ).symm
  refine ⟨w⁻¹, show _ ∧ _ from ⟨?_, ?_⟩, ?_⟩
  · rw [inv_eq_adjugate, hw, hadj]
    exact rat_mem _
  · rw [← Subgroup.coe_inv, inv_inv, hw]
    exact rat_mem δ
  · intro i j hij
    rw [inv_inv]
    show (rat δ * u.1.1) i j ∈ _
    rw [mul_apply_of_uni δ hu]
    have hji : ¬ j < i := not_lt.2 hij.le
    have hne : j ≠ i := hij.ne'
    have hS : δ i j = pick (∑ l : Fin ρ, if l < j then incA D (δ i l) * u.1.1 l j else 0) := by
      rw [hδ, row_eq]
      simp only [hji, hne, if_false, hδ]
    rw [hS]
    exact hpick _

theorem cocompact (D : D7) (ρ : ℕ) :
    ∃ K : Set (UX D ρ), IsCompact K ∧ ∀ u : UX D ρ, ∃ γ ∈ UXQ D ρ, ∃ k ∈ K, u = γ * k := by
  obtain ⟨C, hC, hred⟩ := reduce D ρ
  let C' : Set (AE D) := insert 0 (insert 1 C)
  have hC' : IsCompact C' := (hC.insert 1).insert 0
  let P : Set (Matrix (Fin ρ) (Fin ρ) (AE D)) := Set.univ.pi fun _ => Set.univ.pi fun _ => C'
  have hP : IsCompact P := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC'
  refine ⟨(fun u : UX D ρ => u.1.1) ⁻¹' P, (isClosedEmbedding_val D ρ).isCompact_preimage hP, fun u => ?_⟩
  obtain ⟨γ, hγ, hγu⟩ := hred u
  refine ⟨γ, hγ, γ⁻¹ * u, ?_, (mul_inv_cancel_left γ u).symm⟩
  have hk := (mem_UX_iff (γ⁻¹ * u).1).1 (γ⁻¹ * u).2
  intro i _ j _
  rcases lt_trichotomy i j with h | rfl | h
  · exact Or.inr (Or.inr (hγu i j h))
  · exact Or.inr (Or.inl (hk i i).2)
  · exact Or.inl ((hk i j).1 h)

theorem isMulRightInvariant_of_fundamentalDomain {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ]
    (ν : Measure G) [ν.IsHaarMeasure] {𝓤 : Set G} (h : IsFundamentalDomain Γ 𝓤 ν) (h0 : ν 𝓤 ≠ 0) (h1 : ν 𝓤 ≠ ⊤) :
    ν.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have hm : Measurable (fun x : G => x * g) := measurable_mul_const g
  have hsc := Measure.isMulLeftInvariant_eq_smul (ν.map (fun x : G => x * g)) ν
  set c := Measure.haarScalarFactor (ν.map (fun x : G => x * g)) ν with hc
  have hF1 : IsFundamentalDomain Γ 𝓤 (ν.map (fun x : G => x * g)) :=
    h.mono (by rw [hsc]; exact Measure.smul_absolutelyContinuous)
  have hF2 : IsFundamentalDomain Γ (Equiv.mulRight g '' 𝓤) (ν.map (fun x : G => x * g)) := by
    refine h.image_of_equiv (Equiv.mulRight g) ?_ (Equiv.refl _) ?_
    · refine MeasurePreserving.quasiMeasurePreserving ⟨?_, ?_⟩
      · simpa [Equiv.mulRight_symm] using measurable_mul_const g⁻¹
      · rw [Equiv.mulRight_symm, Equiv.coe_mulRight, Measure.map_map (measurable_mul_const _) hm]
        simp [Function.comp_def, mul_assoc]
    · intro γ x
      simp [Subgroup.smul_def, mul_assoc]
  have e1 : (ν.map (fun x : G => x * g)) (Equiv.mulRight g '' 𝓤) = ν 𝓤 := by
    have := (MeasurableEquiv.mulRight g).map_apply (μ := ν) (Equiv.mulRight g '' 𝓤)
    rw [MeasurableEquiv.coe_mulRight] at this
    rw [this]
    congr 1
    exact (Equiv.mulRight g).preimage_image 𝓤
  have e2 := hF2.measure_eq hF1
  rw [e1, hsc, Measure.smul_apply] at e2
  have e3 : (c : ENNReal) * ν 𝓤 = 1 * ν 𝓤 := by
    rw [one_mul]
    exact (by simpa [ENNReal.smul_def] using e2.symm)
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 h1).1 e3
    exact_mod_cast this
  rw [hsc, hc1, one_smul]

open GlobalTheory.Per.UnitN in
theorem isUnitU_exists_unique_rightInvariant : ∀ (D : D7) (ρ : ℕ), (∃ ν, IsUnitU D ρ ν) ∧ (∀ ν ν', IsUnitU D ρ ν → IsUnitU D ρ ν' → ν = ν') ∧
    ∀ ν, IsUnitU D ρ ν → ν.IsMulRightInvariant := by
  intro D ρ
  obtain ⟨hlc, hsc, ht2⟩ := topology D ρ
  obtain ⟨hcount, hdisc⟩ := rational D ρ
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨K, hK, hcov⟩ := cocompact D ρ
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨ν, 𝓝, hH, hF, h1⟩ := exists_unit_of_cocompact (UXQ D ρ) hK hcov
    exact ⟨ν, hH, 𝓝, hF, h1⟩
  · rintro ν ν' ⟨hH, 𝓤, hF, h1⟩ ⟨hH', 𝓤', hF', h1'⟩
    have hsm := Measure.isMulLeftInvariant_eq_smul ν' ν
    set c := Measure.haarScalarFactor ν' ν with hc
    have hF'' : IsFundamentalDomain (UXQ D ρ) 𝓤 ν' :=
      hF.mono (by rw [hsm]; exact Measure.smul_absolutelyContinuous)
    have e := hF''.measure_eq hF'
    rw [h1', hsm, Measure.smul_apply, h1] at e
    have hc1 : (c : ENNReal) = 1 := by simpa [ENNReal.smul_def] using e
    rw [hsm, ENNReal.coe_eq_one.1 hc1, one_smul]
  · rintro ν ⟨hH, 𝓤, hF, h1⟩
    exact isMulRightInvariant_of_fundamentalDomain (UXQ D ρ) ν hF (by rw [h1]; exact one_ne_zero)
      (by rw [h1]; exact ENNReal.one_ne_top)

end GlobalTheory.UnitU
