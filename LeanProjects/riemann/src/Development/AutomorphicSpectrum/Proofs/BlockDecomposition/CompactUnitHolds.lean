import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDefiniteUnitaryAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedTriangularBounded
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactImageEqUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.AutomorphicL2Unitary
open scoped TensorProduct InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.CompUnitary

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]

theorem compactSpace_quot (hc : ∃ C : Set G, IsCompact C ∧ ∀ g, ∃ γ ∈ Γ, γ * g ∈ C) : CompactSpace (Quot Γ) := by
  obtain ⟨C, hC, h⟩ := hc
  refine ⟨?_⟩
  have e : mk Γ '' C = Set.univ := Set.eq_univ_of_forall fun q => by
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    obtain ⟨γ, hγ, hg⟩ := h g
    exact ⟨_, hg, (mk_eq_iff.2 ⟨⟨γ, hγ⟩, rfl⟩).symm⟩
  rw [← e]
  exact hC.image continuous_quot_mk

theorem isMulRightInvariant_of_cover (hc : ∃ C : Set G, IsCompact C ∧ ∀ g, ∃ γ ∈ Γ, γ * g ∈ C)
    (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := ⟨fun g => by
  obtain ⟨C, hC, hcov⟩ := hc
  have h := isFundamentalDomain_stdDom Γ μ
  have hfin : μ (stdDom Γ) ≠ ⊤ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h]
    refine ((quotMeasure_le (T := C) MeasurableSet.univ fun q _ => ?_).trans_lt hC.measure_lt_top).ne
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    obtain ⟨γ, hγ, hx⟩ := hcov x
    exact ⟨_, hx, (mk_eq_iff.2 ⟨⟨γ, hγ⟩, rfl⟩).symm⟩
  have e := Measure.isMulLeftInvariant_eq_smul (μ.map (· * g)) μ
  have h' : IsFundamentalDomain Γ ((· * g) ⁻¹' stdDom Γ) μ :=
    h.preimage_of_equiv ⟨measurable_mul_const g, e ▸ Measure.smul_absolutelyContinuous⟩ Function.bijective_id
      fun γ x => mul_assoc _ _ _
  have h1 := h'.measure_eq h
  rw [← Measure.map_apply (measurable_mul_const g) (measurableSet_stdDom _), e, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul, ENNReal.mul_eq_right (h.measure_ne_zero (NeZero.ne μ)) hfin, ENNReal.coe_eq_one] at h1
  rw [e, h1, one_smul]⟩

theorem isUnitarisable_of_embedding (hc : ∃ C : Set G, IsCompact C ∧ ∀ g, ∃ γ ∈ Γ, γ * g ∈ C)
    {L H V : Type} [Group L] [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (p : L →* H) (hp : Function.Surjective p) (ι : L →* G) (f : V →ₗ[ℂ] (G → ℂ)) (hf : Function.Injective f)
    (hcont : ∀ v, Continuous (f v)) (hleft : ∀ v, LeftInv Γ (f v))
    (heq : ∀ x v y, f (ρ (p x) v) y = f v (y * ι x)) : GlobalTheory.LGrp.IsUnitarisable ρ := by
  let μ : Measure G := Measure.haar
  haveI : μ.IsMulRightInvariant := isMulRightInvariant_of_cover Γ hc μ
  haveI := compactSpace_quot Γ hc
  have hm : ∀ v, MemL2Quotient Γ μ (f v) := fun v =>
    (GlobalTheory.AutomorphicL2Cocompact.cocompact G Γ μ inferInstance).2.2 _ (hleft v) (hcont v)
  let T : V →ₗ[ℂ] L2 Γ μ :=
    { toFun := fun v => (hm v).toL2
      map_add' := fun v w => by
        apply Lp.ext
        filter_upwards [(hm (v + w)).coeFn_toL2, (hm v).coeFn_toL2, (hm w).coeFn_toL2,
          Lp.coeFn_add (hm v).toL2 (hm w).toL2] with q h1 h2 h3 h4
        rw [h1, h4, Pi.add_apply, h2, h3, map_add]
        rfl
      map_smul' := fun c v => by
        apply Lp.ext
        filter_upwards [(hm (c • v)).coeFn_toL2, (hm v).coeFn_toL2, Lp.coeFn_smul c (hm v).toL2] with q h1 h2 h3
        rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, map_smul]
        rfl }
  have hT : ∀ v, T v = (hm v).toL2 := fun _ => rfl
  have hT0 : ∀ v, T v = 0 → v = 0 := fun v h0 => by
    have h1 : ∀ᵐ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ, GlobalTheory.AutomorphicL2Unitary.descend Γ (f v) q = 0 := by
      filter_upwards [(hm v).coeFn_toL2, Lp.coeFn_zero ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)] with q h1 h2
      rw [← h1, ← hT, h0, h2]
      rfl
    have h2 : ∀ᵐ g ∂μ, f v g = 0 := by
      filter_upwards [ae_quotMeasure_iff.1 h1] with g hg
      rwa [(hleft v).descend_mk] at hg
    have h3 : f v = 0 := (Continuous.ae_eq_iff_eq μ (hcont v) continuous_const).1 h2
    exact hf (by rw [h3, map_zero])
  have hTR : ∀ x v, T (ρ (p x) v) = R Γ μ (ι x) (T v) := fun x v => by
    rw [hT, hT, right_translate_toL2, MemL2Quotient.toL2_eq_iff_ae_eq]
    exact .of_forall fun y => heq x v y
  have hU := isUnitaryRep_R Γ μ
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => ⟪T w, T v⟫_ℂ)
    (fun _ _ _ => by simp [inner_add_right]) (fun _ _ _ => by simp [inner_smul_right])
    (fun _ _ _ => by simp [inner_add_left]) (fun _ _ _ => by simp [inner_smul_left]),
    fun v w => (inner_conj_symm (T v) (T w)).symm, fun v hv => (re_inner_self_pos (𝕜 := ℂ)).2 fun e => hv (hT0 v e),
    fun g v w => ?_⟩
  obtain ⟨x, rfl⟩ := hp g
  change ⟪T (ρ (p x) w), T (ρ (p x) v)⟫_ℂ = ⟪T w, T v⟫_ℂ
  rw [hTR, hTR]
  exact GlobalTheory.AutMult.inner_map_map hU _ _ _

end Abstract

section Concrete

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

local notation "F₀" => maximalRealSubfield E
local notation "σ₀" => (IsCMField.complexConj E : E →ₐ[maximalRealSubfield E] E)

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_HA (n : ℕ) : ∃ j : UA E n ≃ₜ* HA (AF F₀) σ₀ (1 : Matrix (Fin n) (Fin n) E),
    ∀ x, x ∈ ratU E n ↔ j x ∈ HFinIn (AF F₀) σ₀ (1 : Matrix (Fin n) (Fin n) E) := by
  obtain ⟨j, h, -⟩ := GlobalTheory.DefTransfer.Glob.exists_group (E := E) (n := n) 1 1 (by simp [cT])
  exact ⟨j, h⟩

theorem hform_one_ne_zero {n : ℕ} (x : Fin n → E) (hx : x ≠ 0) :
    Formalism.UG.hform (σ₀ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) x x ≠ 0 := by
  intro h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hc : ∀ y : E, τ (IsCMField.complexConj E y) = star (τ y) := fun y =>
    IsCMField.complexEmbedding_complexConj E τ y
  have e : Formalism.UG.hform (σ₀ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) x x =
      ∑ i, IsCMField.complexConj E (x i) * x i := by
    simp [Formalism.UG.hform, Matrix.one_apply]
  have h1 := congrArg τ (e.symm.trans h)
  rw [map_sum, map_zero] at h1
  have h2 : ∑ i, ((Complex.normSq (τ (x i)) : ℝ) : ℂ) = 0 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hc, Complex.star_def, mul_comm, Complex.mul_conj]
  have h3 : ∑ i, Complex.normSq (τ (x i)) = 0 := by exact_mod_cast h2
  refine hx (funext fun i => ?_)
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).1 h3 i (Finset.mem_univ _)
  exact (map_eq_zero τ).1 (Complex.normSq_eq_zero.1 h4)

theorem setup (n : ℕ) : IsTopologicalGroup (UA E n) ∧ LocallyCompactSpace (UA E n) ∧
    SecondCountableTopology (UA E n) ∧ T2Space (UA E n) ∧ DiscreteTopology (ratU E n) ∧
    ∃ C : Set (UA E n), IsCompact C ∧ ∀ g, ∃ γ ∈ ratU E n, γ * g ∈ C := by
  obtain ⟨j, hj⟩ := exists_HA (E := E) n
  obtain ⟨l1, l2, l3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F₀ E σ₀ n 1
  have hcm := GlobalTheory.AdelicU.isCMExt_of_isCMField E
  have hherm : IsHermND σ₀ (1 : Matrix (Fin n) (Fin n) E) := by
    refine ⟨fun a b => ?_, by simp⟩
    by_cases e : a = b
    · subst e; simp
    · simp [Matrix.one_apply, e, Ne.symm e]
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.AnisoCocompact.exists_compact σ₀ hcm 1 hherm hform_one_ne_zero
  haveI := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ₀ (1 : Matrix (Fin n) (Fin n) E)
  have hcf : Continuous (fun x : ratU E n =>
      (⟨j x.1, (hj _).1 x.2⟩ : HFinIn (AF F₀) σ₀ (1 : Matrix (Fin n) (Fin n) E))) :=
    (j.continuous.comp continuous_subtype_val).subtype_mk _
  refine ⟨inferInstance, j.toHomeomorph.isClosedEmbedding.locallyCompactSpace,
    j.toHomeomorph.secondCountableTopology, j.toHomeomorph.isEmbedding.t2Space,
    .of_continuous_injective hcf (fun a b h => Subtype.ext (j.injective (congrArg Subtype.val h))),
    j.symm '' K, hK.image j.symm.continuous, fun g => ?_⟩
  obtain ⟨γ, hγ, k, hk, e⟩ := hKe (j g)
  refine ⟨j.symm γ⁻¹, (hj _).2 (by rw [j.apply_symm_apply]; exact inv_mem hγ), k, hk, ?_⟩
  apply j.injective
  rw [map_mul, j.apply_symm_apply, j.apply_symm_apply, e, inv_mul_cancel_left]

theorem cj_props {w : Pl E} (hw : ¬ IsSplitAt w) :
    (∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧
      ∀ x, Valued.v (cj w x) = Valued.v x := by
  have key : ∀ (v : Pl E) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (GlobalTheory.SplitPts.conjE E k)) →
      (∀ y, Valued.v (f y) = Valued.v y) →
      (∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧
        ∀ x, Valued.v (cj w x) = Valued.v x := by
    rintro v rfl f hf h hval
    have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, h⟩
    obtain ⟨hc, he⟩ := GlobalTheory.ConjAtPlace.cj_spec v hex
    have e : cj v = f := GlobalTheory.ConjAtPlace.ext_of_cont _ _ hc hf he h
    exact ⟨he, fun x => by rw [e]; exact hval x⟩
  exact key _ (GlobalTheory.BCT.GlobLev.conjSrc_eq_of_not_split hw) _ (conjLoc_spec (GlobalTheory.SplitPts.conjE E) _).1
    (conjLoc_spec (GlobalTheory.SplitPts.conjE E) _).2.1 (conjLoc_spec (GlobalTheory.SplitPts.conjE E) _).2.2

theorem surjective_of_cLoc (n : ℕ) (w : Pl E) (p : locU n w →* UL n w) (hp : ∀ x, (p x).1 = cLoc w x.1) :
    Function.Surjective p := by
  intro g
  by_cases hs : IsSplitAt w
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hs
    exact ⟨e.symm g.1, Subtype.ext (by rw [hp, ← he, e.apply_symm_apply])⟩
  · obtain ⟨h1, h2⟩ := cj_props hs
    obtain ⟨e, he⟩ := GlobalTheory.DefU.Inert.locU_equiv E n w (cj w) h1 h2
    have hg : g.1 ∈ UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      have h : UL n w = UJ (cj w) 1 := if_neg hs
      have key : ∀ y : GLw n w, y ∈ UL n w → y ∈ UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
        fun y hy => by rwa [h] at hy
      exact key g.1 g.2
    exact ⟨e.symm ⟨g.1, hg⟩, Subtype.ext (by rw [hp, ← he, e.apply_symm_apply])⟩

end Concrete

theorem compUnit : PositivityTheory.Rg.BcB.F.Eig.CompUnit := by
  rintro E _ _ _ n π hπ w σ ⟨p, hp, hirr, f, hf0, hfm, hf⟩
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := setup (E := E) n
  have hs := surjective_of_cLoc n w p hp
  letI : MeasurableSpace (UA E n) := borel _
  haveI : BorelSpace (UA E n) := ⟨rfl⟩
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    obtain ⟨-, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hirr
    have hW : ∀ g v, v ∈ LinearMap.ker f → σ.ρ g v ∈ LinearMap.ker f := fun g v hv => by
      obtain ⟨x, rfl⟩ := hs g
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hf, hv, map_zero]
    rcases h1 _ hW with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hf0
  exact (GlobalTheory.LGrp.isUnitarisable_iff _).1 (isUnitarisable_of_embedding (ratU E n) t6 σ.ρ p hs (locU n w).subtype f hinj
    (fun v => (hπ.aut _ (hfm v)).cont) (fun v => (hπ.aut _ (hfm v)).left) (fun x v y => by rw [hf]; rfl))

end GlobalTheory.CompanionTheory.CompUnitary
