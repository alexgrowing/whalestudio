import Formalism.AdmissibleDesigns.NonemptyPl
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteExtensionTopology.AddPreservesExpCongruence
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteExtensionTopology.ExpCongruenceExtendsToSum
import Formalism.AdicCompletionExports.AdicCompleteRingEquiv.IsAdicCompleteOfRingEquiv
import Development.AutomorphicArithmetic.CyclotomicBounds.FactorizationConductorLeLocalLevel

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.K.Topo

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions Formalism.MainNotions.N
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.NG (uElt)

section Gen

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def unif : O := Classical.choose (IsDiscreteValuationRing.exists_irreducible O)

theorem unif_irr : Irreducible (unif O) := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible O)

@[reducible] def fracTopology : TopologicalSpace (FractionRing O) :=
  (PI.UnitaryGroupMassFormula.FinExtTop.fracB_basis (unif_irr O)).topology

theorem fracTop_ring : @IsTopologicalRing (FractionRing O) (fracTopology O) _ :=
  (PI.UnitaryGroupMassFormula.FinExtTop.fracB_basis (unif_irr O)).toRing_subgroups_basis.toRingFilterBasis.isTopologicalRing

theorem fracTop_addGroup : @IsTopologicalAddGroup (FractionRing O) (fracTopology O) _ := by
  letI := fracTopology O
  haveI := fracTop_ring O
  infer_instance

section TopO

variable [TopologicalSpace O]

theorem algebraMap_openEmb (hA : IsAdic (IsLocalRing.maximalIdeal O)) :
    @Topology.IsOpenEmbedding O (FractionRing O) _ (fracTopology O) (algebraMap O (FractionRing O)) := by
  letI := fracTopology O
  have hm : ∀ n : ℕ, ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) = {x | unif O ^ n ∣ x} := by
    intro n
    ext x
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer (unif O)).1 (unif_irr O), Ideal.span_singleton_pow,
      SetLike.mem_coe, Ideal.mem_span_singleton]
    rfl
  have hB := PI.UnitaryGroupMassFormula.FinExtTop.fracB_basis (unif_irr O)
  have hR := hB.toRing_subgroups_basis
  set f := algebraMap O (FractionRing O) with hf
  have hnK := hR.hasBasis_nhds
  have hnO := hA.hasBasis_nhds
  have hcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    refine ((hnO x).tendsto_iff (hnK (f x))).2 fun i _ => ⟨i, trivial, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hm] at hz
    show f (x + z) - f x ∈ PI.UnitaryGroupMassFormula.FinExtTop.fracB (unif O) i
    rw [map_add, add_sub_cancel_left]
    exact PI.UnitaryGroupMassFormula.FinExtTop.algebraMap_mem_fracB.2 hz
  have hopen : IsOpenMap f := by
    refine IsOpenMap.of_nhds_le fun x => ?_
    refine Filter.le_map fun s hs => ?_
    obtain ⟨n, -, hn⟩ := (hnO x).mem_iff.1 hs
    refine Filter.mem_of_superset ((hnK (f x)).mem_of_mem (i := n) trivial) ?_
    intro b hb
    obtain ⟨c, hc⟩ := PI.UnitaryGroupMassFormula.FinExtTop.mem_fracB.1 (show b - f x ∈ PI.UnitaryGroupMassFormula.FinExtTop.fracB (unif O) n from hb)
    refine ⟨x + c * unif O ^ n, hn ⟨c * unif O ^ n, ?_, rfl⟩, ?_⟩
    · rw [hm]
      exact Dvd.intro_left c rfl
    · rw [map_add, ← hc, add_sub_cancel]
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont
    (IsFractionRing.injective O (FractionRing O)) hopen

theorem fracTop_smul (hA : IsAdic (IsLocalRing.maximalIdeal O)) :
    @ContinuousSMul O (FractionRing O) _ _ (fracTopology O) := by
  letI := fracTopology O
  haveI := fracTop_ring O
  exact continuousSMul_of_algebraMap O (FractionRing O) (algebraMap_openEmb O hA).continuous

theorem fracTop_open (hA : IsAdic (IsLocalRing.maximalIdeal O)) : @FracTop O _ _ (fracTopology O) :=
  @FracTop.mk O _ _ (fracTopology O) (algebraMap_openEmb O hA)

variable {X' d : Type} [Fintype d] [DecidableEq d]

@[reducible] def rTopology (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) : TopologicalSpace R' :=
  moduleTopology O R'

theorem rTop_isModuleTopology (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) :
    letI := rTopology O R'; IsModuleTopology O R' :=
  letI := rTopology O R'; ⟨rfl⟩

theorem rTop_ring (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsTopologicalRing O]
    (hfin : Module.Finite O R') : @IsTopologicalRing R' (rTopology O R') _ := by
  letI := rTopology O R'
  haveI := rTop_isModuleTopology O R'
  exact IsModuleTopology.isTopologicalRing O R'

theorem rTop_addGroup (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsTopologicalRing O]
    (hfin : Module.Finite O R') : @IsTopologicalAddGroup R' (rTopology O R') _ := by
  letI := rTopology O R'
  haveI := rTop_ring O R' hfin
  infer_instance

theorem rTop_mul (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsTopologicalRing O]
    (hfin : Module.Finite O R') : @ContinuousMul R' (rTopology O R') _ := by
  letI := rTopology O R'
  haveI := rTop_ring O R' hfin
  infer_instance

theorem rTop_smul (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsTopologicalRing O] :
    letI := rTopology O R'; ContinuousSMul O R' := by
  letI := rTopology O R'
  haveI := rTop_isModuleTopology O R'
  exact IsModuleTopology.toContinuousSMul O R'

theorem rTop_constSMul (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsTopologicalRing O] :
    letI := rTopology O R'; ContinuousConstSMul O R' := by
  letI := rTopology O R'
  haveI := rTop_smul O R'
  infer_instance

theorem rTop_fgTop (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsTopologicalRing O] [T2Space O]
    (hfin : Module.Finite O R') : letI := rTopology O R'; IsFGTop O R' := by
  letI := rTopology O R'
  haveI := rTop_isModuleTopology O R'
  haveI := rTop_ring O R' hfin
  haveI := rTop_smul O R'
  have _ := PI.UnitaryGroupMassFormula.FinExtTop.torsionFree_pi_matrix O X' d
  have _ : Module.IsTorsionFree O R' := inferInstance
  have _ : Module.Free O R' := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis O R'
  have hc : Continuous b.equivFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  have _ : T2Space R' := T2Space.of_injective_continuous b.equivFun.injective hc
  exact ⟨hfin, inferInstance, inferInstance⟩

end TopO

theorem finite_of_int {X' d : Type} [Fintype d] [DecidableEq d] [Finite X'] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (hint : ∀ a ∈ R', ∀ x' i j, ∃ c : O, algebraMap O (FractionRing O) c = a x' i j) : Module.Finite O R' := by
  let L : (X' → d → d → O) →ₗ[O] (X' → Matrix d d (FractionRing O)) :=
    { toFun := fun F x' => Matrix.of fun i j => algebraMap O (FractionRing O) (F x' i j)
      map_add' := fun F F' => by funext x'; ext i j; simp
      map_smul' := fun c F => by funext x'; ext i j; simp [Algebra.smul_def] }
  have hle : Subalgebra.toSubmodule R' ≤ LinearMap.range L := by
    intro a ha
    choose F hF using hint a ha
    exact ⟨F, by funext x'; ext i j; exact hF x' i j⟩
  haveI : IsNoetherian O (LinearMap.range L) := inferInstance
  haveI h1 : IsNoetherian O (Subalgebra.toSubmodule R') := isNoetherian_of_le hle
  haveI h2 : IsNoetherian O R' := h1
  infer_instance

end Gen

section Ring

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X d G : Type} [Finite X]
  [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)} {T : Subalgebra O (X → O)}
  {r₀ : G →* (X → Matrix d d O)} {π : X} {χ₁ ε : G →* Oˣ} {g₀ : G} {eB e₁ s : X → Matrix d d O}
  {Dd : RingData O X d G t bl}

theorem finite_X' (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s Dd) : Finite Dd.X' := by
  obtain ⟨h1, h2, -⟩ := hD
  let ι := algebraMap O (FractionRing O)
  let P : X → Polynomial (FractionRing O) := fun x => Formalism.RepresentationBoundsCohomology.ringDataObjects.blockPoly ((eB x).map ι)
    ((eB x * r₀ g₀ x * eB x + s x).map ι)
  let S : Set O := {a | ∃ x, ι a ∈ (P x).roots}
  have hS : S.Finite := by
    have : S ⊆ ⋃ x, ι ⁻¹' ((P x).roots.toFinset : Set (FractionRing O)) := by
      rintro a ⟨x, hx⟩
      exact Set.mem_iUnion.2 ⟨x, by simpa using hx⟩
    refine Set.Finite.subset (Set.finite_iUnion fun x => ?_) this
    exact Set.Finite.preimage (IsFractionRing.injective O (FractionRing O)).injOn (Finset.finite_toSet _)
  haveI : Finite S := hS.to_subtype
  have hmem : ∀ (y : Dd.X') (i : Fin t), ((Dd.rr i : Dd.X' → O) y) ∈ S := by
    intro y i
    refine ⟨Dd.p y, ?_⟩
    have hy : P (Dd.p y) = ∏ j ∈ Finset.range t, (Polynomial.X - Polynomial.C (ι ((Dd.rr j : Dd.X' → O) y))) := h1 y
    rw [Polynomial.mem_roots', hy]
    refine ⟨(Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _).ne_zero, ?_⟩
    rw [Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_range.2 i.2) (by simp)
  let f : Dd.X' → X × (Fin t → S) := fun y => (Dd.p y, fun i => ⟨(Dd.rr i : Dd.X' → O) y, hmem y i⟩)
  refine Finite.of_injective f fun y y' h => ?_
  have hp : Dd.p y = Dd.p y' := congrArg (fun z => z.1) h
  have hr : ∀ i : Fin t, (Dd.rr i : Dd.X' → O) y = (Dd.rr i : Dd.X' → O) y' :=
    fun i => congrArg (fun z => ((z.2 i : S) : O)) h
  obtain ⟨z, -, hz⟩ := h2 (Dd.p y) (fun i => (Dd.rr i : Dd.X' → O) y) (h1 y)
  have e1 := hz y ⟨rfl, fun i _ => rfl⟩
  have e2 := hz y' ⟨hp.symm, fun i hi => (hr ⟨i, hi⟩).symm⟩
  rw [e1, e2]

theorem int_R' (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s Dd) :
    ∀ a ∈ Dd.R', ∀ x' i j, ∃ c : O, algebraMap O (FractionRing O) c = a x' i j := by
  obtain ⟨-, -, -, -, -, -, h7, h8, -⟩ := hD
  intro a ha x' i j
  obtain ⟨S, c, -, rfl⟩ := (h8 a).1 ha
  refine ⟨∑ g ∈ S, c g x' * r₀ g (Dd.p x') i j, ?_⟩
  simp only [Finset.sum_apply, Matrix.sum_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  have := h7 g x'
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply] at *
  rw [Matrix.smul_apply, smul_eq_mul]
  congr 1
  show _ = ((Dd.r g : Dd.R') : Dd.X' → Matrix d d (FractionRing O)) x' i j
  rw [this, Matrix.map_apply]

theorem finite_R' (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s Dd) : Module.Finite O Dd.R' := by
  haveI := finite_X' hD
  exact finite_of_int O Dd.R' (int_R' hD)

end Ring

section Entries

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]

theorem t2Space_fractionRing_of_padicCoeff (ℓ : ℕ) (hO : PadicCoeff ℓ O) (hF : FracTop O) : T2Space (FractionRing O) := by
  have := hO.t2
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  by_cases hxr : x ∈ Set.range (algebraMap O (FractionRing O))
  · obtain ⟨c, rfl⟩ := hxr
    have hc : c ≠ 0 := by rintro rfl; exact hx (map_zero _)
    refine ⟨algebraMap O (FractionRing O) '' {c}ᶜ, ?_, ?_⟩
    · have hopen : IsOpen (algebraMap O (FractionRing O) '' {c}ᶜ) :=
        hF.emb.isOpenMap _ isOpen_compl_singleton
      exact hopen.mem_nhds ⟨0, fun h => hc (h.symm), map_zero _⟩
    · rintro ⟨c', hc', he⟩
      exact hc' (hF.emb.injective he)
  · exact ⟨Set.range (algebraMap O (FractionRing O)), hF.emb.isOpen_range.mem_nhds ⟨0, map_zero _⟩, hxr⟩

variable {X' d : Type} [Fintype d] [DecidableEq d]

theorem continuous_of_entries (ℓ : ℕ) (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [TopologicalSpace R'] [IsTopologicalAddGroup R'] (hO : PadicCoeff ℓ O) (hF : FracTop O)
    (hR : IsFGTop O R') {G : Type} [TopologicalSpace G] (u : G → R')
    (hu : ∀ x' a b, Continuous fun g => ((u g : R') : X' → Matrix d d (FractionRing O)) x' a b) :
    Continuous u := by
  have := hO.compact
  have := hR.t2
  have := hR.csmul
  have := hR.fg
  have := t2Space_fractionRing_of_padicCoeff ℓ hO hF
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O R'
  have hfc : Continuous f := LinearMap.continuous_on_pi f
  have hq : Topology.IsQuotientMap f := Topology.IsQuotientMap.of_surjective_continuous hf hfc
  haveI : CompactSpace R' := Function.Surjective.compactSpace hfc hf
  have hval : Continuous (fun a : R' => (a : X' → Matrix d d (FractionRing O))) := by
    rw [hq.continuous_iff]
    exact LinearMap.continuous_on_pi (R'.val.toLinearMap.comp f)
  have hemb := (hval.isClosedEmbedding Subtype.val_injective).isEmbedding
  rw [hemb.continuous_iff]
  refine continuous_pi fun x' => ?_
  exact continuous_pi fun a => continuous_pi fun b => hu x' a b

end Entries

theorem continuous_of_isLocalHom {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (φ : A →+* B)
    [IsLocalHom φ] : Continuous φ := by
  refine continuous_of_continuousAt_zero φ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := (isAdic_iff.1 hB).2 s hs
  have hopen := (isAdic_iff.1 hA).1 n
  rw [Filter.mem_map]
  filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with x hx
  apply hn
  have hle : (IsLocalRing.maximalIdeal A).map φ ≤ IsLocalRing.maximalIdeal B :=
    Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit φ a ha
  have h1 : φ x ∈ ((IsLocalRing.maximalIdeal A) ^ n).map φ := Ideal.mem_map_of_mem φ hx
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hle n h1

section Rec

open Formalism.RepresentationBoundsCohomology.FIN (IsCycG)

variable {D : D7} (i : D.nd.Loc)

theorem l_mem_max : ((D.nd.l i : ℕ) : D.nd.O i) ∈ IsLocalRing.maximalIdeal (D.nd.O i) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have h2 := Formalism.MainNotions.SumRepresentations.norm_iotaOQ_unit D.nd D.naut i u
  have h3 := Formalism.MainNotions.SumRepresentations.norm_iotaOQ_l D.nd D.naut i
  rw [hu] at h2
  rw [h2] at h3
  exact lt_irrefl _ h3

theorem l_ne_zero : ((D.nd.l i : ℕ) : D.nd.O i) ≠ 0 :=
  Formalism.MainNotions.SumRepresentations.natCast_ne_zero_O D.nd i (D.nd.l i) (D.nd.lPrime i).out.ne_zero

theorem isLocalHom_alg : IsLocalHom (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
  refine ⟨fun z hz => ?_⟩
  by_contra hn
  have h1 : z ∈ IsLocalRing.maximalIdeal ℤ_[D.nd.l i] := hn
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
  obtain ⟨y, rfl⟩ := h1
  rw [map_mul, map_natCast] at hz
  exact (IsLocalRing.mem_maximalIdeal _).1 (l_mem_max i) (isUnit_of_mul_isUnit_left hz)

theorem continuous_alg : Continuous (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
  haveI := isLocalHom_alg i
  exact continuous_of_isLocalHom (ReciprocityTheory.ChartRestriction.T2.padicCoeff_padicInt (p := D.nd.l i)).adic (D.nd.O_adic i) _

theorem compact_O : CompactSpace (D.nd.O i) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ_[D.nd.l i] (D.nd.O i)
  have hc : Continuous f := by
    have : (f : (Fin n → ℤ_[D.nd.l i]) → D.nd.O i) = fun v =>
        ∑ k, algebraMap ℤ_[D.nd.l i] (D.nd.O i) (v k) * f (fun j => if k = j then 1 else 0) := by
      funext v
      rw [LinearMap.pi_apply_eq_sum_univ f v]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def]
    rw [this]
    exact continuous_finset_sum _ fun k _ =>
      ((continuous_alg i).comp (continuous_apply k)).mul continuous_const
  exact hf.compactSpace hc

theorem t2Space_nd_O : T2Space (D.nd.O i) := by
  have hopen : ∀ n : ℕ, IsOpen ((IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) : Set (D.nd.O i)) :=
    (isAdic_iff.1 (D.nd.O_adic i)).1
  have hclosed : ∀ n : ℕ, IsClosed ((IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) : Set (D.nd.O i)) :=
    fun n => AddSubgroup.isClosed_of_isOpen (Submodule.toAddSubgroup (IsLocalRing.maximalIdeal (D.nd.O i) ^ n)) (hopen n)
  have h0 : ({0} : Set (D.nd.O i)) =
      ⋂ n : ℕ, ((IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) : Set (D.nd.O i)) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_iInter, SetLike.mem_coe]
    constructor
    · rintro rfl n
      exact Ideal.zero_mem _
    · intro h
      have h1 : x ∈ (⨅ n : ℕ, IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) := by
        rw [Ideal.mem_iInf]; exact h
      rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top] at h1
      exact h1
  have : IsClosed ({0} : Set (D.nd.O i)) := by
    rw [h0]; exact isClosed_iInter hclosed
  haveI : T1Space (D.nd.O i) := IsTopologicalAddGroup.t1Space _ this
  infer_instance

theorem padicCoeff_O : PadicCoeff (D.nd.l i) (D.nd.O i) where
  ring := D.nd.trO i
  compact := compact_O i
  t2 := t2Space_nd_O i
  adic := D.nd.O_adic i
  p_mem := l_mem_max i
  p_ne := l_ne_zero i

theorem fracTop_O : letI := fracTopology (D.nd.O i); FracTop (D.nd.O i) :=
  fracTop_open (D.nd.O i) (D.nd.O_adic i)

theorem fracTop_addGroup_O : letI := fracTopology (D.nd.O i); IsTopologicalAddGroup (FractionRing (D.nd.O i)) :=
  fracTop_addGroup (D.nd.O i)

theorem fracTop_smul_O : letI := fracTopology (D.nd.O i); ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i)) :=
  fracTop_smul (D.nd.O i) (D.nd.O_adic i)

theorem isCyc_eps : IsCycG (D.nd.l i) (epsU D.nd i) :=
  Formalism.AdicCompletionExports.isCycG_cycZ (D.nd.l i) D.host.E D.nd.Om (D.nd.O i) (algebraMap ℤ_[D.nd.l i] (D.nd.O i))

theorem av_over : ∀ v, IsPlaceOver (Formalism.MainNotions.N.K.Av (D := D) v) v := fun v => D.nd.plOm.2 v

theorem l_or_noReal : D.nd.l i ≠ 2 ∨ InfinitePlace.nrRealPlaces D.host.E = 0 := by
  have := D.host.isCMField_hostE
  exact Or.inr (NumberField.nrRealPlaces_eq_zero_iff.mpr inferInstance)

theorem one_le_localLevel : 1 ≤ D.nd.s0 i := by
  exact UpperTheory.KStar.S0.one_le_localLevel D.nd i

theorem restNLevelExponent_of_two : D.nd.l i = 2 → 2 ≤ D.nd.s0 i := by
  exact UpperTheory.KStar.S0.two_le_localLevel_of_eq_two D.nd i

def yU (u : ℤ_[D.nd.l i]ˣ) : (D.nd.O i)ˣ := Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom u

variable (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)

theorem rows_over : ∀ w ∈ Formalism.MainNotions.N.K.rowsN i dc,
    (Formalism.MainNotions.N.K.Aw i dc w).valuation ((D.nd.l i : ℕ) : D.nd.Om) < 1 ∧
      IsPlaceOver (Formalism.MainNotions.N.K.Aw i dc w) (Formalism.MainNotions.N.K.plOf i dc w) := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
  have hmemS : v ∈ Formalism.MainNotions.N.K.plSet i dc := Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hpl := Formalism.MainNotions.N.K.plOf_idx i dc hmemS
  have hAw : Formalism.MainNotions.N.K.Aw i dc (Formalism.MainNotions.N.K.idx i dc v) = D.nd.plOm.1 v := by
    unfold Formalism.MainNotions.N.K.Aw; rw [hpl]
  rw [hAw, hpl]
  refine ⟨?_, D.nd.plOm.2 v⟩
  have hmem : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := (dc.cover v).1 (Or.inl hv)
  have h := (D.nd.plOm.2 v ((D.nd.l i : ℕ) : 𝓞 D.host.E)).2 hmem
  simpa using h

end Rec

section RecRing

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem finite_RD (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    Module.Finite (D.nd.O i) Dd.R' :=
  finite_R' hD

theorem rTop_addGroup_RD (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    letI := rTopology (D.nd.O i) Dd.R'; IsTopologicalAddGroup Dd.R' :=
  rTop_addGroup (D.nd.O i) Dd.R' (finite_R' hD)

theorem rTop_constSMul_RD : letI := rTopology (D.nd.O i) Dd.R'; ContinuousConstSMul (D.nd.O i) Dd.R' :=
  rTop_constSMul (D.nd.O i) Dd.R'

theorem rTop_mul_RD (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    letI := rTopology (D.nd.O i) Dd.R'; ContinuousMul Dd.R' :=
  rTop_mul (D.nd.O i) Dd.R' (finite_R' hD)

theorem fgTop_RD (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    letI := rTopology (D.nd.O i) Dd.R'; IsFGTop (D.nd.O i) Dd.R' := by
  haveI := t2Space_nd_O i
  exact rTop_fgTop (D.nd.O i) Dd.R' (finite_R' hD)

theorem uElt_cont (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) :
    letI := fracTopology (D.nd.O i); letI := rTopology (D.nd.O i) Dd.R';
    Continuous fun g : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) => uElt Dd.r Dd.χ g := by
  letI := fracTopology (D.nd.O i)
  letI := rTopology (D.nd.O i) Dd.R'
  haveI := fracTop_addGroup (D.nd.O i)
  haveI := fracTop_smul (D.nd.O i) (D.nd.O_adic i)
  haveI := rTop_addGroup (D.nd.O i) Dd.R' (finite_R' hD)
  have hι : Continuous (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) :=
    (algebraMap_openEmb (D.nd.O i) (D.nd.O_adic i)).continuous
  refine continuous_of_entries (D.nd.l i) Dd.R' (padicCoeff_O i) (fracTop_O i) (fgTop_RD i r π g0 eB e₁ s Dd hD) _ ?_
  intro x' a b
  have h7 := hD.2.2.2.2.2.2.1
  have h9 := hD.2.2.2.2.2.2.2.2.1
  have h12 := hD.2.2.2.2.2.2.2.2.2.2.2.1
  have key : ∀ g : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om),
      ((uElt Dd.r Dd.χ g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' a b =
        algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          (((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * Formalism.MainNotions.N.rO D.nd i r (Dd.p x') g a b) := by
    intro g
    simp only [uElt]
    rw [h9, h7, ← map_inv, h12]
    simp [RepresentationBoundsCohomology.repX_apply, Matrix.map_apply, smul_eq_mul, map_mul]
  simp_rw [key]
  refine hι.comp (Continuous.mul ?_ ?_)
  · exact (D.nd.chi_cont i 1).comp continuous_inv
  · exact (hc (Dd.p x')).matrix_elem a b

end RecRing

end Formalism.MainNotions.N.K.Topo

end
