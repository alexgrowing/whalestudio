import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Pointwise

namespace GlobalTheory.ConjTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem symm_alg (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (x : E) :
    c.symm (algebraMap E Ω x) = algebraMap E Ω (τ.symm x) := by
  rw [RingEquiv.symm_apply_eq, hτ, RingEquiv.apply_symm_apply]

def conjG (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) :
    G E Ω →* G E Ω where
  toFun g := AlgEquiv.ofRingEquiv (f := c.symm.trans (g.toRingEquiv.trans c)) (fun x => by
    simp only [RingEquiv.trans_apply, symm_alg c τ hτ, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, hτ, RingEquiv.apply_symm_apply])
  map_one' := by ext y; simp
  map_mul' g h := by ext y; simp

theorem conjG_apply (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (g : G E Ω) (y : Ω) : conjG c τ hτ g y = c (g (c.symm y)) := rfl

theorem conjG_apply_c (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (g : G E Ω) (y : Ω) : conjG c τ hτ g (c y) = c (g y) := by
  rw [conjG_apply, RingEquiv.symm_apply_apply]

theorem conjG_conjG_symm (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (g : G E Ω) : conjG c τ hτ (conjG c.symm τ.symm (symm_alg c τ hτ) g) = g := by
  ext y; simp [conjG_apply]

theorem conjG_continuous [Algebra.IsAlgebraic E Ω] (c : Ω ≃+* Ω) (τ : E ≃+* E)
    (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) : Continuous (conjG c τ hτ) := by
  classical
  apply continuous_of_continuousAt_one (conjG c τ hτ)
  rw [ContinuousAt, map_one]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨S, hS, hSU⟩ := hU
  let b := Module.finBasis E S
  let s : Finset Ω := Finset.univ.image (fun i => c.symm (b i : Ω))
  have hfin : FiniteDimensional E (IntermediateField.adjoin E (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral)
  show _ ∈ nhds (1 : G E Ω)
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨_, hfin, fun g hg => hSU ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
  intro x hx
  have hb : ∀ i, conjG c τ hτ g (b i : Ω) = b i := by
    intro i
    rw [conjG_apply, hg _ (IntermediateField.subset_adjoin _ _ (by simp [s])), RingEquiv.apply_symm_apply]
  have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ω) := by
    have := congrArg (fun z : S => (z : Ω)) (b.sum_repr ⟨x, hx⟩)
    simp only [AddSubmonoidClass.coe_finset_sum, IntermediateField.coe_smul] at this
    exact this.symm
  rw [hx', map_sum]
  simp [map_smul, hb]

theorem mem_Dec_iff' {A : ValuationSubring Ω} {σ : G E Ω} :
    σ ∈ Dec (F := E) A ↔ ∀ y, σ y ∈ A ↔ y ∈ A := by
  constructor
  · exact fun h y => apply_mem_iff_of_mem_Dec h y
  · intro h
    show σ • A = A
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h, mul_inv_apply]

theorem lt_one_transport {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') (y : Ω) :
    A.valuation y < 1 ↔ A'.valuation (c y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hc, ← hc, map_eq_zero_iff _ c.injective]

theorem conjG_mem_Ine {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω) (τ : E ≃+* E)
    (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {g : G E Ω}
    (hg : g ∈ Ine (F := E) A) : conjG c τ hτ g ∈ Ine (F := E) A' := by
  have hsurj : ∀ y', ∃ y, y' = c y := fun y' => ⟨c.symm y', (c.apply_symm_apply y').symm⟩
  refine ⟨?_, ?_⟩
  · have hD : g ∈ Dec (F := E) A := hg.1
    show conjG c τ hτ g ∈ Dec (F := E) A'
    rw [mem_Dec_iff'] at hD ⊢
    intro y'
    obtain ⟨y, rfl⟩ := hsurj y'
    rw [conjG_apply_c, ← hc, ← hc, hD]
  · intro y' hy'
    obtain ⟨y, rfl⟩ := hsurj y'
    rw [conjG_apply_c, ← map_sub, ← lt_one_transport c hc]
    rw [ValuationSubring.valuation_le_one_iff, ← hc, ← ValuationSubring.valuation_le_one_iff] at hy'
    exact hg.2 y hy'

theorem conjG_mem_wild {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω) (τ : E ≃+* E)
    (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {g : G E Ω}
    (hg : ∀ y : Ω, y ≠ 0 → A.valuation (g y / y - 1) < 1) :
    ∀ y : Ω, y ≠ 0 → A'.valuation (conjG c τ hτ g y / y - 1) < 1 := by
  intro y' hy'
  obtain ⟨y, rfl⟩ : ∃ y, y' = c y := ⟨c.symm y', (c.apply_symm_apply y').symm⟩
  have hy : y ≠ 0 := fun h => hy' (by rw [h, map_zero])
  rw [conjG_apply_c, ← map_div₀, ← map_one c, ← map_sub, ← lt_one_transport c hc]
  exact hg y hy

end GlobalTheory.ConjTransport

namespace GlobalTheory

open GlobalTheory.ConjTransport

theorem conjGen_transport_exists : ∀ (D : D7) (w w' : PlE D.host) (γ : GE D.nd), IsConjPl D.host w w' →
    TameGenAt (D.nd.plOm.1 w) γ → ∃ γ' : GE D.nd, IsConjGen D w w' γ γ' ∧ TameGenAt (D.nd.plOm.1 w') γ' := by
  intro D w w' γ hww hγ
  let τ : D.host.E ≃+* D.host.E := (D.host.conj : D.host.E ≃+* D.host.E)
  let c₀ : D.nd.Om ≃+* D.nd.Om := IsAlgClosure.equivOfEquiv D.nd.Om D.nd.Om τ
  have hc₀ : ∀ x, c₀ (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (τ x) :=
    IsAlgClosure.equivOfEquiv_algebraMap D.nd.Om D.nd.Om τ
  set A := D.nd.plOm.1 w with hAdef
  set A' := D.nd.plOm.1 w' with hA'def
  have hA : IsPlaceOver A w := D.nd.plOm.2 w
  have hA' : IsPlaceOver A' w' := D.nd.plOm.2 w'
  let B : ValuationSubring D.nd.Om := A.comap (c₀.symm : D.nd.Om →+* D.nd.Om)
  have hAB : ∀ y, y ∈ A ↔ c₀ y ∈ B := fun y => by
    show y ∈ A ↔ c₀.symm (c₀ y) ∈ A
    rw [RingEquiv.symm_apply_apply]
  have hB : IsPlaceOver B w' := by
    intro x
    let x'' : 𝓞 D.host.E := ⟨τ.symm x, (x.isIntegral_coe).map (τ.symm : D.host.E →+* D.host.E).toIntAlgHom⟩
    have h1 : algebraMap D.host.E D.nd.Om (x : D.host.E) = c₀ (algebraMap D.host.E D.nd.Om (x'' : D.host.E)) := by
      rw [hc₀]; congr 1
      show (x : D.host.E) = τ (τ.symm (x : D.host.E)); exact (τ.apply_symm_apply _).symm
    rw [h1, ← lt_one_transport c₀ hAB, hA x'']
    exact hww x'' x (by show (x : D.host.E) = τ (τ.symm (x : D.host.E)); exact (τ.apply_symm_apply _).symm)
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hB hA'
  let c : D.nd.Om ≃+* D.nd.Om := c₀.trans σ.toRingEquiv
  have hcE : ∀ x, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (τ x) := by
    intro x
    show σ (c₀ _) = _
    rw [hc₀, AlgEquiv.commutes]
  have hcA : ∀ y, y ∈ A ↔ c y ∈ A' := by
    intro y
    rw [hAB, ← hσ, ← ValuationSubring.smul_mem_pointwise_smul_iff (g := σ), AlgEquiv.smul_def]
    rfl
  have hcA' : ∀ y, y ∈ A' ↔ c.symm y ∈ A := by
    intro y
    rw [hcA, RingEquiv.apply_symm_apply]
  refine ⟨conjG c τ hcE γ, ⟨c, fun x => hcE x, hcA, fun y => conjG_apply_c c τ hcE γ y⟩, ?_⟩
  refine ⟨conjG_mem_Ine c τ hcE hcA hγ.1, ?_⟩
  intro h hh
  have h1 := hγ.2 (conjG_mem_Ine c.symm τ.symm (symm_alg c τ hcE) hcA' hh)
  rw [← conjG_conjG_symm c τ hcE h]
  refine closure_mono ?_ (image_closure_subset_closure_image (conjG_continuous c τ hcE) ⟨_, h1, rfl⟩)
  rw [← Subgroup.coe_map, MonoidHom.map_closure]
  refine SetLike.coe_subset_coe.mpr (Subgroup.closure_mono ?_)
  rintro _ ⟨g, hg, rfl⟩
  rcases hg with rfl | hg
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (conjG_mem_wild c τ hcE hcA hg)

end GlobalTheory
