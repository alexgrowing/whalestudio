import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import GroundTheory.LocalFields.MainTheorem
import GroundTheory.LocalFields.PrincipalUnitsRank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology

private theorem ag_lift {G C : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CommGroup C]
    [TopologicalSpace C] [T2Space C] (q : G →* C) (hq : Continuous q) :
    ∃ F : TopologicalAbelianization G →* C, Continuous F ∧ ∀ g : G, F g = q g := by
  have hle : (commutator G).topologicalClosure ≤ q.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker q)
      (isClosed_singleton.preimage hq)
  refine ⟨QuotientGroup.lift _ q hle, ?_, fun g => rfl⟩
  exact continuous_coinduced_dom.2 hq

private theorem ag_map {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] (f : G →* G') (hf : Continuous f) :
    ∃ F : TopologicalAbelianization G →* TopologicalAbelianization G', Continuous F ∧ ∀ g : G, F g = (f g : G') := by
  set M := (commutator G').topologicalClosure
  have hker : ((QuotientGroup.mk' M).comp f).ker = M.comap f := by
    ext x
    simp
  have hle : (commutator G).topologicalClosure ≤ M.comap f := by
    apply Subgroup.topologicalClosure_minimal
    · rw [← hker]
      exact Abelianization.commutator_subset_ker _
    · exact (Subgroup.isClosed_topologicalClosure _).preimage hf
  refine ⟨QuotientGroup.map _ M f hle, ?_, fun g => rfl⟩
  exact continuous_coinduced_dom.2 (continuous_quotient_mk'.comp hf)

open GroundTheory.LocalField ValuativeRel GroundTheory.LocalField.Abstract in
private theorem ag_field (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (ε : G ≃* (Ω ≃ₐ[K] Ω))
    (hε : Continuous ε) (hε' : Continuous ε.symm) :
    ∃ (θ : Kˣ →* TopologicalAbelianization G) (D : TopologicalAbelianization G →* Multiplicative ProfiniteInteger),
      Continuous θ ∧ Function.Injective θ ∧ DenseRange θ ∧
      (∀ H : Subgroup Kˣ, IsOpen (H : Set Kˣ) → H.FiniteIndex →
        ∃ V : Subgroup (TopologicalAbelianization G), IsOpen (V : Set (TopologicalAbelianization G)) ∧ V.comap θ = H) ∧
      Continuous D ∧ (∀ y : Kˣ, D (θ y) = Multiplicative.ofAdd ((ord (y : K) : ℤ) : ProfiniteInteger)) ∧
      ∀ g : G, D (QuotientGroup.mk' _ g) = unramifiedDegree K Ω (ε g) := by
  obtain ⟨F, hF, hFe⟩ := ag_map (ε : G →* (Ω ≃ₐ[K] Ω)) hε
  obtain ⟨F', hF', hF'e⟩ := ag_map (ε.symm : (Ω ≃ₐ[K] Ω) →* G) hε'
  have hFF' : ∀ b, F (F' b) = b := by
    intro b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hF'e, hFe]
    simp
  have hF'F : ∀ a, F' (F a) = a := by
    intro a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    rw [hFe, hF'e]
    simp
  obtain ⟨U, hU, hUe⟩ := ag_lift (unramifiedDegree K Ω) continuous_unramifiedDegree
  set L := localReciprocityLimit K Ω
  have hLart : ∀ x, localArtinMap K Ω x = topologicalAbelianizationEquiv K Ω (L x) :=
    fun x => localArtinMap_apply x
  have hLc : Continuous L := by
    have h : (L : Kˣ → _) = (topologicalAbelianizationEquiv K Ω).symm ∘ localArtinMap K Ω := by
      funext x
      simp [hLart]
    rw [h]
    exact (topologicalAbelianizationEquiv K Ω).symm.continuous.comp continuous_localArtinMap
  have hLi : Function.Injective L := by
    intro x y hxy
    apply injective_localArtinMap (K := K) (Ω := Ω)
    rw [hLart, hLart, hxy]
  have hU' : ∀ x : Kˣ, U (L x) = Multiplicative.ofAdd ((ord (x : K) : ℤ) : ProfiniteInteger) := by
    intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (L x)
    rw [← hg, hUe]
    exact unramifiedDegree_of_mk_eq_localReciprocityLimit hg
  refine ⟨F'.comp L, U.comp F, hF'.comp hLc, ?_, ?_, ?_, hU.comp hF, ?_, ?_⟩
  · intro x y hxy
    apply hLi
    have := congrArg F hxy
    simpa [hFF'] using this
  · exact (Function.Surjective.denseRange (fun a => ⟨F a, hF'F a⟩)).comp
      (denseRange_localReciprocityLimit (K := K) (Ω := Ω)) hF'
  · intro H hHo hHf
    let H' : openFiniteIndex Kˣ := ⟨H, hHo, hHf⟩
    let ψ := ((artinCoord K Ω H').comp
      (topologicalAbelianizationEquiv K Ω).toMulEquiv.toMonoidHom).comp F
    have hψ : Continuous ψ :=
      (continuous_artinCoord H').comp ((topologicalAbelianizationEquiv K Ω).continuous.comp hF)
    haveI := openCompletion.discreteTopology_quotient H'
    refine ⟨ψ.ker, ?_, ?_⟩
    · exact (isOpen_discrete ({1} : Set (Kˣ ⧸ (H : Subgroup Kˣ)))).preimage hψ
    · ext y
      simp only [Subgroup.mem_comap, MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, hFF']
      change artinCoord K Ω H' (topologicalAbelianizationEquiv K Ω (L y)) = 1 ↔ y ∈ H
      rw [← hLart, artinCoord_localArtinMap]
      exact QuotientGroup.eq_one_iff y
  · intro y
    simp [hFF', hU']
  · intro g
    simp [hFe, hUe]

open GroundTheory.LocalField ValuativeRel IsLocalRing in
private theorem ag_char (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Algebra ℚ_[l] k] [ValuativeExtension ℚ_[l] k] : CharP 𝓀[k] l := by
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
  have hnu : ¬ IsUnit ((l : 𝒪[k])) := by
    rintro ⟨u, hu⟩
    have h1 : ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) * (l : 𝒪[k]) = 1 := by
      rw [← hu]
      simp
    have h2 : ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k)) = algebraMap ℚ_[l] k ((l : ℚ_[l])⁻¹) := by
      have := congrArg (fun x : 𝒪[k] => (x : k)) h1
      simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [map_inv₀, map_natCast]
      exact eq_inv_of_mul_eq_one_left this
    have h3 : algebraMap ℚ_[l] k ((l : ℚ_[l])⁻¹) ∈ (ValuativeRel.valuation k).integer := by
      rw [← h2]
      exact (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])).2
    rw [algebraMap_mem_integer_iff, PadicRank.mem_integer_padic_iff] at h3
    rw [norm_inv, Padic.norm_p, inv_inv] at h3
    have : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    linarith
  have hmem : (l : 𝒪[k]) ∈ maximalIdeal 𝒪[k] := (mem_maximalIdeal _).2 hnu
  rw [← map_natCast (residue 𝒪[k]) l]
  exact (residue_eq_zero_iff _).2 hmem

theorem UpperTheory.local_class_field_theory_of_open_embedding :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ), ∃ (K : Type) (_ : Field K) (_ : ValuativeRel K) (_ : TopologicalSpace K) (_ : IsNonarchimedeanLocalField K) (_ : Algebra ℚ_[l] K) (_ : ValuativeExtension ℚ_[l] K) (_ : FiniteDimensional ℚ_[l] K), φ.range.index = Module.finrank ℚ_[l] K ∧ ∃ (θ : Kˣ →* TopologicalAbelianization G) (D : TopologicalAbelianization G →* Multiplicative GroundTheory.LocalField.Abstract.ProfiniteInteger), Continuous θ ∧ Function.Injective θ ∧ DenseRange θ ∧ (∀ H : Subgroup Kˣ, IsOpen (H : Set Kˣ) → H.FiniteIndex → ∃ V : Subgroup (TopologicalAbelianization G), IsOpen (V : Set (TopologicalAbelianization G)) ∧ V.comap θ = H) ∧ Continuous D ∧ (∀ y : Kˣ, D (θ y) = Multiplicative.ofAdd ((GroundTheory.LocalField.ord (y : K) : ℤ) : GroundTheory.LocalField.Abstract.ProfiniteInteger)) ∧ ∀ g : G, φ g ∈ Iq l ↔ D (QuotientGroup.mk' _ g) = 1 := by
  intro l _ G _ _ _ φ hφ
  obtain ⟨K, e, he, he', hcomp, -, hidx, -⟩ := openField φ hφ
  haveI hfin : FiniteDimensional ℚ_[l] K.1 := K.2
  obtain ⟨vr, tp, hloc, hext⟩ :=
    GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] K.1
  letI := vr
  letI := tp
  haveI := hloc
  haveI := hext
  haveI : Algebra.IsAlgebraic K.1 (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) K.1
  haveI : IsAlgClosure K.1 (Om l) := ⟨inferInstance, inferInstance⟩
  haveI : IsSepClosure K.1 (Om l) := inferInstance
  obtain ⟨hc1, hc2⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let ε : G ≃* Gal(Om l/K.1) := e.trans K.1.fixingSubgroupEquiv
  have hε : Continuous ε := hc1.comp he
  have hε' : Continuous ε.symm := he'.comp hc2
  obtain ⟨θ, D, h1, h2, h3, h4, h5, h6, hD⟩ := ag_field K.1 (Om l) ε hε hε'
  refine ⟨K.1, inferInstance, vr, tp, hloc, inferInstance, hext, hfin, hidx, θ, D,
    h1, h2, h3, h4, h5, h6, ?_⟩
  intro g
  have hεg : ∀ x, (ε g) x = φ g x := by
    intro x
    rw [← hcomp]
    rfl
  haveI := ag_char l K.1
  rw [hD g, GroundTheory.LocalField.unramifiedDegree_eq_one_iff]
  simp only [Iq, MaximalUnramifiedExtension, GroundTheory.LocalField.mem_fixingSubgroup_adjoin_iff,
    GroundTheory.LocalField.mem_unramifiedRoots_iff, hεg]
  constructor
  · rintro h ξ ⟨m, hm, hξ⟩
    apply h
    refine ⟨m, ?_, ?_, hξ⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp at hm
      · exact hpos
    · intro hdvd
      exact hm ((CharP.cast_eq_zero_iff _ l m).2 hdvd)
  · rintro h ξ ⟨m, -, hml, hξ⟩
    apply h
    exact ⟨m, fun h0 => hml ((CharP.cast_eq_zero_iff _ l m).1 h0), hξ⟩
