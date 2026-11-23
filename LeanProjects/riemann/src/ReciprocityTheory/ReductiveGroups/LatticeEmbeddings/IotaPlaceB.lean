import Mathlib

noncomputable section
open Cardinal Filter Topology

namespace ReciprocityTheory.ChartRestriction.T1

theorem lat_mk_le_of_denseRange {D X : Type} [TopologicalSpace X] [FirstCountableTopology X] [T2Space X]
    (f : D → X) (hf : DenseRange f) : #X ≤ #D ^ ℵ₀ := by
  classical
  have hseq : ∀ x : X, ∃ u : ℕ → D, Tendsto (f ∘ u) atTop (𝓝 x) := by
    intro x
    have hx : x ∈ closure (Set.range f) := by rw [hf.closure_range]; exact Set.mem_univ x
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 hx
    choose u hu using hv
    refine ⟨u, ?_⟩
    have hfu : f ∘ u = v := funext hu
    rw [hfu]
    exact hlim
  choose g hg using hseq

  have hinj : Function.Injective g := by
    intro x y hxy
    have h' : Tendsto (f ∘ g x) atTop (𝓝 y) := by rw [hxy]; exact hg y
    exact tendsto_nhds_unique (hg x) h'
  calc Cardinal.mk X ≤ Cardinal.mk (ℕ → D) := Cardinal.mk_le_of_injective hinj
    _ = Cardinal.mk D ^ ℵ₀ := by rw [← Cardinal.mk_nat, Cardinal.power_def]

theorem lat_mk_Cp (p : ℕ) [Fact p.Prime] : #ℂ_[p] = 𝔠 := by
  apply le_antisymm
  · have h1 : Cardinal.mk ℚ_[p] ≤ 𝔠 := by
      calc Cardinal.mk ℚ_[p] ≤ Cardinal.mk ℚ ^ ℵ₀ :=
            lat_mk_le_of_denseRange ((↑) : ℚ → ℚ_[p]) (Padic.denseRange_ratCast p)
        _ = 𝔠 := by rw [Cardinal.mkRat, Cardinal.aleph0_power_aleph0]
    have h2 : Cardinal.mk (PadicAlgCl p) ≤ 𝔠 :=
      (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans
        (max_le h1 Cardinal.aleph0_le_continuum)
    calc Cardinal.mk ℂ_[p] ≤ Cardinal.mk (PadicAlgCl p) ^ ℵ₀ :=
          lat_mk_le_of_denseRange ((↑) : PadicAlgCl p → ℂ_[p]) UniformSpace.Completion.denseRange_coe
      _ ≤ 𝔠 ^ ℵ₀ := Cardinal.power_le_power_right h2
      _ = 𝔠 := Cardinal.continuum_power_aleph0
  ·
    obtain ⟨g, -, -, hg⟩ := Perfect.exists_nat_bool_injection (C := (Set.univ : Set ℂ_[p]))
      ⟨isClosed_univ, PerfectSpace.univ_preperfect⟩ ⟨0, trivial⟩
    calc 𝔠 = Cardinal.mk (ℕ → Bool) := by
          rw [← Cardinal.two_power_aleph0, ← Cardinal.mk_nat, ← Cardinal.mk_bool, Cardinal.power_def]
      _ ≤ Cardinal.mk ℂ_[p] := Cardinal.mk_le_of_injective hg

end ReciprocityTheory.ChartRestriction.T1

namespace ReciprocityTheory.ChartRestriction.B3

theorem iop_extEmb {R K L : Type} [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] (f : R →+* K) (g : R →+* L) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ σ : K ≃+* L, ∀ r : R, σ (f r) = g r := by
  letI : Algebra R K := f.toAlgebra
  letI : Algebra R L := g.toAlgebra
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 f.injective
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).2 g.injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L

  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs hR hK
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hR (hKL ▸ hK)
  simp only [Cardinal.lift_id] at h1 h2
  have hst : Cardinal.mk s = Cardinal.mk t := by rw [← h1, ← h2, hKL]
  obtain ⟨e⟩ := Cardinal.eq.1 hst
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let eA : Algebra.adjoin R (Set.range (Subtype.val : s → K)) ≃ₐ[R]
      Algebra.adjoin R (Set.range (Subtype.val : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L eA.toRingEquiv, fun r => ?_⟩
  have e1 : f r = algebraMap (Algebra.adjoin R (Set.range (Subtype.val : s → K))) K
      (algebraMap R _ r) := rfl
  have e2 : g r = algebraMap (Algebra.adjoin R (Set.range (Subtype.val : t → L))) L
      (algebraMap R _ r) := rfl
  rw [e1, IsAlgClosure.equivOfEquiv_algebraMap, e2]
  congr 1
  exact eA.commutes r

end ReciprocityTheory.ChartRestriction.B3
