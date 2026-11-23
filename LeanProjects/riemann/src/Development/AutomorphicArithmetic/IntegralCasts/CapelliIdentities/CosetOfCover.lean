import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qn18.Mat :
    Type → ℕ → Type :=
    fun (C : Type) (N : ℕ) ↦ Matrix (Fin N) (Fin N) C

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qn18.MP :
    (C : Type) → [Field C] → ℕ → Type :=
    fun (C : Type) [Field C] (N : ℕ) ↦ MvPolynomial (Fin N × Fin N) C

noncomputable def UpperTheory.Reformulated.B.Qn18.ev :
    {C : Type} → [inst : Field C] → {N : ℕ} → UpperTheory.Reformulated.B.Qn18.Mat C N → UpperTheory.Reformulated.B.Qn18.MP C N → C :=
    fun {C : Type} [Field C] {N : ℕ} (x : UpperTheory.Reformulated.B.Qn18.Mat C N) (f : UpperTheory.Reformulated.B.Qn18.MP C N) ↦
      (MvPolynomial.eval fun (p : Fin N × Fin N) ↦ x p.1 p.2 : MvPolynomial (Fin N × Fin N) C → C) f

noncomputable def UpperTheory.Reformulated.B.Qn18.dAt :
    {C : Type} →
      [inst : Field C] → {N : ℕ} → UpperTheory.Reformulated.B.Qn18.MP C N → UpperTheory.Reformulated.B.Qn18.Mat C N → UpperTheory.Reformulated.B.Qn18.Mat C N → C :=
    fun {C : Type} [Field C] {N : ℕ} (f : UpperTheory.Reformulated.B.Qn18.MP C N) (x Y : UpperTheory.Reformulated.B.Qn18.Mat C N) ↦
      ∑ p : Fin N × Fin N,
        UpperTheory.Reformulated.B.Qn18.ev x
            ((MvPolynomial.pderiv p : MvPolynomial (Fin N × Fin N) C → MvPolynomial (Fin N × Fin N) C) f) *
          Y p.1 p.2

noncomputable def UpperTheory.Reformulated.B.Qn18.Chain :
    Prop :=
    ∀ (C : Type) [inst : Field C] (N M : ℕ) (φ : UpperTheory.Reformulated.B.Qn18.Mat C N →ₗ[C] UpperTheory.Reformulated.B.Qn18.Mat C M)
      (f : UpperTheory.Reformulated.B.Qn18.MP C M),
      ∃ (f' : UpperTheory.Reformulated.B.Qn18.MP C N),
        (∀ (x : UpperTheory.Reformulated.B.Qn18.Mat C N),
            UpperTheory.Reformulated.B.Qn18.ev x f' =
              UpperTheory.Reformulated.B.Qn18.ev ((φ : UpperTheory.Reformulated.B.Qn18.Mat C N → UpperTheory.Reformulated.B.Qn18.Mat C M) x) f) ∧
          ∀ (x Y : UpperTheory.Reformulated.B.Qn18.Mat C N),
            UpperTheory.Reformulated.B.Qn18.dAt f' x Y =
              UpperTheory.Reformulated.B.Qn18.dAt f ((φ : UpperTheory.Reformulated.B.Qn18.Mat C N → UpperTheory.Reformulated.B.Qn18.Mat C M) x)
                ((φ : UpperTheory.Reformulated.B.Qn18.Mat C N → UpperTheory.Reformulated.B.Qn18.Mat C M) Y)

noncomputable def UpperTheory.Reformulated.B.Qn18.OpenCoset :
    Prop :=
    ∀ (Γ C : Type) [inst : Group Γ] [inst_1 : TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [inst_4 : Field C]
      (n : ℕ) (r : Γ →* GL (Fin n) C) (f : UpperTheory.Reformulated.B.Qn18.MP C n) (O : Set Γ),
      IsOpen O →
        O.Nonempty →
          (∀ g ∈ O, UpperTheory.Reformulated.B.Qn18.ev (↑((r : Γ → GL (Fin n) C) g) : Matrix (Fin n) (Fin n) C) f = (0 : C)) →
            ∃ (U : Subgroup Γ),
              U.Normal ∧
                U.FiniteIndex ∧
                  ∃ (g : Γ),
                    ∀ u ∈ U, UpperTheory.Reformulated.B.Qn18.ev (↑((r : Γ → GL (Fin n) C) (g * u)) : Matrix (Fin n) (Fin n) C) f = (0 : C)

open scoped Pointwise in
private theorem UpperTheory.Reformulated.B.Qn18.coset_of_cover {G : Type} [Group G] [TopologicalSpace G]
    [TopologicalSpace.NoetherianSpace G] (hc : ∀ h : G, Continuous fun x : G => h * x)
    (Z : Set G) (hZ : IsClosed Z) (s : Finset G) (hs : ∀ x : G, ∃ a ∈ s, a * x ∈ Z) :
    ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ ∃ g : G, ∀ u ∈ U, g * u ∈ Z := by
  classical
  haveI : ContinuousConstSMul G G := ⟨hc⟩
  set X : Set G := irreducibleComponent (1 : G) with hX
  have hXc : X ∈ irreducibleComponents G := irreducibleComponent_mem_irreducibleComponents _
  have horb : MulAction.orbit G X ⊆ irreducibleComponents G := by
    rintro _ ⟨h, rfl⟩
    refine ⟨?_, ?_⟩
    · exact hXc.1.image _ (hc h).continuousOn
    · intro Y hY hle
      have h1 : IsIrreducible (h⁻¹ • Y) := IsIrreducible.image hY _ (hc h⁻¹).continuousOn
      have h2 : X ⊆ h⁻¹ • Y := by
        have : h • X ⊆ Y := hle
        exact Set.smul_set_subset_iff_subset_inv_smul_set.mp this
      have h3 : h⁻¹ • Y ⊆ X := hXc.2 h1 h2
      have h4 : Y ⊆ h • X := by
        have := Set.smul_set_subset_iff_subset_inv_smul_set.mp h3
        simpa using this
      exact h4
  have hfin : (MulAction.orbit G X).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset horb
  haveI : (MulAction.stabilizer G X).FiniteIndex := by
    refine ⟨?_⟩
    rw [MulAction.index_stabilizer]
    exact ((Set.ncard_pos hfin).mpr ⟨X, MulAction.mem_orbit_self X⟩).ne'
  obtain ⟨W, hW, hXW⟩ := isIrreducible_iff_sUnion_isClosed.mp hXc.1
    (s.image fun a => (fun x : G => a * x) ⁻¹' Z)
    (by
      intro z hz
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
      exact hZ.preimage (hc a))
    (by
      intro x _
      obtain ⟨a, ha, hx⟩ := hs x
      exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ha), hx⟩)
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hW
  refine ⟨(MulAction.stabilizer G X).normalCore, inferInstance, inferInstance, a, ?_⟩
  intro u hu
  have hu' : u • X = X := Subgroup.normalCore_le _ hu
  have : u ∈ X := by
    rw [← hu']
    exact ⟨1, mem_irreducibleComponent, by simp⟩
  exact hXW this

private theorem UpperTheory.Reformulated.B.Qn18.finite_cover {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (O : Set G) (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ s : Finset G, ∀ x : G, ∃ a ∈ s, a * x ∈ O := by
  obtain ⟨o, ho⟩ := hne
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun a : G => (fun x : G => a * x) ⁻¹' O)
    (fun a => hO.preimage (continuous_const_mul a))
    (fun x _ => Set.mem_iUnion.mpr ⟨o * x⁻¹, by simpa using ho⟩)
  refine ⟨s, fun x => ?_⟩
  simpa using hs (Set.mem_univ x)

theorem UpperTheory.Reformulated.B.Qn18.main :
    UpperTheory.Reformulated.B.Qn18.Chain → UpperTheory.Reformulated.B.Qn18.OpenCoset := by
  intro hch Γ C _ _ _ _ _ n r f O hO hne hf
  obtain ⟨s, hs⟩ := UpperTheory.Reformulated.B.Qn18.finite_cover O hO hne
  let p : Γ → PrimeSpectrum (MvPolynomial (Fin n × Fin n) C) := fun g =>
    ⟨RingHom.ker (MvPolynomial.eval fun q : Fin n × Fin n =>
      (↑(r g) : Matrix (Fin n) (Fin n) C) q.1 q.2), RingHom.ker_isPrime _⟩
  have hp : ∀ (g : Γ) (S : Set (MvPolynomial (Fin n × Fin n) C)),
      p g ∈ PrimeSpectrum.zeroLocus S ↔
        ∀ k ∈ S, UpperTheory.Reformulated.B.Qn18.ev (↑(r g) : Matrix (Fin n) (Fin n) C) k = 0 := by
    intro g S
    rw [PrimeSpectrum.mem_zeroLocus]
    exact Iff.rfl
  let τ : TopologicalSpace Γ := TopologicalSpace.induced p inferInstance
  have hcl : ∀ k : MvPolynomial (Fin n × Fin n) C,
      @IsClosed Γ τ {g | UpperTheory.Reformulated.B.Qn18.ev (↑(r g) : Matrix (Fin n) (Fin n) C) k = 0} := by
    intro k
    refine (@isClosed_induced_iff _ _ _ _ p).mpr ⟨_, PrimeSpectrum.isClosed_zeroLocus {k}, ?_⟩
    ext g
    simp [hp]
  have hN : @TopologicalSpace.NoetherianSpace Γ τ := by
    letI := τ
    exact (@Topology.IsInducing.mk _ _ τ _ p rfl).noetherianSpace
  have hc : ∀ h : Γ, @Continuous Γ Γ τ τ fun x => h * x := by
    intro h
    refine (@continuous_iff_isClosed _ _ τ τ _).mpr ?_
    intro T hT
    obtain ⟨T', hT', rfl⟩ := (@isClosed_induced_iff _ _ _ _ p).mp hT
    obtain ⟨S, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus _).mp hT'
    choose F hF using fun k => hch C n n
      (LinearMap.mulLeft C (↑(r h) : Matrix (Fin n) (Fin n) C)) k
    have : (fun x => h * x) ⁻¹' (p ⁻¹' PrimeSpectrum.zeroLocus S) =
        ⋂ k ∈ S, {g | UpperTheory.Reformulated.B.Qn18.ev (↑(r g) : Matrix (Fin n) (Fin n) C) (F k) = 0} := by
      ext g
      simp only [Set.mem_preimage, hp, Set.mem_iInter, Set.mem_setOf_eq, (hF _).1,
        LinearMap.mulLeft_apply, map_mul, Units.val_mul]
    rw [this]
    exact @isClosed_biInter _ _ τ _ _ fun k _ => hcl (F k)
  exact @UpperTheory.Reformulated.B.Qn18.coset_of_cover Γ _ τ hN hc _ (hcl f) s fun x => by
    obtain ⟨a, ha, hx⟩ := hs x
    exact ⟨a, ha, hf _ hx⟩
