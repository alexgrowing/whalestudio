import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionApplyEquivariantEq
import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionInvariantAndCommutingReps
import Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalFixedVectorsIsotypicOfIrreducib
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.twisted_intertwiner_fixedVectors_of_irreducible :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (_ : GroundTheory.Automorphic.IsSmooth τ) (_ : τ.IsIrreducible) (π : UnitaryRep G H) (s : G ≃ₜ* G) (I : S ≃ₗ[ℂ] S), (∀ g x, I (τ g x) = τ (s g) (I x)) → (∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) → FiniteDimensional ℂ (fixedVectors τ K)) → ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) → fixedVectors τ K ≠ ⊥ → ∃ (T : H →L[ℂ] H) (A : S →ₗ[ℂ] S) (t : ℂ), ((∀ v, T v ∈ fixU π K) ∧ (∀ x, A x ∈ fixedVectors τ K) ∧ (∀ D : Submodule ℂ H, IsClosed (D : Set H) → π.IsInvariant D → ∀ v ∈ D, T v ∈ D) ∧ (∀ (G' : Type) [Group G'] [TopologicalSpace G'] (π' : UnitaryRep G' H), (∀ g h v, π g (π' h v) = π' h (π g v)) → ∀ h v, T (π' h v) = π' h (T v)) ∧ (∀ f, Eqv τ π ⊤ f → ∀ x, T (f x) = f (A x))) ∧ HasFinTrace (A ∘ₗ (I : S →ₗ[ℂ] S)) t ∧ t ≠ 0 := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ hirr π s I hI hfd K hKc hKo hne
  let sK : Subgroup G := K.map s.toMulEquiv.toMonoidHom
  have hsKc : IsCompact (sK : Set G) := by
    have : (sK : Set G) = s '' (K : Set G) := rfl
    rw [this]
    exact hKc.image s.continuous
  have hsKo : IsOpen (sK : Set G) := by
    have : (sK : Set G) = s.toHomeomorph '' (K : Set G) := rfl
    rw [this]
    exact s.toHomeomorph.isOpenMap _ hKo
  let K₁ : Subgroup G := K ⊓ sK
  have hK₁c : IsCompact (K₁ : Set G) := by
    rw [Subgroup.coe_inf]
    exact hKc.inter hsKc
  have hK₁o : IsOpen (K₁ : Set G) := by
    rw [Subgroup.coe_inf]
    exact hKo.inter hsKo
  have hPle : ∀ x ∈ fixedVectors τ K, x ∈ fixedVectors τ K₁ := fun x hx k hk => hx k hk.1
  have hsle : ∀ x ∈ fixedVectors τ sK, x ∈ fixedVectors τ K₁ := fun x hx k hk => hx k hk.2
  have hne₁ : fixedVectors τ K₁ ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have := hPle x hx
    rwa [h] at this
  have hIm : ∀ x ∈ fixedVectors τ K, I x ∈ fixedVectors τ sK := by
    rintro x hx _ ⟨k, hk, rfl⟩
    show τ (s k) (I x) = I x
    rw [← hI, hx k hk]
  have hIs : ∀ y ∈ fixedVectors τ sK, I.symm y ∈ fixedVectors τ K := by
    intro y hy k hk
    apply I.injective
    rw [hI, I.apply_symm_apply]
    exact hy _ ⟨k, hk, rfl⟩
  let ε : S →ₗ[ℂ] fixedVectors τ sK := fixedProj τ hτ hsKc hsKo
  let h : Module.End ℂ (fixedVectors τ K₁) :=
    LinearMap.codRestrict (fixedVectors τ K₁)
      ((I.symm : S →ₗ[ℂ] S) ∘ₗ (fixedVectors τ sK).subtype ∘ₗ ε ∘ₗ (fixedVectors τ K₁).subtype)
      (fun x => hPle _ (hIs _ (ε x).2))
  obtain ⟨T₀, A₀, ⟨c1, c2, c3, c4, c5⟩, c6⟩ :=
    UpperTheory.finiteDimensional_fixedVectors_isotypic_of_irreducible G H S τ hτ hirr π K₁ hK₁c hK₁o (hfd K₁ hK₁c hK₁o) hne₁ h
  obtain ⟨p1, -, p3, -⟩ := UpperTheory.fixedProjection_invariant_and_commuting_reps G G H π π K K
  let e : S →ₗ[ℂ] fixedVectors τ K := fixedProj τ hτ hKc hKo
  let A : S →ₗ[ℂ] S := (fixedVectors τ K).subtype ∘ₗ e ∘ₗ A₀
  let B : S →ₗ[ℂ] S := A ∘ₗ (I : S →ₗ[ℂ] S)
  have hB : ∀ x ∈ fixedVectors τ K, B x = x := by
    intro x hx
    have hIx := hIm x hx
    have h1 : A₀ (I x) = x := by
      have h2 := c6 ⟨I x, hsle _ hIx⟩
      have h3 : ((ε (I x) : fixedVectors τ sK) : S) = I x := fixedProj_apply_of_mem hτ hsKc hsKo hIx
      have h4 : ((h ⟨I x, hsle _ hIx⟩ : fixedVectors τ K₁) : S) = I.symm (ε (I x) : fixedVectors τ sK) := rfl
      rw [h4, h3, I.symm_apply_apply] at h2
      exact h2
    show ((e (A₀ (I x)) : fixedVectors τ K) : S) = x
    rw [h1]
    exact fixedProj_apply_of_mem hτ hKc hKo hx
  have hR : LinearMap.range B = fixedVectors τ K := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (e _).2
    · intro x hx
      exact ⟨x, hB x hx⟩
  haveI hfdR : FiniteDimensional ℂ (LinearMap.range B) := by
    rw [hR]
    exact hfd K hKc hKo
  haveI : Nontrivial (LinearMap.range B) := by
    rw [hR]
    exact Submodule.nontrivial_iff_ne_bot.2 hne
  have hrest : (B.restrict (p := LinearMap.range B) (q := LinearMap.range B)
      fun v _ => LinearMap.mem_range_self B v) = LinearMap.id :=
    LinearMap.ext fun y => Subtype.ext (hB y (hR ▸ y.2))
  refine ⟨prj (fixU π K) ∘L T₀, A, (Module.finrank ℂ (LinearMap.range B) : ℂ),
    ⟨fun v => p1 _, fun x => (e _).2, ?_, ?_, ?_⟩, ⟨hfdR, ?_⟩, ?_⟩
  · intro D hD hinv v hv
    exact p3 D hD hinv _ (c3 D hD hinv v hv)
  · intro G' _ _ π' hc g v
    show prj (fixU π K) (T₀ (π' g v)) = π' g (prj (fixU π K) (T₀ v))
    rw [c4 G' π' hc, ((UpperTheory.fixedProjection_invariant_and_commuting_reps G G' H π π' K ⊥).2.2.2 hc).1]
  · intro f hf x
    show prj (fixU π K) (T₀ (f x)) = f (e (A₀ x))
    rw [c5 f hf]
    exact UpperTheory.fixedProjection_apply_equivariant_eq G H S τ hτ π K hKc hKo f hf _
  · show LinearMap.trace ℂ (LinearMap.range B) (B.restrict (p := LinearMap.range B) (q := LinearMap.range B)
      fun v _ => LinearMap.mem_range_self B v) = _
    rw [hrest, LinearMap.trace_id]
  · exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'
