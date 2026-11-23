import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
import Development.AutomorphicArithmetic.TwistedTraces.IsotypicComponentProductOfSmoothReps
import Development.AutomorphicArithmetic.TwistedTraces.IsotypicSubmoduleProductDecomposition
import Development.AutomorphicArithmetic.TwistedTraces.ExistsScalarOfTwistedIntertwinerCommutingAlgebra
import Development.AutomorphicArithmetic.TwistedTraces.IsotypicSubspaceProductClosed
import Development.AutomorphicArithmetic.TwistedTraces.MemFixedVectorsOfProductOfCompactOpen
import Development.AutomorphicArithmetic.TwistedTraces.TraceRestrictEqOfHasFinTrace
import Development.AutomorphicArithmetic.TwistedTraces.TrOnRestrictAndEqOfMapsInto
import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionInvariantAndCommutingReps
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem prod_fix' {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (v : H) :
    ∀ l : List (H →L[ℂ] H), (∀ a ∈ l, a v = v) → l.prod v = v
  | [], _ => rfl
  | a :: l, hl => by
    rw [List.prod_cons]
    show a (l.prod v) = v
    rw [prod_fix' v l fun b hb => hl b (List.mem_cons_of_mem _ hb), hl a List.mem_cons_self]

theorem UpperTheory.isotypic_intersection_product_eq :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (V Z : Submodule ℂ H), (∀ i, GroundTheory.Automorphic.IsSmooth (τ i)) → (∀ i, (τ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → Z ≤ V → (∀ i, (π i).IsInvariant Z) → (∀ i, V ≤ (spanAll (τ i) (π i) V).topologicalClosure) → (∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∀ L : ∀ i, Subgroup (G i), (∀ i, IsCompact (L i : Set (G i)) ∧ IsOpen (L i : Set (G i))) → (Z ⊓ ⨅ i, fixU (π i) (L i)) ≠ ⊥ → ∃ κ : ℂ, ∀ (T : Fin r → H →L[ℂ] H) (A : ∀ i, S i →ₗ[ℂ] S i) (t : Fin r → ℂ), (∀ i v, T i v ∈ fixU (π i) (L i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T i (f x) = f (A i x)) → (∀ i x, A i x ∈ fixedVectors (τ i) (L i)) → (∀ i, HasFinTrace (A i ∘ₗ (I i : S i →ₗ[ℂ] S i)) (t i)) → trOn (Z ⊓ ⨅ i, fixU (π i) (L i)) ((List.ofFn T).prod ∘L R) = κ * ∏ i, t i := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI L hL hne
  obtain ⟨K, hK, hKL, hsK⟩ : ∃ K : ∀ i, Subgroup (G i),
      (∀ i, IsCompact (K i : Set (G i)) ∧ IsOpen (K i : Set (G i))) ∧ (∀ i, K i ≤ L i) ∧
        ∀ i, ∀ k ∈ K i, (s i).symm k ∈ L i := by
    refine ⟨fun i => L i ⊓ (L i).map ((s i).toMulEquiv : G i →* G i), fun i => ⟨?_, ?_⟩, fun i => inf_le_left, ?_⟩
    · have h2 : IsCompact (((L i).map ((s i).toMulEquiv : G i →* G i) : Subgroup (G i)) : Set (G i)) := by
        rw [Subgroup.coe_map]
        exact (hL i).1.image (s i).continuous
      rw [Subgroup.coe_inf]
      exact (hL i).1.inter h2
    · have h2 : IsOpen (((L i).map ((s i).toMulEquiv : G i →* G i) : Subgroup (G i)) : Set (G i)) := by
        rw [Subgroup.coe_map]
        exact (s i).toHomeomorph.isOpenMap _ (hL i).2
      rw [Subgroup.coe_inf]
      exact (hL i).2.inter h2
    · rintro i k ⟨-, y, hy, rfl⟩
      show (s i).symm (s i y) ∈ L i
      rw [(s i).symm_apply_apply]
      exact hy
  have hXX : (Z ⊓ ⨅ i, fixU (π i) (L i)) ≤ (Z ⊓ ⨅ i, fixU (π i) (K i)) := fun v hv => by
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hv
    exact Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun j u hu =>
      (Submodule.mem_iInf _).1 h2 j u (hKL j hu)⟩
  haveI hfdX : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (K i)) := hadm K hK
  haveI hfdL : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (L i)) := hadm L hL
  have hneX : (Z ⊓ ⨅ i, fixU (π i) (K i)) ≠ ⊥ := fun e => hne (le_bot_iff.1 (e ▸ hXX))
  obtain ⟨h1, c, hcc, hcf, hsp⟩ := UpperTheory.isotypic_component_product_of_smooth_reps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV K hK hfdX hneX
  obtain ⟨h1L, -⟩ := UpperTheory.isotypic_component_product_of_smooth_reps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV L hL hfdL hne
  haveI : ∀ i, FiniteDimensional ℂ (fixedVectors (τ i) (K i)) := fun i => (h1 i).1
  have hLK : ∀ i, fixedVectors (τ i) (L i) ≤ fixedVectors (τ i) (K i) := fun i x hx =>
    mem_fixedVectors.2 fun k hk => mem_fixedVectors.1 hx k (hKL i hk)
  have hIm : ∀ i, ∀ x ∈ fixedVectors (τ i) (L i), I i x ∈ fixedVectors (τ i) (K i) := fun i x hx =>
    mem_fixedVectors.2 fun k hk => by
      have h := hI i ((s i).symm k) x
      rw [(s i).apply_symm_apply, mem_fixedVectors.1 hx _ (hsK i k hk)] at h
      exact h.symm
  let e : ∀ i, fixedVectors (τ i) (K i) →ₗ[ℂ] S i := fun i =>
    (fixedVectors (τ i) (L i)).subtype ∘ₗ fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 ∘ₗ (fixedVectors (τ i) (K i)).subtype
  let J : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i)) := fun i =>
    (((I i : S i →ₗ[ℂ] S i)) ∘ₗ e i).codRestrict (fixedVectors (τ i) (K i)) fun x =>
      hIm i _ (fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 x).2
  have he : ∀ i (x : fixedVectors (τ i) (K i)), (x : S i) ∈ fixedVectors (τ i) (L i) → e i x = x := fun i x hx =>
    fixedProj_apply_of_mem (hsm i) (hL i).1 (hL i).2 hx
  have hJ0 : ∀ i, J i ≠ 0 := fun i h0 => by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (h1L i).2
    have h := LinearMap.congr_fun h0 ⟨x, hLK i hx⟩
    have h' : I i (e i ⟨x, hLK i hx⟩) = 0 := congrArg Subtype.val h
    rw [he i ⟨x, hLK i hx⟩ hx] at h'
    exact hx0 ((I i).map_eq_zero_iff.1 h')
  obtain ⟨ρ, hρ1, hρ2⟩ := UpperTheory.isotypic_submodule_product_decomposition r G H S π τ Z hsm hcm hZc hZi s I R hRZ hRs hI L K hL hKL hsK c J
    (fun i x => rfl) hcf hsp
  obtain ⟨κ, hκ⟩ := UpperTheory.exists_scalar_of_twisted_intertwiner_commuting_algebras r ↥(Z ⊓ ⨅ i, fixU (π i) (K i)) (fun i => fixedVectors (τ i) (K i)) c J ρ hcc hJ0 hρ2
  refine ⟨κ, fun T A t hT1 hT2 hT3 hT4 hA ht => ?_⟩
  let B : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i)) := fun i =>
    (A i ∘ₗ (fixedVectors (τ i) (K i)).subtype).codRestrict (fixedVectors (τ i) (K i)) fun x => hLK i (hA i _)
  have hcomp := UpperTheory.isotypic_subspace_product_closed r G H S π τ Z K c T B hcf hsp (fun i f hf x => hT4 i f hf x)
  have hPrZ : ∀ v ∈ Z, (List.ofFn fun j => prj (fixU (π j) (L j))).prod v ∈ (Z ⊓ ⨅ i, fixU (π i) (L i)) :=
    UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z L (fun j => prj (fixU (π j) (L j)))
      (fun i v => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).1 v)
      (fun i v hv => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).2.2.1 Z hZc (hZi i) v hv)
      (fun i j hij h v => ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G j) H (π i) (π j) (L i) (L j)).2.2.2 (hcm i j hij)).1 h v)
  have hTZ := UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z L T hT1 hT2 hT3
  have hPrFix : ∀ v ∈ (Z ⊓ ⨅ i, fixU (π i) (L i)), (List.ofFn fun j => prj (fixU (π j) (L j))).prod v = v := fun v hv =>
    prod_fix' v _ fun a ha => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      exact (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).2.1 v
        ((Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hv).2 i)
  let W : H →L[ℂ] H := (List.ofFn T).prod ∘L R ∘L (List.ofFn fun j => prj (fixU (π j) (L j))).prod
  have e1 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (K i)) (Z ⊓ ⨅ i, fixU (π i) (K i)) W).1
    ((List.ofFn fun i => c i (B i)).prod * ρ) fun v => by
      rw [Module.End.mul_apply, hcomp, hρ1]
      rfl
  have hWX : ∀ v ∈ (Z ⊓ ⨅ i, fixU (π i) (K i)), W v ∈ (Z ⊓ ⨅ i, fixU (π i) (L i)) := fun v hv =>
    hTZ _ (hRZ _ (Submodule.mem_inf.1 (hPrZ v (Submodule.mem_inf.1 hv).1)).1)
  have e2 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (L i)) (Z ⊓ ⨅ i, fixU (π i) (K i)) W).2 hXX hWX
  let b : Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (L i)) :=
    ((W : H →ₗ[ℂ] H) ∘ₗ (Z ⊓ ⨅ i, fixU (π i) (L i)).subtype).codRestrict _ fun v => hWX _ (hXX v.2)
  have e3 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (L i)) (Z ⊓ ⨅ i, fixU (π i) (L i)) W).1 b fun v => rfl
  have e4 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (L i)) (Z ⊓ ⨅ i, fixU (π i) (L i))
    ((List.ofFn T).prod ∘L R)).1 b fun v => by
      show W v = _
      show (List.ofFn T).prod (R ((List.ofFn fun j => prj (fixU (π j) (L j))).prod (v : H))) = _
      rw [hPrFix _ v.2]
      rfl
  have ht' : ∀ i, LinearMap.trace ℂ (fixedVectors (τ i) (K i)) (B i * J i) = t i := fun i =>
    UpperTheory.trace_restrict_eq_of_hasFinTrace (S i) (fixedVectors (τ i) (L i)) (fixedVectors (τ i) (K i)) (A i ∘ₗ (I i : S i →ₗ[ℂ] S i)) (t i)
      (B i * J i) (e i) (hLK i) (ht i) (fun x => hA i _) (fun x => rfl) (he i)
  rw [e4, ← e3, ← e2, e1, hκ B]
  simp only [ht']
