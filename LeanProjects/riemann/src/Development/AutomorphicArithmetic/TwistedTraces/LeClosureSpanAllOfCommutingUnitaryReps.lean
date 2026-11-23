import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
import Development.AutomorphicArithmetic.TwistedTraces.CommutingSmoothIrreducibleFixedVectors
import Development.AutomorphicArithmetic.TwistedTraces.ExistsCompactOpenFamilyInfFixedNeBot
import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionApplyEquivariantEq
import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionInvariantAndCommutingReps
import Development.AutomorphicArithmetic.TwistedTraces.TrOnRestrictAndEqOfMapsInto

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem prod_keep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Y : Submodule ℂ H) :
    ∀ l : List (H →L[ℂ] H), (∀ a ∈ l, ∀ v ∈ Y, a v ∈ Y) → ∀ v, (v ∈ Y ∨ ∃ a ∈ l, ∀ v, a v ∈ Y) → l.prod v ∈ Y
  | [], _, v, h => by simpa using h
  | a :: l, hl, v, h => by
    rw [List.prod_cons]
    show a (l.prod v) ∈ Y
    have ih := prod_keep Y l (fun b hb => hl b (List.mem_cons_of_mem _ hb)) v
    rcases h with h | ⟨b, hb, h⟩
    · exact hl a List.mem_cons_self _ (ih (Or.inl h))
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact h _
      · exact hl a List.mem_cons_self _ (ih (Or.inr ⟨b, hb, h⟩))

private theorem prod_fix {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (v : H) :
    ∀ l : List (H →L[ℂ] H), (∀ a ∈ l, a v = v) → l.prod v = v
  | [], _ => rfl
  | a :: l, hl => by
    rw [List.prod_cons]
    show a (l.prod v) = v
    rw [prod_fix v l fun b hb => hl b (List.mem_cons_of_mem _ hb), hl a List.mem_cons_self]

set_option maxHeartbeats 800000 in
theorem UpperTheory.le_closure_spanAll_of_commuting_unitaryReps :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (V Z : Submodule ℂ H), (∀ i, GroundTheory.Automorphic.IsSmooth (τ i)) → (∀ i, (τ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → Z ≤ V → (∀ i, (π i).IsInvariant Z) → (∀ i, V ≤ (spanAll (τ i) (π i) V).topologicalClosure) → (∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) → Z ≠ ⊥ → (∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → ∀ i, FiniteDimensional ℂ (fixedVectors (τ i) (U i))) ∧ ∃ N : ℕ, 0 < N ∧ ∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → ∀ (T : Fin r → H →L[ℂ] H) (A : ∀ i, S i →ₗ[ℂ] S i) (B : ∀ i, Module.End ℂ (fixedVectors (τ i) (U i))), (∀ i v, T i v ∈ fixU (π i) (U i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T i (f x) = f (A i x)) → (∀ i x, A i x ∈ fixedVectors (τ i) (U i)) → (∀ i (x : fixedVectors (τ i) (U i)), ((B i x : fixedVectors (τ i) (U i)) : S i) = A i x) → trOn (Z ⊓ ⨅ i, fixU (π i) (U i)) (List.ofFn T).prod = N * ∏ i, LinearMap.trace ℂ (fixedVectors (τ i) (U i)) (B i) := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ V Z hsm hirr hcm hZc hZV hZi hV hfd hne
  have lev := UpperTheory.commuting_smooth_irreducible_fixed_vectors r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV
  have hX : ∀ (U : ∀ i, Subgroup (G i)) v, v ∈ Z ⊓ ⨅ i, fixU (π i) (U i) ↔ v ∈ Z ∧ ∀ i, v ∈ fixU (π i) (U i) := fun U v => by
    simp only [Submodule.mem_inf, Submodule.mem_iInf]
  obtain ⟨U₀, hU₀, h0⟩ := UpperTheory.exists_compactOpen_family_inf_fixed_ne_bot r G H π hcm Z hZc hZi hne
  have hmono : ∀ L U : ∀ i, Subgroup (G i), (∀ i, L i ≤ U i) → Z ⊓ ⨅ i, fixU (π i) (U i) ≤ Z ⊓ ⨅ i, fixU (π i) (L i) :=
    fun L U h v hv => (hX L v).2 ⟨hv.1, fun i u hu => ((hX U v).1 hv).2 i u (h i hu)⟩
  have hmS : ∀ i (L U : Subgroup (G i)), L ≤ U → fixedVectors (τ i) U ≤ fixedVectors (τ i) L :=
    fun i L U h v hv => mem_fixedVectors.2 fun u hu => mem_fixedVectors.1 hv u (h hu)
  have hco : ∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) →
      ∀ i, IsCompact ((U i ⊓ U₀ i : Subgroup (G i)) : Set (G i)) ∧ IsOpen ((U i ⊓ U₀ i : Subgroup (G i)) : Set (G i)) :=
    fun U hU i => ⟨(hU i).1.inter (hU₀ i).1, (hU i).2.inter (hU₀ i).2⟩
  have hne' : ∀ U : ∀ i, Subgroup (G i), (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i)) ≠ ⊥ := fun U e =>
    h0 (le_bot_iff.1 (e ▸ hmono _ U₀ fun i => inf_le_right))
  have hS : ∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) →
      ∀ i, FiniteDimensional ℂ (fixedVectors (τ i) (U i)) := fun U hU i => by
    have := ((lev _ (hco U hU) (hfd _ (hco U hU)) (hne' U)).1 i).1
    exact Submodule.finiteDimensional_of_le (hmS i (U i ⊓ U₀ i) _ inf_le_left)
  refine ⟨hS, ?_⟩
  have shift : ∀ L : ∀ i, Subgroup (G i), (∀ i, IsCompact (L i : Set (G i)) ∧ IsOpen (L i : Set (G i))) →
      (Z ⊓ ⨅ i, fixU (π i) (L i)) ≠ ⊥ → ∃ N : ℕ, ∀ U : ∀ i, Subgroup (G i), (∀ i, L i ≤ U i) → (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → ∀ (T : Fin r → H →L[ℂ] H) (A : ∀ i, S i →ₗ[ℂ] S i) (B : ∀ i, Module.End ℂ (fixedVectors (τ i) (U i))), (∀ i v, T i v ∈ fixU (π i) (U i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T i (f x) = f (A i x)) → (∀ i x, A i x ∈ fixedVectors (τ i) (U i)) → (∀ i (x : fixedVectors (τ i) (U i)), ((B i x : fixedVectors (τ i) (U i)) : S i) = A i x) → trOn (Z ⊓ ⨅ i, fixU (π i) (U i)) (List.ofFn T).prod = N * ∏ i, LinearMap.trace ℂ (fixedVectors (τ i) (U i)) (B i) := by
    intro L hL hLne
    obtain ⟨-, N, hN⟩ := lev L hL (hfd L hL) hLne
    refine ⟨N, fun U hLU hU T A B h1 h2 h3 h4 h5 h6 => ?_⟩
    have k1 : ∀ i j (J : Subgroup (G j)), J ≤ U j → ∀ v ∈ fixU (π j) J, T i v ∈ fixU (π j) J := fun i j J hJ v hv u hu => by
      by_cases e : i = j
      · subst e; exact h1 i v u (hJ hu)
      · rw [← h3 i j e, hv u hu]
    have := hfd L hL
    have := hfd U hU
    have := hS L hL
    have := hS U hU
    let p : ∀ i, fixedVectors (τ i) (L i) →ₗ[ℂ] fixedVectors (τ i) (U i) := fun i =>
      (A i ∘ₗ (fixedVectors (τ i) (L i)).subtype).codRestrict _ fun x => h5 i _
    let q : ∀ i, fixedVectors (τ i) (U i) →ₗ[ℂ] fixedVectors (τ i) (L i) := fun i => Submodule.inclusion (hmS i _ _ (hLU i))
    have e1 := hN T (fun i => q i ∘ₗ p i) (fun i v hv => (hX L _).2 ⟨h2 i v hv.1, fun j => k1 i j _ (hLU j) v (((hX L v).1 hv).2 j)⟩)
      fun i f hf x => h4 i f hf x
    have e2 : ∀ i, LinearMap.trace ℂ _ (q i ∘ₗ p i) = LinearMap.trace ℂ _ (B i) := fun i => by
      rw [LinearMap.trace_comp_comm']
      exact congrArg _ (LinearMap.ext fun x => Subtype.ext (h6 i x).symm)
    simp only [e2] at e1
    rw [← e1]
    refine ((UpperTheory.trOn_restrict_and_eq_of_maps_into H _ _ _).2 (hmono L U hLU) fun v hv => (hX U _).2 ⟨?_, fun j => ?_⟩).symm
    · exact prod_keep Z _ (fun a ha => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact h2 i) v (Or.inl hv.1)
    · exact prod_keep _ _ (fun a ha => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact k1 i j _ le_rfl) v
        (Or.inr ⟨T j, List.mem_ofFn.2 ⟨j, rfl⟩, h1 j⟩)
  have key : ∀ L : ∀ i, Subgroup (G i), (∀ i, L i ≤ U₀ i) → ∀ N : ℕ, (∀ U : ∀ i, Subgroup (G i), (∀ i, L i ≤ U i) → (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → ∀ (T : Fin r → H →L[ℂ] H) (A : ∀ i, S i →ₗ[ℂ] S i) (B : ∀ i, Module.End ℂ (fixedVectors (τ i) (U i))), (∀ i v, T i v ∈ fixU (π i) (U i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T i (f x) = f (A i x)) → (∀ i x, A i x ∈ fixedVectors (τ i) (U i)) → (∀ i (x : fixedVectors (τ i) (U i)), ((B i x : fixedVectors (τ i) (U i)) : S i) = A i x) → trOn (Z ⊓ ⨅ i, fixU (π i) (U i)) (List.ofFn T).prod = N * ∏ i, LinearMap.trace ℂ (fixedVectors (τ i) (U i)) (B i)) →
      Module.finrank ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U₀ i)) = N * ∏ i, Module.finrank ℂ (fixedVectors (τ i) (U₀ i)) := by
    intro L hL N hN
    have := hfd U₀ hU₀
    have := hS U₀ hU₀
    have e1 := hN U₀ hL hU₀ (fun i => prj (fixU (π i) (U₀ i)))
      (fun i => (fixedVectors (τ i) (U₀ i)).subtype ∘ₗ fixedProj (τ i) (hsm i) (hU₀ i).1 (hU₀ i).2) (fun _ => 1)
      (fun i => (UpperTheory.fixedProjection_invariant_and_commuting_reps _ _ H (π i) (π i) (U₀ i) (U₀ i)).1)
      (fun i => (UpperTheory.fixedProjection_invariant_and_commuting_reps _ _ H (π i) (π i) (U₀ i) (U₀ i)).2.2.1 Z hZc (hZi i))
      (fun i j hij => ((UpperTheory.fixedProjection_invariant_and_commuting_reps _ _ H (π i) (π j) (U₀ i) (U₀ j)).2.2.2 (hcm i j hij)).1)
      (fun i f hf x => UpperTheory.fixedProjection_apply_equivariant_eq _ H _ (τ i) (hsm i) (π i) (U₀ i) (hU₀ i).1 (hU₀ i).2 f hf x)
      (fun i x => (fixedProj (τ i) (hsm i) (hU₀ i).1 (hU₀ i).2 x).2)
      (fun i x => (fixedProj_apply_of_mem (hsm i) (hU₀ i).1 (hU₀ i).2 x.2).symm)
    rw [(UpperTheory.trOn_restrict_and_eq_of_maps_into H _ (Z ⊓ ⨅ i, fixU (π i) (U₀ i)) _).1 1 fun v => (prod_fix _ _ fun a ha => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      exact (UpperTheory.fixedProjection_invariant_and_commuting_reps _ _ H (π i) (π i) (U₀ i) (U₀ i)).2.1 _ (((hX U₀ _).1 v.2).2 i)).symm] at e1
    simp only [LinearMap.trace_one] at e1
    exact_mod_cast e1
  obtain ⟨N, hN⟩ := shift U₀ hU₀ h0
  have := hfd U₀ hU₀
  have hpos : 0 < Module.finrank ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U₀ i)) :=
    Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 h0)
  have k0 := key U₀ (fun _ => le_rfl) N hN
  rw [k0] at hpos
  refine ⟨N, Nat.pos_of_mul_pos_right hpos, fun U hU => ?_⟩
  obtain ⟨N', hN'⟩ := shift _ (hco U hU) (hne' U)
  obtain rfl : N' = N := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_mul_pos_left hpos)
    ((key _ (fun _ => inf_le_right) N' hN').symm.trans k0)
  exact hN' U (fun _ => inf_le_left) hU
