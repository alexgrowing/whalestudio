import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionInvariantAndCommutingReps
import Development.AutomorphicArithmetic.TwistedTraces.InfFixedLeSpanFixOfDenseSpanAll
import Development.AutomorphicArithmetic.TwistedTraces.ExistsAlgHomEndFixedVectorsToFixedSubspace

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem comm_adj {A : Type} [Ring A] [Algebra ℂ A] {s t : Set A} (h : ∀ a ∈ s, ∀ b ∈ t, Commute a b) {a b : A}
    (ha : a ∈ Algebra.adjoin ℂ s) (hb : b ∈ Algebra.adjoin ℂ t) : Commute a b :=
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun y hy =>
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha fun x hx => (h x hx y hy).symm).symm

set_option maxHeartbeats 800000 in
theorem UpperTheory.isotypic_component_product_of_smooth_reps :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (V Z : Submodule ℂ H), (∀ i, GroundTheory.Automorphic.IsSmooth (τ i)) → (∀ i, (τ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → Z ≤ V → (∀ i, (π i).IsInvariant Z) → (∀ i, V ≤ (spanAll (τ i) (π i) V).topologicalClosure) → ∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i)) → (Z ⊓ ⨅ i, fixU (π i) (U i)) ≠ ⊥ → (∀ i, FiniteDimensional ℂ (fixedVectors (τ i) (U i)) ∧ fixedVectors (τ i) (U i) ≠ ⊥) ∧ ∃ c : ∀ i, Module.End ℂ (fixedVectors (τ i) (U i)) →ₐ[ℂ] Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i)), (∀ i j, i ≠ j → ∀ a b, Commute (c i a) (c j b)) ∧ (∀ i t f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)) f → ∀ (x : fixedVectors (τ i) (U i)) (y : ↥(Z ⊓ ⨅ i, fixU (π i) (U i))), (y : H) = f x → ((c i t y : ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) : H) = f (t x)) ∧ ∀ i, (Z ⊓ ⨅ i, fixU (π i) (U i)) ≤ spanFix (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)) (U i) := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ V Z hsm hirr hcm hZc hZV hZi hV U hU hfd hne
  set X := Z ⊓ ⨅ i, fixU (π i) (U i) with hX
  let D : Fin r → Submodule ℂ H := fun i => Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)
  have hD : ∀ i v, v ∈ D i ↔ v ∈ Z ∧ ∀ j, j ≠ i → v ∈ fixU (π j) (U j) := fun i v => by
    simp only [D, Submodule.mem_inf, Submodule.mem_iInf]
  have hDc : ∀ i, IsClosed (D i : Set H) := fun i => by
    have : (D i : Set H) = (Z : Set H) ∩ ⋂ j, ⋂ _ : j ≠ i, (fixU (π j) (U j) : Set H) := by
      ext v; rw [SetLike.mem_coe, hD]; simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter]
    rw [this]
    exact hZc.inter (isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_fixU _ _)
  have hDi : ∀ i, (π i).IsInvariant (D i) := fun i g v hv => (hD i _).2 ⟨hZi i g v ((hD i v).1 hv).1, fun j hj u hu => by
    rw [hcm j i hj, ((hD i v).1 hv).2 j hj u hu]⟩
  have hXD : ∀ i, X = D i ⊓ fixU (π i) (U i) := fun i => by
    ext v
    simp only [hX, Submodule.mem_inf, Submodule.mem_iInf, hD]
    refine ⟨fun h => ⟨⟨h.1, fun j _ => h.2 j⟩, h.2 i⟩, fun h => ⟨h.1.1, fun j => ?_⟩⟩
    by_cases e : j = i
    · exact e ▸ h.2
    · exact h.1.2 j e
  have hle : ∀ i, X ≤ spanFix (τ i) (π i) (D i) (U i) := fun i => (hXD i).le.trans
    (UpperTheory.inf_fixed_le_spanFix_of_dense_spanAll (G i) H (S i) (τ i) (hsm i) (π i) (U i) (hU i).1 (hU i).2 V (D i) (hDc i) (hDi i) (inf_le_left.trans hZV) (hV i)
      (hXD i ▸ hfd))
  have hm : ∀ i f, Eqv (τ i) (π i) (D i) f → ∀ x : fixedVectors (τ i) (U i), f x ∈ X := fun i f hf x => by
    rw [hXD i]
    exact ⟨hf.mem _, fun u hu => by rw [← hf.map, mem_fixedVectors.1 x.2 u hu]⟩
  have h1 : ∀ i, FiniteDimensional ℂ (fixedVectors (τ i) (U i)) ∧ fixedVectors (τ i) (U i) ≠ ⊥ := fun i => by
    obtain ⟨f, hf, x, hx, h0⟩ : ∃ f, Eqv (τ i) (π i) (D i) f ∧ ∃ x ∈ fixedVectors (τ i) (U i), f x ≠ 0 := by
      by_contra hno
      push Not at hno
      refine hne (le_bot_iff.1 ((hle i).trans (Submodule.span_le.2 ?_)))
      rintro _ ⟨f, hf, x, hx, rfl⟩
      exact hno f hf x hx
    have := hirr i
    have hinj : Function.Injective f := by
      rcases eq_bot_or_eq_top (⟨LinearMap.ker f, fun g v hv => by
        rw [LinearMap.mem_ker] at hv ⊢; rw [hf.map, hv, map_zero]⟩ : Subrepresentation (τ i)) with e | e
      · exact LinearMap.ker_eq_bot.1 (congrArg Subrepresentation.toSubmodule e)
      · exact (h0 (by rw [LinearMap.ker_eq_top.1 (congrArg Subrepresentation.toSubmodule e)]; rfl)).elim
    refine ⟨Module.Finite.of_injective ((f ∘ₗ (fixedVectors (τ i) (U i)).subtype).codRestrict X (hm i f hf)) fun a b e =>
      Subtype.ext (hinj (congrArg Subtype.val e)), fun e => h0 ?_⟩
    rw [e] at hx
    rw [(Submodule.mem_bot ℂ).1 hx, map_zero]
  refine ⟨h1, ?_⟩
  have := fun i => (h1 i).1
  have := fun i => Submodule.nontrivial_iff_ne_bot.2 (h1 i).2
  choose c hc1 hc2 using fun i => UpperTheory.exists_algHom_end_fixedVectors_to_fixed_subspace (G i) H (S i) (τ i) (hsm i) (hirr i) (π i) (U i) (hU i).1 (hU i).2 (D i) X
    (hDc i) (hDi i) (hXD i) (hle i)
  refine ⟨c, fun i j hij s t => ?_, fun i t f hf x y hy => hc1 i t f hf x y hy, hle⟩
  refine comm_adj ?_ (hc2 i s) (hc2 j t)
  rintro a ⟨g, ha⟩ b ⟨h, hb⟩
  obtain ⟨q1, q2⟩ := (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G j) H (π i) (π j) (U i) (U j)).2.2.2 (hcm i j hij)
  obtain ⟨q3, -⟩ := (UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G i) H (π j) (π i) (U j) (U i)).2.2.2 (hcm j i hij.symm)
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, ha, hb, hb, ha, ← q3, ← q1, q2, hcm i j hij]
