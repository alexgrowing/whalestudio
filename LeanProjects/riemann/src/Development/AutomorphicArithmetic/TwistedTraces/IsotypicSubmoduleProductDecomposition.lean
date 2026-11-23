import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
import Development.AutomorphicArithmetic.TwistedTraces.MemFixedVectorsOfProductOfCompactOpen
import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionInvariantAndCommutingReps
import Development.AutomorphicArithmetic.TwistedTraces.IsotypicProjectionProductCommute
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.isotypic_submodule_product_decomposition :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (Z : Submodule ℂ H) (hsm : ∀ i, GroundTheory.Automorphic.IsSmooth (τ i)), (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → (∀ i, (π i).IsInvariant Z) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∀ (L K : ∀ i, Subgroup (G i)) (hL : (∀ i, IsCompact (L i : Set (G i)) ∧ IsOpen (L i : Set (G i)))), (∀ i, K i ≤ L i) → (∀ i, ∀ k ∈ K i, (s i).symm k ∈ L i) → ∀ (c : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i)) →ₐ[ℂ] Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (K i))) (J : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i))), (∀ i (x : fixedVectors (τ i) (K i)), ((J i x : fixedVectors (τ i) (K i)) : S i) = I i (fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 x : S i)) → (∀ i t f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f → ∀ (x : fixedVectors (τ i) (K i)) (y : ↥(Z ⊓ ⨅ i, fixU (π i) (K i))), (y : H) = f x → ((c i t y : ↥(Z ⊓ ⨅ i, fixU (π i) (K i))) : H) = f (t x)) → (∀ i, (Z ⊓ ⨅ i, fixU (π i) (K i)) ≤ spanFix (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) (K i)) → ∃ ρ : Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (K i)), (∀ v : ↥(Z ⊓ ⨅ i, fixU (π i) (K i)), ((ρ v : ↥(Z ⊓ ⨅ i, fixU (π i) (K i))) : H) = R ((List.ofFn fun j => prj (fixU (π j) (L j))).prod v)) ∧ ∀ i a b, b * J i = J i * a → ρ * c i a = c i b * ρ := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ Z hsm hc hZc hZi s I R hRZ hRs hI L K hL hKL hsK c J hJ hcf hsp
  let X : Submodule ℂ H := Z ⊓ ⨅ i, fixU (π i) (K i)
  let Pr : H →L[ℂ] H := (List.ofFn fun j => prj (fixU (π j) (L j))).prod
  have hPr : ∀ v ∈ Z, Pr v ∈ (Z ⊓ ⨅ j, fixU (π j) (L j)) :=
    UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z L (fun j => prj (fixU (π j) (L j)))
      (fun i v => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).1 v)
      (fun i v hv => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).2.2.1 Z hZc (hZi i) v hv)
      (fun i j hij h v => ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G j) H (π i) (π j) (L i) (L j)).2.2.2 (hc i j hij)).1 h v)
  have hRX : ∀ v ∈ Z, R (Pr v) ∈ X := fun v hv => by
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 (hPr v hv)
    refine Submodule.mem_inf.2 ⟨hRZ _ h1, (Submodule.mem_iInf _).2 fun j u hu => ?_⟩
    have h := hRs j ((s j).symm u) _ h1
    rw [(s j).apply_symm_apply] at h
    rw [← h, (Submodule.mem_iInf _).1 h2 j _ (hsK j u hu)]
  have hm : ∀ i f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f →
      ∀ x ∈ fixedVectors (τ i) (K i), f x ∈ X := fun i f hf x hx => by
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 (hf.mem x)
    refine Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun j => ?_⟩
    by_cases e : j = i
    · subst e
      exact fun u hu => by rw [← hf.map, mem_fixedVectors.1 hx u hu]
    · exact (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 h2 j) e
  let ρ : Module.End ℂ X := ((R : H →ₗ[ℂ] H) ∘ₗ (Pr : H →ₗ[ℂ] H) ∘ₗ X.subtype).codRestrict X
    fun v => hRX _ (Submodule.mem_inf.1 v.2).1
  refine ⟨ρ, fun v => rfl, fun i a b hab => ?_⟩
  have key : ∀ y ∈ spanFix (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) (K i),
      ∃ h : y ∈ X, ρ (c i a ⟨y, h⟩) = c i b (ρ ⟨y, h⟩) := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, x, hx, rfl⟩ := hy
      obtain ⟨f', hf', hff⟩ := UpperTheory.isotypic_projection_product_commute r G H S π τ Z hsm hc hZc hZi s I R hRZ hRs hI L K hL hKL hsK i f hf
      have hρ : ∀ (x' : fixedVectors (τ i) (K i)) (h : f x' ∈ X), ((ρ ⟨f x', h⟩ : X) : H) = f' (J i x') := by
        intro x' h
        rw [hJ]
        exact hff x'
      have hy := hm i f hf x hx
      refine ⟨hy, Subtype.ext ?_⟩
      have e1 : c i a ⟨f x, hy⟩ = ⟨f (a ⟨x, hx⟩), hm i f hf _ (a ⟨x, hx⟩).2⟩ :=
        Subtype.ext (hcf i a f hf ⟨x, hx⟩ _ rfl)
      have e2 : ((c i b (ρ ⟨f x, hy⟩) : X) : H) = f' (b (J i ⟨x, hx⟩)) :=
        hcf i b f' hf' (J i ⟨x, hx⟩) _ (hρ ⟨x, hx⟩ hy)
      have e3 : b (J i ⟨x, hx⟩) = J i (a ⟨x, hx⟩) := LinearMap.congr_fun hab ⟨x, hx⟩
      rw [e1, e2, e3]
      exact hρ _ _
    | zero => exact ⟨X.zero_mem, by
        show ρ (c i a 0) = c i b (ρ 0)
        simp only [map_zero]⟩
    | add u v _ _ h1 h2 =>
      obtain ⟨p, hp⟩ := h1
      obtain ⟨q, hq⟩ := h2
      refine ⟨X.add_mem p q, ?_⟩
      show ρ (c i a (⟨u, p⟩ + ⟨v, q⟩)) = c i b (ρ (⟨u, p⟩ + ⟨v, q⟩))
      rw [map_add, map_add, map_add, map_add, hp, hq]
    | smul k u _ h1 =>
      obtain ⟨p, hp⟩ := h1
      refine ⟨X.smul_mem k p, ?_⟩
      show ρ (c i a (k • ⟨u, p⟩)) = c i b (ρ (k • ⟨u, p⟩))
      rw [map_smul, map_smul, map_smul, map_smul, hp]
  exact LinearMap.ext fun v => (key v (hsp i v.2)).2
