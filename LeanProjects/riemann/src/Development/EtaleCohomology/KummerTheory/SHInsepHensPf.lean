import Development.EtaleCohomology.KummerTheory.SHInsepPf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

noncomputable section
open scoped TensorProduct
open GlobalTheory.EtC IsLocalRing Polynomial

namespace LateralTheory.KummerTheory

theorem hens_root_of_sub {R S : Type*} [CommRing R] [CommRing S] [HenselianLocalRing R] [IsLocalRing S]
    (φ : R →+* S) (hc : (maximalIdeal S).comap φ = maximalIdeal R) (f : S[X]) (hf : f.Monic) (a₀ : S)
    (hlift : ∀ n, f.coeff n ∈ Set.range φ) (ha : a₀ ∈ Set.range φ) (h1 : f.eval a₀ ∈ maximalIdeal S)
    (h2 : IsUnit (f.derivative.eval a₀)) : ∃ a, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal S := by
  obtain ⟨g, hg, -, hgm⟩ := lifts_and_degree_eq_and_monic ((lifts_iff_coeff_lifts f).2 hlift) hf
  obtain ⟨b₀, rfl⟩ := ha
  have hmem : ∀ x, x ∈ maximalIdeal R ↔ φ x ∈ maximalIdeal S := fun x => by rw [← hc]; rfl
  have e1 : φ (g.eval b₀) = f.eval (φ b₀) := by rw [← hg, eval_map, eval₂_at_apply]
  have e2 : φ (g.derivative.eval b₀) = f.derivative.eval (φ b₀) := by
    rw [← hg, derivative_map, eval_map, eval₂_at_apply]
  have hu : IsUnit (g.derivative.eval b₀) := by
    by_contra hu
    have := (hmem _).1 ((mem_maximalIdeal _).2 hu)
    rw [e2] at this
    exact (mem_maximalIdeal _).1 this h2
  obtain ⟨b, hb, hbb⟩ := HenselianLocalRing.is_henselian g hgm b₀ ((hmem _).2 (e1 ▸ h1)) hu
  refine ⟨φ b, ?_, ?_⟩
  · rw [IsRoot.def] at hb ⊢
    rw [← hg, eval_map, eval₂_at_apply, hb, map_zero]
  · rw [← map_sub]; exact (hmem _).1 hbb

abbrev incMap (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [CommRing A] [Algebra κ A]
    (L : IntermediateField κ K) : A ⊗[κ] L →ₐ[A] A ⊗[κ] K :=
  Algebra.TensorProduct.map (AlgHom.id A A) L.val

theorem incMap_mono {κ K A : Type} [Field κ] [Field K] [Algebra κ K] [CommRing A] [Algebra κ A]
    {L L' : IntermediateField κ K} (h : L ≤ L') {x : A ⊗[κ] K} (hx : x ∈ (incMap κ K A L).range) :
    x ∈ (incMap κ K A L').range := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨Algebra.TensorProduct.map (AlgHom.id A A) (IntermediateField.inclusion h) y, ?_⟩
  have : (incMap κ K A L').comp (Algebra.TensorProduct.map (AlgHom.id A A) (IntermediateField.inclusion h))
      = incMap κ K A L := Algebra.TensorProduct.ext' (fun a l => by simp)
  exact congrArg (fun F : A ⊗[κ] L →ₐ[A] A ⊗[κ] K => F y) this

theorem exists_fd_range {κ K A : Type} [Field κ] [Field K] [Algebra κ K] [Algebra.IsIntegral κ K] [CommRing A]
    [Algebra κ A] (s : Finset (A ⊗[κ] K)) :
    ∃ L : IntermediateField κ K, FiniteDimensional κ L ∧ ∀ x ∈ s, x ∈ (incMap κ K A L).range := by
  have one : ∀ x : A ⊗[κ] K, ∃ L : IntermediateField κ K, FiniteDimensional κ L ∧ x ∈ (incMap κ K A L).range := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨⊥, inferInstance, zero_mem _⟩
    | tmul a k =>
      refine ⟨IntermediateField.adjoin κ {k},
        IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral k), ?_⟩
      exact ⟨a ⊗ₜ ⟨k, IntermediateField.mem_adjoin_simple_self κ k⟩, by simp⟩
    | add x y hx hy =>
      obtain ⟨L₁, h₁, hx⟩ := hx
      obtain ⟨L₂, h₂, hy⟩ := hy
      exact ⟨L₁ ⊔ L₂, inferInstance, add_mem (incMap_mono le_sup_left hx) (incMap_mono le_sup_right hy)⟩
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊥, inferInstance, by simp⟩
  | insert a s _ ih =>
    obtain ⟨L₁, h₁, ha⟩ := one a
    obtain ⟨L₂, h₂, hs⟩ := ih
    refine ⟨L₁ ⊔ L₂, inferInstance, ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact incMap_mono le_sup_left ha
    · exact incMap_mono le_sup_right (hs x hx)

theorem SHInsepHens_of (hL : SHInsepLoc) : SHInsepHens := by
  intro κ K A _ _ _ _ _ _ hA _
  have hA' := hA
  obtain ⟨_, -⟩ := hA'
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a₀ h1 h2
  classical
  obtain ⟨L, hFD, hs⟩ := exists_fd_range (A := A) (insert a₀ (f.support.image f.coeff))
  have : IsLocalRing (A ⊗[κ] L) := hL κ L A hA
  have : HenselianLocalRing (A ⊗[κ] L) := GlobalTheory.henselianLocalRing_of_finite A _
  have hint : (incMap κ K A L).toRingHom.IsIntegral := by
    refine RingHom.IsIntegral.tower_top (algebraMap A (A ⊗[κ] L)) _ ?_
    have e : (incMap κ K A L).toRingHom.comp (algebraMap A (A ⊗[κ] L)) = algebraMap A (A ⊗[κ] K) :=
      (incMap κ K A L).comp_algebraMap
    rw [e]
    exact fun x => Algebra.IsIntegral.isIntegral (R := A) x
  have hc : (maximalIdeal (A ⊗[κ] K)).comap (incMap κ K A L).toRingHom = maximalIdeal (A ⊗[κ] L) :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hint _)
  refine hens_root_of_sub (incMap κ K A L).toRingHom hc f hf a₀ ?_ ?_ h1 h2
  · intro n
    by_cases hn : n ∈ f.support
    · exact (AlgHom.mem_range _).1 (hs _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hn)))
    · exact ⟨0, by simp [Polynomial.notMem_support_iff.1 hn]⟩
  · exact (AlgHom.mem_range _).1 (hs _ (Finset.mem_insert_self _ _))

end LateralTheory.KummerTheory
