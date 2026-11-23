import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomAlgebraicClosureApplyEqPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetOfRingHomCompEqOfFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFieldEmbeddingStalkOfFiniteStalkMapStatement

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.LevelFinite.finite_of_isAlgebraic : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (K0 : Subfield Ω), R.FG → (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → (∀ a : o, algebraMap o Ω a ∈ K0) → Algebra.IsAlgebraic K0 Ω → Module.Finite K0 Ω := by
  intro o Ω _ _ _ R K0 hfg hfrac ho halg
  obtain ⟨s, hs⟩ := hfg
  have hL : FiniteDimensional K0 (IntermediateField.adjoin K0 (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (halg.isAlgebraic x).isIntegral)
  have hR : ∀ a ∈ R, a ∈ IntermediateField.adjoin K0 (s : Set Ω) := by
    intro a ha
    rw [← hs] at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin K0 _ hx
    | algebraMap r => exact IntermediateField.algebraMap_mem _ (⟨_, ho r⟩ : K0)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have htop : IntermediateField.adjoin K0 (s : Set Ω) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, ha, c, hc, rfl⟩ := hfrac z
    exact div_mem (hR a ha) (hR c hc)
  rw [htop] at hL
  exact (IntermediateField.topEquiv (F := K0) (E := Ω)).toLinearEquiv.finiteDimensional

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  first
  | rfl
  | simp [spMap, ← Spec.map_comp]
  | (simp only [spMap]; rw [← Spec.map_comp]; rfl)

private theorem pow_injective_of_transcendental {Ω : Type} [Field Ω] (K0 : Subfield Ω) (z : Ω) (hz : Transcendental K0 z) :
    Function.Injective (fun m : ℕ => z ^ m) := by
  have h0 : z ≠ 0 := fun h => hz (h ▸ isAlgebraic_zero)
  have h1 : ∀ k : ℕ, 0 < k → z ^ k ≠ 1 := by
    intro k hk hzk
    apply hz
    refine ⟨Polynomial.X ^ k - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero hk 1, ?_⟩
    simp [hzk]
  have key : ∀ m m' : ℕ, m < m' → z ^ m = z ^ m' → False := by
    intro m m' h hmm
    apply h1 (m' - m) (Nat.sub_pos_of_lt h)
    have : z ^ m * z ^ (m' - m) = z ^ m * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, hmm]
    exact mul_left_cancel₀ (pow_ne_zero _ h0) this
  intro m m' hmm
  simp only at hmm
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key m m' h hmm
  · exact key m' m h hmm.symm

theorem GlobalTheory.LevelFinite.finite_ratio_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (X : Scheme.{0}) (x : Sp R ⟶ X) (I : Type) [Finite I] (v : I → R), R.FG → (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → ((spMap R.val.toRingHom ≫ x).stalkMap (genericPoint (Sp Ω))).hom.Finite → (∀ (K : Type) [Field K] [IsAlgClosed K] (c : I → K), Set.Finite {y : Sp K ⟶ X | ∃ σ : R →+* K, spMap σ ≫ x = y ∧ ∃ u : K, u ≠ 0 ∧ ∀ i, σ (v i) = u * c i}) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {z | ∃ i i', z = (v i : Ω) / (v i' : Ω)})) Ω := by
  intro o Ω _ _ _ R X x I _ v hfg hfrac hfin hpts
  refine GlobalTheory.LevelFinite.finite_of_isAlgebraic o Ω R _ hfg hfrac
    (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩)) ⟨fun z => ?_⟩
  by_contra hz
  obtain ⟨φ, hφ, hφeq⟩ := GlobalTheory.T.exists_finite_fieldEmbedding_stalk_of_finite_stalkMap Ω X (spMap R.val.toRingHom ≫ x) hfin
  have hτ : ∀ m : ℕ, ∃ τ : Ω →ₐ[Subfield.closure (Set.range (algebraMap o Ω) ∪
      {z | ∃ i i', z = (v i : Ω) / (v i' : Ω)})] AlgebraicClosure Ω,
      τ z = algebraMap Ω (AlgebraicClosure Ω) z ^ (m + 1) :=
    fun m => GlobalTheory.T.exists_algHom_algebraicClosure_apply_eq_pow' Ω _ z hz (m + 1) m.succ_pos
  choose τ hτ using hτ
  have hfib : ∀ y : Sp (AlgebraicClosure Ω) ⟶ X,
      Set.Finite {τ' : Ω →+* AlgebraicClosure Ω | spMap τ' ≫ spMap R.val.toRingHom ≫ x = y} := by
    intro y
    by_cases hne : ∃ τ0 : Ω →+* AlgebraicClosure Ω, spMap τ0 ≫ spMap R.val.toRingHom ≫ x = y
    · obtain ⟨τ0, hτ0⟩ := hne
      refine (GlobalTheory.T.finite_setOf_ringHom_comp_eq_of_finite' _ Ω _ φ (τ0.comp φ) hφ).subset ?_
      intro τ' hτ'
      exact hφeq _ τ' τ0 (hτ'.trans hτ0.symm)
    · convert Set.finite_empty
      ext τ'
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hne ⟨τ', h⟩
  have hS := hpts (AlgebraicClosure Ω) (fun i => algebraMap Ω (AlgebraicClosure Ω) (v i))
  have hinj : Function.Injective (fun m : ℕ => ((τ m : Ω →ₐ[_] AlgebraicClosure Ω) : Ω →+* AlgebraicClosure Ω)) := by
    intro m m' hmm
    have h1 : τ m z = τ m' z := by
      simpa using congrArg (fun f : Ω →+* AlgebraicClosure Ω => f z) hmm
    rw [hτ, hτ, ← map_pow, ← map_pow] at h1
    exact Nat.succ_injective (pow_injective_of_transcendental _ z hz ((algebraMap Ω (AlgebraicClosure Ω)).injective h1))
  apply Set.infinite_range_of_injective hinj
  refine (hS.biUnion (fun y _ => hfib y)).subset ?_
  rintro _ ⟨m, rfl⟩
  refine Set.mem_biUnion (x := spMap ((τ m : Ω →+* AlgebraicClosure Ω)) ≫ spMap R.val.toRingHom ≫ x) ?_ rfl
  refine ⟨((τ m : Ω →+* AlgebraicClosure Ω)).comp R.val.toRingHom, by rw [spMap_comp_moduli_spaces, Category.assoc], ?_⟩
  by_cases h : ∃ i, (v i : Ω) ≠ 0
  · obtain ⟨i0, hi0⟩ := h
    have hc0 : algebraMap Ω (AlgebraicClosure Ω) (v i0) ≠ 0 := by
      exact (map_ne_zero _).mpr hi0
    have hτ0 : τ m (v i0) ≠ 0 := by
      exact (map_ne_zero _).mpr hi0
    refine ⟨τ m (v i0) / algebraMap Ω (AlgebraicClosure Ω) (v i0), div_ne_zero hτ0 hc0, fun i => ?_⟩
    have hr : (v i : Ω) / (v i0 : Ω) ∈ Subfield.closure (Set.range (algebraMap o Ω) ∪
        {z | ∃ i i', z = (v i : Ω) / (v i' : Ω)}) := Subfield.subset_closure (Or.inr ⟨i, i0, rfl⟩)
    have hfix : τ m ((v i : Ω) / (v i0 : Ω)) = algebraMap Ω (AlgebraicClosure Ω) ((v i : Ω) / (v i0 : Ω)) := by
      have := (τ m).commutes ⟨_, hr⟩
      rw [IsScalarTower.algebraMap_apply _ Ω (AlgebraicClosure Ω)] at this
      exact this
    have key : τ m (v i) = τ m ((v i : Ω) / (v i0 : Ω)) * τ m (v i0) := by
      rw [← map_mul, div_mul_cancel₀ _ hi0]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [show (R.val.toRingHom (v i) : Ω) = v i from rfl, key, hfix, map_div₀]
    ring
  · push_neg at h
    refine ⟨1, one_ne_zero, fun i => ?_⟩
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [show (R.val.toRingHom (v i) : Ω) = v i from rfl, h i]
    simp
