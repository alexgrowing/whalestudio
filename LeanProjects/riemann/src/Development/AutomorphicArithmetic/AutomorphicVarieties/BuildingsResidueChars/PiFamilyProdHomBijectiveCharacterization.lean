import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsotypicSeparatesAndEmbedsIntoInvariantSubspace
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne UpperTheory.V.Hi
open UpperTheory.V.W (Plc)

namespace UpperTheory.V.ProductGroupInvariantVectors

private def prodHom {R S : Type} [CommRing R] [Fintype S] [DecidableEq S] {H : S → Type} [∀ u, Group (H u)]
    {m : S → ℕ} (c : ∀ u, H u →* Matrix (Fin (m u)) (Fin (m u)) R) :
    (∀ u, H u) →* Matrix (∀ u, Fin (m u)) (∀ u, Fin (m u)) R where
  toFun k := Matrix.of fun i a => ∏ u, c u (k u) (i u) (a u)
  map_one' := by
    ext i a
    simp only [Matrix.of_apply, Pi.one_apply, map_one, Matrix.one_apply]
    by_cases h : i = a
    · subst h; simp
    · rw [if_neg h]
      obtain ⟨u, hu⟩ := Function.ne_iff.1 h
      exact Finset.prod_eq_zero (Finset.mem_univ u) (if_neg hu)
  map_mul' k k' := by
    ext i a
    simp only [Matrix.of_apply, Pi.mul_apply, map_mul, Matrix.mul_apply]
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]

private theorem prodHom_apply {R S : Type} [CommRing R] [Fintype S] [DecidableEq S] {H : S → Type}
    [∀ u, Group (H u)] {m : S → ℕ} (c : ∀ u, H u →* Matrix (Fin (m u)) (Fin (m u)) R)
    (k : ∀ u, H u) (i a : ∀ u, Fin (m u)) : prodHom c k i a = ∏ u, c u (k u) (i u) (a u) := rfl

private theorem sum_single {S : Type} [Fintype S] [DecidableEq S] {H : S → Type}
    [∀ u, Group (H u)] {m : S → ℕ} (c : ∀ u, H u →* Matrix (Fin (m u)) (Fin (m u)) ℂ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (f : (∀ u, Fin (m u)) → M) (u : S) (k : H u)
    (i : ∀ u, Fin (m u)) :
    ∑ a, prodHom c (Pi.mulSingle u k) i a • f a = ∑ b, c u k (i u) b • f (Function.update i u b) := by
  symm
  refine Finset.sum_of_injOn (fun b => Function.update i u b) ?_ ?_ ?_ ?_
  · intro b _ b' _ h
    exact Function.update_injective i u h
  · intro b _; simp
  · intro a _ ha
    have : ∃ v, v ≠ u ∧ i v ≠ a v := by
      by_contra hc
      apply ha
      refine ⟨a u, by simp, ?_⟩
      funext v
      by_cases hv : v = u
      · subst hv; simp
      · simp only [Function.update_of_ne hv]
        by_contra h2
        exact hc ⟨v, hv, h2⟩
    obtain ⟨v, hv, hne⟩ := this
    rw [prodHom_apply, Finset.prod_eq_zero (Finset.mem_univ v), zero_smul]
    rw [Pi.mulSingle_eq_of_ne hv, map_one, Matrix.one_apply_ne hne]
  · intro b _
    rw [prodHom_apply, Finset.prod_eq_single u]
    · simp
    · intro v _ hv
      rw [Pi.mulSingle_eq_of_ne hv, map_one, Function.update_of_ne hv, Matrix.one_apply_eq]
    · simp

private theorem inv_iff {S : Type} [Fintype S] [DecidableEq S] {H : S → Type}
    [∀ u, Group (H u)] {m : S → ℕ} (c : ∀ u, H u →* Matrix (Fin (m u)) (Fin (m u)) ℂ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (∀ u, H u) M)
    (F : (∀ u, Fin (m u)) → M) :
    (∀ k i, ∑ a, prodHom c k i a • ρ k (F a) = F i) ↔
      ∀ u (k : H u) i, ∑ b, c u k (i u) b • ρ (Pi.mulSingle u k) (F (Function.update i u b)) = F i := by
  constructor
  · intro h u k i
    rw [← h (Pi.mulSingle u k) i, sum_single c (fun a => ρ (Pi.mulSingle u k) (F a))]
  · intro h
    let A : (∀ u, H u) → ((∀ u, Fin (m u)) → M) → ((∀ u, Fin (m u)) → M) :=
      fun k F i => ∑ a, prodHom c k i a • ρ k (F a)
    have hmul : ∀ k k' F, A (k * k') F = A k (A k' F) := by
      intro k k' F
      funext i
      simp only [A, map_mul, Matrix.mul_apply, Module.End.mul_apply, map_sum, map_smul,
        Finset.smul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    have hone : ∀ F, A 1 F = F := by
      intro F
      funext i
      simp [A, Matrix.one_apply]
    let W : Subgroup (∀ u, H u) :=
      { carrier := {k | A k F = F}
        mul_mem' := by
          intro k k' hk hk'
          change A (k * k') F = F
          change A k F = F at hk
          change A k' F = F at hk'
          rw [hmul, hk', hk]
        one_mem' := hone F
        inv_mem' := by
          intro k hk
          change A k⁻¹ F = F
          change A k F = F at hk
          conv_lhs => rw [← hk]
          rw [← hmul, inv_mul_cancel, hone] }
    intro k i
    have hk : k ∈ W := by
      refine Subgroup.pi_mem_of_mulSingle_mem k fun u => ?_
      change A _ F = F
      funext i
      simp only [A]
      rw [sum_single c (fun a => ρ (Pi.mulSingle u (k u)) (F a))]
      exact h u (k u) i
    exact congrFun hk i

private theorem main {S : Type} [Fintype S] [DecidableEq S] {G : S → Type} [∀ u, Group (G u)]
    [∀ u, TopologicalSpace (G u)] [∀ u, IsTopologicalGroup (G u)] (K : ∀ u, Subgroup (G u)) {m : S → ℕ}
    (c : ∀ u, K u → Fin (m u) → Fin (m u) → ℂ)
    {M : Type} [AddCommGroup M] [Module ℂ M] [Nontrivial M] (ρ : Representation ℂ (∀ u, G u) M)
    (σ : ∀ u, SmIrr (G u)) (hσ : ∀ u, IsoSum (ρ.comp (MonoidHom.mulSingle G u)) ⊤ (σ u)) :
    (∃ F : (∀ u, Fin (m u)) → M, F ≠ 0 ∧ ∀ u (k : K u) i,
      ∑ b, c u k (i u) b • ρ (Pi.mulSingle u (k : G u)) (F (Function.update i u b)) = F i) ↔
    ∀ u, ∃ y : Fin (m u) → (σ u).V, y ≠ 0 ∧ ∀ (k : K u) i, ∑ a, c u k i a • (σ u).ρ k (y a) = y i := by
  constructor
  · rintro ⟨F, hF, h⟩ u
    obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hF
    obtain ⟨p, hp, hp0⟩ := (UpperTheory.isotypic_separates_and_embeds_into_invariant_subspace (G u) M _ (σ u) (hσ u)).1 (F i0) hi0
    refine ⟨fun a => p (F (Function.update i0 u a)), ?_, ?_⟩
    · intro h0
      apply hp0
      simpa using congrFun h0 (i0 u)
    · intro k b
      have h1 := congrArg p (h u k (Function.update i0 u b))
      simp only [Function.update_self, Function.update_idem, map_sum, map_smul] at h1
      beta_reduce
      rw [← h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← hp]; rfl
  · intro hy
    choose y hy0 hy using hy
    suffices hT : ∀ T : Finset S, ∃ F : (∀ u, Fin (m u)) → M, F ≠ 0 ∧ ∀ u ∈ T, ∀ (k : K u) i,
        ∑ b, c u k (i u) b • ρ (Pi.mulSingle u (k : G u)) (F (Function.update i u b)) = F i by
      obtain ⟨F, hF, h⟩ := hT Finset.univ
      exact ⟨F, hF, fun u => h u (Finset.mem_univ u)⟩
    choose b0 hb0 using fun u => Function.ne_iff.1 (hy0 u)
    intro T
    induction T using Finset.induction_on with
    | empty =>
      obtain ⟨x, hx⟩ := exists_ne (0 : M)
      exact ⟨fun _ => x, fun h => hx (congrFun h b0), by simp⟩
    | insert u T hu ih =>
      let Y : Submodule ℂ ((∀ u, Fin (m u)) → M) :=
        { carrier := {F | ∀ u ∈ T, ∀ (k : K u) i,
            ∑ b, c u k (i u) b • ρ (Pi.mulSingle u (k : G u)) (F (Function.update i u b)) = F i}
          add_mem' := by
            intro F F' hF hF' v hv k i
            simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
            rw [hF v hv k i, hF' v hv k i]
          zero_mem' := by intro v hv k i; simp
          smul_mem' := by
            intro r F hF v hv k i
            simp only [Pi.smul_apply, map_smul]
            rw [← hF v hv k i, Finset.smul_sum]
            exact Finset.sum_congr rfl fun b _ => smul_comm _ _ _ }
      have hY : Y ≠ ⊥ := by
        obtain ⟨F, hF, h⟩ := ih
        exact (Submodule.ne_bot_iff Y).2 ⟨F, h, hF⟩
      obtain ⟨s, hs, hsY, hsρ⟩ := (UpperTheory.isotypic_separates_and_embeds_into_invariant_subspace (G u) M _ (σ u) (hσ u)).2 _ Y hY (by
        intro g F hF v hv k i
        have hne : v ≠ u := fun h => hu (h ▸ hv)
        change ∑ b, c v k (i v) b • ρ (Pi.mulSingle v (k : G v))
          (ρ (Pi.mulSingle u g) (F (Function.update i v b))) = ρ (Pi.mulSingle u g) (F i)
        rw [← hF v hv k i, map_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_smul, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          (Pi.mulSingle_commute (Ne.symm hne) g (k : G v)).eq])
      have h0 : s (y u (b0 u)) ≠ 0 := fun h => hb0 u (hs (by rw [h]; simp))
      obtain ⟨i0, hi0⟩ := Function.ne_iff.1 h0
      refine ⟨fun i => s (y u (i u)) (Function.update i u (i0 u)), ?_, ?_⟩
      · intro h
        apply hi0
        simpa using congrFun h (Function.update i0 u (b0 u))
      · intro v hv k i
        rcases Finset.mem_insert.1 hv with rfl | hv
        · simp only [Function.update_self, Function.update_idem]
          rw [← hy v k (i v), map_sum, Finset.sum_apply]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [map_smul, Pi.smul_apply, hsρ]; rfl
        · have hne : v ≠ u := fun h => hu (h ▸ hv)
          have h1 := hsY (y u (i u)) v hv k (Function.update i u (i0 u))
          simp only [Function.update_of_ne hne] at h1
          beta_reduce
          rw [← h1]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Function.update_of_ne hne.symm, Function.update_comm hne]

end UpperTheory.V.ProductGroupInvariantVectors

open UpperTheory.V.ProductGroupInvariantVectors in
theorem UpperTheory.piFamilyProdHom_bijective_characterization :
    ∀ (O : Type) [CommRing O] (j : O →+* ℂ) (S : Type) [Fintype S] [DecidableEq S] (G : S → Type) [∀ u, Group (G u)] [∀ u, TopologicalSpace (G u)] [∀ u, IsTopologicalGroup (G u)] (K : ∀ u, Subgroup (G u)) (m : S → ℕ) (τ : ∀ u, K u →* GL (Fin (m u)) O), ∃ (m' : ℕ) (τ' : Subgroup.pi Set.univ K →* GL (Fin m') O), (∀ k : Subgroup.pi Set.univ K, (∀ u, τ u ⟨k.1 u, k.2 u trivial⟩ = 1) → τ' k = 1) ∧ ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [Nontrivial M] (ρ : Representation ℂ (∀ u, G u) M) (σ : ∀ u, SmIrr (G u)), (∀ u, IsoSum (ρ.comp (MonoidHom.mulSingle G u)) ⊤ (σ u)) → ((∃ F : Fin m' → M, F ≠ 0 ∧ ∀ (k : Subgroup.pi Set.univ K) i, ∑ a, j (τ' k i a) • ρ k (F a) = F i) ↔ ∀ u, ∃ y : Fin (m u) → (σ u).V, y ≠ 0 ∧ ∀ (k : K u) i, ∑ a, j (τ u k i a) • (σ u).ρ k (y a) = y i) := by
  intro O _ j S _ _ G _ _ _ K m τ
  let e := Fintype.equivFin (∀ u, Fin (m u))
  let r : Subgroup.pi Set.univ K →* (∀ u, K u) :=
    { toFun := fun k u => ⟨k.1 u, k.2 u trivial⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let t : ∀ u, K u →* Matrix (Fin (m u)) (Fin (m u)) O := fun u => (Units.coeHom _).comp (τ u)
  let c : ∀ u, K u →* Matrix (Fin (m u)) (Fin (m u)) ℂ := fun u => (j.mapMatrix.toMonoidHom).comp (t u)
  let Q : Subgroup.pi Set.univ K →* Matrix (Fin _) (Fin _) O :=
    ((Matrix.reindexAlgEquiv O O e).toMulEquiv.toMonoidHom).comp ((prodHom t).comp r)
  have hQ : ∀ k i a, Q k i a = ∏ u, t u (r k u) (e.symm i u) (e.symm a u) := fun _ _ _ => rfl
  refine ⟨_, Q.toHomUnits, ?_, ?_⟩
  · intro k hk
    apply Units.ext
    change Q k = 1
    rw [← map_one Q]
    ext i a
    rw [hQ, hQ]
    refine Finset.prod_congr rfl fun u _ => ?_
    have : t u (r k u) = t u (r 1 u) := by
      rw [map_one, Pi.one_apply, map_one]
      exact congrArg Units.val (hk u)
    rw [this]
  · intro M _ _ _ ρ σ hσ
    let ι : (∀ u, K u) →* (∀ u, G u) :=
      { toFun := fun k u => k u
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : ∀ u (k : K u), ι (Pi.mulSingle u k) = Pi.mulSingle u (k : G u) := by
      intro u k
      funext v
      change ((Pi.mulSingle u k : ∀ u, K u) v : G v) = _
      by_cases hv : v = u
      · subst hv; simp
      · simp [Pi.mulSingle_eq_of_ne hv]
    have hj : ∀ k i a, j (Q.toHomUnits k i a) = prodHom c (r k) (e.symm i) (e.symm a) := by
      intro k i a
      change j (Q k i a) = _
      rw [hQ, map_prod]; rfl
    refine Iff.trans ?_ (main K (fun u k i a => c u k i a) ρ σ hσ)
    have key := fun F => inv_iff c (ρ.comp ι) F
    simp only [MonoidHom.comp_apply, hι] at key
    simp only [← key, hj]
    constructor
    · rintro ⟨F, hF, h⟩
      refine ⟨fun i => F (e i), fun h0 => hF ?_, fun k i => ?_⟩
      · funext i
        simpa using congrFun h0 (e.symm i)
      · have h1 := h ⟨ι k, fun u _ => (k u).2⟩ (e i)
        beta_reduce
        rw [← h1, ← e.sum_comp]
        simp only [Equiv.symm_apply_apply]
        rfl
    · rintro ⟨F, hF, h⟩
      refine ⟨fun i => F (e.symm i), fun h0 => hF ?_, fun k i => ?_⟩
      · funext i
        simpa using congrFun h0 (e i)
      · beta_reduce
        rw [← h (r k) (e.symm i), ← e.symm.sum_comp]
        rfl
