import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.MapStdPoly
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.SchurOrthogonality.URepSchur

open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.admitted

namespace FinOfPIAux

variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem inner_left (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (g : G) (v w : H) :
    ⟪σ g v, w⟫_ℂ = ⟪v, σ g⁻¹ w⟫_ℂ := by
  let U : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := hσ g }
  have h1 : ⟪σ g v, σ g (σ g⁻¹ w)⟫_ℂ = ⟪v, σ g⁻¹ w⟫_ℂ := U.inner_map_map v (σ g⁻¹ w)
  have h2 : σ g (σ g⁻¹ w) = w := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  rwa [h2] at h1

theorem star_eq (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (g : G) : star (σ g) = σ g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  rw [inner_left σ hσ g⁻¹, inv_inv]

theorem mem_unitary (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (g : G) :
    σ g ∈ unitary (H →L[ℂ] H) := by
  rw [Unitary.mem_iff, star_eq σ hσ, ← map_mul, ← map_mul, inv_mul_cancel, mul_inv_cancel, map_one]
  exact ⟨rfl, rfl⟩

theorem schur (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (T : H →L[ℂ] H) (hT : ∀ g v, T (σ g v) = σ g (T v)) : ∃ c : ℂ, ∀ v, T v = c • v := by
  rcases subsingleton_or_nontrivial H with h | h
  · exact ⟨0, fun v => Subsingleton.elim _ _⟩
  let _ : TopologicalSpace G := ⊥
  have : DiscreteTopology G := ⟨rfl⟩
  let π : CompanionTheory.LimBd.URep.UnitaryRep G H :=
    { toHom := σ.codRestrict (unitary (H →L[ℂ] H)) (mem_unitary σ hσ)
      continuous_orbit' := fun v => continuous_of_discreteTopology }
  have hπ : π.IsIrreducible := ⟨h, fun S hS hinv => hirr S hS fun g v hv => hinv g v hv⟩
  obtain ⟨c, hc⟩ := hπ.exists_eq_smul_one (T := T) (fun g v => hT g v)
  exact ⟨c, fun v => by rw [hc]; rfl⟩

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def diag (T : H →L[ℂ] H) : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm : (ι → H) →L[ℂ] PiLp 2 (fun _ : ι => H)).comp
    (ContinuousLinearMap.pi fun i => T.comp (PiLp.proj 2 (fun _ : ι => H) i))

omit [CompleteSpace H] [Fintype ι] [DecidableEq ι] in
@[simp] theorem diag_apply (T : H →L[ℂ] H) (z : PiLp 2 (fun _ : ι => H)) (i : ι) : diag T z i = T (z i) := rfl

def incl (j : ι) : H →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm : (ι → H) →L[ℂ] PiLp 2 (fun _ : ι => H)).comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => H) j)

omit [CompleteSpace H] [Fintype ι] in
theorem incl_apply (j : ι) (v : H) (i : ι) : incl j v i = (Pi.single j v : ι → H) i := rfl

omit [CompleteSpace H] in
theorem sum_incl (z : PiLp 2 (fun _ : ι => H)) : ∑ j, incl j (z j) = z := by
  ext i
  simp [incl_apply, Pi.single_apply]

omit [CompleteSpace H] in
theorem diag_incl (T : H →L[ℂ] H) (j : ι) (v : H) : diag T (incl j v) = incl j (T v) := by
  ext i
  rw [diag_apply, incl_apply, incl_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

omit [CompleteSpace H] [DecidableEq ι] in
theorem proj_comm (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (C : Submodule ℂ (PiLp 2 (fun _ : ι => H))) [C.HasOrthogonalProjection]
    (hC : ∀ g, ∀ z ∈ C, diag (σ g) z ∈ C) (g : G) (z : PiLp 2 (fun _ : ι => H)) :
    C.starProjection (diag (σ g) z) = diag (σ g) (C.starProjection z) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hC g _ (C.starProjection_apply_mem z)
  · intro w hw
    rw [← map_sub]
    have h : ⟪diag (σ g) (z - C.starProjection z), w⟫_ℂ = ⟪z - C.starProjection z, diag (σ g⁻¹) w⟫_ℂ := by
      simp only [PiLp.inner_apply, diag_apply, inner_left σ hσ]
    rw [h]
    exact C.starProjection_inner_eq_zero z _ (hC _ _ hw)

theorem diag_mem (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (C : Submodule ℂ (PiLp 2 (fun _ : ι => H))) (hcl : IsClosed (C : Set (PiLp 2 (fun _ : ι => H))))
    (hC : ∀ g, ∀ z ∈ C, diag (σ g) z ∈ C) (T : H →L[ℂ] H) (z : PiLp 2 (fun _ : ι => H)) (hz : z ∈ C) :
    diag T z ∈ C := by
  have : CompleteSpace C := hcl.completeSpace_coe
  have hs : ∀ i j : ι, ∃ c : ℂ, ∀ v, C.starProjection (incl j v) i = c • v := by
    intro i j
    refine schur σ hσ hirr ((PiLp.proj 2 (fun _ : ι => H) i).comp (C.starProjection.comp (incl j))) ?_
    intro g v
    show C.starProjection (incl j (σ g v)) i = σ g (C.starProjection (incl j v) i)
    rw [← diag_incl, proj_comm σ hσ C hC, diag_apply]
  choose c hc using hs
  have hQ : ∀ (w : PiLp 2 (fun _ : ι => H)) (i : ι), C.starProjection w i = ∑ j, c i j • w j := by
    intro w i
    conv_lhs => rw [← sum_incl w, map_sum]
    simp [hc]
  have h1 : C.starProjection z = z := Submodule.starProjection_eq_self_iff.mpr hz
  have h2 : C.starProjection (diag T z) = diag T z := by
    ext i
    rw [hQ, diag_apply, ← h1, hQ, h1]
    simp
  exact Submodule.starProjection_eq_self_iff.mp h2

theorem sum_eq_zero (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (L : ι → H →L[ℂ] H) (y : ι → H) (h : ∀ g, ∑ k, L k (σ g (y k)) = 0) (T : H →L[ℂ] H) :
    ∑ k, L k (T (y k)) = 0 := by
  let Λ : PiLp 2 (fun _ : ι => H) →L[ℂ] H := ∑ k, (L k).comp (PiLp.proj 2 (fun _ : ι => H) k)
  have hΛ : ∀ z, Λ z = ∑ k, L k (z k) := fun z => by simp [Λ]
  let C : Submodule ℂ (PiLp 2 (fun _ : ι => H)) :=
    ⨅ g : G, LinearMap.ker ((Λ.comp (diag (σ g)) : PiLp 2 (fun _ : ι => H) →L[ℂ] H) :
      PiLp 2 (fun _ : ι => H) →ₗ[ℂ] H)
  have hmem : ∀ z, z ∈ C ↔ ∀ g, ∑ k, L k (σ g (z k)) = 0 := by
    intro z
    simp [C, hΛ]
  have hcl : IsClosed (C : Set (PiLp 2 (fun _ : ι => H))) := by
    simp only [C, Submodule.coe_iInf]
    exact isClosed_iInter fun g => (Λ.comp (diag (σ g))).isClosed_ker
  have hC : ∀ g, ∀ z ∈ C, diag (σ g) z ∈ C := by
    intro g z hz
    rw [hmem] at hz ⊢
    intro g'
    simpa using hz (g' * g)
  have := (hmem _).mp (diag_mem σ hσ hirr C hcl hC T (WithLp.toLp 2 y) ((hmem _).mpr h)) 1
  simpa using this

theorem word_update {R : Type*} [Ring R] (E : R) {n : ℕ} (f : Fin n → R) (k : Fin n) :
    ∃ A B : R, ∀ T, word E (List.ofFn (Function.update f k T)) = A * T * B := by
  induction n with
  | zero => exact k.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) k
    · refine ⟨E, word E (List.ofFn fun i => f i.succ), fun T => ?_⟩
      simp [List.ofFn_succ]
    · obtain ⟨A, B, h⟩ := ih (fun i => f i.succ) k
      refine ⟨E * f 0 * A, B, fun T => ?_⟩
      have h1 : (fun i : Fin n => Function.update f k.succ T i.succ) = Function.update (fun i => f i.succ) k T := by
        funext i
        by_cases hi : i = k
        · subst hi; simp
        · rw [Function.update_of_ne hi, Function.update_of_ne (fun e => hi (Fin.succ_injective _ e))]
      rw [List.ofFn_succ, word_cons, h1, h, Function.update_of_ne (Fin.succ_ne_zero _).symm]
      simp [mul_assoc]

theorem stdPoly_update {R : Type*} [Ring R] (E : R) {M : ℕ} (a : Fin M → R) (j : Fin M) :
    ∃ A B : Equiv.Perm (Fin M) → R, ∀ T, stdPoly E (Function.update a j T) = ∑ π, A π * T * B π := by
  have h : ∀ π : Equiv.Perm (Fin M), ∃ A B : R, ∀ T,
      word E (List.ofFn fun i => Function.update a j T (π i)) = A * T * B := by
    intro π
    obtain ⟨A, B, h⟩ := word_update E (fun i => a (π i)) (π.symm j)
    refine ⟨A, B, fun T => ?_⟩
    rw [← h]
    congr 2
    funext i
    by_cases hi : i = π.symm j
    · subst hi; simp
    · rw [Function.update_of_ne hi, Function.update_of_ne (fun e => hi (by rw [← e]; simp))]
  choose A B h using h
  refine ⟨fun π => ((Equiv.Perm.sign π : ℤ) : R) * A π, B, fun T => ?_⟩
  simp only [stdPoly, h, mul_assoc]

theorem stdPoly_all (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (E : H →L[ℂ] H) (M : ℕ) (h : ∀ g : Fin M → G, stdPoly E (fun i => σ (g i)) = 0) (a : Fin M → H →L[ℂ] H) :
    stdPoly E a = 0 := by
  have key : ∀ (s : Finset (Fin M)) (a : Fin M → H →L[ℂ] H), (∀ i, i ∉ s → ∃ g, σ g = a i) → stdPoly E a = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a ha
      choose g hg using fun i => ha i (Finset.notMem_empty i)
      have := h g
      simpa only [hg] using this
    | insert j s hj ih =>
      intro a ha
      obtain ⟨A, B, hAB⟩ := stdPoly_update E a j
      have h0 : ∀ g, stdPoly E (Function.update a j (σ g)) = 0 := by
        intro g
        apply ih
        intro i hi
        by_cases hij : i = j
        · subst hij; exact ⟨g, by simp⟩
        · rw [Function.update_of_ne hij]
          exact ha i (by simp [hij, hi])
      rw [← Function.update_eq_self j a, hAB]
      ext v
      have := sum_eq_zero σ hσ hirr A (fun π => B π v) (fun g => by
        have h1 := congrArg (fun X : H →L[ℂ] H => X v) ((hAB (σ g)).symm.trans (h0 g))
        simpa using h1) (a j)
      simpa using this
  exact key Finset.univ a fun i hi => absurd (Finset.mem_univ i) hi

section Rank

variable (E : H →L[ℂ] H) (M : ℕ) (φ : ℕ → H →L[ℂ] ℂ) (x : ℕ → H)

omit [CompleteSpace H] in
theorem word_range' (hφ : ∀ i ≤ M, ∀ j ≤ M, φ i (E (x j)) = if i = j then 1 else 0) (n k : ℕ) (hk : k + n = M) :
    word E ((List.range' k n).map fun a => (φ (a + 1)).smulRight (x a)) (x M) = E (x k) := by
  induction n generalizing k with
  | zero => simp [← hk]
  | succ n ih =>
    rw [List.range'_succ, List.map_cons, word_cons, mul_apply_eq_comp, mul_apply_eq_comp,
      ih (k + 1) (by omega), ContinuousLinearMap.smulRight_apply, hφ _ (by omega) _ (by omega)]
    simp

omit [CompleteSpace H] in
theorem word_cases (hφ : ∀ i ≤ M, ∀ j ≤ M, φ i (E (x j)) = if i = j then 1 else 0) (l : List ℕ)
    (hl : ∀ a ∈ l, a < M) :
    word E (l.map fun a => (φ (a + 1)).smulRight (x a)) (x M) = 0 ∨
      ∃ k, k + l.length = M ∧ l = List.range' k l.length := by
  induction l with
  | nil => exact Or.inr ⟨M, rfl, rfl⟩
  | cons a l ih =>
    have ha : a < M := hl a (by simp)
    rw [List.map_cons, word_cons, mul_apply_eq_comp, mul_apply_eq_comp]
    rcases ih (fun b hb => hl b (by simp [hb])) with h | ⟨k, hk, h⟩
    · left; rw [h]; simp
    · by_cases hak : a + 1 = k
      · right
        refine ⟨a, by simp; omega, ?_⟩
        rw [List.length_cons, List.range'_succ, hak, ← h]
      · left
        rw [h, word_range' E M φ x hφ _ k hk, ContinuousLinearMap.smulRight_apply, hφ _ (by omega) _ (by omega),
          if_neg hak]
        simp

theorem ofFn_val (M : ℕ) : (List.ofFn fun i : Fin M => (i : ℕ)) = List.range' 0 M := by
  apply List.ext_getElem <;> simp

omit [CompleteSpace H] in
theorem stdPoly_apply (hφ : ∀ i ≤ M, ∀ j ≤ M, φ i (E (x j)) = if i = j then 1 else 0) :
    stdPoly E (fun a : Fin M => (φ (a + 1)).smulRight (x a)) (x M) = E (x 0) := by
  have hm : ∀ π : Equiv.Perm (Fin M), (List.ofFn fun i => (φ (π i + 1)).smulRight (x (π i))) =
      (List.ofFn fun i => (π i : ℕ)).map fun a => (φ (a + 1)).smulRight (x a) := by
    intro π
    rw [List.map_ofFn]; rfl
  rw [stdPoly, sum_apply, Finset.sum_eq_single 1]
  · rw [hm]
    simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one, id]
    rw [ofFn_val, word_range' E M φ x hφ M 0 (by omega)]
  · intro π _ hπ
    rw [hm, mul_apply_eq_comp]
    rcases word_cases E M φ x hφ (List.ofFn fun i => (π i : ℕ)) (by simp [List.mem_ofFn]) with h | ⟨k, hk, h⟩
    · rw [h, map_zero]
    · exfalso
      apply hπ
      rw [List.length_ofFn] at hk h
      obtain rfl : k = 0 := by omega
      rw [← ofFn_val] at h
      ext i
      exact congrFun (List.ofFn_injective h) i
  · intro h; exact absurd (Finset.mem_univ _) h

end Rank

omit [CompleteSpace H] in
theorem exists_dual {n : ℕ} (y : Fin n → H) (hy : LinearIndependent ℂ y) :
    ∃ φ : Fin n → H →L[ℂ] ℂ, ∀ i j, φ i (y j) = if i = j then 1 else 0 := by
  let S := Submodule.span ℂ (Set.range y)
  have : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range y)
  let b := Module.Basis.span hy
  have h : ∀ i, ∃ ψ : H →L[ℂ] ℂ, ∀ s : S, ψ s = b.coord i s := by
    intro i
    obtain ⟨ψ, hψ, -⟩ := exists_extension_norm_eq S (LinearMap.toContinuousLinearMap (b.coord i))
    exact ⟨ψ, hψ⟩
  choose φ hφ using h
  refine ⟨φ, fun i j => ?_⟩
  have : (b j : H) = y j := congrArg Subtype.val (Module.Basis.span_apply hy j)
  rw [← this, hφ, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]

omit [CompleteSpace H] in
theorem rank_le (E : H →L[ℂ] H) (M : ℕ) (h : ∀ a : Fin M → H →L[ℂ] H, stdPoly E a = 0) :
    Module.rank ℂ (LinearMap.range (E : H →ₗ[ℂ] H)) ≤ M := by
  by_contra hlt
  have hle : ((M + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ (LinearMap.range (E : H →ₗ[ℂ] H)) := by
    rw [Nat.cast_succ]
    exact Cardinal.natCast_add_one_le_iff.mpr (not_le.mp hlt)
  obtain ⟨v, hv⟩ := Module.le_rank_iff.mp hle
  have hy : LinearIndependent ℂ fun i => (v i : H) :=
    hv.map' (LinearMap.range (E : H →ₗ[ℂ] H)).subtype (Submodule.ker_subtype _)
  obtain ⟨φ, hφ⟩ := exists_dual _ hy
  choose x hx using fun i => (v i).2
  have hx' : ∀ i, E (x i) = v i := hx
  let φ' : ℕ → H →L[ℂ] ℂ := fun i => if hi : i < M + 1 then φ ⟨i, hi⟩ else 0
  let x' : ℕ → H := fun i => if hi : i < M + 1 then x ⟨i, hi⟩ else 0
  have hφ' : ∀ i ≤ M, ∀ j ≤ M, φ' i (E (x' j)) = if i = j then 1 else 0 := by
    intro i hi j hj
    simp only [φ', x', dif_pos (Nat.lt_succ_of_le hi), dif_pos (Nat.lt_succ_of_le hj), hx', hφ, Fin.mk.injEq]
  have h1 := stdPoly_apply E M φ' x' hφ'
  rw [h] at h1
  have h2 := hφ' 0 (Nat.zero_le _) 0 (Nat.zero_le _)
  rw [← h1] at h2
  simp at h2

end FinOfPIAux

theorem finite_rank_of_irreducible_unitary : FinOfPI := by
  intro G _ H _ _ _ σ hσ hirr E M h
  have hr := FinOfPIAux.rank_le E M (FinOfPIAux.stdPoly_all σ hσ hirr E M h)
  exact ⟨Module.rank_lt_aleph0_iff.mp (hr.trans_lt (Cardinal.natCast_lt_aleph0 (n := M))),
    Module.finrank_le_of_rank_le hr⟩

end CompanionTheory.D.gk.admitted
