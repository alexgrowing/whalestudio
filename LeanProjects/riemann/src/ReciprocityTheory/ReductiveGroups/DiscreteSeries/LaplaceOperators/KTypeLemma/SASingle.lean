import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.EqZeroOfCoef

noncomputable section

open Finset Matrix Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D} {M : Type*} [AddCommGroup M] [Module ℂ M]

def aF (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ D) (w0 : H)
    (g : Matrix (Fin n) (Fin n) ℂ) : V →ₗ[ℂ] ℂ :=
  (innerₛₗ ℂ w0) ∘ₗ (σ g : H →ₗ[ℂ] H) ∘ₗ D.subtype ∘ₗ V.subtype

def Xi (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ D) (w0 : H)
    (EM : Fin n → Fin n → Module.End ℂ M) (φ : M) (l : M →ₗ[ℂ] ℂ) (c' : Fin n)
    (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) : KS (n := n) V →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun p => (ei X s c' p.2 * l (wB EM φ X s p.1)) • aF σ V w0 (ei X s)

theorem Xi_single (w0 : H) (EM : Fin n → Fin n → Module.End ℂ M) (φ : M) (l : M →ₗ[ℂ] ℂ) (c' : Fin n)
    (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    Xi σ V w0 EM φ l c' X s (Finsupp.single p v) =
      ei X s c' p.2 * l (wB EM φ X s p.1) * aF σ V w0 (ei X s) v := by
  simp [Xi]

theorem sA_single (hV : IsKStableSub ε E V) (a b : Fin n) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    sA ε E V hV a b (Finsupp.single p v) =
      (∑ w' ∈ (adLW a b p.1).support, adLW a b p.1 w' • Finsupp.single (w', p.2) v) +
      (if h : ε a = ε b then Finsupp.single p ⟨E a b v, hV a b h v v.2⟩ else 0) +
      (if p.2 = b then Finsupp.single (p.1, a) v else 0) := by
  simp only [sA, Finsupp.lsum_single, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Finsupp.lsingle_apply]
  congr 1
  · congr 1
    split_ifs <;> rfl
  · split_ifs <;> rfl

theorem deriv_aF (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (w0 : H)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (s : ℝ) (v : V) :
    HasDerivAt (fun s => aF σ V w0 (ei X s) v)
      (-⟪w0, σ (ei X s) ((actM E X (v : D) : D) : H)⟫_ℂ) s := by
  have h := coef_deriv hσ hD (exp_smul_mem_UJset hX (-s)) hX w0 (v : D)
  rw [← sub_self s] at h
  have h2 := h.scomp s ((hasDerivAt_id s).const_sub s)
  refine HasDerivAt.congr_deriv (h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)) ?_
  · show ⟪w0, σ (ei X t) _⟫_ℂ = ⟪w0, σ (_ * NormedSpace.exp (((s - t : ℝ) : ℂ) • X)) _⟫_ℂ
    rw [← exp_add_smul, show -s + (s - t) = -t by ring]; rfl
  · simp [ei]

theorem deriv_Xi (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKStableSub ε E V)
    (w0 : H) (EM : Fin n → Fin n → Module.End ℂ M) (φ : M) (l : M →ₗ[ℂ] ℂ) (c' : Fin n)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (s : ℝ) (y : KS (n := n) V) :
    HasDerivAt (fun s => Xi σ V w0 EM φ l c' X s y)
      (-(Xi σ V w0 EM φ l c' X s ((∑ a, ∑ b, X a b • sA ε E V hV a b) y))) s := by
  induction y using Finsupp.induction_linear with
  | zero => simpa using hasDerivAt_const s (0 : ℂ)
  | add y y' h h' =>
    simp only [map_add, neg_add]
    exact h.add h'
  | single p v =>
    simp only [Xi_single]
    refine ((((deriv_entries X 0 s c' p.2).1.mul (deriv_word EM φ X s p.1 l))).mul
      (deriv_aF hσ hD w0 hX.1 s v)).congr_deriv ?_
    set A := aF σ V w0 (ei X s) with hA
    set B := l (wB EM φ X s p.1) with hB
    have t1 : ∀ a b, Xi σ V w0 EM φ l c' X s
        (∑ w' ∈ (adLW a b p.1).support, adLW a b p.1 w' • Finsupp.single (w', p.2) v) =
        ei X s c' p.2 * l (Finsupp.linearCombination ℂ (wB EM φ X s) (adLW a b p.1)) * A v := by
      intro a b
      simp only [map_sum, map_smul, Xi_single, Finsupp.linearCombination_apply, Finsupp.sum,
        smul_eq_mul, mul_sum, sum_mul]
      exact sum_congr rfl fun _ _ => by ring
    have t2 : ∀ a b, X a b * Xi σ V w0 EM φ l c' X s
        (if h : ε a = ε b then Finsupp.single p ⟨E a b v, hV a b h v v.2⟩ else 0) =
        ei X s c' p.2 * B * (X a b * ⟪w0, σ (ei X s) ((E a b (v : D) : D) : H)⟫_ℂ) := by
      intro a b
      split_ifs with h
      · rw [Xi_single]
        show _ * (_ * ⟪w0, σ (ei X s) ((E a b (v : D) : D) : H)⟫_ℂ) = _
        ring
      · simp [inK_apply_eq_zero hX h]
    have t3 : ∀ a b, Xi σ V w0 EM φ l c' X s (if p.2 = b then Finsupp.single (p.1, a) v else 0) =
        if p.2 = b then ei X s c' a * B * A v else 0 := by
      intro a b
      split_ifs
      · rw [Xi_single]
      · exact map_zero _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sA_single, map_add,
      smul_eq_mul, mul_add, sum_add_distrib, t1, t2, t3, mul_ite, mul_zero, sum_ite_eq, mem_univ,
      if_true, adX, actM, Submodule.coe_sum, Submodule.coe_smul, inner_sum, inner_smul_right,
      Matrix.mul_apply, Pi.mul_apply, ← mul_sum, ← hB]
    have u1 : ∑ a, ∑ b, X a b * (ei X s c' p.2 *
        l (Finsupp.linearCombination ℂ (wB EM φ X s) (adLW a b p.1)) * A v) =
        ei X s c' p.2 * (∑ a, ∑ b, X a b *
          l (Finsupp.linearCombination ℂ (wB EM φ X s) (adLW a b p.1))) * A v := by
      simp only [mul_sum, sum_mul]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    have u3 : ∑ a, X a p.2 * (ei X s c' a * B * A v) = (∑ a, ei X s c' a * X a p.2) * B * A v := by
      simp only [sum_mul]
      exact sum_congr rfl fun _ _ => by ring
    rw [u1, u3]
    ring

theorem Xi_vanish (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) [FiniteDimensional ℂ V]
    (hV : IsKStableSub ε E V) (w0 : H) (EM : Fin n → Fin n → Module.End ℂ M) (φ : M) (l : M →ₗ[ℂ] ℂ)
    (c' : Fin n) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (W : Submodule ℂ (KS (n := n) V))
    (hW : IsKStableSub ε (sA ε E V hV) W) (h0 : ∀ y ∈ W, Xi σ V w0 EM φ l c' X 0 y = 0) (s : ℝ) :
    ∀ y ∈ W, Xi σ V w0 EM φ l c' X s y = 0 := by
  intro x hx
  set R := x.support.sup fun p => p.1.length with hR
  let S : Set (List (Fin n × Fin n) × Fin n) := {p | p.1.length ≤ R}
  have hSf : S.Finite := ((List.finite_length_le (Fin n × Fin n) R).prod Set.finite_univ).subset
    fun p hp => ⟨hp, trivial⟩
  have := hSf.to_subtype
  have : FiniteDimensional ℂ (Finsupp.supported V ℂ S) :=
    Module.Finite.equiv (Finsupp.supportedEquivFinsupp (M := V) (R := ℂ) S).symm
  have : FiniteDimensional ℂ (W ⊓ Finsupp.supported V ℂ S : Submodule ℂ _) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hS : ∀ a b, ∀ y ∈ Finsupp.supported V ℂ S, sA ε E V hV a b y ∈ Finsupp.supported V ℂ S := by
    intro a b y hy
    rw [← Finsupp.sum_single y, Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun p hp => ?_
    have hpS : p.1.length ≤ R := hy hp
    rw [sA_single]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun w' hw' =>
      Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℂ _ ?_)) ?_) ?_
    · show w'.length ≤ R
      rw [adLW_length a b _ _ hw']; exact hpS
    · split_ifs
      · exact Finsupp.single_mem_supported ℂ _ hpS
      · exact Submodule.zero_mem _
    · split_ifs
      · exact Finsupp.single_mem_supported ℂ _ hpS
      · exact Submodule.zero_mem _
  have hA : ∀ y ∈ W ⊓ Finsupp.supported V ℂ S,
      (∑ a, ∑ b, X a b • sA ε E V hV a b) y ∈ W ⊓ Finsupp.supported V ℂ S := by
    intro y hy
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    by_cases h : ε a = ε b
    · exact Submodule.smul_mem _ _ ⟨hW a b h y hy.1, hS a b y hy.2⟩
    · rw [inK_apply_eq_zero hX h, zero_smul]; exact Submodule.zero_mem _
  have key := ode_zero ((∑ a, ∑ b, X a b • sA ε E V hV a b).restrict hA)
    (fun s => Xi σ V w0 EM φ l c' X s ∘ₗ (W ⊓ Finsupp.supported V ℂ S).subtype)
    (fun s y => deriv_Xi hσ hD hV w0 EM φ l c' hX s y) (LinearMap.ext fun y => h0 y y.2.1) s
  exact LinearMap.congr_fun key
    ⟨x, hx, fun p hp => Finset.le_sup (f := fun p : List (Fin n × Fin n) × Fin n => p.1.length) hp⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA
