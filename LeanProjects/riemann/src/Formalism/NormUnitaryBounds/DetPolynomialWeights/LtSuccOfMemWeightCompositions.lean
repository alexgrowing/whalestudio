import Formalism.NormUnitaryBounds.Statement
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShearCoefficients

open MvPolynomial

noncomputable section

universe u

namespace Formalism.NormUnitaryCountingLemmas

namespace WeightCompositions

lemma weight_hom {σ M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] (g : M →+ M')
    (w : σ → M) (d : σ →₀ ℕ) :
    Finsupp.weight (fun i => g (w i)) d = g (Finsupp.weight w d) := by
  simp only [Finsupp.weight_apply, Finsupp.sum, map_sum, map_nsmul]

lemma weight_mapDomain {σ τ M : Type*} [AddCommMonoid M] (f : σ → τ) (w : τ → M)
    (d : σ →₀ ℕ) :
    Finsupp.weight w (Finsupp.mapDomain f d) = Finsupp.weight (fun i => w (f i)) d := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index]
  · intro; simp
  · intros; exact add_smul _ _ _

variable {N n : ℕ}

lemma sum_coordWt (d : (Fin N × Fin n) →₀ ℕ) :
    ∑ k, Finsupp.weight (coordWt N n) d k = ∑ p, d p := by
  simp only [Finsupp.weight_eq_sum, Finset.sum_apply, coordWt, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Pi.single_apply]

lemma sum_blockWt (d : (Fin N × Fin n) →₀ ℕ) :
    ∑ j, Finsupp.weight (blockWt N n) d j = ∑ p, d p := by
  simp only [Finsupp.weight_eq_sum, Finset.sum_apply, blockWt, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Pi.single_apply]

lemma weight_one (d : (Fin N × Fin n) →₀ ℕ) :
    Finsupp.weight (fun _ : Fin N × Fin n => (1 : ℕ)) d = ∑ p, d p := by
  simp [Finsupp.weight_eq_sum]

lemma weight_coordKWt (k : Fin n) (d : (Fin N × Fin n) →₀ ℕ) :
    Finsupp.weight (coordKWt N n k) d = Finsupp.weight (coordWt N n) d k := by
  simp only [Finsupp.weight_eq_sum, Finset.sum_apply, coordWt, coordKWt, Pi.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Pi.single_apply, eq_comm]

lemma comp_sum_components {σ M K : Type*} [Field K] [AddCommMonoid M] [DecidableEq M]
    (φ : σ → M) (S : Finset M) (g : S → MvPolynomial σ K)
    (hg : ∀ m : S, g m ∈ weightedHomogeneousSubmodule K φ (m : M)) (m : S) :
    weightedHomogeneousComponent φ (m : M) (∑ m', g m') = g m := by
  rw [map_sum]
  rw [Finset.sum_congr rfl fun m' _ => weightedHomogeneousComponent_of_mem (m := (m : M)) (hg m')]
  rw [Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    rw [if_neg]
    exact fun h => hb (Subtype.ext h.symm)
  · simp

lemma finrank_eq_sum_components {σ M K : Type*} [Field K] [AddCommMonoid M] [DecidableEq M]
    (φ : σ → M) (V : Submodule K (MvPolynomial σ K)) [FiniteDimensional K V] (S : Finset M)
    (hcomp : ∀ F ∈ V, ∀ m, weightedHomogeneousComponent φ m F ∈ V)
    (hS : ∀ F ∈ V, ∀ m ∉ S, weightedHomogeneousComponent φ m F = 0) :
    Module.finrank K V =
      ∑ m ∈ S, Module.finrank K ↥(V ⊓ weightedHomogeneousSubmodule K φ m) := by
  classical
  let W : S → Submodule K (MvPolynomial σ K) :=
    fun m => V ⊓ weightedHomogeneousSubmodule K φ (m : M)
  have : ∀ m : S, FiniteDimensional K (W m) :=
    fun m => Submodule.finiteDimensional_of_le inf_le_left
  let Φ : V →ₗ[K] (∀ m : S, W m) := LinearMap.pi fun m =>
    { toFun := fun F => ⟨weightedHomogeneousComponent φ (m : M) (F : MvPolynomial σ K),
        hcomp F F.2 m, weightedHomogeneousComponent_mem _ _ _⟩
      map_add' := by intro a b; ext1; simp
      map_smul' := by intro c a; ext1; simp }
  have hΦ : ∀ F m, ((Φ F m : W m) : MvPolynomial σ K) =
      weightedHomogeneousComponent φ (m : M) (F : MvPolynomial σ K) := fun F m => rfl
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro F hF
    have h0 : ∀ m, weightedHomogeneousComponent φ m (F : MvPolynomial σ K) = 0 := by
      intro m
      by_cases hm : m ∈ S
      · have := congrArg Subtype.val (congrFun hF ⟨m, hm⟩)
        rw [hΦ] at this
        simpa using this
      · exact hS F F.2 m hm
    apply Subtype.ext
    ext d
    have := congrArg (coeff d) (h0 (Finsupp.weight φ d))
    rw [coeff_weightedHomogeneousComponent, if_pos rfl] at this
    simpa using this
  have hsurj : Function.Surjective Φ := by
    intro g
    refine ⟨⟨∑ m : S, ((g m : W m) : MvPolynomial σ K),
      Submodule.sum_mem _ fun m _ => (g m).2.1⟩, ?_⟩
    funext m
    apply Subtype.ext
    rw [hΦ]
    exact comp_sum_components φ S (fun m : S => ((g m : W m) : MvPolynomial σ K))
      (fun m : S => (g m).2.2) m
  rw [(LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_pi_fintype]
  exact Finset.sum_coe_sort S (fun m => Module.finrank K ↥(V ⊓ weightedHomogeneousSubmodule K φ m))

variable {K : Type u} [Field K] (ν : Fin N → ℕ)

lemma mem_block {F : MvPolynomial (Fin N × Fin n) K} (hF : F ∈ H K ν) :
    F ∈ weightedHomogeneousSubmodule K (blockWt N n) ν := by
  unfold H at hF
  exact (Submodule.mem_inf.mp hF).1

lemma H_le_total :
    H K (n := n) ν ≤
      weightedHomogeneousSubmodule K (fun _ : Fin N × Fin n => (1 : ℕ)) (∑ j, ν j) := by
  intro F hF
  have hb := mem_block ν hF
  rw [mem_weightedHomogeneousSubmodule] at hb ⊢
  intro d hd
  rw [weight_one, ← sum_blockWt, hb hd]

instance finiteDimensional_H : FiniteDimensional K (H K (n := n) ν) := by
  have : FiniteDimensional K
      (weightedHomogeneousSubmodule K (fun _ : Fin N × Fin n => (1 : ℕ)) (∑ j, ν j)) :=
    Module.Finite.iff_fg.mpr
      (weightedHomogeneousSubmodule_fg K _ (fun _ => one_ne_zero) _)
  exact Submodule.finiteDimensional_of_le (H_le_total ν)

def S0 (n s : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (s + 1)).filter (fun w => ∑ k, w k = s)

lemma mem_S0_of_sum_eq {s : ℕ} {w : Fin n → ℕ} (h : ∑ k, w k = s) : w ∈ S0 n s := by
  simp only [S0, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun k => ?_, h⟩
  rw [← h]
  exact Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))

lemma sum_eq_of_mem_weightCompositions {s : ℕ} {w : Fin n → ℕ} (h : w ∈ S0 n s) : ∑ k, w k = s :=
  (Finset.mem_filter.mp h).2

lemma lt_succ_of_mem_weightCompositions {s : ℕ} {w : Fin n → ℕ} (h : w ∈ S0 n s) (k : Fin n) : w k < s + 1 := by
  have := (Finset.mem_filter.mp h).1
  rw [Fintype.mem_piFinset] at this
  exact Finset.mem_range.mp (this k)

lemma comp_eq_zero {F : MvPolynomial (Fin N × Fin n) K} (hF : F ∈ H K ν) (w : Fin n → ℕ)
    (hw : w ∉ S0 n (∑ j, ν j)) : weightedHomogeneousComponent (coordWt N n) w F = 0 := by
  apply weightedHomogeneousComponent_eq_zero'
  intro d hd hdw
  apply hw
  have hb : Finsupp.weight (blockWt N n) d = ν := mem_block ν hF (mem_support_iff.mp hd)
  apply mem_S0_of_sum_eq
  rw [← hdw, sum_coordWt, ← sum_blockWt, hb]

lemma finrank_Hw_le (h3p : NormUnitaryPermutationInvariance.{u}) (σ : Equiv.Perm (Fin n)) (w : Fin n → ℕ) :
    Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) w) ≤
      Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) (w ∘ σ.symm)) := by
  let f : Fin N × Fin n → Fin N × Fin n := fun p => (p.1, σ p.2)
  have hf : Function.Injective f := by
    intro a b h
    simp only [f, Prod.mk.injEq] at h
    exact Prod.ext h.1 (σ.injective h.2)
  let g : (Fin n → ℕ) →+ (Fin n → ℕ) :=
    { toFun := fun v => v ∘ σ.symm, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hg : (fun i => coordWt N n (f i)) = fun i => g (coordWt N n i) := by
    funext i k
    simp only [coordWt, f, g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
      Pi.single_apply, Equiv.symm_apply_eq]
  have hmem : ∀ F ∈ H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) w,
      rename f F ∈ H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) (w ∘ σ.symm) := by
    intro F hF
    rw [Submodule.mem_inf] at hF ⊢
    refine ⟨h3p K N n ν σ F hF.1, ?_⟩
    have hw := hF.2
    rw [mem_weightedHomogeneousSubmodule] at hw ⊢
    intro d hd
    by_contra hne
    apply hd
    apply coeff_rename_eq_zero
    intro u hu
    by_contra hu0
    apply hne
    rw [← hu, weight_mapDomain, hg, weight_hom, hw hu0]
    rfl
  have : FiniteDimensional K
      ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) (w ∘ σ.symm)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  let L : ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) w) →ₗ[K]
      ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) (w ∘ σ.symm)) :=
    { toFun := fun F => ⟨rename f F, hmem F F.2⟩
      map_add' := by intros; ext1; simp
      map_smul' := by intros; ext1; simp }
  apply LinearMap.finrank_le_finrank_of_injective (f := L)
  intro a b hab
  apply Subtype.ext
  exact rename_injective f hf (congrArg Subtype.val hab)

lemma finrank_Hw_perm (h3p : NormUnitaryPermutationInvariance.{u}) (σ : Equiv.Perm (Fin n)) (w : Fin n → ℕ) :
    Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) (w ∘ σ)) =
      Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) w) := by
  apply le_antisymm
  · have h := finrank_Hw_le (K := K) ν h3p σ (w ∘ σ)
    have e : (w ∘ σ) ∘ σ.symm = w := by funext k; simp
    rwa [e] at h
  · have h := finrank_Hw_le (K := K) ν h3p σ.symm w
    rwa [Equiv.symm_symm] at h

def Dw (K : Type u) [Field K] (ν : Fin N → ℕ) (w : Fin n → ℕ) : ℕ :=
  Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) w)

lemma coordWt_to_coordKWt (k : Fin n) {w : Fin n → ℕ} {G : MvPolynomial (Fin N × Fin n) K}
    (hG : G ∈ weightedHomogeneousSubmodule K (coordWt N n) w) :
    G ∈ weightedHomogeneousSubmodule K (coordKWt N n k) (w k) := by
  rw [mem_weightedHomogeneousSubmodule] at hG ⊢
  intro d hd
  rw [weight_coordKWt, hG hd]

lemma finrank_T_inf (k : Fin n) (i : ℕ) (w : Fin n → ℕ) :
    Module.finrank K ↥((H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i) ⊓
        weightedHomogeneousSubmodule K (coordWt N n) w) =
      if w k = i then Dw K ν w else 0 := by
  split_ifs with h
  · have heq : (H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i) ⊓
        weightedHomogeneousSubmodule K (coordWt N n) w =
        H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) w := by
      apply le_antisymm
      · exact inf_le_inf_right _ inf_le_left
      · intro F hF
        rw [Submodule.mem_inf] at hF
        rw [Submodule.mem_inf, Submodule.mem_inf]
        exact ⟨⟨hF.1, h ▸ coordWt_to_coordKWt k hF.2⟩, hF.2⟩
    rw [heq]
    rfl
  · have heq : (H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i) ⊓
        weightedHomogeneousSubmodule K (coordWt N n) w = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro F hF
      by_contra hne
      rw [Submodule.mem_inf, Submodule.mem_inf] at hF
      apply h
      exact IsWeightedHomogeneous.inj_right hne (coordWt_to_coordKWt k hF.2) hF.1.2
    rw [heq]
    simp

lemma T_comp (h3w : NormUnitaryWeight.{u}) (k : Fin n) (i : ℕ) :
    ∀ F ∈ H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i, ∀ w,
      weightedHomogeneousComponent (coordWt N n) w F ∈
        H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i := by
  classical
  intro F hF w
  rw [Submodule.mem_inf] at hF ⊢
  refine ⟨h3w K N n ν F hF.1 w, ?_⟩
  have hi := hF.2
  rw [mem_weightedHomogeneousSubmodule] at hi ⊢
  intro d hd
  apply hi
  intro h0
  apply hd
  rw [coeff_weightedHomogeneousComponent, h0]
  simp

theorem count (h3p : NormUnitaryPermutationInvariance.{u}) (h3w : NormUnitaryWeight.{u}) (ν : Fin N → ℕ) (k : Fin n) :
    n * ∑ i ∈ Finset.range (∑ j, ν j + 1),
        i * Module.finrank K (H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i :
          Submodule K (MvPolynomial (Fin N × Fin n) K)) =
      (∑ j, ν j) * Module.finrank K (H K (n := n) ν) := by
  classical
  set s := ∑ j, ν j with hs

  have hT : ∀ i, Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i) =
      ∑ w ∈ S0 n s, if w k = i then Dw K ν w else 0 := by
    intro i
    have : FiniteDimensional K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i) :=
      Submodule.finiteDimensional_of_le inf_le_left
    rw [finrank_eq_sum_components (coordWt N n) _ (S0 n s) (T_comp ν h3w k i)
      (fun F hF w hw => comp_eq_zero ν (Submodule.mem_inf.mp hF).1 w hw)]
    exact Finset.sum_congr rfl fun w _ => finrank_T_inf ν k i w
  have hH : Module.finrank K (H K (n := n) ν) = ∑ w ∈ S0 n s, Dw K ν w :=
    finrank_eq_sum_components (coordWt N n) _ (S0 n s) (fun F hF w => h3w K N n ν F hF w)
      (fun F hF w hw => comp_eq_zero ν hF w hw)
  have hL : ∑ i ∈ Finset.range (s + 1),
      i * Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i) =
      ∑ w ∈ S0 n s, w k * Dw K ν w := by
    simp only [hT, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (lt_succ_of_mem_weightCompositions hw k))]
  have hA : ∀ k', ∑ w ∈ S0 n s, w k' * Dw K ν w = ∑ w ∈ S0 n s, w k * Dw K ν w := by
    intro k'
    let σ := Equiv.swap k k'
    let e : (Fin n → ℕ) ≃ (Fin n → ℕ) :=
      { toFun := fun w => w ∘ σ, invFun := fun w => w ∘ σ.symm,
        left_inv := fun w => by funext x; simp, right_inv := fun w => by funext x; simp }
    apply Finset.sum_equiv e
    · intro w
      constructor
      · intro hw
        apply mem_S0_of_sum_eq
        rw [← sum_eq_of_mem_weightCompositions hw]
        exact Equiv.sum_comp σ w
      · intro hw
        apply mem_S0_of_sum_eq
        rw [← sum_eq_of_mem_weightCompositions hw]
        exact (Equiv.sum_comp σ w).symm
    · intro w _
      show w k' * Dw K ν w = (w ∘ σ) k * Dw K ν (w ∘ σ)
      rw [Function.comp_apply, Equiv.swap_apply_left]
      unfold Dw
      rw [finrank_Hw_perm ν h3p σ w]
  rw [hL]
  calc n * ∑ w ∈ S0 n s, w k * Dw K ν w
      = ∑ k' : Fin n, ∑ w ∈ S0 n s, w k' * Dw K ν w := by
        rw [Finset.sum_congr rfl (fun k' _ => hA k'), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
    _ = ∑ w ∈ S0 n s, (∑ k', w k') * Dw K ν w := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ = ∑ w ∈ S0 n s, s * Dw K ν w :=
        Finset.sum_congr rfl fun w hw => by rw [sum_eq_of_mem_weightCompositions hw]
    _ = s * Module.finrank K (H K (n := n) ν) := by rw [← Finset.mul_sum, hH]

end WeightCompositions

end Formalism.NormUnitaryCountingLemmas
