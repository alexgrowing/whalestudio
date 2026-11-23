import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.UnipotentFundamentalDomain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd

noncomputable section

open scoped TensorProduct
open Matrix

namespace MassDataMassesW.NRatW

section Gen

variable {E S : Type} [Field E] [CommRing S] (ψ : E →+* S) {n r : ℕ}

theorem up_span (e : Fin r → Fin n → E) (s : Set (Fin r)) {w : Fin n → E}
    (hw : w ∈ Submodule.span E (e '' s)) :
    (fun i => ψ (w i)) ∈ Submodule.span S ((fun b i => ψ (e b i)) '' s) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact Submodule.subset_span ⟨b, hb, rfl⟩
  | zero =>
    have : (fun i => ψ ((0 : Fin n → E) i)) = 0 := by funext i; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun i => ψ ((x + y) i)) = (fun i => ψ (x i)) + (fun i => ψ (y i)) := by funext i; simp
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have : (fun i => ψ ((c • x) i)) = ψ c • (fun i => ψ (x i)) := by funext i; simp
    rw [this]; exact Submodule.smul_mem _ _ hx

theorem map_sub_one_mulVec (M : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    (M.map ψ - 1) *ᵥ (fun i => ψ (x i)) = fun i => ψ (((M - 1) *ᵥ x) i) := by
  funext i
  rw [RingHom.map_mulVec]
  have h : (M - 1).map ψ = M.map ψ - 1 := by
    ext a b
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, map_sub]
    split_ifs <;> simp
  rw [h]
  rfl

theorem down_span (hψ : Function.Injective ψ) (e K : Fin r → Fin n → E)
    (hK : ∀ c b, ∑ j, K c j * e b j = if c = b then 1 else 0) (s : Set (Fin r)) (w : Fin n → E)
    (hw : (fun i => ψ (w i)) ∈ Submodule.span S ((fun b i => ψ (e b i)) '' s)) :
    w ∈ Submodule.span E (e '' s) := by
  classical
  set T := Finset.univ.filter (fun b => b ∈ s) with hT
  have key : ∀ x ∈ Submodule.span S ((fun b i => ψ (e b i)) '' s),
      x = ∑ b ∈ T, (∑ j, ψ (K b j) * x j) • (fun i => ψ (e b i)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      have h1 : ∀ b, (∑ j, ψ (K b j) * ψ (e c j)) = if b = c then 1 else 0 := by
        intro b
        have := congrArg ψ (hK b c)
        simp only [map_sum, map_mul] at this
        rw [this]; split_ifs <;> simp
      simp only [h1, ite_smul, one_smul, zero_smul]
      rw [Finset.sum_ite_eq' T c]
      rw [if_pos (by simp [hT, hc])]
    | zero => simp
    | add x y _ _ hx hy =>
      conv_lhs => rw [hx, hy]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← add_smul]
      congr 1
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    | smul c x _ hx =>
      conv_lhs => rw [hx]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_smul]
      congr 1
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
  have h := key _ hw
  have h2 : (fun i => ψ (w i)) = fun i => ψ ((∑ b ∈ T, (∑ j, K b j * w j) • e b) i) := by
    rw [h]
    funext i
    simp [Finset.sum_apply, map_sum, map_mul]
  have h3 : w = ∑ b ∈ T, (∑ j, K b j * w j) • e b := by
    funext i
    exact hψ (congrFun h2 i)
  rw [h3]
  refine Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, ?_, rfl⟩)
  simpa [hT] using hb

theorem perp_up (M : Matrix (Fin n) (Fin n) E) (e f K : Fin r → Fin n → E)
    (hKf : ∀ a b, ∑ j, K a j * f b j = if a = b then 1 else 0)
    (hrat : ∀ y : Fin n → E, (∀ a, ∑ j, K a j * y j = 0) →
      (M - 1) *ᵥ y ∈ Submodule.span E (Set.range e))
    (y : Fin n → S) (hy : ∀ a, ∑ j, ψ (K a j) * y j = 0) :
    (M.map ψ - 1) *ᵥ y ∈ Submodule.span S (Set.range fun b i => ψ (e b i)) := by
  classical
  set p : Fin n → Fin n → E := fun j => Pi.single j 1 - ∑ b, K b j • f b with hp
  have hpK : ∀ j a, ∑ i, K a i * p j i = 0 := by
    intro j a
    simp only [hp, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    have h1 : ∑ i, K a i * (Pi.single j (1 : E) : Fin n → E) i = K a j := by
      simp [Pi.single_apply]
    have h2 : ∑ b, ∑ i, K a i * (K b j * f b i) = K a j := by
      have : ∀ b, ∑ i, K a i * (K b j * f b i) = K b j * (if a = b then 1 else 0) := by
        intro b
        rw [← hKf a b, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [h1, h2, sub_self]
  have hy' : y = ∑ j, y j • (fun i => ψ (p j i)) := by
    funext i
    simp only [hp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, map_sub, map_sum, map_mul,
      mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    have h1 : ∑ j, y j * ψ ((Pi.single j (1 : E) : Fin n → E) i) = y i := by
      simp [Pi.single_apply]
    have h2 : ∑ j, ∑ b, y j * (ψ (K b j) * ψ (f b i)) = 0 := by
      rw [Finset.sum_comm]
      have : ∀ b, ∑ j, y j * (ψ (K b j) * ψ (f b i)) = (∑ j, ψ (K b j) * y j) * ψ (f b i) := by
        intro b
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
      simp only [this, hy, zero_mul, Finset.sum_const_zero]
    rw [h1, h2, sub_zero]
  rw [hy', Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Matrix.mulVec_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [map_sub_one_mulVec]
  have := up_span ψ e Set.univ (w := (M - 1) *ᵥ p j) (by rw [Set.image_univ]; exact hrat _ (hpK j))
  rwa [Set.image_univ] at this

end Gen

end MassDataMassesW.NRatW
