import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAvgClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerKAvgNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactAverageKFiniteFiniteRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRankOneIsAvg

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.Closed

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem exists_apply_eq (h : Std ε σ) (P : (H → H) → Prop) (a1 : ∀ g ∈ UJset ε, P (σ g))
    (a2 : ∀ T T' : H → H, P T → P T' → P (fun w => T w + T' w) ∧ P (fun w => T (T' w)))
    (a3 : ∀ (c : ℂ) (T : H → H), P T → P (fun w => c • T w))
    (a4 : ∀ e : KG ε → ℂ, KFinFun ε e → P (kAvg ε σ e)) (a5 : P (fun _ => 0))
    {a : H} (ha : a ≠ 0) {v : H} (hv : IsKFin ε σ v) : ∃ T : H → H, P T ∧ T a = v := by
  obtain ⟨c1, c2, c3, c4⟩ := kCoef_kAvg n ε H σ h.1
  let A : Submodule ℂ H :=
    { carrier := {x | ∃ T : H → H, P T ∧ T a = x}
      add_mem' := by
        rintro _ _ ⟨T, hT, rfl⟩ ⟨T', hT', rfl⟩
        exact ⟨_, (a2 T T' hT hT').1, rfl⟩
      zero_mem' := ⟨_, a5, rfl⟩
      smul_mem' := by
        rintro c _ ⟨T, hT, rfl⟩
        exact ⟨_, a3 c T hT, rfl⟩ }
  have hA : ∀ T : H → H, P T → ∀ x ∈ A, T x ∈ A := by
    rintro T hT _ ⟨T', hT', rfl⟩
    exact ⟨_, (a2 T T' hT hT').2, rfl⟩
  have haA : a ∈ A := ⟨_, a1 1 (one_mem_UJ ε), sigma_one h.1 a⟩
  have hdense : Dense (A : Set H) :=
    dense_of_irred h.2.1 (fun g hg x hx => hA _ (a1 g hg) x hx) ((Submodule.ne_bot_iff _).2 ⟨a, haA, ha⟩)
  have hrange : ∀ e : KG ε → ℂ, KFinFun ε e → ∀ w, kAvg ε σ e w ∈ A := by
    intro e he w
    have hc : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
    obtain ⟨m, b, c, -, -, -, hbc⟩ := kAvg_finite_rank n ε H σ h e he
    obtain ⟨Q, hQ⟩ := c3 e hc
    let F : Submodule ℂ H := Submodule.span ℂ (Set.range b)
    haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
    haveI : FiniteDimensional ℂ (A ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_inf_right A F
    have hcl : IsClosed (Q ⁻¹' ((A ⊓ F : Submodule ℂ H) : Set H)) :=
      (Submodule.closed_of_finiteDimensional _).preimage Q.continuous
    have hsub : (A : Set H) ⊆ Q ⁻¹' ((A ⊓ F : Submodule ℂ H) : Set H) := by
      intro x hx
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [hQ]; exact hA _ (a4 e he) x hx
      · rw [hQ, hbc]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have := closure_minimal hsub hcl (hdense w)
    rw [← hQ]
    exact (Submodule.mem_inf.1 this).1
  obtain ⟨S, hS, hvS, hK⟩ := hv
  haveI : FiniteDimensional ℂ (S ⊓ A : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S A
  obtain ⟨w, hw, y, hy, hvwy⟩ := (S ⊓ A).exists_add_mem_mem_orthogonal v
  have hyS : y ∈ S := by
    have := S.sub_mem hvS (Submodule.mem_inf.1 hw).1
    rwa [hvwy, add_sub_cancel_left] at this
  have hy0 : y = 0 := by
    by_contra hy0
    have hk := c1 y ⟨S, hS, hyS, hK⟩
    have hc : Continuous fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ := by
      obtain ⟨F, -, h1, h2, -⟩ := hk
      exact h2 _ h1
    exact c2 y hy0 (Submodule.inner_left_of_mem_orthogonal
      (Submodule.mem_inf.2 ⟨c4 _ hc S hS hK y hyS, hrange _ hk y⟩) hy)
  rw [hvwy, hy0, add_zero]
  exact (Submodule.mem_inf.1 hw).2

theorem rank_one_mem (h : Std ε σ) (P : (H → H) → Prop) (A1 : ∀ g ∈ UJset ε, P (σ g))
    (A2 : ∀ T T' : H → H, P T → P T' → P (fun w => T w + T' w) ∧ P (fun w => T (T' w)))
    (A3 : ∀ (c : ℂ) (T : H → H), P T → P (fun w => c • T w)) (A5 : P (fun _ => 0))
    {e : KG ε → ℂ} (hQavg : P (kAvg ε σ e)) {m : ℕ} {a c : Fin m → H} (ha : Orthonormal ℂ a)
    (hQ : ∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j) (k : Fin m) :
    P (fun w => ⟪c k, w⟫_ℂ • ∑ i, ⟪c i, c k⟫_ℂ • a i) := by
  obtain ⟨d, hd⟩ := h.2.2.2.1
  let V : Submodule ℂ (Fin m × Fin m → ℂ) :=
    Submodule.span ℂ ((fun g (p : Fin m × Fin m) => ⟪c p.1, σ g (a p.2)⟫_ℂ) '' UJset ε)
  have hV : ∀ M ∈ V, P (fun w => ∑ i, ∑ j, (M (i, j) * ⟪c j, w⟫_ℂ) • a i) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, hg, rfl⟩ := hM
      have := (A2 _ _ hQavg (A2 _ _ (A1 g hg) hQavg).2).2
      simp only [hQ, map_sum, map_smul, inner_sum, inner_smul_right, Finset.sum_smul] at this
      simpa only [mul_comm] using this
    | zero => simpa using A5
    | add M N _ _ hM hN =>
      simpa only [Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib] using (A2 _ _ hM hN).1
    | smul t M _ hM =>
      simpa only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, mul_assoc] using A3 t _ hM
  have hN : (fun p : Fin m × Fin m => if p.2 = k then ⟪c p.1, c k⟫_ℂ else 0) ∈ V := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have e : ∀ z : Fin m → H, φ (fun p => ⟪c p.1, z p.2⟫_ℂ) =
        ∑ j, ⟪∑ i, star (φ fun q => if (i, j) = q then 1 else 0) • c i, z j⟫_ℂ := fun z => by
      rw [LinearMap.pi_apply_eq_sum_univ, Fintype.sum_prod_type, Finset.sum_comm]
      simp [sum_inner, inner_smul_left, mul_comm]
    have hy := eq_zero_of_sum_coef hd ha (y := fun j => ∑ i, star (φ fun q => if (i, j) = q then 1 else 0) • c i)
      (fun g hg => by rw [← e fun j => σ g (a j)]; exact hφ _ (Submodule.subset_span ⟨g, hg, rfl⟩))
    have := e fun j => if j = k then c k else 0
    simp only [hy, inner_zero_left, Finset.sum_const_zero] at this
    refine Eq.trans (congrArg φ ?_) this
    funext p
    by_cases hp : p.2 = k <;> simp [hp]
  have := hV _ hN
  simp only [ite_mul, zero_mul, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  simpa only [Finset.smul_sum, smul_smul, mul_comm] using this

end GlobalTheory.TypeSum.Closed

namespace GlobalTheory.TypeSum

theorem rank_one_mem_of_closed : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ Q : (H → H) → Prop, (∀ g ∈ UJset ε, Q (σ g)) → (∀ T T' : H → H, Q T → Q T' → Q (fun w => T w + T' w) ∧ Q (fun w => T (T' w))) → (∀ (c : ℂ) (T : H → H), Q T → Q (fun w => c • T w)) → (∀ e : KG ε → ℂ, KFinFun ε e → Q (kAvg ε σ e)) → Q (fun _ => 0) → ∀ e : KG ε → ℂ, KFinFun ε e → ∃ (m : ℕ) (a c : Fin m → H), (∀ j, IsKFin ε σ (a j)) ∧ (∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j) ∧ ∀ j u, IsKFin ε σ u → Q (fun w => ⟪c j, w⟫_ℂ • u) := by
  intro n ε H _ _ _ σ h Q q1 q2 q3 q4 q5 e he
  obtain ⟨m, a, c, ha, haK, -, hQ⟩ := kAvg_finite_rank n ε H σ h e he
  refine ⟨m, a, c, haK, hQ, fun k u hu => ?_⟩
  obtain ⟨-, -, c3, -⟩ := kCoef_kAvg n ε H σ h.1
  let P : (H → H) → Prop := fun T => Q T ∧ ∀ (z : ℂ) (w : H), T (z • w) = z • T w
  have p1 : ∀ g ∈ UJset ε, P (σ g) := fun g hg => ⟨q1 g hg, fun z w => map_smul (σ g) z w⟩
  have p2 : ∀ T T' : H → H, P T → P T' → P (fun w => T w + T' w) ∧ P (fun w => T (T' w)) :=
    fun T T' hT hT' => ⟨⟨(q2 T T' hT.1 hT'.1).1, fun z w => by simp only [hT.2, hT'.2, smul_add]⟩,
      ⟨(q2 T T' hT.1 hT'.1).2, fun z w => by simp only [hT.2, hT'.2]⟩⟩
  have p3 : ∀ (c : ℂ) (T : H → H), P T → P (fun w => c • T w) :=
    fun c T hT => ⟨q3 c T hT.1, fun z w => by simp only [hT.2, smul_comm c z]⟩
  have p4 : ∀ e : KG ε → ℂ, KFinFun ε e → P (kAvg ε σ e) := by
    intro e he
    refine ⟨q4 e he, fun z w => ?_⟩
    have hc : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
    obtain ⟨L, hL⟩ := c3 e hc
    rw [← hL, ← hL, map_smul]
  have p5 : P (fun _ => 0) := ⟨q5, fun z w => (smul_zero z).symm⟩
  by_cases hk : c k = 0
  · have : (fun w => ⟪c k, w⟫_ℂ • u) = fun _ => 0 := by funext w; simp [hk]
    rw [this]; exact q5
  set b := ∑ i, ⟪c i, c k⟫_ℂ • a i with hb
  have hb0 : b ≠ 0 := by
    intro h0
    apply hk
    have := ha.inner_right_fintype (fun i => ⟪c i, c k⟫_ℂ) k
    rw [← hb, h0, inner_zero_right] at this
    exact inner_self_eq_zero.1 this.symm
  obtain ⟨T, hT, hTb⟩ := Closed.exists_apply_eq h P p1 p2 p3 p4 p5 hb0 hu
  have hR := Closed.rank_one_mem h P p1 p2 p3 p5 (p4 e he) ha hQ k
  have := (p2 T _ hT hR).2.1
  have e' : (fun w => T (⟪c k, w⟫_ℂ • b)) = fun w => ⟪c k, w⟫_ℂ • u := by
    funext w; rw [hT.2, hTb]
  rw [← e']; exact this

end GlobalTheory.TypeSum

end
