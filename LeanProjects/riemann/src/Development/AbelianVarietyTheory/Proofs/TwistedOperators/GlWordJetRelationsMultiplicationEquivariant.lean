import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.SphJet

theorem rev_ofFn_succ {A : Type} {m : ℕ} (α : Fin (m + 1) → A) :
    (List.ofFn α).reverse = α (Fin.last m) :: (List.ofFn (Fin.init α)).reverse := by
  rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
  rfl

theorem wordFun_move_letter {M : Type} [AddCommGroup M] {n : ℕ} (B : List (Fin n × Fin n) → M)
    (hB : ∀ (l₁ l₂ : List (Fin n × Fin n)) (a b c d : Fin n),
      B (l₁ ++ (a, b) :: (c, d) :: l₂) - B (l₁ ++ (c, d) :: (a, b) :: l₂) =
        (if b = c then B (l₁ ++ (a, d) :: l₂) else 0) - (if d = a then B (l₁ ++ (c, b) :: l₂) else 0))
    (c d : Fin n) : ∀ (m : ℕ) (α : Fin m → Fin n × Fin n) (p : List (Fin n × Fin n)),
      B (p ++ (c, d) :: (List.ofFn α).reverse) - B (p ++ ((List.ofFn α).reverse ++ [(c, d)])) =
        ∑ i, ((if d = (α i).1 then B (p ++ (List.ofFn (Function.update α i (c, (α i).2))).reverse) else 0) -
          (if (α i).2 = c then B (p ++ (List.ofFn (Function.update α i ((α i).1, d))).reverse) else 0)) := by
  intro m
  induction m with
  | zero => intro α p; simp
  | succ m ih =>
    intro α p
    rw [Fin.sum_univ_castSucc]
    have hl : ∀ q, (List.ofFn (Function.update α (Fin.last m) q)).reverse =
        q :: (List.ofFn (Fin.init α)).reverse := by
      intro q; rw [rev_ofFn_succ, Function.update_self, Fin.init_update_last]
    have hc : ∀ (i : Fin m) q, (List.ofFn (Function.update α i.castSucc q)).reverse =
        α (Fin.last m) :: (List.ofFn (Function.update (Fin.init α) i q)).reverse := by
      intro i q
      rw [rev_ofFn_succ, Function.update_of_ne (Fin.castSucc_ne_last i).symm, Fin.init_update_castSucc]
    simp only [hl, hc]
    have hi : ∀ i : Fin m, α i.castSucc = Fin.init α i := fun i => rfl
    simp only [hi]
    rw [rev_ofFn_succ α]
    have h1 := ih (Fin.init α) (p ++ [α (Fin.last m)])
    have h2 := hB p (List.ofFn (Fin.init α)).reverse c d (α (Fin.last m)).1 (α (Fin.last m)).2
    simp only [List.append_assoc, List.cons_append, List.nil_append, Prod.mk.eta] at h1 h2 ⊢
    rw [← h1, ← h2]
    abel

theorem jetRel_equivariant : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (m : ℕ), LowData ε E Λ u j → JetRel ε E Λ u j B → ∀ c d : Fin n, ε c = ε d → ∀ y y' : W, j y' = E d c (j y) → ∀ G G' : (Fin m → Fin n × Fin n) → W, arrTo V n m (fun α => j (G' α)) = arrE E m c d (arrTo V n m fun α => j (G α)) → ∑ α, B (List.ofFn α).reverse y (G' α) = ∑ α, B (List.ofFn α).reverse y' (G α) := by
  intro V W _ _ _ _ n ε E Λ u j B m hL hJ c d hcd y y' hy G G' hG
  have hex : ∀ x : W, ∃ x' : W, j x' = E c d (j x) := by
    intro x
    have h1 : j x ∈ kSpan ε E u := by
      rw [← hL.2.2.2.2]; exact ⟨x, rfl⟩
    have h2 := compact_span_compact_stable ε E u c d hcd _ h1
    rw [← hL.2.2.2.2] at h2
    exact h2
  choose T hT using hex
  have happ : ∀ (F : (Fin m → Fin n × Fin n) → V) α, arrTo V n m F α = F α := by
    intro F α; simp [arrTo]
  have hG' : ∀ α, G' α = ∑ i, ((if (α i).1 = c then G (Function.update α i (d, (α i).2)) else 0) -
      (if (α i).2 = d then G (Function.update α i ((α i).1, c)) else 0)) + T (G α) := by
    intro α
    apply j.injective
    have h := congrArg (fun F : Arr V n m => F α) hG
    simp only [arr_operator_apply, factorAction_apply', happ] at h
    rw [h, map_add, map_sum, hT]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hR : ∀ α : Fin m → Fin n × Fin n, B (List.ofFn α).reverse y' (G α) =
      ∑ i, ((if d = (α i).1 then B (List.ofFn (Function.update α i (c, (α i).2))).reverse y (G α) else 0) -
          (if (α i).2 = c then B (List.ofFn (Function.update α i ((α i).1, d))).reverse y (G α) else 0)) +
        B (List.ofFn α).reverse y (T (G α)) := by
    intro α
    have h := wordFun_move_letter (fun l => B l y (G α)) (fun l₁ l₂ a b c d => by
      have := congrArg (fun φ : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ => φ y (G α)) (hJ.1 l₁ l₂ a b c d)
      simp only [LinearMap.sub_apply] at this
      rw [this]
      split_ifs <;> simp) c d m α []
    simp only [List.nil_append] at h
    rw [← h, hJ.2.1 _ c d hcd y (G α) _ (hT _), hJ.2.2.1 _ c d hcd y y' _ hy]
    ring
  simp only [hR, hG', map_add, map_sum, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_sub, Finset.sum_sub_distrib]
  congr 1
  · refine ((Finset.sum_congr rfl fun α _ =>
      (apply_ite (B (List.ofFn α).reverse y) _ _ _).trans (by rw [map_zero]))).trans
      ((sum_update_first_index_swap i c d (fun α β => B (List.ofFn α).reverse y (G β))).trans ?_)
    refine Finset.sum_congr rfl fun β _ => ?_
    by_cases h : (β i).1 = d
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · exact ((Finset.sum_congr rfl fun α _ =>
      (apply_ite (B (List.ofFn α).reverse y) _ _ _).trans (by rw [map_zero]))).trans
      (sum_update_second_index_swap i c d (fun α β => B (List.ofFn α).reverse y (G β)))

end GlobalTheory.SphJet
