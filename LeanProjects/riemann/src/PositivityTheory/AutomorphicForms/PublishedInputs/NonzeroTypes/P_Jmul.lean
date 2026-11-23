import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace P_Jmul

theorem inPow_zero_of_KO {n : ℕ} {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (i j : Fin n) :
    InPow 0 ((g : Matrix (Fin n) (Fin n) k) i j) := by
  obtain ⟨g', rfl⟩ := hg
  exact ⟨(g' : Matrix (Fin n) (Fin n) 𝒪[k]) i j, by simp, rfl⟩

theorem inPow_mono {a b : ℕ} (hab : a ≤ b) {x : k} (hx : InPow b x) : InPow a x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, Ideal.pow_le_pow_right hab hy, rfl⟩

theorem inPow_mul {a b : ℕ} {x y : k} (hx : InPow a x) (hy : InPow b y) : InPow (a + b) (x * y) := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨x' * y', by rw [pow_add]; exact Ideal.mul_mem_mul hx' hy', map_mul _ _ _⟩

theorem inPow_add {a : ℕ} {x y : k} (hx : InPow a x) (hy : InPow a y) : InPow a (x + y) := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨x' + y', add_mem hx' hy', map_add _ _ _⟩

theorem inPow_zero (a : ℕ) : InPow a (0 : k) := ⟨0, zero_mem _, map_zero _⟩

theorem inPow_sum {a : ℕ} {ι : Type} (s : Finset ι) (f : ι → k) (h : ∀ i ∈ s, InPow a (f i)) :
    InPow a (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using inPow_zero (k := k) a
  | cons i s hi ih =>
    rw [Finset.sum_cons]
    exact inPow_add (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

end P_Jmul

theorem step_Jmul {n : ℕ} (G : Grp k n) : JacquetMultiplicativeProp G := by
  intro hcc0 hcb g hg h hh
  have hcc := fun a b c => hcc0 G.s G.μ (fun a b => ⟨cc G.μ a b, hcb.2.2.2 a b⟩) a b c
  simp only [Grp.JSet, Set.mem_ofPred_eq] at hg hh ⊢
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hh1, hh2⟩ := hh
  refine ⟨mul_mem hg1 hh1, fun i j hij => ?_⟩
  rw [Units.val_mul, Matrix.mul_apply]
  refine P_Jmul.inPow_sum _ _ fun l _ => ?_
  rcases le_or_gt (G.bl l) (G.bl j) with hl | hl
  · have hp := P_Jmul.inPow_mul (hg2 i l (lt_of_le_of_lt hl hij)) (P_Jmul.inPow_zero_of_KO hh1 l j)
    rw [add_zero] at hp
    exact P_Jmul.inPow_mono (G.ball _ _ _ _ hl hij le_rfl) hp
  rcases le_or_gt (G.bl i) (G.bl l) with hl' | hl'
  · have hp := P_Jmul.inPow_mul (P_Jmul.inPow_zero_of_KO hg1 i l) (hh2 l j (lt_of_lt_of_le hij hl'))
    rw [zero_add] at hp
    exact P_Jmul.inPow_mono (G.ball _ _ _ _ le_rfl hij hl') hp
  · have hp := P_Jmul.inPow_mul (hg2 i l hl') (hh2 l j hl)
    refine P_Jmul.inPow_mono ?_ hp
    exact le_trans (hcc (G.bl j) (G.bl l) (G.bl i)).2.2
      (max_le (Nat.le_add_left _ _) (Nat.le_add_right _ _))

end UpperTheory.TNZ.Grp
