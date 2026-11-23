import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcEvGLGenPtInt

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qc_colH_succ_le {n : ℕ} (mu : Fin n → ℤ) (c : ℤ) : colH mu (c + 1) ≤ colH mu c := by
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
  omega

lemma qc_canT_std {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : StdT (canT mu) := by
  intro c hc t
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro x hx
  simp only [canT, Finset.mem_map, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  exact ⟨⟨a.1, lt_of_lt_of_le a.2 (qc_colH_succ_le mu c)⟩, rfl⟩

section SMu

variable {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}

lemma qc_prim (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β)
    (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I) (m : ℤ)
    (hm : ∀ i, m ∣ ph i (canT mu)) : m ∣ 1 := by
  classical
  have : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _
  choose q hq using hm
  have hy : ∑ i, q i • β i ∈ Submodule.span ℤ (Set.range fun I : {I : TIdx mu // StdT I} => brk mu I.1) := by
    rw [(hS n mu hmu).2, ← hβ.2.1]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy
  have hcan : brk mu (canT mu) = m • ∑ i, q i • β i := by
    rw [← hph]
    simp only [zsmul_eq_mul, Finset.mul_sum, hq, Int.cast_mul, mul_assoc]
  let c0 : {I : TIdx mu // StdT I} := ⟨canT mu, qc_canT_std mu⟩
  have h0 : ∑ I : {I : TIdx mu // StdT I}, ((if I = c0 then 1 else 0) - m * r I) • brk mu I.1 = 0 := by
    have h2 : ∀ I : {I : TIdx mu // StdT I}, ((if I = c0 then 1 else 0) - m * r I) • brk mu I.1 =
        (if I = c0 then brk mu I.1 else 0) - (m : GLCoord ℤ n) * (r I • brk mu I.1) := by
      intro I
      split_ifs <;> simp [zsmul_eq_mul, sub_mul, mul_assoc]
    simp only [h2, Finset.sum_sub_distrib, ← Finset.mul_sum, hr, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_eq_zero, ← zsmul_eq_mul]
    exact hcan
  have h1 := Fintype.linearIndependent_iff.1 (hS n mu hmu).1 _ h0 c0
  simp only [if_true] at h1
  exact ⟨r c0, by linarith⟩

theorem qc_colFam_SMu (hA : LemmaA) (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β) :
    Nonempty (ColFam M) := by
  classical
  have hex : ∀ I : TIdx mu, ∃ c : M.ι → ℤ, ∑ i, c i • β i = brk mu I := fun I =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (by rw [hβ.2.1]; exact Submodule.subset_span ⟨I, rfl⟩)
  choose c hc using hex
  let ph : Matrix M.ι (TIdx mu) ℤ := fun i I => c I i
  have hph : ∀ I, ∑ i, ph i I • β i = brk mu I := hc
  have hpr := qc_prim hS hmu hβ ph hph
  refine ⟨{ J := Unit, mu := fun _ => mu, dom := fun _ => hmu, ph := fun _ => ph,
            equiv := fun _ => qc_equiv hA hS hmu hβ ph hph, indepP := ?_, indepQ := ?_, rank := ?_ }⟩
  · intro p hp nu
    have := Fact.mk hp
    rw [linearIndependent_subsingleton_index_iff]
    intro j h0
    have h1 := hpr (p : ℤ) fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (congrFun h0 i)
    have h2 : p ∣ 1 := by exact_mod_cast h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  · intro nu
    rw [linearIndependent_subsingleton_index_iff]
    intro j h0
    have h1 := hpr 0 fun i => by
      have := congrFun h0 i
      simp only [Pi.zero_apply, Int.cast_eq_zero] at this
      rw [this]
    simp at h1
  · simp [qc_card_eq hS hmu hβ]

end SMu

theorem qc_colFam_triv {n : ℕ} [NeZero n] (M : GLMod n) (h1 : Fintype.card M.ι = 1) (hA : ∀ i j, M.A i j = 1) :
    Nonempty (ColFam M) := by
  classical
  have hE : IsEmpty ↥(TCols (0 : Fin n → ℤ)) :=
    ⟨fun x => by simpa [TCols] using x.2⟩
  obtain ⟨i0, hi0⟩ := Fintype.card_eq_one_iff.1 h1
  have hU : Unique M.ι := ⟨⟨i0⟩, hi0⟩
  refine ⟨{ J := Unit, mu := fun _ => 0, dom := fun _ => fun _ _ _ => le_rfl, ph := fun _ => fun _ _ => 1,
            equiv := ?_, indepP := ?_, indepQ := ?_, rank := ?_ }⟩
  · intro _
    ext i I
    show (∑ k, M.A i k * (Int.castRingHom (GLCoord ℤ n)) 1) =
      ∑ K : TIdx (0 : Fin n → ℤ), (Int.castRingHom (GLCoord ℤ n)) 1 * TMat 0 K I
    simp [hA, TMat]
  · intro p hp nu
    have := Fact.mk hp
    rw [linearIndependent_subsingleton_index_iff]
    intro j h0
    simpa using congrFun h0 i0
  · intro nu
    rw [linearIndependent_subsingleton_index_iff]
    intro j h0
    simpa using congrFun h0 i0
  · have : Unique {I : TIdx (0 : Fin n → ℤ) // StdT I} :=
      ⟨⟨⟨canT 0, qc_canT_std 0⟩⟩, fun I => Subtype.ext (Subsingleton.elim _ _)⟩
    simp [h1, dMu]

end Formalism.InvariantFactorPaths.ColumnFamilies
