import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.MemPw
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.CompIterateFrobenius

noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial

theorem fl_deg {k E : Type*} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [CharP E p]
    (hroot : ∀ a : k, ∃ w : E, w ^ (p ^ c) = algebraMap k E a) :
    (Pj E p c).relfinrank ⊤ = finrank k (Tw k p c) := by
  set f := algebraMap k E with hf
  set Fr := iterateFrobenius E p c with hFr
  set K : Subfield E := f.fieldRange with hK
  set Kq : Subfield E := (Fr.comp f).fieldRange with hKq
  have hmapK : K.map Fr = Kq := RingHom.map_fieldRange _ _
  have hmapT : (⊤ : Subfield E).map Fr = Pj E p c := map_top_Pj p c
  have h3 : Kq.relfinrank (Pj E p c) = K.relfinrank ⊤ := by
    rw [← hmapK, ← hmapT, Subfield.relfinrank_map_map]
  have h4 : Kq ≤ K := by
    intro y hy
    obtain ⟨a, rfl⟩ := RingHom.mem_fieldRange.1 hy
    exact RingHom.mem_fieldRange.2 ⟨a ^ p ^ c, by rw [RingHom.comp_apply, hFr, iterateFrobenius_def, map_pow]⟩
  have h5 : K ≤ Pj E p c := by
    intro y hy
    obtain ⟨a, rfl⟩ := RingHom.mem_fieldRange.1 hy
    obtain ⟨w, hw⟩ := hroot a
    exact (mem_Pj p).2 ⟨w, hw⟩
  have hA := Subfield.relfinrank_mul_relfinrank h4 (le_top : K ≤ ⊤)
  have hB := Subfield.relfinrank_mul_relfinrank (h4.trans h5) (le_top : Pj E p c ≤ ⊤)
  have hKtop : K.relfinrank ⊤ = finrank k E := by
    have := IntermediateField.relfinrank_bot_left (⊤ : IntermediateField k E)
    rw [IntermediateField.finrank_top'] at this
    rw [← this, IntermediateField.relfinrank, IntermediateField.bot_toSubfield,
      IntermediateField.top_toSubfield]
  have hpos : 0 < K.relfinrank ⊤ := hKtop ▸ Module.finrank_pos
  have h9 : Kq.relfinrank K = finrank k (Tw k p c) := by
    rw [Subfield.relfinrank_eq_finrank_of_le h4]
    symm
    refine Algebra.finrank_eq_of_equiv_equiv (Fr.comp f).rangeRestrictFieldEquiv
      (f.rangeRestrictFieldEquiv.trans
        (RingEquiv.subfieldCongr (Subfield.extendScalars_toSubfield h4).symm)) ?_
    ext a
    show (((Fr.comp f).rangeRestrictFieldEquiv a : Kq) : E) = f (iterateFrobenius k p c a)
    rw [RingHom.rangeRestrictFieldEquiv_apply_coe, RingHom.comp_apply, hFr, iterateFrobenius_def,
      iterateFrobenius_def, map_pow]
  rw [h3] at hB
  rw [← h9]
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hB, ← hA, mul_comm]

theorem fieldGen {k E : Type*} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [FiniteDimensional k (Tw k p c)]
    (hroot : ∀ a : k, ∃ w : E, w ^ (p ^ c) = algebraMap k E a) :
    ∃ n : ℕ, finrank k (Tw k p c) = (p ^ c) ^ n ∧
      ∃ α : Fin n → E, Algebra.adjoin k (Set.range (fun b : E => b ^ (p ^ c)) ∪ Set.range α) = ⊤ := by
  have : CharP E p := charP_of_injective_algebraMap (algebraMap k E).injective p
  have hdeg := fl_deg p c hroot
  suffices H : ∃ n, finrank k (Tw k p c) = (p ^ c) ^ n ∧
      ∃ α : Fin n → E, Subfield.closure ((Pj E p c : Set E) ∪ Set.range α) = ⊤ by
    obtain ⟨n, hn, α, hα⟩ := H
    refine ⟨n, hn, α, ?_⟩
    have hadj : IntermediateField.adjoin k
        (Set.range (fun b : E => b ^ (p ^ c)) ∪ Set.range α) = ⊤ := by
      apply IntermediateField.toSubfield_injective
      rw [IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield, eq_top_iff, ← hα]
      apply Subfield.closure_mono
      apply Set.union_subset
      · intro y hy
        exact Or.inr (Or.inl ((mem_Pj p).1 hy))
      · intro y hy
        exact Or.inr (Or.inr hy)
    rw [← IntermediateField.adjoin_toSubalgebra, hadj, IntermediateField.top_toSubalgebra]
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · refine ⟨0, ?_, Fin.elim0, ?_⟩
    · rw [← hdeg, pow_zero, Subfield.relfinrank_eq_one_iff, Pj_zero]
    · rw [Pj_zero]
      exact eq_top_iff.2 fun y _ => Subfield.subset_closure (Or.inl (Subfield.mem_top y))
  · have hfin : (Pj E p c).relfinrank ⊤ ≠ 0 := by
      rw [hdeg]
      exact Module.finrank_pos.ne'
    obtain ⟨n, hn, α, hα⟩ := fl_frob p c hc hfin
    exact ⟨n, hdeg ▸ hn, α, hα⟩

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
