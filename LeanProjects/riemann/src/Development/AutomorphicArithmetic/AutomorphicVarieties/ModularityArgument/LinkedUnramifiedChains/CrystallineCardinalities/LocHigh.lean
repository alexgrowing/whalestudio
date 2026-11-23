import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LocLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.MatrixEntryZeroTwoSubmodule
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LowerTriangularAbsorbsTorsion
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

section
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {D : Type} [Group D] [TopologicalSpace D]

end

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.locHigh :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (d : ℕ) (t : D →* GL (Fin 3) O), (l : O) ≠ 0 → LE l D ε d → GenI l I d → TriRep t → ∀ i : Fin 2, UnitStep I ε t i → ∃ C : ℕ, ∀ k, 0 < k → Nat.card (Ok l O k) ^ (7 + 3 * d) ≤ C * (ZF (l := l) I k t).ncard := by
  classical
  intro l _ O _ _ _ _ _ D _ _ _ _ I ε d t hl hLE hG hT i hU
  obtain ⟨c, hc0, hy⟩ := yEx l O D I ε d t hl hLE hG hT i hU
  have hOk := okFin l O hl
  haveI : Finite (O ⧸ Ideal.span {c}) := hOk.2.1 c hc0
  refine ⟨Nat.card (O ⧸ Ideal.span {c}), fun k hk => ?_⟩
  haveI : Finite (Ok l O k) := hOk.1 k
  obtain ⟨hZfin, -⟩ := locLow l O D I ε d t hl hLE hG hT k hk
  have hW := low0 l O D I ε d t hl hLE hG hT i hU k hk
  obtain ⟨y, hyZ, s0, hys⟩ := hy k hk
  set mc : Ok l O k := Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) c with hmc
  have hmem : ∀ w ∈ ZF (l := l) I k t, ∀ a : Ok l O k, w + a • y ∈ ZF (l := l) I k t := by
    intro w hw a
    obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
    obtain ⟨hy1, hy2, hy3, hy4⟩ := hyZ
    refine ⟨hw1.add (hy1.comp (fun x => a • x)), ?_, ?_, ?_⟩
    · intro s s'
      simp only [Pi.add_apply, Pi.smul_apply, hw2 s s', hy2 s s', cj, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul, smul_add]
      abel
    · intro s p q hpq
      simp [hw3 s p q hpq, hy3 s p q hpq]
    · intro s hs p
      simp [hw4 s hs p, hy4 s hs p]
  set W := {z | z ∈ ZF (l := l) I k t ∧ ∀ s, z s i.castSucc i.castSucc = z s i.succ i.succ} with hWdef
  let J : Ideal (Ok l O k) := Ideal.span {mc}
  let g : Ok l O k → Ok l O k := fun b => if h : ∃ a, a * mc = b then h.choose else 0
  have hg : ∀ b ∈ (J : Set (Ok l O k)), g b * mc = b := by
    intro b hb
    have h : ∃ a, a * mc = b := Ideal.mem_span_singleton'.mp hb
    simp only [g, dif_pos h]
    exact h.choose_spec
  have hcount : (W ×ˢ (J : Set (Ok l O k))).ncard ≤ (ZF (l := l) I k t).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun p => p.1 + g p.2 • y) ?_ ?_ hZfin
    · rintro ⟨w, b⟩ ⟨hw, -⟩
      exact hmem w hw.1 _
    · rintro ⟨w, b⟩ ⟨hw, hb⟩ ⟨w', b'⟩ ⟨hw', hb'⟩ h
      dsimp only at h hw hb hw' hb'
      have h1 := congrFun (congrFun (congrFun h s0) i.castSucc) i.castSucc
      have h2 := congrFun (congrFun (congrFun h s0) i.succ) i.succ
      simp only [Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2
      have hwa : w s0 i.castSucc i.castSucc = w s0 i.succ i.succ := hw.2 s0
      have hwb : w' s0 i.castSucc i.castSucc = w' s0 i.succ i.succ := hw'.2 s0
      have hbb : b = b' := by
        linear_combination -(hg b hb) + hg b' hb' - (g b - g b') * hys + h1 - h2 - hwa + hwb
      subst hbb
      have : w = w' := add_right_cancel h
      simp [this]
  have hJ : Nat.card (Ok l O k) ≤ Nat.card (O ⧸ Ideal.span {c}) * (J : Set (Ok l O k)).ncard := by
    have h1 : Nat.card (Ok l O k) = Nat.card J * Nat.card (Ok l O k ⧸ J) :=
      Submodule.card_eq_card_quotient_mul_card J
    have h2 : Nat.card (Ok l O k ⧸ J) ≤ Nat.card (O ⧸ Ideal.span {c}) := by
      let φ : O →+* Ok l O k ⧸ J := (Ideal.Quotient.mk J).comp (Ideal.Quotient.mk _)
      have hφ : ∀ a ∈ Ideal.span {c}, φ a = 0 := by
        intro a ha
        obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [map_mul, show φ c = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
          mul_zero]
      apply Nat.card_le_card_of_surjective (Ideal.Quotient.lift _ φ hφ)
      apply Ideal.Quotient.lift_surjective_of_surjective
      exact Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
    rw [h1, mul_comm, ← Nat.card_coe_set_eq]
    exact Nat.mul_le_mul_right _ h2
  calc Nat.card (Ok l O k) ^ (7 + 3 * d)
      = Nat.card (Ok l O k) ^ (6 + 3 * d) * Nat.card (Ok l O k) := by ring
    _ ≤ W.ncard * (Nat.card (O ⧸ Ideal.span {c}) * (J : Set (Ok l O k)).ncard) := Nat.mul_le_mul hW hJ
    _ = Nat.card (O ⧸ Ideal.span {c}) * (W ×ˢ (J : Set (Ok l O k))).ncard := by rw [Set.ncard_prod]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hcount
