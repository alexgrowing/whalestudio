import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinrankSpanImageLe

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem mem_levels_iff' {N : ℕ} (G : Formalism.GM.M.BlockData N) (x : (Fin G.T.t → ℕ) × ℕ) :
    x ∈ levels G ↔ G.LevelOK x.1 x.2 := by
  unfold levels
  simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨⟨fun i => ?_, ?_⟩, h⟩⟩
  · have hle := Finset.single_le_sum (s := Finset.univ) (f := fun a => G.LL.deg a)
      (fun a _ => Nat.zero_le _) (Finset.mem_univ (⟨min (G.T.pos i) (N - 1), by
        rcases Nat.eq_zero_or_pos N with h0 | h0
        · exact absurd G.uPos.2 (by omega)
        · omega⟩ : Fin N))
    have h1 := (h.1 i).1
    omega
  · have h2 := h.2
    have h3 := min_le_right (G.LL.deg G.uPos) G.B
    omega

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestBClvl : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b → ∀ l ∈ lv C0 CE1 CE2 X aTop b,
      Module.finrank (KK X.O) (Submodule.span (KK X.O)
        ((blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b).gens X.O (r := X.r) l.1 l.2)) ≤
      Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2)

theorem restBCdim_of (h : RestBClvl C0 CE1 CE2 X) : RestBCdim C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hk
  rw [finrank_blockLat X.O X.p X.r (Formalism.MainNotions.G.GLWeightTheory.valuation_properties_hold X.std.1.prime X.setting) (X.S C0 CE1 CE2) aTop aPlus X.m b]
  unfold blockRank
  simp only
  set D := blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b with hD
  have hU : Submodule.span (KK X.O) ((D.SSZ X.O (r := X.r) : Submodule X.O _) :
        Set (MvPolynomial (BVar (2 * X.s + 1) X.r D.T.t) (KK X.O))) ≤
      ⨆ l ∈ lv C0 CE1 CE2 X aTop b, Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2) := by
    rw [Submodule.span_le]
    intro x hx
    have hx' : x ∈ Submodule.span X.O (⋃ (j : Fin D.T.t → ℕ) (jp : ℕ) (_ : D.LevelOK j jp), D.gens X.O (r := X.r) j jp) := hx
    refine Submodule.span_induction (p := fun x _ => x ∈ ⨆ l ∈ lv C0 CE1 CE2 X aTop b,
        Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) ?_ ?_ ?_ ?_ hx'
    · intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨j, jp, hl, hy⟩ := hy
      have hmem : ((j, jp) : Lv C0 CE1 CE2 X) ∈ lv C0 CE1 CE2 X aTop b := by
        exact (mem_levels_iff' (gB C0 CE1 CE2 X aTop 0 b) (j, jp)).2 hl
      exact (le_iSup₂ (f := fun (l : Lv C0 CE1 CE2 X) (_ : l ∈ lv C0 CE1 CE2 X aTop b) =>
        Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) (j, jp) hmem) (Submodule.subset_span hy)
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      rw [algebra_compatible_smul (KK X.O) a x]
      exact Submodule.smul_mem _ _ hx
  have := span_SSZ_finite (O := X.O) (r := X.r) D
  have hfd : ∀ l ∈ lv C0 CE1 CE2 X aTop b,
      FiniteDimensional (KK X.O) (Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) := by
    intro l hl
    have hsub : Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2) ≤
        Submodule.span (KK X.O) ((D.SSZ X.O (r := X.r) : Submodule X.O _) :
          Set (MvPolynomial (BVar (2 * X.s + 1) X.r D.T.t) (KK X.O))) := by
      apply Submodule.span_mono
      intro y hy
      apply Submodule.subset_span
      refine Set.mem_iUnion.2 ⟨l.1, Set.mem_iUnion.2 ⟨l.2, Set.mem_iUnion.2 ⟨?_, hy⟩⟩⟩
      exact (mem_levels_iff' (gB C0 CE1 CE2 X aTop 0 b) l).1 hl
    exact Submodule.finiteDimensional_of_le hsub
  obtain ⟨hfd2, hle⟩ := finrank_biSup_le (fun l : Lv C0 CE1 CE2 X =>
    Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) (lv C0 CE1 CE2 X aTop b) hfd
  calc Module.finrank (KK X.O) (Submodule.span (KK X.O) ((D.SSZ X.O (r := X.r) : Submodule X.O _) :
          Set (MvPolynomial (BVar (2 * X.s + 1) X.r D.T.t) (KK X.O))))
      ≤ Module.finrank (KK X.O) (⨆ l ∈ lv C0 CE1 CE2 X aTop b,
          Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2) : Submodule (KK X.O) _) :=
        Submodule.finrank_mono hU
    _ ≤ ∑ l ∈ lv C0 CE1 CE2 X aTop b, Module.finrank (KK X.O) (Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) :=
        hle
    _ ≤ ∑ l ∈ lv C0 CE1 CE2 X aTop b,
          Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) :=
        Finset.sum_le_sum fun l hl => h aTop hT aPlus hP b hk l hl

end Formalism.MainNotions.G.SymmetricFormBlocks

end
