import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityDropZeroBlocksStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd

universe u

theorem sub_positions_univ {α : Type u} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (i : Fin h) :
    ∃ o : Fin (sub W c i).length → Fin W.length, StrictMono o ∧ (∀ j, c j = i ↔ j ∈ Set.range o) ∧
      ∀ a, (sub W c i).get a = W.get (o a) := by
  have key : ∀ L : List (Fin W.length), L.Pairwise (· < ·) → (∀ j, j ∈ L ↔ c j = i) →
      ∃ o : Fin (L.map W.get).length → Fin W.length, StrictMono o ∧ (∀ j, c j = i ↔ j ∈ Set.range o) ∧
        ∀ a, (L.map W.get).get a = W.get (o a) := by
    intro L hpw hmem
    have hlen : (L.map W.get).length = L.length := by simp
    refine ⟨fun a => L.get (Fin.cast hlen a), ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : Fin.cast hlen a < Fin.cast hlen b := by
        first
        | exact hab
        | simpa [Fin.lt_def] using hab
      exact List.pairwise_iff_get.1 hpw (Fin.cast hlen a) (Fin.cast hlen b) hab'
    · intro j
      constructor
      · intro hj
        obtain ⟨n, hn⟩ := List.mem_iff_get.1 ((hmem j).2 hj)
        refine ⟨Fin.cast hlen.symm n, ?_⟩
        first
        | exact hn
        | simpa using hn
      · rintro ⟨a, rfl⟩
        exact (hmem _).1 (List.mem_iff_get.2 ⟨_, rfl⟩)
    · intro a
      simp [List.get_eq_getElem]
  exact key ((List.finRange W.length).filter (fun p => decide (c p = i)))
    ((List.pairwise_lt_finRange _).filter _) (fun j => by simp)

end GlobalTheory.CompanionTheory.FineProd

namespace GlobalTheory.CompanionTheory.FineProd

theorem jm_row : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (W : List (IrrGL k)) (c : Fin W.length → Fin h) (i : Fin h) (Y : Fin W.length → IrrGL k), (∀ j, c j = i → Y j = W.get j) → (∀ j, c j ≠ i → (Y j).1 = 0) → ∀ (hd : ∑ j, (Y j).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), jm Y hd π = jmL (sub W c i) π := by
  intro k _ _ _ _ h N W c i Y hY h0 hd V _ _ π
  obtain ⟨o, ho, hr, hg⟩ := sub_positions_univ W c i
  have hget : (sub W c i).get = fun a => Y (o a) := by
    funext a
    rw [hg a, hY (o a) ((hr (o a)).2 ⟨a, rfl⟩)]
  have hsum : ∑ a, (Y (o a)).1 = N := by
    rw [← hd]
    have himg : ∑ j ∈ Finset.univ.image o, (Y j).1 = ∑ a, (Y (o a)).1 :=
      Finset.sum_image (fun a _ b _ e => ho.injective e)
    rw [← himg]
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro j _ hj
    refine h0 j ?_
    intro e
    obtain ⟨a, rfl⟩ := (hr j).1 e
    exact hj (Finset.mem_image_of_mem o (Finset.mem_univ a))
  have hnz : ∀ j, (Y j).1 ≠ 0 → j ∈ Set.range o := by
    intro j hj
    refine (hr j).1 ?_
    by_contra e
    exact hj (h0 j e)
  have hdeg : ∑ a, ((sub W c i).get a).1 = N := by
    rw [hget]
    exact hsum
  have hcongr : ∀ {r : ℕ} (x y : Fin r → IrrGL k) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N),
      x = y → jm x hx π = jm y hy π := by
    intro r x y hx hy e
    subst e
    rfl
  rw [GlobalTheory.T.jacquet_multiplicity_drop_zero_blocks Y hd o ho hnz hsum π, jmL, dif_pos hdeg]
  exact hcongr _ _ _ _ hget.symm

end GlobalTheory.CompanionTheory.FineProd
