import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursOfSubquotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleOfPermStatement
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

section Comb

variable {T : Type*}

theorem interleave_nil_left {v w : List T} (h : Zc.Comb.Interleave [] v w) : w = v := by
  generalize hu : ([] : List T) = u at h
  induction h with
  | nil => rfl
  | left _ _ => cases hu
  | right _ ih => rw [ih hu]

theorem interleave_nil_right {u w : List T} (h : Zc.Comb.Interleave u [] w) : w = u := by
  generalize hv : ([] : List T) = v at h
  induction h with
  | nil => rfl
  | left _ ih => rw [ih hv]
  | right _ _ => cases hv

theorem interleave_single {a : T} {v w : List T} (h : Zc.Comb.Interleave [a] v w) :
    ∃ P Q : List T, v = P ++ Q ∧ w = P ++ a :: Q := by
  generalize hu : [a] = u at h
  induction h with
  | nil => cases hu
  | @left a' u v w h _ =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hu
    exact ⟨[], v, rfl, by rw [interleave_nil_left h]; rfl⟩
  | @right a' u v w _ ih =>
    obtain ⟨P, Q, rfl, rfl⟩ := ih hu
    exact ⟨a' :: P, Q, rfl, rfl⟩

theorem shuffle_two_single {a : T} {D w : List T} (h : Zc.Comb.Shuffle [[a], D] w) :
    ∃ P Q : List T, D = P ++ Q ∧ w = P ++ a :: Q := by
  cases h with
  | cons hs hi =>
    cases hs with
    | cons hs' hi' =>
      cases hs'
      rw [interleave_nil_right hi'] at hi
      exact interleave_single hi

end Comb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem decW_single (ρ : IrrGL k) (hρ : ρ.IsCusp) : decW (Segment.single ρ hρ) = [ρ] := by
  simp [decW, Segment.single, Segment.term]

theorem words_of_subq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hW : ShlP k) (σ b : IrrGL k) (Δ : Segment k)
    (hb : IsLSeg Δ b.rep) (hσ : SubqL σ [nxt Δ, b]) (l : List (IrrGL k)) (hl : ∀ ρ ∈ l, ρ.IsCusp) (he : EmbL σ l) :
    ∃ P Q : List (IrrGL k), decW Δ = P ++ Q ∧ l = P ++ nxt Δ :: Q := by
  obtain ⟨hd1, hsub⟩ := hσ
  obtain ⟨hd2, f, hf⟩ := he
  have := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible σ.2.rep.irr
  have hnt : ∃ v, f v ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : σ.2.rep.V)
    exact ⟨v, fun h => hv (hf (h.trans (f.toLinearMap.map_zero).symm))⟩
  have h1 : 1 ≤ jm l.get hd2 σ.rep := GlobalTheory.T.jacquet_multiplicity_pos hA l.get hd2 σ.rep σ.2.rep.smooth f hnt
  have hwd : Wd σ.rep l := ⟨hd2, by intro h; rw [h] at h1; simp at h1⟩
  have hwd2 : Wd (prodIrr [nxt Δ, b].get hd1) l :=
    GlobalTheory.T.word_occurs_of_subquotient _ σ.rep (isSmooth_prodIrr _ _) hsub l hwd
  have hc : (nxt Δ).IsCusp := Δ.isCusp_first.nu _
  obtain ⟨L, hL, hsh⟩ := hW [nxt Δ, b].get hd1 ![Segment.single (nxt Δ) hc, Δ] (by
      intro i
      fin_cases i
      · exact (single_spec hc).2.1
      · exact hb) l hl hwd2
  have hL' : L.Perm [Segment.single (nxt Δ) hc, Δ] := by
    rw [← Multiset.coe_eq_coe, hL]
    simp [Fin.univ_val_map]
  have h2 := GlobalTheory.T.shuffle_of_perm _ _ l hsh (hL'.map decW)
  rw [List.map_cons, List.map_cons, List.map_nil, decW_single] at h2
  exact shuffle_two_single h2

end PositivityTheory.Exh

end
