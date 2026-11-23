import Formalism.HermitianCurvature.HermitianCurvatureProofs.OfFnSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LoeSubStates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeAtMinusW

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem rhyp_nodes (hTR : TopRatio) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (hC : 28 * Real.exp 1 ≤ Cc) (v : Fin S.f) (a : List C.Letter)
    (ha : D.AdmAt S v a) {K d : ℕ} (haN : a.length + K ≤ S.Ntop) (grid : Fin K → Fin (d + 1) → ℝ)
    (hmem : ∀ (b : Fin K) j, grid b j ∈ S.grid v (a.length + K - (b : ℕ)))
    (n : Fin K → Fin (d + 1))
    (hcut : KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (n b)) a))
    (e : Wd.Ix (Fin a.length)) (ρ : M.Ty (D.parOf S v)) :
    RHyp (p v).l0 a e ρ (S.P v) (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
      (Real.sqrt (S.T * S.T'))⁻¹) (List.ofFn fun b => grid b (n b)) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -⟩ := hv v
  rw [hl0]
  refine rhyp_of _ a e ρ _ _ _ fun ys₁ y ys₂ hsplit => ?_
  obtain ⟨b₀, hb₀, rfl, hlen, hlater⟩ := ofFn_split (fun b => grid b (n b)) ys₁ y ys₂ hsplit

  have hc : KB.CutWord (D.parOf S v) (S.l + 1) ((true, grid b₀ (n b₀)) :: KB.plusW ys₂ a) := by
    rw [PBD.cutWord_iff] at hcut ⊢
    rw [PBF.plusW_eq, hsplit] at hcut
    have hsub : ((true, grid b₀ (n b₀)) :: KB.plusW ys₂ a).Sublist
        ((ys₁ ++ grid b₀ (n b₀) :: ys₂).map (fun y => (true, y)) ++ a) := by
      rw [PBF.plusW_eq, List.map_append, List.map_cons, List.append_assoc, List.cons_append]
      exact List.sublist_append_right _ _
    exact ⟨fun x hx => hcut.1 x (hsub.subset hx), hcut.2.sublist hsub⟩
  have hgr : ∃ m, grid b₀ (n b₀) ∈ S.grid v m := ⟨_, hmem b₀ (n b₀)⟩
  have hl : (KB.plusW ys₂ a).length < S.Ntop := by
    rw [PBF.plusW_eq, List.length_append, List.length_map]; omega
  have hfar : ∀ x ∈ KB.plusW ys₂ a, (S.Ntop : ℝ) ^ 2 + 1 ≤ |grid b₀ (n b₀) - x.2| ∧
      (x.1 = false → (S.Ntop : ℝ) ^ 2 + 1 ≤ |grid b₀ (n b₀) - (x.2 - 1)|) := by
    intro x hx
    rw [PBF.plusW_eq, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hx
      obtain ⟨b', hb', rfl⟩ := hlater y' hy'
      refine ⟨?_, fun h => absurd h (by simp)⟩
      have := PBD.sep_grid S hGo v (hmem b₀ (n b₀)) (hmem b' (n b')) (by
        have : (b₀ : ℕ) < b' := hb'
        have hb'K := b'.isLt
        omega) (e := 0) (e' := 0) (by simp) (by simp)
      simpa using this
    · have hy : (false = false ∧ ∃ a', a.length < a' ∧ a' ≤ S.Ntop ∧ grid b₀ (n b₀) ∈ S.grid v a') ∨
          (false = true ∧ grid b₀ (n b₀) ∈ S.grid1 v ∧ ∀ x ∈ a, PBD.Sep (true, grid b₀ (n b₀)) x) :=
        Or.inl ⟨rfl, a.length + K - (b₀ : ℕ), by have := b₀.isLt; omega, by omega, hmem b₀ (n b₀)⟩
      obtain ⟨h1, h2⟩ := node_far hB v a ha (grid b₀ (n b₀)) false hy x hx
      simp only [Bool.false_eq_true, if_false] at h1 h2
      unfold PBD.nodeOf at h1 h2
      by_cases hx1 : x.1 = true
      · rw [if_pos hx1] at h1
        exact ⟨h1, fun h => absurd h (by simp [hx1])⟩
      · rw [if_neg hx1] at h1 h2
        rw [sub_add_cancel] at h2
        exact ⟨h2, fun _ => h1⟩
  have := hTR Cb Cc E Wp Wq S p f χ A₀ hB hC v (KB.plusW ys₂ a) (grid b₀ (n b₀)) hc hgr hl hfar
    (KB.firstSt ys₂ e) ρ
  exact this

end asm

end

end Formalism.FourierDecayAlt.P.PBL
