import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorUniformizerExponent
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.OriginBoxVac

section Alg
variable {k : Type} [Field k] [ValuativeRel k]

theorem unit_mul_mem_integer_iff (u : kˣ) (x : k) :
    (u : k) * x ∈ 𝒪[k] ↔ valuation k x ≤ valuation k ((u⁻¹ : kˣ) : k) := by
  have hu : valuation k (u : k) ≠ 0 := by simp
  rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    ← one_mul (valuation k (u : k))⁻¹, le_mul_inv_iff₀ (zero_lt_iff.2 hu), mul_comm]

theorem scale_eq (ϖ : kˣ) (a A B : ℤ) (x : k) :
    (((ϖ ^ a)⁻¹ : kˣ) : k) * (((ϖ ^ A : kˣ) : k) * x * (((ϖ ^ B)⁻¹ : kˣ) : k)) =
      ((ϖ ^ (A - B - a) : kˣ) : k) * x := by
  have h : ϖ ^ (A - B - a) = (ϖ ^ a)⁻¹ * ϖ ^ A * (ϖ ^ B)⁻¹ := by
    rw [_root_.zpow_sub, _root_.zpow_sub]; group
  rw [h, Units.val_mul, Units.val_mul]; ring

theorem scaled_mem_iff (ϖ : kˣ) (a A B : ℤ) (x : k) :
    (((ϖ ^ a)⁻¹ : kˣ) : k) * (((ϖ ^ A : kˣ) : k) * x * (((ϖ ^ B)⁻¹ : kˣ) : k)) ∈ 𝒪[k] ↔
      valuation k x ≤ valuation k ((ϖ ^ (a - A + B) : kˣ) : k) := by
  rw [scale_eq, unit_mul_mem_integer_iff, ← _root_.zpow_neg, show -(A - B - a) = a - A + B by ring]

end Alg

theorem basePt_zero_of_var {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} (r : n ⊕ Fin c) (s : n' ⊕ Fin (c + 1)) (h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) :
    basePt c (0 : Matrix n n' k) r s = 0 := by
  rcases r with r | r <;> rcases s with s | s <;> simp [basePt, Free, Kept] at h ⊢ <;> omega

end GlobalTheory.OriginBoxVac

namespace GlobalTheory.OriginBoxVac

theorem moveArgs_one_entry {k : Type} [Field k] (G : Grid k) (g : G.VertexGroup) (z : G.Args) (b : Edge)
    (dt : Fin (G.rank b.tgt) → kˣ) (ds : Fin (G.rank b.src) → kˣ) (ht : g b.tgt = diagGL dt)
    (hsrc : g b.src = diagGL ds) (r : Fin (G.rank b.tgt)) (s : Fin (G.rank b.src)) :
    G.moveArgs .one g z b r s = (dt r : k) * z b r s * ((ds s)⁻¹ : kˣ) := by
  have h1 : ((g b.src)⁻¹).val = diagonal fun i => (((ds i)⁻¹ : kˣ) : k) := by rw [hsrc]; rfl
  simp only [Grid.moveArgs, Assignment.read, invT_inv_val, invT_val]
  rw [h1, ht, diagGL_val, diagonal_transpose, diagonal_transpose, mul_diagonal, diagonal_mul]

end GlobalTheory.OriginBoxVac

namespace GlobalTheory.OriginBox
open GlobalTheory.OriginBoxVac

theorem indicator_moveArgs_origin {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (a a' : ℤ) (g : G.VertexGroup)
    (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j) (e : Vars G) :
    Set.indicator {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]}
      (1 : G.Args → ℂ) (G.moveArgs .one g (fill hs 0 0 e)) = (box G ϖ a a').indicator (1 : Vars G → ℂ) e := by
  classical
  set M := G.moveArgs .one g (fill hs 0 0 e) with hMdef
  have hM : ∀ (j : ℕ) (r : Fin (G.rank (G.m, j))) (s : Fin (G.rank (G.m, j + 1))), M (.theta G.m j) r s =
      ((ϖ ^ vtxExp a a' (G.m - 1 - j) (topRank G j) r : kˣ) : k) * downMap hs 0 e j s r *
        (((ϖ ^ vtxExp a a' (G.m - 1 - (j + 1)) (topRank G (j + 1)) s)⁻¹ : kˣ) : k) := by
    intro j r s
    rw [hMdef, moveArgs_one_entry G g _ (.theta G.m j)
      (fun x => ϖ ^ vtxExp a a' (G.m - 1 - j) (topRank G j) x)
      (fun x => ϖ ^ vtxExp a a' (G.m - 1 - (j + 1)) (topRank G (j + 1)) x) (hg j) (hg (j + 1)),
      fill_theta, transpose_apply]
  have hE : ∀ (j : ℕ) (hj : j < G.m - 1) (r' : Fin (topRank G j) ⊕ Fin (G.m - 2 - j + 1))
      (s' : Fin (topRank G (j + 1)) ⊕ Fin (G.m - 2 - j)),
      M (.theta G.m j) (frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; omega) r')
        (frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); omega) s') =
      ((ϖ ^ auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) r' : kˣ) : k) * stepPt ((0 : ColArgs G) j) (e ⟨j, hj⟩) s' r' *
        (((ϖ ^ auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) s')⁻¹ : kˣ) : k) := by
    intro j hj r' s'
    rw [hM, show G.m - 1 - j = G.m - 2 - j + 1 by omega, vtxExp_frame,
      show G.m - 1 - (j + 1) = G.m - 2 - j by omega, vtxExp_frame]
    congr 2
    simp only [downMap, dif_pos hj, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]

  have hbox : ∀ (j : ℕ) (hj : j < G.m - 1) (r' : Fin (topRank G j) ⊕ Fin (G.m - 2 - j + 1))
      (s' : Fin (topRank G (j + 1)) ⊕ Fin (G.m - 2 - j)) (hv : Free ((G.m - 2 - j) / 2 + 1) (s', r') ∨ Kept (s', r')),
      (((ϖ ^ a)⁻¹ : kˣ) : k) * M (.theta G.m j) (frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; omega) r')
        (frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); omega) s') ∈ 𝒪[k] ↔
      valuation k (e ⟨j, hj⟩ ⟨(s', r'), hv⟩) ≤ valuation k ((ϖ ^ boxExp G a a' ⟨j, hj⟩ ⟨(s', r'), hv⟩ : kˣ) : k) := by
    intro j hj r' s' hv
    rw [hE, scaled_mem_iff]
    simp only [stepPt, Matrix.add_apply, of_apply, dif_pos hv, Pi.zero_apply, basePt_zero_of_var s' r' hv, zero_add]
    rfl
  have key : (∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * M b i j ∈ 𝒪[k]) ↔ e ∈ box G ϖ a a' := by
    constructor
    · intro H j _ v _
      have hb : Edge.theta G.m j ∈ oppositePath G.m := by have := j.2; simp [oppositePath]; omega
      exact (hbox j j.2 v.1.2 v.1.1 v.2).1 (H _ hb _ _)
    · intro he b hb r s
      simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
      rcases hb with ⟨i, -, rfl⟩ | ⟨j, hj, rfl⟩
      · have h0 : M (.ex i G.m) = 0 := by
          simp only [hMdef, Grid.moveArgs, fill_ex, Pi.zero_apply, transpose_zero, Matrix.mul_zero, Matrix.zero_mul]
        simp [h0]
      · rcases Nat.lt_or_ge j (G.m - 1) with hj' | hj'
        · obtain ⟨r', rfl⟩ := (frame (a := topRank G j) (c := G.m - 2 - j + 1) (b := G.rank (G.m, j)) (by have := topRank_add hs j; omega)).surjective r
          obtain ⟨s', rfl⟩ := (frame (a := topRank G (j + 1)) (c := G.m - 2 - j) (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); omega)).surjective s
          by_cases hv : Free ((G.m - 2 - j) / 2 + 1) (s', r') ∨ Kept (s', r')
          · exact (hbox j hj' r' s' hv).2 (he ⟨j, hj'⟩ trivial ⟨(s', r'), hv⟩ trivial)
          · rw [hE j hj', scale_eq]
            simp only [stepPt, Matrix.add_apply, of_apply, dif_neg hv, add_zero, Pi.zero_apply]
            rcases s' with s' | l <;> rcases r' with r' | i
            · simp [basePt]
            · simp [basePt]
            · simp [basePt]
            · simp only [basePt, fromBlocks_apply₂₂, of_apply]
              split_ifs with hli
              · have h0 : auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) (Sum.inr i : Fin (topRank G j) ⊕ _) -
                    auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) (Sum.inr l : Fin (topRank G (j + 1)) ⊕ _) - a = 0 := by
                  simp only [auxiliaryVectorUniformizerExponent, hli]; push_cast; ring
                rw [h0]; simp
              · simp
        · have hjm : j + 1 = G.m := by omega
          have h0 : M (.theta G.m j) r s = 0 := by
            rw [hM]; simp [downMap, show ¬ j < G.m - 1 by omega, hjm]
          simp [h0]
  by_cases he : e ∈ box G ϖ a a'
  · rw [Set.indicator_of_mem he]
    exact Set.indicator_of_mem (s := {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]}) (key.2 he) _
  · rw [Set.indicator_of_notMem he]
    exact Set.indicator_of_notMem (s := {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]}) (fun h => he (key.1 h)) _

end GlobalTheory.OriginBox
