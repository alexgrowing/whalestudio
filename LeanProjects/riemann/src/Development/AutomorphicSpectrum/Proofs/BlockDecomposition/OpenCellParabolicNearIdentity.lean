import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Small

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rowD (i t : ℕ) (b : Fin (t + 1)) : Fin ((i + 1) + (t + 1) + 1) := Fin.castSucc (Fin.natAdd (i + 1) b)

theorem ePG_true_rowD (i t : ℕ) (b : Fin (t + 1)) : ePG (i + 1) (t + 1) ⟨true, b⟩ = rowD i t b :=
  Fin.ext (by simp [rowD, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val])

def ent {n : ℕ} (a b : Fin (n + 1)) (p : Mir k n) : k :=
  ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b

theorem continuous_ent {n : ℕ} (a b : Fin (n + 1)) : Continuous (ent (k := k) a b) :=
  (Units.continuous_val.comp continuous_subtype_val).matrix_elem a b

theorem ent_last_last {n : ℕ} (p : Mir k n) : ent (Fin.last n) (Fin.last n) p = 1 := by
  have hh := (mem_Mir_iff k _).1 p.2
  show ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1
  rw [hh]
  simp [eLast]

theorem colMat_mul_castSucc {n : ℕ} (v : Fin n → k) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (a : Fin n)
    (c : Fin (n + 1)) : (colMat k n v * A) (Fin.castSucc a) c = v a * A (Fin.last n) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
  · simp [colMat]
  · intro l _ hl
    simp [colMat, hl]
  · simp

theorem continuous_colMat_append (i t : ℕ) :
    Continuous fun d : Fin (t + 1) → k => colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := by
  refine continuous_matrix fun a b => ?_
  by_cases hb : b = Fin.last _
  · subst hb
    induction a using Fin.lastCases with
    | last => simpa [colMat] using continuous_const
    | cast a =>
      induction a using Fin.addCases with
      | left a => simpa [colMat] using continuous_const
      | right a =>
        have e : ∀ d : Fin (t + 1) → k, colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)
            (Fin.castSucc (Fin.natAdd (i + 1) a)) (Fin.last _) = d a := by
          intro d
          unfold colMat
          rw [if_pos rfl, Fin.lastCases_castSucc, Fin.append_right]
        exact (continuous_apply a).congr fun d => (e d).symm
  · simpa [colMat, hb] using continuous_const

theorem continuous_dEmb (i t : ℕ) : Continuous (dEmb k i t) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (continuous_colMat_append i t)
  · exact continuous_const.sub (continuous_colMat_append i t)

theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  show (1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) 0) : Matrix _ _ k) = 1
  have : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext a
    induction a using Fin.addCases <;> simp
  rw [this, colMat_zero, add_zero]

def delta (i t : ℕ) (u : Mir k ((i + 1) + (t + 1))) : Fin (t + 1) → k :=
  fun b => - ent (rowD i t b) (Fin.last _) u

theorem continuous_delta (i t : ℕ) : Continuous (delta (k := k) i t) :=
  continuous_pi fun b => (continuous_ent _ _).neg

theorem delta_one (i t : ℕ) : delta (k := k) i t 1 = 0 := by
  funext b
  have h0 : (1 : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) (rowD i t b) (Fin.last _) = 0 :=
    Matrix.one_apply_ne (Fin.castSucc_ne_last _)
  show - ((1 : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) (rowD i t b) (Fin.last _)) = 0
  rw [h0, neg_zero]

theorem eq_delta (i t : ℕ) (h u : Mir k ((i + 1) + (t + 1))) (hH : h ∈ HPG k (i + 1) (t + 1))
    (d : Fin (t + 1) → k) (e : h = dEmb k i t d * u) : d = delta i t u := by
  funext b
  have hp : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ parab k (ePG (i + 1) (t + 1)) := hH
  have hz := mem_parab_iff.1 hp true false b (Fin.last (i + 1)) (by decide)
  rw [ePG_true_rowD, ePG_false_last] at hz
  have hv : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val =
      (1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)) *
        ((u : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val := by
    rw [e]; rfl
  have hz' : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val
      (rowD i t b) (Fin.last _) = 0 := hz
  rw [hv, add_mul, one_mul, Matrix.add_apply, rowD, colMat_mul_castSucc] at hz'
  have h1 : ((u : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val (Fin.last _) (Fin.last _) = 1 :=
    ent_last_last u
  rw [h1, mul_one, Fin.append_right] at hz'
  show d b = - ent (rowD i t b) (Fin.last _) u
  exact eq_neg_of_add_eq_zero_right hz'

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Small

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

open Small in
theorem h_small : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (O : Set (Mir k ((i + 1) + t + 1))) (hO : O ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1))),
    ∃ N ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ (h : Mir k ((i + 1) + (t + 1))), h ∈ HPG k (i + 1) (t + 1) →
      ∀ (d : Fin (t + 1) → k) (x : Mir k ((i + 1) + t + 1)), x ∈ N →
        dEmb k i t d * wEl k i t = h * wEl k i t * x → h ∈ O := by
  intro k _ _ _ _ i t O hO
  let w : Mir k ((i + 1) + (t + 1)) := wEl k i t
  let f : Mir k ((i + 1) + (t + 1)) → Mir k ((i + 1) + (t + 1)) :=
    fun x => dEmb k i t (delta i t (w * x⁻¹ * w⁻¹)) * (w * x⁻¹ * w⁻¹)
  have hu : Continuous fun x : Mir k ((i + 1) + (t + 1)) => w * x⁻¹ * w⁻¹ :=
    (continuous_const.mul continuous_inv).mul continuous_const
  have hf : Continuous f :=
    ((continuous_dEmb i t).comp ((continuous_delta i t).comp hu)).mul hu
  have f1 : f 1 = 1 := by
    have e : w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹ = 1 := by group
    show dEmb k i t (delta i t (w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹)) * (w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹) = 1
    rw [e, delta_one, dEmb_zero, one_mul]
  refine ⟨f ⁻¹' O, hf.continuousAt.preimage_mem_nhds (by rw [f1]; exact hO), ?_⟩
  intro h hH d x hx e
  have e' : h = dEmb k i t d * (w * x⁻¹ * w⁻¹) := by
    have e2 : dEmb k i t d * w = h * w * x := e
    calc h = (h * w * x) * x⁻¹ * w⁻¹ := by group
      _ = (dEmb k i t d * w) * x⁻¹ * w⁻¹ := by rw [e2]
      _ = dEmb k i t d * (w * x⁻¹ * w⁻¹) := by group
  have hd := eq_delta i t h _ hH d e'
  have hfx : f x = h := by
    show dEmb k i t (delta i t (w * x⁻¹ * w⁻¹)) * (w * x⁻¹ * w⁻¹) = h
    rw [← hd, ← e']
  have : f x ∈ O := hx
  rwa [hfx] at this

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO

end
