import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirProj

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Chart

open GlobalTheory.CompanionTheory.BZPhiPG.Cells

section Alg

variable {k : Type} [Field k]

def rowM {ι : Type} [DecidableEq ι] (ρ : ι → k) (c j : ι) : Matrix ι ι k :=
  ((1 : Matrix ι ι k).updateRow c ρ).submatrix (Equiv.swap c j) id

theorem rowM_det_ne {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ι → k) (c j : ι) (hc : ρ c ≠ 0) :
    (rowM ρ c j).det ≠ 0 := by
  have hT : ((1 : Matrix ι ι k).updateRow c ρ).det = ρ c := by
    have h := Matrix.cramer_transpose_apply (1 : Matrix ι ι k) ρ c
    rw [Matrix.transpose_one, Matrix.cramer_one] at h
    simpa using h.symm
  have h := Matrix.det_permute (Equiv.swap c j) ((1 : Matrix ι ι k).updateRow c ρ)
  have h2 : (rowM ρ c j).det = _ := h
  rw [h2, hT]
  refine mul_ne_zero ?_ hc
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap c j)) with e | e <;> simp [e]

theorem rowM_row {ι : Type} [DecidableEq ι] (ρ : ι → k) (c j : ι) : rowM ρ c j j = ρ := by
  ext x
  show ((1 : Matrix ι ι k).updateRow c ρ) (Equiv.swap c j j) x = ρ x
  simp

theorem rowM_zero {ι : Type} [DecidableEq ι] (s : ι → Prop) (ρ : ι → k) (c j : ι) (hc : s c) (hj : s j)
    (r x : ι) (hr : ¬ s r) (hx : s x) : rowM ρ c j r x = 0 := by
  have hrc : r ≠ c := fun e => hr (e ▸ hc)
  have hrj : r ≠ j := fun e => hr (e ▸ hj)
  have hrx : r ≠ x := fun e => hr (e ▸ hx)
  show ((1 : Matrix ι ι k).updateRow c ρ) (Equiv.swap c j r) x = 0
  rw [Equiv.swap_apply_of_ne_of_ne hrc hrj, Matrix.updateRow_ne hrc, Matrix.one_apply_ne hrx]

open Classical in

def rowB {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ι → k) (c j : ι) : GL ι k :=
  if h : (rowM ρ c j).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero _ h else 1

theorem rowB_val {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ι → k) (c j : ι) (hc : ρ c ≠ 0) :
    (rowB ρ c j).val = rowM ρ c j := by
  rw [rowB, dif_pos (rowM_det_ne ρ c j hc)]
  rfl

end Alg

section Top

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]

theorem continuousOn_GL {X ι : Type} [TopologicalSpace X] [Fintype ι] [DecidableEq ι] (f : X → GL ι k) (V : Set X)
    (hf : ContinuousOn (fun x => (f x).val) V) : ContinuousOn f V := by
  rw [continuousOn_iff_continuous_restrict] at hf ⊢
  refine Units.continuous_iff.2 ⟨hf, ?_⟩
  have hdet : Continuous fun x : V => ((f x).val).det := hf.matrix_det
  have hne : ∀ x : V, ((f x).val).det ≠ 0 := fun x => (Matrix.GeneralLinearGroup.det (f x)).ne_zero
  have e : (fun x : V => (((f x)⁻¹ : GL ι k)).val) = fun x : V => (((f x).val).det)⁻¹ • ((f x).val).adjugate := by
    funext x
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  show Continuous (fun x : V => (((f x)⁻¹ : GL ι k)).val)
  rw [e]
  exact (hdet.inv₀ hne).smul hf.matrix_adjugate

theorem continuousOn_rowM {X ι : Type} [TopologicalSpace X] [DecidableEq ι] (ρ : X → ι → k) (c j : ι)
    (hρ : Continuous ρ) : Continuous fun x => rowM (ρ x) c j := by
  refine continuous_matrix fun a b => ?_
  show Continuous fun x => ((1 : Matrix ι ι k).updateRow c (ρ x)) (Equiv.swap c j a) b
  by_cases h : Equiv.swap c j a = c
  · simp only [h, Matrix.updateRow_self]
    exact (continuous_apply b).comp hρ
  · simp only [Matrix.updateRow_ne h]
    exact continuous_const

end Top

section Group

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem core' (i t : ℕ) (p : Mir k ((i + 1) + t + 1)) (X B : GL (Fin ((i + 1) + t + 1)) k) (j : Fin ((i + 1) + t + 1))
    (hX : X.val j = eLast k ((i + 1) + t))
    (hBj : B.val j = (mirabolicProjection k _ p⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val (Fin.last ((i + 1) + t)))
    (hB : ∀ r x : Fin ((i + 1) + t + 1), ¬ r.val < i + 1 → x.val < i + 1 → B.val r x = 0) :
    ∃ hM : (X⁻¹ * B * mirabolicProjection k _ p) ∈ Mir k ((i + 1) + t), ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k),
      p = h * dEmb k i t d * levi k _ X * sEmb k ((i + 1) + t) ⟨_, hM⟩ := by
  set g : GL (Fin ((i + 1) + t + 1)) k := mirabolicProjection k _ p with hg
  have hginv : mirabolicProjection k _ p⁻¹ = g⁻¹ := map_inv _ _
  rw [hginv] at hBj
  have hM : (X⁻¹ * B * g) ∈ Mir k ((i + 1) + t) := by
    have h1 : (g⁻¹ * (B⁻¹ * X)) ∈ Mir k ((i + 1) + t) := by
      rw [mem_Mir_iff, Units.val_mul, Matrix.mul_apply_eq_vecMul, ← hBj, ← Matrix.mul_apply_eq_vecMul, ← Units.val_mul,
        mul_inv_cancel_left, hX]
    have h2 := (Mir k ((i + 1) + t)).inv_mem h1
    simpa [mul_assoc] using h2
  let v : Fin ((i + 1) + (t + 1)) → k := fun r =>
    (p : GL (Fin ((i + 1) + t + 1 + 1)) k).val (Fin.castSucc r) (Fin.last _)
  let v' : Fin ((i + 1) + (t + 1)) → k := B.val.mulVec v
  let a : Fin ((i + 1) + (t + 1)) → k := Fin.append (fun x => v' (Fin.castAdd (t + 1) x)) (0 : Fin (t + 1) → k)
  let d : Fin (t + 1) → k := fun x => v' (Fin.natAdd (i + 1) x)
  let b : Fin ((i + 1) + (t + 1)) → k := Fin.append (0 : Fin (i + 1) → k) d
  have hsum : a + b = v' := by
    funext x
    induction x using Fin.addCases with
    | left x => simp [a, b]
    | right x => simp [a, b, d]
  let ua : Mir k ((i + 1) + t + 1) := ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd a), MirU_le_Mir k _ ⟨_, rfl⟩⟩
  have hua : ua ∈ HPG k (i + 1) (t + 1) := by
    refine mem_HPG_of (I := i + 1) (T := t + 1) ua ?_ ?_
    · intro x y
      refine unip_castSucc_castSucc _ a _ _ ?_
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
    · intro x
      refine (unip_apply_castSucc_last k _ _ _).trans ?_
      show a (Fin.natAdd (i + 1) x) = 0
      simp [a]
  have hlB : levi k _ B⁻¹ ∈ HPG k (i + 1) (t + 1) := by
    have : levi k _ B ∈ HPG k (i + 1) (t + 1) := by
      refine mem_HPG_of (I := i + 1) (T := t + 1) _ ?_ ?_
      · intro x y
        refine (glEmb_castSucc_castSucc _ B _ _).trans ?_
        exact hB _ _ (by simp; omega) (by simp; omega)
      · intro x
        exact glEmb_castSucc_last _ B _
    rw [map_inv]
    exact (HPG k (i + 1) (t + 1)).inv_mem this
  refine ⟨hM, levi k _ B⁻¹ * ua, (HPG k (i + 1) (t + 1)).mul_mem hlB hua, d, ?_⟩
  apply Subtype.ext
  have hp : (p : GL (Fin ((i + 1) + t + 1 + 1)) k) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) * glEmb k _ g := eq_unip_glEmb p
  have e1 : unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) *
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v') := by
    rw [← map_mul, ← ofAdd_add, hsum]
  have e2 : glEmb k _ B * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v') * glEmb k _ B := glEmb_mul_unip' k _ B _
  have e3 : glEmb k _ X * glEmb k _ (X⁻¹ * B * g) = glEmb k _ B * glEmb k _ g := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  show (p : GL (Fin ((i + 1) + t + 1 + 1)) k) = glEmb k _ B⁻¹ * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) *
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b) *
      glEmb k _ X * glEmb k _ (X⁻¹ * B * g)
  calc (p : GL (Fin ((i + 1) + t + 1 + 1)) k)
      = (glEmb k _ B)⁻¹ * (glEmb k _ B * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v)) * glEmb k _ g := by
        rw [hp]; group
    _ = (glEmb k _ B)⁻¹ * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v') * (glEmb k _ B * glEmb k _ g) := by
        rw [e2]; simp only [mul_assoc]
    _ = _ := by
        rw [← e3, ← e1, map_inv]; simp only [mul_assoc]

end Group

theorem chart :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ)
      (p₀ : Mir k ((i + 1) + t + 1)), p₀ ∉ Cl k i t →
  ∃ V ∈ nhds p₀, ∃ μ : Mir k ((i + 1) + t + 1) → Mir k ((i + 1) + t), ContinuousOn μ V ∧
    ∀ p ∈ V, ∃ h ∈ HPG k (i + 1) (t + 1), ∃ d : Fin (t + 1) → k,
      p = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) (μ p) := by
  classical
  intro k _ _ _ _ i t p₀ h₀
  have hp' : ¬ _ := fun h => h₀ ((Cl_iff i t p₀).2 h)
  push_neg at hp'
  obtain ⟨c, hcs, hc⟩ := hp'
  have hj : (piPerm i t (Fin.last ((i + 1) + t))).val < i + 1 := by rw [piPerm_last_val]; omega
  set j := piPerm i t (Fin.last ((i + 1) + t)) with hjdef
  let ρ : Mir k ((i + 1) + t + 1) → Fin ((i + 1) + t + 1) → k := fun p =>
    (mirabolicProjection k _ p⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val (Fin.last ((i + 1) + t))
  have hG : Continuous fun p : Mir k ((i + 1) + t + 1) => mirabolicProjection k _ p :=
    GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k _
  have hρ : Continuous ρ := by
    have hv : Continuous fun p : Mir k ((i + 1) + t + 1) =>
        ((mirabolicProjection k _ p⁻¹ : GL (Fin ((i + 1) + t + 1)) k) : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) :=
      Units.continuous_val.comp (hG.comp continuous_inv)
    exact continuous_pi fun x => hv.matrix_elem _ _
  let V : Set (Mir k ((i + 1) + t + 1)) := {p | ρ p c ≠ 0}
  have hV : IsOpen V := isOpen_ne_fun ((continuous_apply c).comp hρ) continuous_const
  let W : Mir k ((i + 1) + t + 1) → GL (Fin ((i + 1) + t + 1)) k := fun p =>
    (wGL k i t)⁻¹ * rowB (ρ p) c j * mirabolicProjection k _ p
  let μ : Mir k ((i + 1) + t + 1) → Mir k ((i + 1) + t) := fun p =>
    if h : W p ∈ Mir k ((i + 1) + t) then ⟨W p, h⟩ else 1
  have key : ∀ p ∈ V, ∃ hM : W p ∈ Mir k ((i + 1) + t), ∃ h ∈ HPG k (i + 1) (t + 1), ∃ d : Fin (t + 1) → k,
      p = h * dEmb k i t d * levi k _ (wGL k i t) * sEmb k ((i + 1) + t) ⟨_, hM⟩ := by
    intro p hp
    refine core' i t p (wGL k i t) (rowB (ρ p) c j) j (wGL_row i t) ?_ ?_
    · rw [rowB_val _ _ _ hp, rowM_row]
    · intro r x hr hx
      rw [rowB_val _ _ _ hp]
      exact rowM_zero (fun x : Fin ((i + 1) + t + 1) => x.val < i + 1) _ c j hcs hj r x hr hx
  refine ⟨V, hV.mem_nhds hc, μ, ?_, ?_⟩
  · have hB : ContinuousOn (fun p => rowB (ρ p) c j) V := by
      refine continuousOn_GL _ _ ?_
      refine (continuousOn_rowM ρ c j hρ).continuousOn.congr ?_
      intro p hp
      exact rowB_val _ _ _ hp
    have hW : ContinuousOn W V :=
      (continuousOn_const.mul hB).mul hG.continuousOn
    refine (Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_iff).2 ?_
    refine hW.congr ?_
    intro p hp
    obtain ⟨hM, -⟩ := key p hp
    show ((μ p : Mir k ((i + 1) + t)) : GL _ k) = W p
    simp only [μ, dif_pos hM]
  · intro p hp
    obtain ⟨hM, h, hh, d, e⟩ := key p hp
    refine ⟨h, hh, d, ?_⟩
    have hμ : μ p = ⟨W p, hM⟩ := dif_pos hM
    rw [hμ]
    exact e

end GlobalTheory.CompanionTheory.BZPhiPG.Chart

end
