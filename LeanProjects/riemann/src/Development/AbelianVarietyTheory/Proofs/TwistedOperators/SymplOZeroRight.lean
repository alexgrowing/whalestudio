import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.AnnPieces

variable {D : D7}

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  unfold hO
  simp only [Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_zero_right (S T : HSp D) (x : WO S T) : hO S T x 0 = 0 := by
  unfold hO
  simp

theorem hO_zero_left (S T : HSp D) (y : WO S T) : hO S T 0 y = 0 := by
  unfold hO
  simp

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO
  rw [hO_add_right, mul_add, map_add]

theorem symplO_zero_right (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  unfold symplO
  rw [hO_zero_right, mul_zero, map_zero]

theorem symplO_neg_right (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := symplO_add_right S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem mxAt_mul {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {a : Mx D m n} (ha : MxAt P a) (M : Mx D n k) : MxAt P (a ⬝ M) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem mxAt_zero {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} : MxAt P (0 : Mx D m n) := fun _ _ => zero_mem _

theorem mxAt_add {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {a b : Mx D m n} (ha : MxAt P a) (hb : MxAt P b) : MxAt P (a + b) :=
  fun i j => add_mem (ha i j) (hb i j)

theorem mxAt_neg {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {a : Mx D m n} (ha : MxAt P a) : MxAt P (-a) :=
  fun i j => neg_mem (ha i j)

variable {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

theorem hO_extY_right (u : WO V W) (a' : Mx D W.rank ρ) : hO V W u (d.extY W a') = hO V W (d.extX W (u ⬝ d.jX)) (d.extY W a') := by
  rw [d.hO_coordS, d.hO_coordS]
  simp only [HypDec.extY_apply, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pY_jX, HypDec.pY_j0, HypDec.pY_jY,
    HypDec.pX_jX, HypDec.pX_j0, HypDec.pX_jY, Matrix.mul_zero, Matrix.mul_one, hO_zero_right, pairS, adj_zero,
    Matrix.zero_mul, Matrix.trace_zero, add_zero]

theorem hO_extX_left (a : Mx D W.rank ρ) (u' : WO V W) : hO V W (d.extX W a) u' = hO V W (d.extX W a) (d.extY W (u' ⬝ d.jY)) := by
  rw [d.hO_coordS, d.hO_coordS]
  simp only [HypDec.extY_apply, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pY_jX, HypDec.pY_j0, HypDec.pY_jY,
    HypDec.pX_jX, HypDec.pX_j0, HypDec.pX_jY, Matrix.mul_zero, Matrix.mul_one, pairS, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.trace_zero, add_zero, zero_add, hO_zero_left, hO_zero_right]

end GlobalTheory.AscFin.AnnPieces

namespace GlobalTheory.AscFin.AnnPieces

variable {D : D7} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (d : HypDec V V₀ ρ) (ψ : AddChar (AF D.host.F) ℂ) (Γ : AddSubgroup (WO V W))

theorem symplO_extY_right (u : WO V W) (a' : Mx D W.rank ρ) :
    symplO V W u (d.extY W a') = symplO V W (d.extX W (u ⬝ d.jX)) (d.extY W a') := by
  unfold symplO
  rw [hO_extY_right]

theorem symplO_extX_left (a : Mx D W.rank ρ) (u' : WO V W) :
    symplO V W (d.extX W a) u' = symplO V W (d.extX W a) (d.extY W (u' ⬝ d.jY)) := by
  unfold symplO
  rw [← hO_extX_left]

theorem extY_mul_jY (a' : Mx D W.rank ρ) : d.extY W a' ⬝ d.jY = a' := by
  rw [HypDec.extY_apply, Matrix.mul_assoc, HypDec.pY_jY, Matrix.mul_one]

theorem extX_mul_jX (a : Mx D W.rank ρ) : d.extX W a ⬝ d.jX = a := by
  rw [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]

def annY : AddSubgroup (Mx D W.rank ρ) where
  carrier := {a' | MxAt (fun _ => True) a' ∧ ∀ a, d.extX W a ∈ Γ → ψ (symplO V W (d.extX W a) (d.extY W a')) = 1}
  zero_mem' := ⟨mxAt_zero, fun a _ => by rw [map_zero, symplO_zero_right, AddChar.map_zero_eq_one]⟩
  add_mem' := fun {x y} hx hy => ⟨mxAt_add hx.1 hy.1, fun a ha => by
    rw [map_add, symplO_add_right, AddChar.map_add_eq_mul, hx.2 a ha, hy.2 a ha, one_mul]⟩
  neg_mem' := fun {x} hx => ⟨mxAt_neg hx.1, fun a ha => by
    rw [map_neg, symplO_neg_right, AddChar.map_neg_eq_inv, hx.2 a ha, inv_one]⟩

def annSet : Set (WO V W) := {u' | MxAt (fun _ => True) u' ∧ ∀ u ∈ Γ, ψ (symplO V W u u') = 1}

variable {d ψ Γ}

theorem extY_mem_annSet (hX : ∀ u ∈ Γ, d.extX W (u ⬝ d.jX) ∈ Γ) {a' : Mx D W.rank ρ} (ha' : a' ∈ annY d ψ Γ) :
    d.extY W a' ∈ annSet ψ Γ :=
  ⟨mxAt_mul ha'.1 _, fun u hu => by rw [symplO_extY_right]; exact ha'.2 _ (hX u hu)⟩

theorem mul_jY_mem_annY {u' : WO V W} (hu' : u' ∈ annSet ψ Γ) : u' ⬝ d.jY ∈ annY d ψ Γ :=
  ⟨mxAt_mul hu'.1 _, fun a ha => by rw [← symplO_extX_left]; exact hu'.2 _ ha⟩

theorem annY_eq_image (hX : ∀ u ∈ Γ, d.extX W (u ⬝ d.jX) ∈ Γ) :
    (annY d ψ Γ : Set (Mx D W.rank ρ)) = (fun u : WO V W => u ⬝ d.jY) '' annSet ψ Γ :=
  Set.ext fun a' => ⟨fun h => ⟨_, extY_mem_annSet hX h, extY_mul_jY d a'⟩, by
    rintro ⟨u, hu, rfl⟩
    exact mul_jY_mem_annY hu⟩

theorem A₂_eq (dW : HypDec W W₀ σ) (Γ₂ : AddSubgroup (WO V W)) :
    (piecesOf d dW ψ Γ Γ₂).A₂ = annY d ψ Γ := by
  show AddSubgroup.closure (annY d ψ Γ : Set (Mx D W.rank ρ)) = _
  exact AddSubgroup.closure_eq _

theorem pieces_dualA (dW : HypDec W W₀ σ) (Γ₂ : AddSubgroup (WO V W))
    (hX : ∀ u ∈ Γ, d.extX W (u ⬝ d.jX) ∈ Γ)
    (hc : IsCompact (annSet ψ Γ))
    (ho : ∃ U : Set (WO V W), IsOpen U ∧ (0 : WO V W) ∈ U ∧
      ∀ u' ∈ U, MxAt (fun _ => True) u' → ∀ u ∈ Γ, ψ (symplO V W u u') = 1)
    (hb : ∀ u, MxAt (fun _ => True) u → (∀ u' ∈ annSet ψ Γ, ψ (symplO V W u u') = 1) → u ∈ Γ) :
    FinLat (piecesOf d dW ψ Γ Γ₂).A₂ ∧
      (∀ a, MxAt (fun _ => True) a → (a ∈ (piecesOf d dW ψ Γ Γ₂).A₁ ↔
        ∀ a' ∈ (piecesOf d dW ψ Γ Γ₂).A₂, ψ (symplO V W (d.extX W a) (d.extY W a')) = 1)) ∧
      (∀ a', MxAt (fun _ => True) a' → (a' ∈ (piecesOf d dW ψ Γ Γ₂).A₂ ↔
        ∀ a ∈ (piecesOf d dW ψ Γ Γ₂).A₁, ψ (symplO V W (d.extX W a) (d.extY W a')) = 1)) := by
  rw [A₂_eq]
  refine ⟨⟨fun a' ha' => ha'.1, ?_, ?_⟩, fun a ha => ⟨fun h a' ha' => ha'.2 a h, fun h => ?_⟩,
    fun a' ha' => ⟨fun h a ha => h.2 a ha, fun h => ⟨ha', h⟩⟩⟩
  · rw [annY_eq_image hX]
    exact hc.image (continuous_id.matrix_mul continuous_const)
  · obtain ⟨U, hU, h0, hUm⟩ := ho
    refine ⟨(fun a' => d.extY W a') ⁻¹' U, hU.preimage (continuous_id.matrix_mul continuous_const), ?_, ?_⟩
    · show d.extY W 0 ∈ U
      rw [map_zero]
      exact h0
    · intro a' ha' hfin
      refine ⟨hfin, fun b hb' => ?_⟩
      have := hUm _ ha' (mxAt_mul hfin _) _ hb'
      rwa [symplO_extY_right, extX_mul_jX] at this
  · show d.extX W a ∈ Γ
    refine hb _ (mxAt_mul ha _) fun u' hu' => ?_
    rw [symplO_extX_left]
    exact h _ (mul_jY_mem_annY hu')

end GlobalTheory.AscFin.AnnPieces

end
