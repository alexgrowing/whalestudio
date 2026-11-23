import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.GelFlagA

noncomputable section

open Matrix Module
open scoped ContDiff

namespace PositivityTheory.RgBcC.VC.GFB

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def lmul (a b : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => a * y * b
      map_add' := fun y z => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c y => by simp [Matrix.mul_smul, Matrix.smul_mul] }

theorem lmul_apply (a b y : Mat n) : lmul a b y = a * y * b := rfl

theorem mul_mem_GLs {a y b : Mat n} (ha : a ∈ GLs n) (hy : y ∈ GLs n) (hb : b ∈ GLs n) : a * y * b ∈ GLs n := by
  show (a * y * b).det ≠ 0
  rw [Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero ha hy) hb

theorem comp_lmul {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {F : Mat n → V} (hF : ContDiffOn ℝ ∞ F (GLs n))
    {a b : Mat n} (ha : a ∈ GLs n) (hb : b ∈ GLs n) : ContDiffOn ℝ ∞ (fun y => F (a * y * b)) (GLs n) :=
  hF.comp (lmul a b).contDiff.contDiffOn fun _ hy => mul_mem_GLs ha hy hb

theorem gel_sub (hGC : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (s : Bool) (m : ℕ)
    {F₁ F₂ : Mat n → V} (h₁ : ContDiffOn ℝ ∞ F₁ (GLs n)) (h₂ : ContDiffOn ℝ ∞ F₂ (GLs n)) {g₀ : Mat n} (hg₀ : g₀ ∈ GLs n) :
    gel s m (fun y => F₁ y - F₂ y) g₀ = gel s m F₁ g₀ - gel s m F₂ g₀ := by
  have hP : ContDiffOn ℝ ∞ (fun y => (F₁ y, F₂ y)) (GLs n) := h₁.prodMk h₂
  have hc := (hGC n (V × V) V s m _ hP).2 g₀ hg₀
  have c1 := hc.2.2 (ContinuousLinearMap.fst ℂ V V - ContinuousLinearMap.snd ℂ V V)
  have c2 := hc.2.2 (ContinuousLinearMap.fst ℂ V V)
  have c3 := hc.2.2 (ContinuousLinearMap.snd ℂ V V)
  have e1 : (fun y => (ContinuousLinearMap.fst ℂ V V - ContinuousLinearMap.snd ℂ V V) (F₁ y, F₂ y)) =
      fun y => F₁ y - F₂ y := by funext y; simp
  have e2 : (fun y => (ContinuousLinearMap.fst ℂ V V) (F₁ y, F₂ y)) = F₁ := by funext y; simp
  have e3 : (fun y => (ContinuousLinearMap.snd ℂ V V) (F₁ y, F₂ y)) = F₂ := by funext y; simp
  rw [e1] at c1; rw [e2] at c2; rw [e3] at c3
  rw [c1, c2, c3]; simp

theorem gel_transport (hGC : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (s : Bool) (m : ℕ)
    {F : Mat n → V} (hF : ContDiffOn ℝ ∞ F (GLs n)) {a b : Mat n} (ha : a ∈ GLs n) (hb : b ∈ GLs n) :
    gel s m (fun y => F (a * y * b)) 1 = gel s m F (a * b) := by
  have hF' : ContDiffOn ℝ ∞ (fun y => F (a * y)) (GLs n) := by
    simpa using comp_lmul hF ha (show (1 : Mat n) ∈ GLs n by show (1 : Mat n).det ≠ 0; simp)
  have h1 := ((hGC n V V s m _ hF').2 1 (show (1 : Mat n) ∈ GLs n by show (1 : Mat n).det ≠ 0; simp)).2.1 b hb
  have h2 := ((hGC n V V s m _ hF).2 b hb).2.1 a ha
  have e : (fun y => F (a * y * b)) = fun y => (fun y' => F (a * y')) (y * b) := by
    funext y; simp [Matrix.mul_assoc]
  rw [e, h1.2, one_mul, h2.1]

theorem map_eq_of_le {W : Submodule ℂ (Fin n → ℂ)} {q : Mat n} (hq : IsUnit q) (h : ∀ v ∈ W, q *ᵥ v ∈ W) :
    W.map (Matrix.mulVecLin q) = W := by
  have hinj : Function.Injective (Matrix.mulVecLin q) := Matrix.mulVec_injective_iff_isUnit.2 hq
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩; exact h v hv
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W)).symm

end PositivityTheory.RgBcC.VC.GFB
