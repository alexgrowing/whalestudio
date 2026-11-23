import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact

noncomputable section

namespace GlobalTheory.Doubling

open Matrix Formalism.UG

variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}

section Block

variable (e : m ⊕ n ≃ ι)

def blkMat (x : Matrix m m A) (y : Matrix n n A) : Matrix ι ι A := (fromBlocks x 0 0 y).submatrix e.symm e.symm

def pairVec {X : Type} (x : m → X) (y : n → X) : ι → X := Sum.elim x y ∘ e.symm

@[simp] theorem pairVec_inl {X : Type} (x : m → X) (y : n → X) (i : m) : pairVec e x y (e (.inl i)) = x i := by
  simp [pairVec]

@[simp] theorem pairVec_inr {X : Type} (x : m → X) (y : n → X) (i : n) : pairVec e x y (e (.inr i)) = y i := by
  simp [pairVec]

theorem pairVec_eta {X : Type} (w : ι → X) : pairVec e (fun i => w (e (.inl i))) (fun i => w (e (.inr i))) = w := by
  funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp

theorem submatrix_blkMat (x : Matrix m m A) (y : Matrix n n A) : (blkMat e x y).submatrix e e = fromBlocks x 0 0 y := by
  simp [blkMat]

theorem submatrix_inj {M N : Matrix ι ι A} (h : M.submatrix e e = N.submatrix e e) : M = N := by
  simpa using congrArg (fun X => X.submatrix e.symm e.symm) h

theorem blkMat_map (f : A → B) (hf : f 0 = 0) (x : Matrix m m A) (y : Matrix n n A) :
    (blkMat e x y).map f = blkMat e (x.map f) (y.map f) := by
  simp [blkMat, ← submatrix_map, fromBlocks_map, Matrix.map_zero _ hf]

theorem cT_blkMat (σ : A →+* A) (x : Matrix m m A) (y : Matrix n n A) :
    cT σ (blkMat e x y) = blkMat e (cT σ x) (cT σ y) := by
  rw [cT, blkMat_map e _ (map_zero σ)]
  simp [blkMat, cT, fromBlocks_transpose]

theorem blkMat_inj {x x' : Matrix m m A} {y y' : Matrix n n A} : blkMat e x y = blkMat e x' y' ↔ x = x' ∧ y = y' := by
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2]⟩
  have := congrArg (fun X => X.submatrix e e) h
  simpa [submatrix_blkMat] using this

variable [Fintype m] [Fintype n] [Fintype ι]

theorem blkMat_mul (x x' : Matrix m m A) (y y' : Matrix n n A) :
    blkMat e x y * blkMat e x' y' = blkMat e (x * x') (y * y') := by
  simp [blkMat, submatrix_mul_equiv, fromBlocks_multiply]

theorem mulVec_pairVec (M : Matrix ι ι A) (x : m → A) (y : n → A) : M *ᵥ pairVec e x y =
    pairVec e ((M.submatrix e e).toBlocks₁₁ *ᵥ x + (M.submatrix e e).toBlocks₁₂ *ᵥ y)
      ((M.submatrix e e).toBlocks₂₁ *ᵥ x + (M.submatrix e e).toBlocks₂₂ *ᵥ y) := by
  funext j
  obtain ⟨i | i, rfl⟩ := e.surjective j <;>
    simp [mulVec, dotProduct, ← e.sum_comp, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]

theorem pairVec_vecMul (M : Matrix ι ι A) (x : m → A) (y : n → A) : pairVec e x y ᵥ* M =
    pairVec e (x ᵥ* (M.submatrix e e).toBlocks₁₁ + y ᵥ* (M.submatrix e e).toBlocks₂₁)
      (x ᵥ* (M.submatrix e e).toBlocks₁₂ + y ᵥ* (M.submatrix e e).toBlocks₂₂) := by
  funext j
  obtain ⟨i | i, rfl⟩ := e.surjective j <;>
    simp [vecMul, dotProduct, ← e.sum_comp, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]

theorem blkMat_mulVec (x : Matrix m m A) (y : Matrix n n A) (u : m → A) (v : n → A) :
    blkMat e x y *ᵥ pairVec e u v = pairVec e (x *ᵥ u) (y *ᵥ v) := by
  simp [mulVec_pairVec, submatrix_blkMat]

variable [DecidableEq m] [DecidableEq n] [DecidableEq ι]

omit [Fintype m] [Fintype n] [Fintype ι] in
theorem blkMat_one : blkMat e (1 : Matrix m m A) (1 : Matrix n n A) = 1 := by simp [blkMat]

theorem det_blkMat (x : Matrix m m A) (y : Matrix n n A) : (blkMat e x y).det = x.det * y.det := by
  simp [blkMat]

def blkGL : GL m A × GL n A →* GL ι A where
  toFun g := ⟨blkMat e g.1.1 g.2.1, blkMat e (g.1⁻¹).1 (g.2⁻¹).1, by simp [blkMat_mul, blkMat_one],
    by simp [blkMat_mul, blkMat_one]⟩
  map_one' := Units.ext (blkMat_one e)
  map_mul' _ _ := Units.ext (blkMat_mul e _ _ _ _).symm

@[simp] theorem val_blkGL (g : GL m A × GL n A) : (blkGL e g).1 = blkMat e g.1.1 g.2.1 := rfl

theorem blkGL_injective : Function.Injective (blkGL (A := A) e) := fun _ _ h =>
  have := (blkMat_inj e).1 (congrArg Units.val h)
  Prod.ext (Units.ext this.1) (Units.ext this.2)

theorem bc_blkGL (f : A →+* B) (x : GL m A) (y : GL n A) : bc f (blkGL e (x, y)) = blkGL e (bc f x, bc f y) :=
  Units.ext (blkMat_map e f (map_zero f) _ _)

theorem blkGL_mem_UJ {σ : A →+* A} {J : Matrix m m A} {J' : Matrix n n A} {x : GL m A} {y : GL n A} :
    blkGL e (x, y) ∈ UJ σ (blkMat e J J') ↔ x ∈ UJ σ J ∧ y ∈ UJ σ J' := by
  change cT σ (blkMat e x.1 y.1) * _ * blkMat e x.1 y.1 = _ ↔ _
  rw [cT_blkMat, blkMat_mul, blkMat_mul, blkMat_inj]
  rfl

theorem UJ_neg (σ : A →+* A) (J : Matrix n n A) : UJ σ (-J) = UJ σ J := by
  ext g
  change cT σ g.1 * (-J) * g.1 = -J ↔ cT σ g.1 * J * g.1 = J
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem continuous_blkGL [TopologicalSpace A] : Continuous (blkGL (A := A) e) := by
  have h : Continuous fun p : Matrix m m A × Matrix n n A => blkMat e p.1 p.2 :=
    (continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd).matrix_submatrix _ _
  exact Units.continuous_iff.2 ⟨h.comp ((Units.continuous_val.comp continuous_fst).prodMk
    (Units.continuous_val.comp continuous_snd)), h.comp ((Units.continuous_coe_inv.comp continuous_fst).prodMk
    (Units.continuous_coe_inv.comp continuous_snd))⟩

omit [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι]

def sumLat {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] (L : Submodule O (m → X)) (L' : Submodule O (n → X)) :
    Submodule O (ι → X) :=
  L.comap (LinearMap.funLeft O X (e ∘ .inl)) ⊓ L'.comap (LinearMap.funLeft O X (e ∘ .inr))

theorem mem_sumLat {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {L : Submodule O (m → X)}
    {L' : Submodule O (n → X)} {w : ι → X} :
    w ∈ sumLat e L L' ↔ (fun i => w (e (.inl i))) ∈ L ∧ (fun i => w (e (.inr i))) ∈ L' := Iff.rfl

theorem pairVec_mem_sumLat {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {L : Submodule O (m → X)}
    {L' : Submodule O (n → X)} {x : m → X} {y : n → X} : pairVec e x y ∈ sumLat e L L' ↔ x ∈ L ∧ y ∈ L' := by
  simp [mem_sumLat]

theorem blkGL_mem_stabGL [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι]
    {O : Type} [CommRing O] [Algebra O A] {L : Submodule O (m → A)} {L' : Submodule O (n → A)} {x : GL m A} {y : GL n A} :
    blkGL e (x, y) ∈ stabGL (sumLat e L L') ↔ x ∈ stabGL L ∧ y ∈ stabGL L' := by
  refine ⟨fun h => ⟨fun u => ?_, fun v => ?_⟩, fun h w => ?_⟩
  · simpa [blkMat_mulVec, pairVec_mem_sumLat] using h (pairVec e u 0)
  · simpa [blkMat_mulVec, pairVec_mem_sumLat] using h (pairVec e 0 v)
  · rw [← pairVec_eta e w, val_blkGL, blkMat_mulVec, pairVec_mem_sumLat, pairVec_mem_sumLat]
    exact and_congr (h.1 _) (h.2 _)

end Block

section Siegel

variable (e : n ⊕ n ≃ ι)

def dblGram (J : Matrix n n A) : Matrix ι ι A := blkMat e J (-J)

variable (A) in

def diagSub : Submodule A (ι → A) :=
  LinearMap.eqLocus (LinearMap.funLeft A A (e ∘ .inl)) (LinearMap.funLeft A A (e ∘ .inr))

variable (A) in

def antiSub : Submodule A (ι → A) :=
  LinearMap.eqLocus (LinearMap.funLeft A A (e ∘ .inl)) (-LinearMap.funLeft A A (e ∘ .inr))

theorem pairVec_mem_diagSub {x y : n → A} : pairVec e x y ∈ diagSub A e ↔ x = y := by
  simp [diagSub, funext_iff, LinearMap.funLeft_apply]

theorem pairVec_mem_antiSub {x y : n → A} : pairVec e x y ∈ antiSub A e ↔ x = -y := by
  simp [antiSub, funext_iff, LinearMap.funLeft_apply]

theorem mem_diagSub {w : ι → A} : w ∈ diagSub A e ↔ ∃ x, w = pairVec e x x := by
  refine ⟨fun h => ⟨fun i => w (e (.inl i)), ?_⟩, by rintro ⟨x, rfl⟩; exact (pairVec_mem_diagSub e).2 rfl⟩
  rw [← pairVec_eta e w, pairVec_mem_diagSub] at h
  nth_rewrite 2 [h]
  exact (pairVec_eta e w).symm

theorem mem_antiSub {w : ι → A} : w ∈ antiSub A e ↔ ∃ x, w = pairVec e x (-x) := by
  refine ⟨fun h => ⟨fun i => w (e (.inl i)), ?_⟩, by rintro ⟨x, rfl⟩; exact (pairVec_mem_antiSub e).2 (neg_neg _).symm⟩
  rw [← pairVec_eta e w, pairVec_mem_antiSub] at h
  nth_rewrite 2 [h]
  rw [neg_neg]
  exact (pairVec_eta e w).symm

theorem isCompl_diagSub_antiSub [Invertible (2 : A)] : IsCompl (diagSub A e) (antiSub A e) := by
  have h2 : ⅟(2 : A) * 2 = 1 := invOf_mul_self _
  refine ⟨Submodule.disjoint_def.2 fun w h h' => ?_, codisjoint_iff.2 (eq_top_iff.2 fun w _ => ?_)⟩
  · obtain ⟨x, rfl⟩ := (mem_diagSub e).1 h
    have h3 := (pairVec_mem_antiSub e).1 h'
    have : x = 0 := funext fun i => by
      have := congrFun h3 i
      simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
      linear_combination ⅟(2 : A) * this - x i * h2
    rw [this]; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  · refine Submodule.mem_sup.2 ⟨_, (mem_diagSub e).2 ⟨fun i => ⅟(2 : A) * (w (e (.inl i)) + w (e (.inr i))), rfl⟩,
      _, (mem_antiSub e).2 ⟨fun i => ⅟(2 : A) * (w (e (.inl i)) - w (e (.inr i))), rfl⟩, funext fun j => ?_⟩
    obtain ⟨i | i, rfl⟩ := e.surjective j
    · simp only [Pi.add_apply, pairVec_inl]; linear_combination w (e (.inl i)) * h2
    · simp only [Pi.add_apply, pairVec_inr, Pi.neg_apply]; linear_combination w (e (.inr i)) * h2

def leviMat (M : Matrix ι ι A) : Matrix n n A := (M.submatrix e e).toBlocks₁₁ + (M.submatrix e e).toBlocks₁₂

def quotMat (M : Matrix ι ι A) : Matrix n n A := (M.submatrix e e).toBlocks₁₁ - (M.submatrix e e).toBlocks₂₁

def KeepsDiag (M : Matrix ι ι A) : Prop :=
  (M.submatrix e e).toBlocks₂₁ + (M.submatrix e e).toBlocks₂₂ = leviMat e M

theorem leviMat_blkMat (x y : Matrix n n A) : leviMat e (blkMat e x y) = x := by simp [leviMat, submatrix_blkMat]
theorem keepsDiag_blkMat {x y : Matrix n n A} : KeepsDiag e (blkMat e x y) ↔ y = x := by
  simp [KeepsDiag, leviMat, submatrix_blkMat]

theorem leviMat_map (f : A →+* B) (M : Matrix ι ι A) : leviMat e (M.map f) = (leviMat e M).map f := by
  ext i j; simp [leviMat, toBlocks₁₁, toBlocks₁₂]

theorem keepsDiag_iff {M : Matrix ι ι A} : KeepsDiag e M ↔ ∀ i j,
    M (e (.inr i)) (e (.inl j)) + M (e (.inr i)) (e (.inr j)) =
      M (e (.inl i)) (e (.inl j)) + M (e (.inl i)) (e (.inr j)) := by
  exact Matrix.ext_iff.symm

theorem KeepsDiag.map {M : Matrix ι ι A} (h : KeepsDiag e M) (f : A →+* B) : KeepsDiag e (M.map f) :=
  (keepsDiag_iff e).2 fun i j => by simpa using congrArg f ((keepsDiag_iff e).1 h i j)

variable [Fintype n] [Fintype ι]

theorem hform_dblGram (σ : A →+* A) (J : Matrix n n A) (x y x' y' : n → A) :
    hform σ (dblGram e J) (pairVec e x y) (pairVec e x' y') = hform σ J x x' - hform σ J y y' := by
  simp [hform, ← e.sum_comp, dblGram, blkMat, sub_eq_add_neg]

variable {e}

theorem KeepsDiag.mulVec_diag {M : Matrix ι ι A} (h : KeepsDiag e M) (x : n → A) :
    M *ᵥ pairVec e x x = pairVec e (leviMat e M *ᵥ x) (leviMat e M *ᵥ x) := by
  rw [mulVec_pairVec, ← add_mulVec, ← add_mulVec, h, leviMat]

theorem KeepsDiag.quotMat_eq {M : Matrix ι ι A} (h : KeepsDiag e M) :
    quotMat e M = (M.submatrix e e).toBlocks₂₂ - (M.submatrix e e).toBlocks₁₂ := by
  rw [quotMat, sub_eq_sub_iff_add_eq_add, ← leviMat, ← h, add_comm]

theorem KeepsDiag.mulVec_quot {M : Matrix ι ι A} (h : KeepsDiag e M) (x y : n → A) (i : n) :
    (M *ᵥ pairVec e x y) (e (.inl i)) - (M *ᵥ pairVec e x y) (e (.inr i)) = (quotMat e M *ᵥ (x - y)) i := by
  rw [mulVec_sub]
  nth_rewrite 2 [h.quotMat_eq]
  simp only [mulVec_pairVec, pairVec_inl, pairVec_inr, quotMat, sub_mulVec, Pi.add_apply, Pi.sub_apply]
  ring

variable [DecidableEq n] [DecidableEq ι]

theorem KeepsDiag.det_eq {M : Matrix ι ι A} (h : KeepsDiag e M) : M.det = (leviMat e M).det * (quotMat e M).det := by
  have h1 : fromBlocks (1 : Matrix n n A) 0 (-1) 1 * M.submatrix e e * fromBlocks (1 : Matrix n n A) 0 1 1 =
      fromBlocks (leviMat e M) (M.submatrix e e).toBlocks₁₂ 0 (quotMat e M) := by
    rw [h.quotMat_eq]
    conv_lhs => rw [← fromBlocks_toBlocks (M.submatrix e e)]
    simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero, add_zero,
      zero_add, Matrix.neg_mul, fromBlocks_inj]
    refine ⟨rfl, trivial, ?_, by abel⟩
    rw [add_add_add_comm, ← neg_add, ← leviMat, ← h, neg_add_cancel]
  simpa using congrArg det h1

theorem keepsDiag_of_mulVec {M : Matrix ι ι A} (h : ∀ w ∈ diagSub A e, M *ᵥ w ∈ diagSub A e) : KeepsDiag e M := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  have := h _ ((pairVec_mem_diagSub e).2 (rfl : (Pi.single j 1 : n → A) = _))
  rw [mulVec_pairVec, pairVec_mem_diagSub] at this
  rw [leviMat, add_mulVec, add_mulVec, this]

theorem mem_stabGL_diagSub {p : GL ι A} : p ∈ stabGL (diagSub A e) ↔ KeepsDiag e p.1 := by
  refine ⟨fun h => keepsDiag_of_mulVec fun w hw => (h w).1 hw, fun h w => ?_⟩
  have hu : IsUnit (quotMat e p.1).det := by
    have := (isUnit_iff_isUnit_det _).1 p.isUnit
    rw [h.det_eq] at this
    exact isUnit_of_mul_isUnit_right this
  obtain ⟨x, y, rfl⟩ : ∃ x y, w = pairVec e x y := ⟨_, _, (pairVec_eta e w).symm⟩
  rw [pairVec_mem_diagSub, ← pairVec_eta e (p.1 *ᵥ _), pairVec_mem_diagSub, ← sub_eq_zero,
    ← sub_eq_zero (a := fun i => (p.1 *ᵥ pairVec e x y) (e (.inl i))),
    show ((fun i => (p.1 *ᵥ pairVec e x y) (e (.inl i))) - fun i => (p.1 *ᵥ pairVec e x y) (e (.inr i))) =
      quotMat e p.1 *ᵥ (x - y) from funext (h.mulVec_quot x y)]
  refine ⟨fun h0 => by rw [h0, mulVec_zero], fun h0 => ?_⟩
  have := congrArg (fun v => (quotMat e p.1)⁻¹ *ᵥ v) h0
  simpa [mulVec_mulVec, nonsing_inv_mul _ hu] using this

theorem leviMat_mul {M N : Matrix ι ι A} (hM : KeepsDiag e M) (hN : KeepsDiag e N) :
    leviMat e (M * N) = leviMat e M * leviMat e N := by
  refine Matrix.ext_of_mulVec_single fun j => funext fun i => ?_
  have h1 := congrFun (mulVec_pairVec e (M * N) (Pi.single j 1) (Pi.single j 1)) (e (.inl i))
  rw [← mulVec_mulVec, hN.mulVec_diag, hM.mulVec_diag, pairVec_inl, pairVec_inl, ← add_mulVec, mulVec_mulVec] at h1
  exact h1.symm

variable (e)

def leviGL : stabGL (diagSub A e) →* GL n A :=
  MonoidHom.toHomUnits
    { toFun := fun p => leviMat e p.1.1
      map_one' := by rw [← leviMat_blkMat e (1 : Matrix n n A) 1, blkMat_one]; rfl
      map_mul' := fun p q => leviMat_mul (mem_stabGL_diagSub.1 p.2) (mem_stabGL_diagSub.1 q.2) }

@[simp] theorem val_leviGL (p : stabGL (diagSub A e)) : (leviGL e p).1 = leviMat e p.1.1 := rfl

theorem quot_levi {σ : A →+* A} {J : Matrix n n A} {M : Matrix ι ι A} (hM : cT σ M * dblGram e J * M = dblGram e J)
    (h : KeepsDiag e M) : cT σ (quotMat e M) * J * leviMat e M = J := by
  have h1 : cT σ (M.submatrix e e) * fromBlocks J 0 0 (-J) * M.submatrix e e = fromBlocks J 0 0 (-J) := by
    rw [← submatrix_blkMat e, show cT σ (M.submatrix e e) = (cT σ M).submatrix e e from rfl, submatrix_mul_equiv,
      submatrix_mul_equiv]
    exact congrArg (fun X => X.submatrix e e) hM
  rw [← fromBlocks_toBlocks (M.submatrix e e)] at h1
  simp only [cT, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_zero, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, fromBlocks_inj] at h1
  rw [quotMat, cT, Matrix.map_sub _ (map_sub σ), transpose_sub, Matrix.sub_mul, Matrix.sub_mul]
  nth_rewrite 2 [← h]
  rw [leviMat, Matrix.mul_add, Matrix.mul_add]
  refine Eq.trans ?_ ((congrArg₂ (· + ·) h1.1 h1.2.1).trans (add_zero J))
  abel

def rightAct (l : ι → A) (M : Matrix ι ι A) : ι → A := l ᵥ* (blkMat e 1 (-1) * M * blkMat e 1 (-1))

def rowEval (l w : ι → A) : A := l ⬝ᵥ (blkMat e (1 : Matrix n n A) (-1) *ᵥ w)

theorem sgn_mul_sgn : blkMat e (1 : Matrix n n A) (-1) * blkMat e (1 : Matrix n n A) (-1) = 1 := by
  simp [blkMat_mul, blkMat_one]

end Siegel

section Levi

variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]

theorem det_quot_mul_det_levi {σ : A →+* A} {J : Matrix n n A} (hJ : IsUnit J.det) {M : Matrix ι ι A}
    (hM : cT σ M * dblGram e J * M = dblGram e J) (h : KeepsDiag e M) :
    σ (quotMat e M).det * (leviMat e M).det = 1 := by
  have h1 := congrArg det (quot_levi e hM h)
  rw [det_mul, det_mul, cT, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
  exact hJ.mul_left_cancel (by linear_combination h1)

variable [Invertible (2 : A)]

def cayley : GL ι A :=
  ⟨(fromBlocks 1 1 1 (-1)).submatrix e.symm e.symm, ⅟(2 : A) • (fromBlocks 1 1 1 (-1)).submatrix e.symm e.symm, by
    rw [Matrix.mul_smul, submatrix_mul_equiv, fromBlocks_multiply, ← blkMat_one e, blkMat]
    refine congrArg (fun X : Matrix (n ⊕ n) (n ⊕ n) A => X.submatrix e.symm e.symm) (a₁ := ⅟(2 : A) • fromBlocks _ _ _ _) ?_
    simp [fromBlocks_smul, ← two_smul A, smul_smul], by
    rw [Matrix.smul_mul, submatrix_mul_equiv, fromBlocks_multiply, ← blkMat_one e, blkMat]
    refine congrArg (fun X : Matrix (n ⊕ n) (n ⊕ n) A => X.submatrix e.symm e.symm) (a₁ := ⅟(2 : A) • fromBlocks _ _ _ _) ?_
    simp [fromBlocks_smul, ← two_smul A, smul_smul]⟩

theorem cayley_mulVec (x y : n → A) : (cayley e).1 *ᵥ pairVec e x y = pairVec e (x + y) (x - y) := by
  simp [mulVec_pairVec, cayley, neg_mulVec, sub_eq_add_neg]

def leviElt : GL n A × GL n A →* GL ι A := (MulAut.conj (cayley e)).toMonoidHom.comp (blkGL e)

theorem leviElt_mulVec (g : GL n A × GL n A) (x y : n → A) : (leviElt e g).1 *ᵥ pairVec e (x + y) (x - y) =
    pairVec e (g.1.1 *ᵥ x + g.2.1 *ᵥ y) (g.1.1 *ᵥ x - g.2.1 *ᵥ y) := by
  rw [← cayley_mulVec, ← cayley_mulVec, ← blkMat_mulVec, mulVec_mulVec, mulVec_mulVec, ← val_blkGL, ← Units.val_mul,
    ← Units.val_mul]
  simp [leviElt]

theorem leviElt_diag (g : GL n A × GL n A) (x : n → A) :
    (leviElt e g).1 *ᵥ pairVec e x x = pairVec e (g.1.1 *ᵥ x) (g.1.1 *ᵥ x) := by
  simpa using leviElt_mulVec e g x 0

theorem leviElt_anti (g : GL n A × GL n A) (y : n → A) :
    (leviElt e g).1 *ᵥ pairVec e y (-y) = pairVec e (g.2.1 *ᵥ y) (-(g.2.1 *ᵥ y)) := by
  simpa using leviElt_mulVec e g 0 y

theorem leviElt_mem_diag (g : GL n A × GL n A) : leviElt e g ∈ stabGL (diagSub A e) :=
  mem_stabGL_diagSub.2 (keepsDiag_of_mulVec fun w hw => by
    obtain ⟨x, rfl⟩ := (mem_diagSub e).1 hw
    rw [leviElt_diag, pairVec_mem_diagSub])

theorem leviElt_mem_anti (g : GL n A × GL n A) : leviElt e g ∈ stabGL (antiSub A e) := by
  have h : ∀ g : GL n A × GL n A, ∀ w ∈ antiSub A e, (leviElt e g).1 *ᵥ w ∈ antiSub A e := fun g w hw => by
    obtain ⟨x, rfl⟩ := (mem_antiSub e).1 hw
    rw [leviElt_anti, pairVec_mem_antiSub, neg_neg]
  refine fun w => ⟨h g w, fun hw => ?_⟩
  have := h g⁻¹ _ hw
  rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec] at this

theorem leviMat_leviElt (g : GL n A × GL n A) : leviMat e (leviElt e g).1 = g.1.1 := by
  refine Matrix.ext_of_mulVec_single fun j => funext fun i => ?_
  have := congrFun ((mem_stabGL_diagSub.1 (leviElt_mem_diag e g)).mulVec_diag (Pi.single j 1)) (e (.inl i))
  rw [leviElt_diag, pairVec_inl, pairVec_inl] at this
  exact this.symm

theorem leviElt_mem_UJ {σ : A →+* A} {J : Matrix n n A} {α β : GL n A} (h1 : cT σ β.1 * J * α.1 = J)
    (h2 : cT σ α.1 * J * β.1 = J) : leviElt e (α, β) ∈ UJ σ (dblGram e J) := by
  have hT : cT σ (cayley (A := A) e).1 = (cayley e).1 := by
    change ((fromBlocks 1 1 1 (-1) : Matrix (n ⊕ n) (n ⊕ n) A).map σ)ᵀ.submatrix e.symm e.symm = _
    simp [cayley, fromBlocks_map, fromBlocks_transpose, Matrix.map_neg _ (map_neg σ), Matrix.map_one _ (map_zero σ) (map_one σ)]
  have hQ : cT σ (cayley (A := A) e).1 * dblGram e J * (cayley e).1 =
      (fromBlocks 0 (J + J) (J + J) 0).submatrix e.symm e.symm := by
    rw [hT]
    simp [cayley, dblGram, blkMat, submatrix_mul_equiv, fromBlocks_multiply]
  have hB : cT σ (blkMat e α.1 β.1) * (cT σ (cayley (A := A) e).1 * dblGram e J * (cayley e).1) * blkMat e α.1 β.1 =
      cT σ (cayley (A := A) e).1 * dblGram e J * (cayley e).1 := by
    rw [hQ, cT_blkMat]
    simp [blkMat, submatrix_mul_equiv, fromBlocks_multiply, Matrix.mul_add, Matrix.add_mul, h1, h2]
  change cT σ ((cayley e).1 * blkMat e α.1 β.1 * (cayley e)⁻¹.1) * _ * ((cayley e).1 * blkMat e α.1 β.1 * (cayley e)⁻¹.1) = _
  calc _ = cT σ (cayley (A := A) e)⁻¹.1 * (cT σ (blkMat e α.1 β.1) *
        (cT σ (cayley (A := A) e).1 * dblGram e J * (cayley e).1) * blkMat e α.1 β.1) * (cayley e)⁻¹.1 := by
        simp only [cT_mul, Matrix.mul_assoc]
    _ = cT σ ((cayley (A := A) e).1 * (cayley (A := A) e)⁻¹.1) * dblGram e J * ((cayley e).1 * (cayley e)⁻¹.1) := by
        rw [hB]; simp only [cT_mul, Matrix.mul_assoc]
    _ = _ := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]

theorem exists_leviElt_mem_UJ {σ : A →+* A} (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A} (hJ : cT σ J = J)
    (hu : IsUnit J.det) (α : GL n A) : ∃ β : GL n A, leviElt e (α, β) ∈ UJ σ (dblGram e J) := by
  have hc : ∀ X : Matrix n n A, cT σ (cT σ X) = X := fun X => by ext i j; exact hσ _
  obtain ⟨U, rfl⟩ := (isUnit_iff_isUnit_det J).2 hu
  let γ : GL n A := U * α⁻¹ * U⁻¹
  let β : GL n A := ⟨cT σ γ.1, cT σ γ⁻¹.1, by rw [← cT_mul, Units.inv_mul, cT_one], by rw [← cT_mul, Units.mul_inv, cT_one]⟩
  have h1 : cT σ β.1 * U.1 * α.1 = U.1 := by
    rw [show cT σ β.1 = γ.1 from hc _, ← Units.val_mul, ← Units.val_mul]
    simp [γ]
  refine ⟨β, leviElt_mem_UJ e h1 ?_⟩
  have := congrArg (cT σ) h1
  rwa [cT_mul, cT_mul, hc, hJ, ← Matrix.mul_assoc] at this

end Levi

section Group

variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι] {G : Type} [Group G]
  (mat : G →* GL ι A)

def siegelOf : Subgroup G := (stabGL (diagSub A e)).comap mat

def leviOf : siegelOf e mat →* GL n A := (leviGL e).comp (mat.subgroupComap _)

def aOf : siegelOf e mat →* Aˣ := GeneralLinearGroup.det.comp (leviOf e mat)

def unipOf : Subgroup G := (leviOf e mat).ker.map (siegelOf e mat).subtype

def leviSubOf : Subgroup G := siegelOf e mat ⊓ (stabGL (antiSub A e)).comap mat

variable {e mat}

theorem mem_siegelOf {g : G} : g ∈ siegelOf e mat ↔ KeepsDiag e (mat g).1 := mem_stabGL_diagSub

@[simp] theorem val_leviOf (p : siegelOf e mat) : (leviOf e mat p).1 = leviMat e (mat p).1 := rfl
@[simp] theorem val_aOf (p : siegelOf e mat) : (aOf e mat p).1 = (leviMat e (mat p).1).det := rfl

theorem mem_unipOf {g : G} : g ∈ unipOf e mat ↔ g ∈ siegelOf e mat ∧ leviMat e (mat g).1 = 1 :=
  ⟨by rintro ⟨p, hp, rfl⟩; exact ⟨p.2, congrArg Units.val hp⟩, fun h => ⟨⟨g, h.1⟩, Units.ext h.2, rfl⟩⟩

variable [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G]

theorem isClosed_siegelOf [T2Space A] (h : Continuous mat) : IsClosed (siegelOf e mat : Set G) := by
  have h1 : ∀ i j, Continuous fun g => (mat g).1 i j := fun i j => (Units.continuous_val.comp h).matrix_elem i j
  have : (siegelOf e mat : Set G) = ⋂ i, ⋂ j, {g | (mat g).1 (e (.inr i)) (e (.inl j)) + (mat g).1 (e (.inr i)) (e (.inr j)) =
      (mat g).1 (e (.inl i)) (e (.inl j)) + (mat g).1 (e (.inl i)) (e (.inr j))} := by
    ext g; simp [mem_siegelOf, keepsDiag_iff]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ((h1 _ _).add (h1 _ _)) ((h1 _ _).add (h1 _ _))

theorem continuous_leviOf (h : Continuous mat) : Continuous (leviOf e mat) := by
  have h1 : Continuous fun M : Matrix ι ι A => leviMat e M :=
    continuous_matrix fun i j => (continuous_id.matrix_elem _ _).add (continuous_id.matrix_elem _ _)
  exact Units.continuous_iff.2 ⟨h1.comp (Units.continuous_val.comp (h.comp continuous_subtype_val)),
    (h1.comp (Units.continuous_coe_inv.comp (h.comp continuous_subtype_val))).congr fun p => by
      rw [← map_inv, val_leviOf, Subgroup.coe_inv, map_inv]; rfl⟩

theorem continuous_aOf (h : Continuous mat) : Continuous (aOf e mat) :=
  Units.continuous_iff.2 ⟨(Units.continuous_val.comp (continuous_leviOf h)).matrix_det,
    (Units.continuous_coe_inv.comp (continuous_leviOf (e := e) h)).matrix_det.congr fun p => by
      rw [← map_inv, aOf, MonoidHom.comp_apply, map_inv]; rfl⟩

end Group

section Series

open scoped NNReal
open MeasureTheory

variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι] {G : Type} [Group G]
  (mat : G →* GL ι A) (ν : Aˣ →* ℝ≥0) (K : Subgroup G)

def absAOf : siegelOf e mat →* ℝ≥0 := ν.comp (aOf e mat)

def IwasawaOf : Prop := IsIwasawa (absAOf e mat ν) K

def hgtOf : G → ℝ≥0 := iwAbs (absAOf e mat ν) K

def degPSOf [TopologicalSpace G] (μ : Aˣ →* Circle) (s : ℂ) : Submodule ℂ (G → ℂ) :=
  indSpace (absAOf e mat ν) K (μ.comp (aOf e mat)) (s + (Fintype.card n : ℂ) / 2)

def flatOf (Φ : G → ℂ) (s₀ s : ℂ) : G → ℂ := flatSec (absAOf e mat ν) K Φ s₀ s

variable {e mat ν K}

theorem mem_degPSOf [TopologicalSpace G] {μ : Aˣ →* Circle} {s : ℂ} {Φ : G → ℂ} : Φ ∈ degPSOf e mat ν K μ s ↔
    (∀ (p : siegelOf e mat) (g : G),
      Φ (p * g) = μ (aOf e mat p) * npow (ν (aOf e mat p)) (s + (Fintype.card n : ℂ) / 2) * Φ g) ∧
      Continuous Φ ∧ IsKFinite K Φ := Iff.rfl

theorem flatOf_apply (Φ : G → ℂ) (s₀ s : ℂ) (g : G) :
    flatOf e mat ν K Φ s₀ s g = Φ g * npow (hgtOf e mat ν K g) (s - s₀) := rfl

theorem hgtOf_pos (g : G) : 0 < hgtOf e mat ν K g := iwAbs_pos _ _ g

theorem IwasawaOf.hgtOf_mul (h : IwasawaOf e mat ν K) (p : siegelOf e mat) {k : G} (hk : k ∈ K) :
    hgtOf e mat ν K (p * k) = ν (aOf e mat p) := IsIwasawa.iwAbs_mul h p hk

variable [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in

theorem iwasawaOf_of_isCompact (hm : Continuous mat) (hν : Continuous ν) (hK : IsCompact (K : Set G))
    (h : ∀ g : G, ∃ p : siegelOf e mat, ∃ k ∈ K, g = p * k) : IwasawaOf e mat ν K :=
  isIwasawa_of_isCompact (isClosed_siegelOf hm) (hν.comp (continuous_aOf hm)) hK h

theorem IwasawaOf.continuous_hgtOf (h : IwasawaOf e mat ν K) (hm : Continuous mat) (hν : Continuous ν)
    (hK : IsCompact (K : Set G)) : Continuous (hgtOf e mat ν K) :=
  IsIwasawa.continuous_iwAbs h (isClosed_siegelOf hm) (hν.comp (continuous_aOf hm)) hK

theorem IwasawaOf.flatOf_mem (h : IwasawaOf e mat ν K) (hm : Continuous mat) (hν : Continuous ν)
    (hK : IsCompact (K : Set G)) {μ : Aˣ →* Circle} {s₀ : ℂ} {Φ : G → ℂ} (hΦ : Φ ∈ degPSOf e mat ν K μ s₀) (s : ℂ) :
    flatOf e mat ν K Φ s₀ s ∈ degPSOf e mat ν K μ s :=
  IsIwasawa.flatSec_mem h (isClosed_siegelOf hm) (hν.comp (continuous_aOf hm)) hK hΦ s

theorem IwasawaOf.spherical_mem (h : IwasawaOf e mat ν K) (hm : Continuous mat) (hν : Continuous ν)
    (hK : IsCompact (K : Set G)) (s : ℂ) :
    (fun g => npow (hgtOf e mat ν K g) (s + (Fintype.card n : ℂ) / 2)) ∈ degPSOf e mat ν K 1 s :=
  IsIwasawa.npow_iwAbs_mem h (isClosed_siegelOf hm) (hν.comp (continuous_aOf hm)) hK _

end Series

section Io

variable [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι] (σ : A →+* A)

def sumU (e : m ⊕ n ≃ ι) {J : Matrix m m A} {J' : Matrix n n A} {Q : Matrix ι ι A} (h : Q = blkMat e J J') :
    UJ σ J × UJ σ J' →* UJ σ Q :=
  ((blkGL e).comp ((UJ σ J).subtype.prodMap (UJ σ J').subtype)).codRestrict _ fun g =>
    h ▸ (blkGL_mem_UJ e).2 ⟨g.1.2, g.2.2⟩

def ioU (e : n ⊕ n ≃ ι) {J : Matrix n n A} {Q : Matrix ι ι A} (h : Q = dblGram e J) : UJ σ J × UJ σ J →* UJ σ Q :=
  ((blkGL e).comp ((UJ σ J).subtype.prodMap (UJ σ J).subtype)).codRestrict _ fun g =>
    h ▸ (blkGL_mem_UJ e).2 ⟨g.1.2, (UJ_neg σ J).symm ▸ g.2.2⟩

theorem coe_ioU (e : n ⊕ n ≃ ι) {J : Matrix n n A} {Q : Matrix ι ι A} (h : Q = dblGram e J) (g : UJ σ J × UJ σ J) :
    (ioU σ e h g : GL ι A) = blkGL e (g.1, g.2) := rfl

end Io

example (g : ℤ) : leviMat (Equiv.refl (Unit ⊕ Unit)) (blkMat (Equiv.refl _) (of fun _ _ => g) (of fun _ _ => g)) () () = g ∧
    leviMat (Equiv.refl (Unit ⊕ Unit)) (fromBlocks (0 : Matrix Unit Unit ℤ) 1 1 0) = 1 ∧
    quotMat (Equiv.refl (Unit ⊕ Unit)) (fromBlocks (0 : Matrix Unit Unit ℤ) 1 1 0) = -1 := by
  simp [leviMat, quotMat, blkMat]

end GlobalTheory.Doubling

end
