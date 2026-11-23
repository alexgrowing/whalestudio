import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviOntoS
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SignActionMapComm

noncomputable section

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Matrix Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf

namespace LeviEltPf

section Mat

variable (I : AutInst) {k : ℕ}

abbrev Jf : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))

def colM (b : Fin k → VA I) : Matrix (Fin I.n) (Fin k) (I.E ⊗[I.F] Af I.F) := Matrix.of fun l i => b i l

def rowM (b : Fin k → VA I) : Matrix (Fin k) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
  Formalism.UG.cT (sigA I) (colM I b) * Jf I

theorem rowM_mulVec (b : Fin k → VA I) (y : VA I) : rowM I b *ᵥ y = fun i => hA I (b i) y := by
  funext i
  simp only [rowM, colM, hA, Formalism.UG.hform, Formalism.UG.cT, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem rowM_mul_colM (b d : Fin k → VA I) (i j : Fin k) : (rowM I b * colM I d) i j = hA I (b i) (d j) := by
  have h := congrFun (rowM_mulVec I b (d j)) i
  rw [← h]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, colM, Matrix.of_apply]

theorem colM_mulVec (b : Fin k → VA I) (w : Fin k → I.E ⊗[I.F] Af I.F) :
    colM I b *ᵥ w = ∑ i, w i • b i := by
  funext l
  simp only [colM, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem cT_add' {m p : Type} (M N : Matrix m p (I.E ⊗[I.F] Af I.F)) :
    Formalism.UG.cT (sigA I) (M + N) = Formalism.UG.cT (sigA I) M + Formalism.UG.cT (sigA I) N := by
  ext; simp [Formalism.UG.cT]

theorem cT_sub' {m p : Type} (M N : Matrix m p (I.E ⊗[I.F] Af I.F)) :
    Formalism.UG.cT (sigA I) (M - N) = Formalism.UG.cT (sigA I) M - Formalism.UG.cT (sigA I) N := by
  ext; simp [Formalism.UG.cT]

theorem cT_smul' {m p : Type} (a : I.E ⊗[I.F] Af I.F) (M : Matrix m p (I.E ⊗[I.F] Af I.F)) :
    Formalism.UG.cT (sigA I) (a • M) = sigA I a • Formalism.UG.cT (sigA I) M := by
  ext; simp [Formalism.UG.cT]

theorem cT_cT {m p : Type} (M : Matrix m p (I.E ⊗[I.F] Af I.F)) :
    Formalism.UG.cT (sigA I) (Formalism.UG.cT (sigA I) M) = M := by
  ext; simp [Formalism.UG.cT, sigA_sigA]

theorem cT_Jf : Formalism.UG.cT (sigA I) (Jf I) = Jf I := by
  ext i j
  simp only [Formalism.UG.cT, Jf, Matrix.transpose_apply, Matrix.map_apply, sigA_inclE, J_conj]

def Mk (b d : Fin k → VA I) (X Y : Matrix (Fin k) (Fin k) (I.E ⊗[I.F] Af I.F)) :
    Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
  1 + colM I b * X * rowM I d + colM I d * Y * rowM I b

variable {I}

theorem Mk_mul (b d : Fin k → VA I) (η : I.E ⊗[I.F] Af I.F)
    (hDB : rowM I d * colM I b = η • 1) (hDD : rowM I d * colM I d = 0)
    (hBB : rowM I b * colM I b = 0) (hBD : rowM I b * colM I d = sigA I η • 1)
    (X Y X' Y' : Matrix (Fin k) (Fin k) (I.E ⊗[I.F] Af I.F)) :
    Mk I b d X Y * Mk I b d X' Y' =
      Mk I b d (X + X' + X * ((η • 1) * X')) (Y + Y' + Y * ((sigA I η • 1) * Y')) := by
  first | exact UpperTheory.Reformulated.B.Qk24.Mk_mul .. | (apply UpperTheory.Reformulated.B.Qk24.Mk_mul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk24.Mk_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk24.Mk_mul <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk24.Mk_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk24.Mk_mul <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB hDD hBB hBD X Y X' Y' | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB hDD hBB hBD X Y X' | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB hDD hBB hBD X Y | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB hDD hBB hBD X | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB hDD hBB hBD | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB hDD hBB | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB hDD | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η hDB | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d η | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b d | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k b | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I k | exact @UpperTheory.Reformulated.B.Qk24.Mk_mul I

theorem colM_smul (b : Fin k → VA I) (η : I.E ⊗[I.F] Af I.F) (hb : ∀ i, η • b i = b i)
    (Z : Matrix (Fin k) (Fin k) (I.E ⊗[I.F] Af I.F)) : colM I b * Z = colM I b * (η • Z) := by
  ext l j
  simp only [Matrix.mul_apply, colM, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := congrFun (hb i) l
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [← mul_assoc, mul_comm (b i l) η, h]

theorem Mk_eq_one (b d : Fin k → VA I) (X Y : Matrix (Fin k) (Fin k) (I.E ⊗[I.F] Af I.F))
    (hX : colM I b * X = 0) (hY : colM I d * Y = 0) : Mk I b d X Y = 1 := by
  simp [Mk, hX, hY]

theorem Mk_cT (b d : Fin k → VA I) (X Y : Matrix (Fin k) (Fin k) (I.E ⊗[I.F] Af I.F)) :
    Formalism.UG.cT (sigA I) (Mk I b d X Y) * Jf I =
      Jf I * Mk I b d (Formalism.UG.cT (sigA I) Y) (Formalism.UG.cT (sigA I) X) := by
  simp only [Mk, rowM, cT_add', Formalism.UG.cT_mul, Formalism.UG.cT_one, cT_cT, cT_Jf, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
  abel

end Mat

section Frame

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word}

theorem eta_sig {η : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hew : η * X.ew = η) : η * sigA X.B.I η = 0 := by
  have h : η * sigA X.B.I η = η * sigA X.B.I η * (X.ew * sigA X.B.I X.ew) := by
    conv_lhs => rw [← hew, map_mul]
    ring
  rw [h, X.ew_orth, mul_zero]

theorem sig_eta_ew {η : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hew : η * X.ew = η) : sigA X.B.I η * X.ew = 0 := by
  have h : sigA X.B.I η * X.ew = sigA X.B.I η * (X.ew * sigA X.B.I X.ew) := by
    conv_lhs => rw [← hew, map_mul]
    ring
  rw [h, X.ew_orth, mul_zero]

variable {η : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} {b d : Fin D.R.k → VA X.B.I}

theorem frame_DB (h : IsDualFrame X u η b d) : rowM X.B.I d * colM X.B.I b = η • 1 := by
  ext i j
  rw [rowM_mul_colM, h.2.2.2.2.2.2.2.1 i j, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem frame_DD (h : IsDualFrame X u η b d) : rowM X.B.I d * colM X.B.I d = 0 := by
  ext i j
  rw [rowM_mul_colM, ← (h.2.2.2.2.2.1 i).2.2.2, ← (h.2.2.2.2.2.1 j).2.2.2, hA_smul_left, hA_smul_right,
    sigA_sigA]
  have := eta_sig h.2.2.1
  simp only [Matrix.zero_apply]
  linear_combination (hA X.B.I (d i) (d j)) * this

theorem frame_BB (h : IsDualFrame X u η b d) : rowM X.B.I b * colM X.B.I b = 0 := by
  ext i j
  rw [rowM_mul_colM, ← (h.2.2.2.2.2.1 i).2.2.1, ← (h.2.2.2.2.2.1 j).2.2.1, hA_smul_left, hA_smul_right]
  have := eta_sig h.2.2.1
  simp only [Matrix.zero_apply]
  linear_combination (hA X.B.I (b i) (b j)) * this

theorem frame_BD (h : IsDualFrame X u η b d) : rowM X.B.I b * colM X.B.I d = sigA X.B.I η • 1 := by
  ext i j
  rw [rowM_mul_colM, hA_symm, h.2.2.2.2.2.2.2.1 j i, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (Ne.symm hij), if_neg hij]; simp

theorem Mk_inv (h : IsDualFrame X u η b d) (C C' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (h1 : η • (C * C') = η • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _)) :
    Mk X.B.I b d (C - 1) (Formalism.UG.cT (sigA X.B.I) C' - 1) * Mk X.B.I b d (C' - 1) (Formalism.UG.cT (sigA X.B.I) C - 1)
      = 1 := by
  rw [Mk_mul b d η (frame_DB h) (frame_DD h) (frame_BB h) (frame_BD h)]
  have hid : η * η = η := h.2.1
  apply Mk_eq_one
  · rw [colM_smul b η (fun i => (h.2.2.2.2.2.1 i).2.2.1)]
    have e : η • (C - 1 + (C' - 1) + (C - 1) * ((η • 1) * (C' - 1))) = η • (C * C') - η • 1 := by
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_add, smul_add, smul_smul, hid]
      have : C - 1 + (C' - 1) + (C - 1) * (C' - 1) = C * C' - 1 := by noncomm_ring
      rw [← smul_add, ← smul_add, this, smul_sub]
    rw [e, h1, sub_self, Matrix.mul_zero]
  · have hsid : sigA X.B.I η * sigA X.B.I η = sigA X.B.I η := by rw [← map_mul, hid]
    rw [colM_smul d (sigA X.B.I η) (fun i => (h.2.2.2.2.2.1 i).2.2.2)]
    have h1' : sigA X.B.I η • (Formalism.UG.cT (sigA X.B.I) C' * Formalism.UG.cT (sigA X.B.I) C) = sigA X.B.I η • 1 := by
      have := congrArg (Formalism.UG.cT (sigA X.B.I)) h1
      rwa [cT_smul', cT_smul', Formalism.UG.cT_mul, Formalism.UG.cT_one] at this
    have e : sigA X.B.I η • (Formalism.UG.cT (sigA X.B.I) C' - 1 + (Formalism.UG.cT (sigA X.B.I) C - 1) +
        (Formalism.UG.cT (sigA X.B.I) C' - 1) * ((sigA X.B.I η • 1) * (Formalism.UG.cT (sigA X.B.I) C - 1))) =
        sigA X.B.I η • (Formalism.UG.cT (sigA X.B.I) C' * Formalism.UG.cT (sigA X.B.I) C) - sigA X.B.I η • 1 := by
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_add, smul_add, smul_smul, hsid]
      have : Formalism.UG.cT (sigA X.B.I) C' - 1 + (Formalism.UG.cT (sigA X.B.I) C - 1) +
          (Formalism.UG.cT (sigA X.B.I) C' - 1) * (Formalism.UG.cT (sigA X.B.I) C - 1) =
          Formalism.UG.cT (sigA X.B.I) C' * Formalism.UG.cT (sigA X.B.I) C - 1 := by noncomm_ring
      rw [← smul_add, ← smul_add, this, smul_sub]
    rw [e, h1', sub_self, Matrix.mul_zero]

end Frame

section Main

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem hA_sum_smul (x : VA X.B.I) {k : ℕ} (w : Fin k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (b : Fin k → VA X.B.I) :
    hA X.B.I x (∑ l, w l • b l) = ∑ l, w l * hA X.B.I x (b l) := by
  rw [← hL_apply, map_sum]
  simp only [LinearMap.map_smul, hL_apply, smul_eq_mul]

theorem resT_of_mem (v : TR.Pl) {x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hx : x ∈ IntAf X.B.I.F X.B.I.E) :
    resT TR v x = TR.res v ⟨x, hx⟩ := dif_pos hx

theorem resT_add (v : TR.Pl) {x y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hx : x ∈ IntAf X.B.I.F X.B.I.E)
    (hy : y ∈ IntAf X.B.I.F X.B.I.E) : resT TR v (x + y) = resT TR v x + resT TR v y := by
  rw [resT_of_mem TR v (add_mem hx hy), resT_of_mem TR v hx, resT_of_mem TR v hy, ← map_add]; rfl

theorem resT_sub (v : TR.Pl) {x y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hx : x ∈ IntAf X.B.I.F X.B.I.E)
    (hy : y ∈ IntAf X.B.I.F X.B.I.E) : resT TR v (x - y) = resT TR v x - resT TR v y := by
  rw [resT_of_mem TR v (sub_mem hx hy), resT_of_mem TR v hx, resT_of_mem TR v hy, ← map_sub]; rfl

theorem resT_mul (v : TR.Pl) {x y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hx : x ∈ IntAf X.B.I.F X.B.I.E)
    (hy : y ∈ IntAf X.B.I.F X.B.I.E) : resT TR v (x * y) = resT TR v x * resT TR v y := by
  rw [resT_of_mem TR v (mul_mem hx hy), resT_of_mem TR v hx, resT_of_mem TR v hy, ← map_mul]; rfl

theorem resT_sum (v : TR.Pl) {k : ℕ} (f : Fin k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (hf : ∀ l, f l ∈ IntAf X.B.I.F X.B.I.E) : resT TR v (∑ l, f l) = ∑ l, resT TR v (f l) := by
  rw [resT_of_mem TR v (Subring.sum_mem _ fun l _ => hf l)]
  have e : (⟨∑ l, f l, Subring.sum_mem _ fun l _ => hf l⟩ : ↥(IntAf X.B.I.F X.B.I.E)) =
      ∑ l, (⟨f l, hf l⟩ : ↥(IntAf X.B.I.F X.B.I.E)) := Subtype.ext (by simp)
  rw [e, map_sum]
  exact Finset.sum_congr rfl fun l _ => (resT_of_mem TR v (hf l)).symm

theorem resT_one (v : TR.Pl) : resT TR v 1 = 1 := by
  rw [resT_of_mem TR v (one_mem _)]; exact map_one _

theorem resT_zero (v : TR.Pl) : resT TR v 0 = 0 := by
  rw [resT_of_mem TR v (zero_mem _)]; exact map_zero _

theorem resT_ew (v : TR.Pl) : resT TR v X.ew = 1 := by
  rw [resT_of_mem TR v X.ew_int]
  have e : (⟨X.ew, X.ew_int⟩ : ↥(IntAf X.B.I.F X.B.I.E)) =
      ⟨X.ew * ((1 : ↥(IntAf X.B.I.F X.B.I.E)) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
        (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int (1 : ↥(IntAf X.B.I.F X.B.I.E)).2⟩ :=
    Subtype.ext (by simp)
  rw [e, TR.res_ew, map_one]

theorem resT_zmod (v : TR.Pl) {x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hx : x ∈ IntAf X.B.I.F X.B.I.E)
    (c : Prop) [Decidable c] (h : ZMod' X.B.I X.B.g (x - if c then X.ew else 0)) :
    resT TR v x = if c then 1 else 0 := by
  have hc : (if c then X.ew else 0) ∈ IntAf X.B.I.F X.B.I.E := by
    split_ifs
    · exact X.ew_int
    · exact zero_mem _
  have hz : resT TR v (x - if c then X.ew else 0) = 0 := by
    rw [resT_of_mem TR v (sub_mem hx hc)]
    obtain ⟨t, ht, e⟩ := h
    refine (TR.res_ker ⟨_, sub_mem hx hc⟩).2 ⟨X.ew * t, mul_mem X.ew_int ht, ?_⟩ v
    show X.ew * (x - if c then X.ew else 0) = _
    rw [e]; ring
  rw [resT_sub TR v hx hc] at hz
  rw [sub_eq_zero.1 hz]
  split_ifs
  · exact resT_ew TR v
  · exact resT_zero TR v

variable (u : D.what₂.Word)

variable {η : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} {b d : Fin D.R.k → VA X.B.I}

theorem Mk_int (hb : ∀ i, b i ∈ X.B.I.Lf) (hd : ∀ i, d i ∈ X.B.I.Lf)
    (Xm Ym : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (hX : ∀ i j, Xm i j ∈ IntAf X.B.I.F X.B.I.E) (hY : ∀ i j, Ym i j ∈ IntAf X.B.I.F X.B.I.E)
    {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) : Mk X.B.I b d Xm Ym *ᵥ y ∈ X.B.I.Lf := by
  simp only [Mk, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, rowM_mulVec, colM_mulVec]
  refine add_mem (add_mem hy (Submodule.sum_mem _ fun i _ => ?_)) (Submodule.sum_mem _ fun i _ => ?_)
  · have hc : (Xm *ᵥ fun j => hA X.B.I (d j) y) i ∈ IntAf X.B.I.F X.B.I.E := by
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => mul_mem (hX i j) (hA_int X.B.I (hd j) hy)
    exact X.B.I.Lf.smul_mem (⟨_, hc⟩ : ↥(IntAf X.B.I.F X.B.I.E)) (hb i)
  · have hc : (Ym *ᵥ fun j => hA X.B.I (b j) y) i ∈ IntAf X.B.I.F X.B.I.E := by
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => mul_mem (hY i j) (hA_int X.B.I (hb j) hy)
    exact X.B.I.Lf.smul_mem (⟨_, hc⟩ : ↥(IntAf X.B.I.F X.B.I.E)) (hd i)

theorem Mk_fix (Xm Ym : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) {y : VA X.B.I}
    (hfix : ∀ i, hA X.B.I y (b i) = 0 ∧ hA X.B.I y (d i) = 0) : Mk X.B.I b d Xm Ym *ᵥ y = y := by
  have h1 : (fun i => hA X.B.I (d i) y) = 0 := funext fun i => by
    rw [hA_symm, (hfix i).2, map_zero]; rfl
  have h2 : (fun i => hA X.B.I (b i) y) = 0 := funext fun i => by
    rw [hA_symm, (hfix i).1, map_zero]; rfl
  simp only [Mk, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, rowM_mulVec, h1, h2,
    Matrix.mulVec_zero, add_zero]

theorem one_int (i j : Fin D.R.k) :
    (1 : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) i j ∈ IntAf X.B.I.F X.B.I.E := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem levi_element_exists : LeviElt TR u := by
  intro η b d h C C' hC h1 h2
  obtain ⟨-, -, hew, -, -, hbd, hfix, -, hcong⟩ := id h
  have hb : ∀ i, b i ∈ X.B.I.Lf := fun i => (hbd i).1
  have hd : ∀ i, d i ∈ X.B.I.Lf := fun i => (hbd i).2.1
  have hX : ∀ i j, (C - 1) i j ∈ IntAf X.B.I.F X.B.I.E := fun i j => by
    rw [Matrix.sub_apply]; exact sub_mem (hC i j).1 (one_int i j)
  have hX' : ∀ i j, (C' - 1) i j ∈ IntAf X.B.I.F X.B.I.E := fun i j => by
    rw [Matrix.sub_apply]; exact sub_mem (hC i j).2 (one_int i j)
  have hY : ∀ i j, (Formalism.UG.cT (sigA X.B.I) C' - 1) i j ∈ IntAf X.B.I.F X.B.I.E := fun i j => by
    rw [Matrix.sub_apply]
    exact sub_mem (sigA_mem X.B.I (hC j i).2) (one_int i j)
  have hY' : ∀ i j, (Formalism.UG.cT (sigA X.B.I) C - 1) i j ∈ IntAf X.B.I.F X.B.I.E := fun i j => by
    rw [Matrix.sub_apply]
    exact sub_mem (sigA_mem X.B.I (hC j i).1) (one_int i j)
  have hMN := Mk_inv h C C' h1
  have hNM := Mk_inv h C' C h2
  let g : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :=
    ⟨Mk X.B.I b d (C - 1) (Formalism.UG.cT (sigA X.B.I) C' - 1), Mk X.B.I b d (C' - 1) (Formalism.UG.cT (sigA X.B.I) C - 1),
      hMN, hNM⟩
  have hU : g ∈ Formalism.UG.UPts X.B.I.cm.sig X.B.I.J (Af X.B.I.F) := by
    show Formalism.UG.cT (sigA X.B.I) (Mk X.B.I b d (C - 1) (Formalism.UG.cT (sigA X.B.I) C' - 1)) * Jf X.B.I *
      Mk X.B.I b d (C - 1) (Formalism.UG.cT (sigA X.B.I) C' - 1) = Jf X.B.I
    rw [Mk_cT]
    simp only [cT_sub', cT_cT, Formalism.UG.cT_one]
    rw [Matrix.mul_assoc, hNM, Matrix.mul_one]
  refine ⟨⟨g, hU⟩, ?_, ?_, ?_⟩
  · show ∀ x, x ∈ X.B.I.Lf ↔ Mk X.B.I b d (C - 1) (Formalism.UG.cT (sigA X.B.I) C' - 1) *ᵥ x ∈ X.B.I.Lf
    intro x
    refine ⟨fun hx => Mk_int hb hd _ _ hX hY hx, fun hx => ?_⟩
    have := Mk_int hb hd _ _ hX' hY' hx
    rwa [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec] at this
  · intro y hy
    exact Mk_fix _ _ (hfix y hy)
  · intro v
    ext i j
    have hBw : (fun l => hA X.B.I (b l) (X.bw j)) = 0 := funext fun l => by
      rw [← (hbd l).2.2.1, X.bw_w j, hA_smul_left, hA_smul_right, ← mul_assoc, sig_eta_ew hew, zero_mul]; rfl
    have hbwL : X.bw j ∈ X.B.I.Lf := (X.vectorsInLattice.2.2 j).1
    have hbwdL : X.bwd i ∈ X.B.I.Lf := (X.vectorsInLattice.2.2 i).2
    have hval : hA X.B.I (X.bwd i) (Mk X.B.I b d (C - 1) (Formalism.UG.cT (sigA X.B.I) C' - 1) *ᵥ X.bw j) =
        hA X.B.I (X.bwd i) (X.bw j) + ∑ l, (∑ m, (C - 1) l m * hA X.B.I (d m) (X.bw j)) *
          hA X.B.I (X.bwd i) (b l) := by
      simp only [Mk, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, rowM_mulVec, hBw,
        Matrix.mulVec_zero, add_zero, colM_mulVec, hA_add_right, hA_sum_smul]
      rfl
    show resT TR v (hA X.B.I (X.bwd i) (Mk X.B.I b d (C - 1) (Formalism.UG.cT (sigA X.B.I) C' - 1) *ᵥ X.bw j)) =
      resT TR v (C i j)
    have hi1 : ∀ m, hA X.B.I (d m) (X.bw j) ∈ IntAf X.B.I.F X.B.I.E := fun m => hA_int X.B.I (hd m) hbwL
    have hi2 : ∀ l, hA X.B.I (X.bwd i) (b l) ∈ IntAf X.B.I.F X.B.I.E := fun l => hA_int X.B.I hbwdL (hb l)
    have hin : ∀ l, (∑ m, (C - 1) l m * hA X.B.I (d m) (X.bw j)) ∈ IntAf X.B.I.F X.B.I.E := fun l =>
      Subring.sum_mem _ fun m _ => mul_mem (hX l m) (hi1 m)
    rw [hval, resT_add TR v (hA_int X.B.I hbwdL hbwL)
      (Subring.sum_mem _ fun l _ => mul_mem (hin l) (hi2 l)),
      resT_sum TR v _ (fun l => mul_mem (hin l) (hi2 l))]
    simp only [resT_mul TR v (hin _) (hi2 _), resT_sum TR v _ (fun m => mul_mem (hX _ m) (hi1 m)),
      resT_mul TR v (hX _ _) (hi1 _)]
    rw [resT_zmod TR v (hA_int X.B.I hbwdL hbwL) (i = j) (X.bw_dual i j)]
    have e2 : ∀ l, resT TR v (hA X.B.I (X.bwd i) (b l)) = if i = l then 1 else 0 := fun l =>
      resT_zmod TR v (hi2 l) (i = l) (hcong i l).1
    have e3 : ∀ m, resT TR v (hA X.B.I (d m) (X.bw j)) = if m = j then 1 else 0 := fun m =>
      resT_zmod TR v (hi1 m) (m = j) (hcong m j).2
    simp only [e2, e3, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    rw [Matrix.sub_apply, resT_sub TR v (hC i j).1 (one_int i j), Matrix.one_apply]
    split_ifs
    · rw [resT_one]; ring
    · rw [resT_zero]; ring

end Main

end LeviEltPf

end Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf
