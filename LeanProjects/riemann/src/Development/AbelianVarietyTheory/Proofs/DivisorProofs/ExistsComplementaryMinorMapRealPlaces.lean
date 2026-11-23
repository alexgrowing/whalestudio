import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluckerMinorsProportional
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PluckerStar

open MvPolynomial Matrix

variable {a a' : ℕ}

def joinFun (h : a + a' = a + a') (s : {s : Fin a → Fin (a + a') // StrictMono s}) : Fin (a + a') → Fin (a + a') :=
  Fin.addCases (fun i => s.1 i) (fun j => (GlobalTheory.BotMatch.complSub h s).1 j)

theorem joinFun_injective (h : a + a' = a + a') (s : {s : Fin a → Fin (a + a') // StrictMono s}) :
    Function.Injective (joinFun h s) := by
  have hr := GlobalTheory.BotMatch.range_complSub h s
  have hc : ∀ j i, (GlobalTheory.BotMatch.complSub h s).1 j ≠ s.1 i := by
    intro j i e
    have : (GlobalTheory.BotMatch.complSub h s).1 j ∈ Set.range (GlobalTheory.BotMatch.complSub h s).1 := ⟨j, rfl⟩
    rw [hr, e] at this
    exact this ⟨i, rfl⟩
  intro k₁ k₂
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k₁ <;> refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k₂ <;>
    simp only [joinFun, Fin.addCases_left, Fin.addCases_right] <;> intro e
  · rw [s.2.injective e]
  · exact absurd e.symm (hc j' i)
  · exact absurd e (hc j i')
  · rw [(GlobalTheory.BotMatch.complSub h s).2.injective e]

def joinPerm (h : a + a' = a + a') (s : {s : Fin a → Fin (a + a') // StrictMono s}) : Equiv.Perm (Fin (a + a')) :=
  Equiv.ofBijective (joinFun h s) (Finite.injective_iff_bijective.mp (joinFun_injective h s))

theorem joinPerm_castAdd (h : a + a' = a + a') (s : {s : Fin a → Fin (a + a') // StrictMono s}) (i : Fin a) :
    joinPerm h s (Fin.castAdd a' i) = s.1 i := by
  simp [joinPerm, joinFun]

theorem joinPerm_natAdd (h : a + a' = a + a') (s : {s : Fin a → Fin (a + a') // StrictMono s}) (j : Fin a') :
    joinPerm h s (Fin.natAdd a j) = (GlobalTheory.BotMatch.complSub h s).1 j := by
  simp [joinPerm, joinFun]

theorem jacobi (N : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) (hN : N.det ≠ 0) (π : Equiv.Perm (Fin (a + a'))) :
    (Matrix.of fun i i' : Fin a => N⁻¹ (Fin.castAdd a' i') (π (Fin.castAdd a' i))).det =
      ((Equiv.Perm.sign π : ℤ) : ℂ) * (N.det)⁻¹ *
        (Matrix.of fun j j' : Fin a' => N (π (Fin.natAdd a j)) (Fin.natAdd a j')).det := by
  have hU : IsUnit N.det := isUnit_iff_ne_zero.mpr hN
  have h1 : N⁻¹.submatrix id π * N.submatrix π id = 1 := by
    rw [Matrix.submatrix_mul_equiv (e₂ := π) (e₃ := id)]
    simp [Matrix.nonsing_inv_mul _ hU]
  set e := (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))
  have h2 : (N⁻¹.submatrix id π).submatrix e e * (N.submatrix π id).submatrix e e = 1 := by
    rw [Matrix.submatrix_mul_equiv (e₂ := e), h1, Matrix.submatrix_one_equiv]
  have h3 := GlobalTheory.det_mul_det_toBlocks₂₂_of_mul_eq_one _ _ h2
  have hd : ((N⁻¹.submatrix id π).submatrix e e).det = ((Equiv.Perm.sign π : ℤ) : ℂ) * (N.det)⁻¹ := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_permute', Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rw [hd] at h3
  have hA : (Matrix.of fun i i' : Fin a => N⁻¹ (Fin.castAdd a' i') (π (Fin.castAdd a' i))) =
      ((N⁻¹.submatrix id π).submatrix e e).toBlocks₁₁.transpose := by
    ext i i'; simp [Matrix.toBlocks₁₁, e]
  have hB : (Matrix.of fun j j' : Fin a' => N (π (Fin.natAdd a j)) (Fin.natAdd a j')) =
      ((N.submatrix π id).submatrix e e).toBlocks₂₂ := by
    ext j j'; simp [Matrix.toBlocks₂₂, e]
  rw [hA, hB, Matrix.det_transpose, ← h3]

variable {ι : Type} [Fintype ι]

theorem eq_zero_of_eval {σ : Type} (Q S : MvPolynomial σ ℂ) (hS : ∃ x, eval x S ≠ 0)
    (h : ∀ x, eval x S ≠ 0 → eval x Q = 0) : Q = 0 := by
  have hQS : Q * S = 0 := MvPolynomial.funext fun x => by
    by_cases hx : eval x S = 0
    · simp [hx]
    · simp [h x hx]
  have hS0 : S ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hS
    simp at hx
  exact (mul_eq_zero.mp hQS).resolve_right hS0

theorem eval_rowSub {d b : ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) (x : ι × Fin d × Fin b → ℂ)
    (P : GlobalTheory.MinorFrame.Pol ι d b) :
    eval x (GlobalTheory.MinorFrame.rowSub κ P) = eval (fun y => ∑ i', κ y.1 i' y.2.1 * x (y.1, i', y.2.2)) P := by
  have : (eval x).comp (GlobalTheory.MinorFrame.rowSub κ : GlobalTheory.MinorFrame.Pol ι d b →ₐ[ℂ] GlobalTheory.MinorFrame.Pol ι d b).toRingHom =
      eval (fun y => ∑ i', κ y.1 i' y.2.1 * x (y.1, i', y.2.2)) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [GlobalTheory.MinorFrame.rowSub]
    · intro y; simp [GlobalTheory.MinorFrame.rowSub]
  exact RingHom.congr_fun this P

def xPt (N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ) : ι × Fin (a + a') × Fin a → ℂ :=
  fun y => (N y.1)⁻¹ (Fin.castAdd a' y.2.2) y.2.1

def yPt (N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ) : ι × Fin (a + a') × Fin a' → ℂ :=
  fun y => N y.1 y.2.1 (Fin.natAdd a y.2.2)

theorem eval_minorAt {d b : ℕ} (x : ι × Fin d × Fin b → ℂ) (τ : ι) (s : Fin b → Fin d) :
    eval x (GlobalTheory.MinorFrame.minorAt τ s) = (Matrix.of fun i i' : Fin b => x (τ, s i, i')).det := by
  rw [GlobalTheory.MinorFrame.minorAt, RingHom.map_det]
  congr 1
  ext i i'
  simp

theorem eval_xPt_minorAt (h : a + a' = a + a') (N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ) (τ : ι)
    (hN : (N τ).det ≠ 0) (s : {s : Fin a → Fin (a + a') // StrictMono s}) :
    eval (xPt N) (GlobalTheory.MinorFrame.minorAt τ s.1) =
      ((Equiv.Perm.sign (joinPerm h s) : ℤ) : ℂ) * ((N τ).det)⁻¹ *
        eval (yPt N) (GlobalTheory.MinorFrame.minorAt τ (GlobalTheory.BotMatch.complSub h s).1) := by
  rw [eval_minorAt, eval_minorAt]
  have := jacobi (N τ) hN (joinPerm h s)
  simp only [joinPerm_castAdd, joinPerm_natAdd] at this
  exact this

def sgn {n : ι → ℕ} (h : a + a' = a + a') (T : GlobalTheory.MinorFrame.Tup ι a (a + a') n) : ℤˣ :=
  ∏ τ, ∏ j, Equiv.Perm.sign (joinPerm h (T τ j))

def cTup {n : ι → ℕ} (h : a + a' = a + a') (T : GlobalTheory.MinorFrame.Tup ι a (a + a') n) : GlobalTheory.MinorFrame.Tup ι a' (a + a') n :=
  fun τ k => GlobalTheory.BotMatch.complSub h (T τ k)

def lam (n : ι → ℕ) (N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ) : ℂ := ∏ τ, ((N τ).det)⁻¹ ^ n τ

theorem eval_xPt_prodMinors {n : ι → ℕ} (h : a + a' = a + a') (N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ)
    (hN : ∀ τ, (N τ).det ≠ 0) (T : GlobalTheory.MinorFrame.Tup ι a (a + a') n) :
    eval (xPt N) (GlobalTheory.MinorFrame.prodMinors T) =
      lam n N * (((sgn h T : ℤˣ) : ℤ) : ℂ) * eval (yPt N) (GlobalTheory.MinorFrame.prodMinors (cTup h T)) := by
  simp only [GlobalTheory.MinorFrame.prodMinors, map_prod, eval_xPt_minorAt h N _ (hN _), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, lam, sgn, cTup, Units.coe_prod, Int.cast_prod]
  ring

def bottomMinors : GlobalTheory.MinorFrame.Pol ι (a + a') a' := ∏ τ, GlobalTheory.MinorFrame.minorAt τ (fun j : Fin a' => Fin.natAdd a j)

theorem eval_bottomMinors (y : ι × Fin (a + a') × Fin a' → ℂ) :
    eval y (bottomMinors (a := a)) = ∏ τ, (Matrix.of fun j j' : Fin a' => y (τ, Fin.natAdd a j, j')).det := by
  simp only [bottomMinors, map_prod, eval_minorAt]

theorem exists_eval_bottomMinors_ne_zero : ∃ y : ι × Fin (a + a') × Fin a' → ℂ, eval y (bottomMinors (a := a)) ≠ 0 := by
  refine ⟨yPt (fun _ => 1), ?_⟩
  rw [eval_bottomMinors, Finset.prod_ne_zero_iff]
  intro τ _
  have : (Matrix.of fun j j' : Fin a' => yPt (a := a) (ι := ι) (fun _ => 1) (τ, Fin.natAdd a j, j')) = 1 := by
    ext j j'
    simp [yPt, Matrix.one_apply]
  rw [this, Matrix.det_one]
  exact one_ne_zero

theorem exists_frame (y : ι × Fin (a + a') × Fin a' → ℂ) (hy : eval y (bottomMinors (a := a)) ≠ 0) :
    ∃ N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ, (∀ τ, (N τ).det ≠ 0) ∧ yPt N = y := by
  rw [eval_bottomMinors, Finset.prod_ne_zero_iff] at hy
  refine ⟨fun τ => (Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) ℂ) (Matrix.of fun i j => y (τ, Fin.castAdd a' i, j)) 0
    (Matrix.of fun i j => y (τ, Fin.natAdd a i, j))).reindex finSumFinEquiv finSumFinEquiv, fun τ => ?_, ?_⟩
  · rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    exact hy τ (Finset.mem_univ _)
  · funext ⟨τ, k, j⟩
    simp only [yPt, Matrix.reindex_apply, Matrix.submatrix_apply]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp

theorem exists_star (n : ι → ℕ) (h : a + a' = a + a') :
    ∃ Pl : GlobalTheory.MinorFrame.Pol ι (a + a') a →ₗ[ℂ] GlobalTheory.MinorFrame.Pol ι (a + a') a',
      (∀ T : GlobalTheory.MinorFrame.Tup ι a (a + a') n,
        Pl (GlobalTheory.MinorFrame.prodMinors T) = (((sgn h T : ℤˣ) : ℤ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (cTup h T)) ∧
      ∀ (κ : ι → Matrix.unitaryGroup (Fin (a + a')) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := ι) a (a + a') n,
        Pl (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ)) P) =
          (GlobalTheory.MinorFrame.detChar n (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)))⁻¹ •
            GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)) (Pl P) := by
  classical
  let A : (GlobalTheory.MinorFrame.Tup ι a (a + a') n → ℂ) →ₗ[ℂ] GlobalTheory.MinorFrame.Pol ι (a + a') a :=
    Fintype.linearCombination ℂ (fun T => GlobalTheory.MinorFrame.prodMinors T)
  let B : (GlobalTheory.MinorFrame.Tup ι a (a + a') n → ℂ) →ₗ[ℂ] GlobalTheory.MinorFrame.Pol ι (a + a') a' :=
    Fintype.linearCombination ℂ (fun T => (((sgn h T : ℤˣ) : ℤ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (cTup h T))
  have key : ∀ c N, (∀ τ, (N τ).det ≠ 0) → eval (xPt N) (A c) = lam n N * eval (yPt N) (B c) := by
    intro c N hN
    simp only [A, B, Fintype.linearCombination_apply, map_sum, smul_eq_C_mul, eval_mul, eval_C, Finset.mul_sum,
      eval_xPt_prodMinors h N hN]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  have hlam : ∀ N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ, (∀ τ, (N τ).det ≠ 0) → lam n N ≠ 0 := by
    intro N hN
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (inv_ne_zero (hN τ))
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    apply eq_zero_of_eval _ (bottomMinors (a := a)) exists_eval_bottomMinors_ne_zero
    intro y hy
    obtain ⟨N, hN, rfl⟩ := exists_frame y hy
    have := key c N hN
    rw [hc, map_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (hlam N hN)
  let f : LinearMap.range A →ₗ[ℂ] GlobalTheory.MinorFrame.Pol ι (a + a') a' :=
    ((LinearMap.ker A).liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap
  obtain ⟨Pl, hPl⟩ := LinearMap.exists_extend f
  have hPlA : ∀ c, Pl (A c) = B c := by
    intro c
    have := LinearMap.congr_fun hPl ⟨A c, LinearMap.mem_range_self A c⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image,
      Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hsingle : ∀ T, A (Pi.single T 1) = GlobalTheory.MinorFrame.prodMinors T := by
    intro T
    simp [A, Fintype.linearCombination_apply_single]
  have hrange : ∀ Q ∈ GlobalTheory.MinorFrame.inv (ι := ι) a (a + a') n, ∃ c, A c = Q := by
    intro Q hQ
    have hle : Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := a + a') (n := n))) ≤
        LinearMap.range A := by
      rw [Submodule.span_le]
      rintro _ ⟨T, rfl⟩
      exact ⟨Pi.single T 1, hsingle T⟩
    exact hle (GlobalTheory.MinorFrame.inv_le_span_prodMinors a (a + a') n hQ)
  refine ⟨Pl, fun T => ?_, fun κ P hP => ?_⟩
  · rw [← hsingle T, hPlA]
    simp [B, Fintype.linearCombination_apply_single]
  · obtain ⟨c, rfl⟩ := hrange P hP
    obtain ⟨c', hc'⟩ := hrange _ (GlobalTheory.MinorFrame.rowSub_mem_inv
      (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ)) hP)
    rw [← hc', hPlA, hPlA, ← sub_eq_zero]
    apply eq_zero_of_eval _ (bottomMinors (a := a)) exists_eval_bottomMinors_ne_zero
    intro y hy
    obtain ⟨N, hN, rfl⟩ := exists_frame y hy
    have hu : ∀ τ, (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)ᵀ *
        (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ) = 1 := by
      intro τ
      have h0 : star (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) * (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) = 1 := (κ τ).2.1
      ext i j
      have := congrArg (fun M : Matrix (Fin (a + a')) (Fin (a + a')) ℂ => M j i) h0
      simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, eq_comm, mul_comm] using this
    have hκ : ∀ τ, (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).det ≠ 0 := by
      intro τ hz
      have := congrArg Matrix.det (hu τ)
      rw [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    let N' : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ :=
      fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)ᵀ * N τ
    have hN' : ∀ τ, (N' τ).det ≠ 0 := by
      intro τ
      simp only [N', Matrix.det_mul, Matrix.det_transpose]
      exact mul_ne_zero (hκ τ) (hN τ)
    have hX : xPt N' = fun y => ∑ i', (κ y.1 : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ) i' y.2.1 *
        xPt N (y.1, i', y.2.2) := by
      funext ⟨τ, k, i⟩
      have hinv : (N' τ)⁻¹ = (N τ)⁻¹ * (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ) := by
        simp only [N']
        rw [Matrix.mul_inv_rev, Matrix.inv_eq_right_inv (hu τ)]
      simp only [xPt, hinv, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun _ _ => ?_
      ring
    have hY : yPt N' = fun y => ∑ i', (κ y.1 : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) i' y.2.1 * yPt N (y.1, i', y.2.2) := by
      funext ⟨τ, k, j⟩
      simp [yPt, N', Matrix.mul_apply]
    have hlam' : lam n N' = lam n N * (GlobalTheory.MinorFrame.detChar n (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)))⁻¹ := by
      simp only [lam, N', GlobalTheory.MinorFrame.detChar, Matrix.det_mul, Matrix.det_transpose, mul_inv, mul_pow,
        Finset.prod_mul_distrib, inv_pow, Finset.prod_inv_distrib]
      ring
    have hX' : ∀ Q, eval (xPt N) (GlobalTheory.MinorFrame.rowSub
        (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ)) Q) = eval (xPt N') Q := by
      intro Q
      rw [eval_rowSub, hX]
    have hY' : ∀ Q, eval (yPt N') Q =
        eval (yPt N) (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)) Q) := by
      intro Q
      rw [eval_rowSub, hY]
    have e1 := key c' N hN
    have e2 := key c N' hN'
    rw [hc', hX', e2, hY', hlam'] at e1
    rw [map_sub, smul_eq_C_mul, eval_mul, eval_C, sub_eq_zero]
    apply mul_left_cancel₀ (hlam N hN)
    rw [← e1]
    ring

end GlobalTheory.PluckerStar

namespace GlobalTheory.BotMatch

theorem minorF_rfl_eq_prodMinors {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : GlobalTheory.NormSum.Tup D a d n) :
    GlobalTheory.BotFormula.minorF rfl rfl T = GlobalTheory.MinorFrame.prodMinors (ι := D.what₂.Tau) T := by
  unfold GlobalTheory.BotFormula.minorF
  have : (fun k : D.what₂.Tau × Fin d × Fin a => (k.1, Fin.cast (rfl : d = d) k.2.1, Fin.cast (rfl : a = a) k.2.2)) = id := by
    funext k
    simp
  rw [this, MvPolynomial.rename_id]
  rfl

theorem complementary_minor_map : ∀ (D : D7) {a a' d : ℕ} (had : a + a' = d) (n : D.what₂.Tau → ℕ),
    ∃ (Pl : PolF D d a →ₗ[ℂ] PolF D d a') (ε : Tup D a d n → ℤˣ),
      (∀ T : Tup D a d n, Pl (GlobalTheory.BotFormula.minorF rfl rfl T) =
        ((ε T : ℤ) : ℂ) • GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) ∧
      ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a d n,
        Pl (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) =
          (GlobalTheory.MinorFrame.detChar n (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)))⁻¹ • GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (Pl P) := by
  intro D a a' d had n
  subst had
  obtain ⟨Pl, h1, h2⟩ := GlobalTheory.PluckerStar.exists_star (ι := D.what₂.Tau) n (rfl : a + a' = a + a')
  refine ⟨Pl, fun T => GlobalTheory.PluckerStar.sgn rfl T, fun T => ?_, h2⟩
  rw [minorF_rfl_eq_prodMinors, minorF_rfl_eq_prodMinors]
  exact h1 T

end GlobalTheory.BotMatch
