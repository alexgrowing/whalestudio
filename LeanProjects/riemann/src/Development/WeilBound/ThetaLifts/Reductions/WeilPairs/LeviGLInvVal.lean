import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.CAFInvol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.LeviParabolicGL

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

def Pm (ι R : Type) [CommRing R] [DecidableEq ι] : Matrix (ι ⊕ ι) (ι ⊕ ι) R := Matrix.fromBlocks 1 1 1 (-1)

def sM (c : R →+* R) (J b : Matrix ι ι R) : Matrix ι ι R := J⁻¹ * (b.map c)ᵀ * J

def L (c : R →+* R) (r : R) (J a b : Matrix ι ι R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Pm ι R * Matrix.fromBlocks a 0 0 (sM c J b) * (r • Pm ι R)

theorem PQ {r : R} (hr : 2 * r = 1) : Pm ι R * (r • Pm ι R) = 1 := by
  have hrr : r • (1 : Matrix ι ι R) + r • 1 = 1 := by
    rw [← add_smul, ← two_mul, hr, one_smul]
  rw [Matrix.mul_smul, Pm, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, ← Matrix.fromBlocks_one]
  simp [hrr]

theorem QP {r : R} (hr : 2 * r = 1) : (r • Pm ι R) * Pm ι R = 1 := mul_eq_one_comm.1 (PQ hr)

theorem mapT_mul (c : R →+* R) (x y : Matrix ι ι R) : ((x * y).map c)ᵀ = (y.map c)ᵀ * (x.map c)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem mapT_one (c : R →+* R) : ((1 : Matrix ι ι R).map c)ᵀ = 1 := by
  rw [Matrix.map_one _ c.map_zero c.map_one, Matrix.transpose_one]

theorem sM_mul (c : R →+* R) {J : Matrix ι ι R} (hJu : IsUnit J.det) (b b' : Matrix ι ι R) :
    sM c J b * sM c J b' = sM c J (b' * b) := by
  have j1 : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJu
  simp only [sM]
  calc J⁻¹ * (b.map c)ᵀ * J * (J⁻¹ * (b'.map c)ᵀ * J) = J⁻¹ * ((b.map c)ᵀ * (J * J⁻¹) * (b'.map c)ᵀ) * J := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [j1, Matrix.mul_one, ← mapT_mul]

theorem sM_one (c : R →+* R) {J : Matrix ι ι R} (hJu : IsUnit J.det) : sM c J 1 = 1 := by
  simp only [sM, mapT_one, Matrix.mul_one]
  exact Matrix.nonsing_inv_mul J hJu

theorem L_mul (c : R →+* R) {r : R} (hr : 2 * r = 1) {J : Matrix ι ι R} (hJu : IsUnit J.det) (a b a' b' : Matrix ι ι R) :
    L c r J a b * L c r J a' b' = L c r J (a * a') (b' * b) := by
  simp only [L]
  calc Pm ι R * Matrix.fromBlocks a 0 0 (sM c J b) * (r • Pm ι R) *
        (Pm ι R * Matrix.fromBlocks a' 0 0 (sM c J b') * (r • Pm ι R))
      = Pm ι R * (Matrix.fromBlocks a 0 0 (sM c J b) * ((r • Pm ι R) * Pm ι R) *
          Matrix.fromBlocks a' 0 0 (sM c J b')) * (r • Pm ι R) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [QP hr, Matrix.mul_one, Matrix.fromBlocks_multiply, sM_mul c hJu]; simp

theorem L_one (c : R →+* R) {r : R} (hr : 2 * r = 1) {J : Matrix ι ι R} (hJu : IsUnit J.det) :
    L c r J 1 1 = 1 := by
  simp only [L, sM_one c hJu, Matrix.fromBlocks_one, Matrix.mul_one]
  exact PQ hr

theorem L_col (c : R →+* R) {r : R} (hr : 2 * r = 1) (J a b : Matrix ι ι R) :
    L c r J a b * Matrix.fromRows (1 : Matrix ι ι R) (1 : Matrix ι ι R) =
      Matrix.fromRows (1 : Matrix ι ι R) (1 : Matrix ι ι R) * a := by
  have hrr : r • (1 : Matrix ι ι R) + r • 1 = 1 := by
    rw [← add_smul, ← two_mul, hr, one_smul]
  have q1 : (r • Pm ι R) * Matrix.fromRows (1 : Matrix ι ι R) (1 : Matrix ι ι R) =
      Matrix.fromRows (1 : Matrix ι ι R) (0 : Matrix ι ι R) := by
    rw [Matrix.smul_mul, Pm, Matrix.fromBlocks_mul_fromRows]
    ext i j
    rcases i with i | i <;> by_cases h : i = j <;>
      (try simp [Matrix.one_apply, h]) <;> linear_combination hr
  simp only [L]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, q1, Matrix.fromBlocks_mul_fromRows, Pm, Matrix.fromBlocks_mul_fromRows,
    Matrix.fromRows_mul]
  simp

theorem L_unitary (c : R →+* R) (hcc : ∀ x, c (c x) = x) {r : R} (hr : 2 * r = 1) {J : Matrix ι ι R}
    (hJ : (J.map c)ᵀ = J) (hJu : IsUnit J.det) (a b : Matrix ι ι R) (hba : b * a = 1) :
    ((L c r J a b).map c)ᵀ * Matrix.fromBlocks J 0 0 (-J) * L c r J a b = Matrix.fromBlocks J 0 0 (-J) := by
  have hcr : c r = r := by
    have := congrArg c hr
    rw [map_mul, map_ofNat, map_one] at this
    linear_combination r * this - c r * hr
  have hT : ∀ {κ : Type} [Fintype κ] (x y : Matrix κ κ R), ((x * y).map c)ᵀ = (y.map c)ᵀ * (x.map c)ᵀ := by
    intro κ _ x y
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hTT : ∀ x : Matrix ι ι R, (((x.map c)ᵀ).map c)ᵀ = x := by
    intro x; ext i j; exact hcc _
  have j1 : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJu
  set s := sM c J b with hs
  set u := (a.map c)ᵀ with hu
  have k1 : u * J * s = J := by
    rw [hs, sM]
    calc u * J * (J⁻¹ * (b.map c)ᵀ * J) = u * (J * J⁻¹) * (b.map c)ᵀ * J := by simp only [Matrix.mul_assoc]
      _ = J := by rw [j1, Matrix.mul_one, hu, ← mapT_mul, hba, mapT_one, Matrix.one_mul]
  have k2 : (s.map c)ᵀ * J * a = J := by
    have := congrArg (fun x : Matrix ι ι R => (x.map c)ᵀ) k1
    simp only [hT, hJ] at this
    rw [hu, hTT] at this
    rw [Matrix.mul_assoc, this]
  set P := Pm ι R with hP
  set Q := r • P with hQ
  have pT : (P.map c)ᵀ = P := by
    rw [hP, Pm]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply, apply_ite c, eq_comm]
  have qT : (Q.map c)ᵀ = Q := by
    ext i j
    have := congrFun (congrFun pT i) j
    simp only [hQ, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hcr] at this ⊢
    rw [this]
  have p1 : P * Q = 1 := PQ hr
  have p2 : Q * P = 1 := QP hr
  have e1 : P * Matrix.fromBlocks J 0 0 (-J) * P = Matrix.fromBlocks 0 (J + J) (J + J) 0 := by
    rw [hP, Pm, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]; simp
  have e2 : ((Matrix.fromBlocks a 0 0 s).map c)ᵀ = Matrix.fromBlocks u 0 0 (s.map c)ᵀ := by
    rw [hu, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]; simp
  have e3 : Matrix.fromBlocks u 0 0 (s.map c)ᵀ * Matrix.fromBlocks 0 (J + J) (J + J) 0 * Matrix.fromBlocks a 0 0 s =
      Matrix.fromBlocks 0 (J + J) (J + J) 0 := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_add, Matrix.add_mul, k1, k2]
  show ((P * Matrix.fromBlocks a 0 0 s * Q).map c)ᵀ * Matrix.fromBlocks J 0 0 (-J) * (P * Matrix.fromBlocks a 0 0 s * Q) = _
  rw [hT, hT, pT, qT, e2]
  calc Q * (Matrix.fromBlocks u 0 0 (s.map c)ᵀ * P) * Matrix.fromBlocks J 0 0 (-J) *
        (P * Matrix.fromBlocks a 0 0 s * Q)
      = Q * (Matrix.fromBlocks u 0 0 (s.map c)ᵀ * (P * Matrix.fromBlocks J 0 0 (-J) * P) *
          Matrix.fromBlocks a 0 0 s) * Q := by simp only [Matrix.mul_assoc]
    _ = (Q * P) * Matrix.fromBlocks J 0 0 (-J) * (P * Q) := by
        rw [e1, e3, ← e1]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [p1, p2, Matrix.one_mul, Matrix.mul_one]

theorem L_map {R' : Type} [CommRing R'] (φ : R →+* R') (c : R →+* R) (c' : R' →+* R')
    (hφ : ∀ x, φ (c x) = c' (φ x)) (r : R) {J : Matrix ι ι R} (hJu : IsUnit J.det) (a b : Matrix ι ι R) :
    (L c r J a b).map φ = L c' (φ r) (J.map φ) (a.map φ) (b.map φ) := by
  have hinv : (J⁻¹).map φ = (J.map φ)⁻¹ := by
    refine (Matrix.inv_eq_left_inv ?_).symm
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul J hJu, Matrix.map_one _ φ.map_zero φ.map_one]
  have hP : (Pm ι R).map φ = Pm ι R' := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Pm, Matrix.one_apply, apply_ite φ]
  have hQ : (r • Pm ι R).map φ = φ r • Pm ι R' := by
    ext i j
    have := congrFun (congrFun hP i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at this ⊢
    rw [this]
  have hb : ((b.map c)ᵀ).map φ = ((b.map φ).map c')ᵀ := by
    ext i j; simp [hφ]
  simp only [L, sM, Matrix.map_mul, hP, hQ, Matrix.fromBlocks_map, hinv, hb, Matrix.map_zero _ φ.map_zero]

variable {n : ℕ}

def leviGL (c : R →+* R) {r : R} (hr : 2 * r = 1) {J : Matrix (Fin n) (Fin n) R} (hJu : IsUnit J.det) :
    GL (Fin n) R →* GL (Fin (n + n)) R where
  toFun t := ⟨(L c r J t.1 (t⁻¹).1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    (L c r J (t⁻¹).1 t.1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    by rw [Matrix.submatrix_mul_equiv, L_mul c hr hJu, t.mul_inv, L_one c hr hJu, Matrix.submatrix_one_equiv],
    by rw [Matrix.submatrix_mul_equiv, L_mul c hr hJu, t.inv_mul, L_one c hr hJu, Matrix.submatrix_one_equiv]⟩
  map_one' := by
    ext1
    simp only [Units.val_one, inv_one, Units.val_mk, L_one c hr hJu, Matrix.submatrix_one_equiv]
  map_mul' s t := by
    ext1
    simp only [Units.val_mul, mul_inv_rev, Units.val_mk]
    rw [Matrix.submatrix_mul_equiv, L_mul c hr hJu]

theorem leviGL_val (c : R →+* R) {r : R} (hr : 2 * r = 1) {J : Matrix (Fin n) (Fin n) R} (hJu : IsUnit J.det)
    (t : GL (Fin n) R) : ((leviGL c hr hJu t : GL (Fin (n + n)) R) : Matrix (Fin (n + n)) (Fin (n + n)) R) =
      (L c r J t.1 (t⁻¹).1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl

theorem leviGL_mem (c : R →+* R) (hcc : ∀ x, c (c x) = x) {r : R} (hr : 2 * r = 1) {J : Matrix (Fin n) (Fin n) R}
    (hJ : (J.map c)ᵀ = J) (hJu : IsUnit J.det) (t : GL (Fin n) R) :
    leviGL c hr hJu t ∈ Formalism.UG.UJ c ((Matrix.fromBlocks J 0 0 (-J)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) := by
  show Formalism.UG.cT c ((L c r J t.1 (t⁻¹).1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) *
    (Matrix.fromBlocks J 0 0 (-J)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
    (L c r J t.1 (t⁻¹).1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
    (Matrix.fromBlocks J 0 0 (-J)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  have e : Formalism.UG.cT c ((L c r J t.1 (t⁻¹).1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) =
      (((L c r J t.1 (t⁻¹).1).map c)ᵀ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  rw [e, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    L_unitary c hcc hr hJ hJu _ _ t.inv_mul]

theorem leviGL_col (c : R →+* R) {r : R} (hr : 2 * r = 1) {J : Matrix (Fin n) (Fin n) R} (hJu : IsUnit J.det)
    (t : GL (Fin n) R) :
    ((leviGL c hr hJu t : GL (Fin (n + n)) R) : Matrix (Fin (n + n)) (Fin (n + n)) R) *
        PositivityTheory.ThKW.ModulusFactorDefinition.dC R n = PositivityTheory.ThKW.ModulusFactorDefinition.dC R n * t.1 := by
  rw [leviGL_val]
  simp only [PositivityTheory.ThKW.ModulusFactorDefinition.dC, diagCols]
  rw [Matrix.submatrix_mul_equiv]
  exact congrArg (fun X => Matrix.submatrix X finSumFinEquiv.symm id) (L_col c hr J t.1 (t⁻¹).1)

theorem leviGL_map {R' : Type} [CommRing R'] (φ : R →+* R') (c : R →+* R) (c' : R' →+* R')
    (hφ : ∀ x, φ (c x) = c' (φ x)) {r : R} (hr : 2 * r = 1) (hr' : 2 * φ r = 1)
    {J : Matrix (Fin n) (Fin n) R} (hJu : IsUnit J.det) (hJu' : IsUnit (J.map φ).det) (t : GL (Fin n) R) :
    Formalism.UG.bc φ (leviGL c hr hJu t) = leviGL c' hr' hJu' (Matrix.GeneralLinearGroup.map φ t) := by
  ext1
  show ((L c r J t.1 (t⁻¹).1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm).map φ =
    (L c' (φ r) (J.map φ) (t.1.map φ) ((t⁻¹).1.map φ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  rw [← Matrix.submatrix_map, L_map φ c c' hφ r hJu]

end PositivityTheory.ThKW.LeviParabolicGL

set_option maxHeartbeats 800000 in
open PositivityTheory.ThKW.LeviParabolicGL in

theorem PositivityTheory.ThKW.PhaseFourierInjectivity.levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E), IsHermND σ JT →
    ∃ m : GL (Fin nT) (AF F ⊗[F] E) →* GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT), Continuous m ∧
      (∀ t, mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) (m t) * PositivityTheory.ThKW.ModulusFactorDefinition.dC (AF F ⊗[F] E) nT =
        PositivityTheory.ThKW.ModulusFactorDefinition.dC (AF F ⊗[F] E) nT * t.1) ∧
      ∀ a : GL (Fin nT) E, m (Matrix.GeneralLinearGroup.map (incAF F E) a) ∈
        GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := by
  intro F E _ _ _ _ _ σ B hB n JT hT
  classical
  have hc : IsCMExt F E σ := hB.cm
  have hcc := GlobalTheory.SplitLagrF.cAF_invol hc
  have hccE : ∀ x : E, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => GlobalTheory.SplitDetCharF.sig_invol hc x
  set rE : E := (2 : E)⁻¹ with hrE
  have hrE2 : 2 * rE = 1 := mul_inv_cancel₀ two_ne_zero
  have hr : 2 * (inclR (F := F) (AF F)) rE = 1 := by
    have := congrArg (inclR (F := F) (AF F)) hrE2
    rwa [map_mul, map_ofNat, map_one] at this
  have hJ : ((JR (F := F) (AF F) JT).map (cAF σ))ᵀ = JR (F := F) (AF F) JT := by
    ext i j
    show (1 : AF F) ⊗ₜ[F] σ (JT j i) = (1 : AF F) ⊗ₜ[F] JT i j
    rw [hT.1]
  have hJE : (JT.map (σ : E →+* E))ᵀ = JT := by
    ext i j
    exact hT.1 i j
  have hu : IsUnit (JR (F := F) (AF F) JT).det := by
    have := ((Ne.isUnit hT.2).map (inclR (F := F) (AF F)))
    rwa [RingHom.map_det] at this
  have huE : IsUnit JT.det := Ne.isUnit hT.2
  have eJ : JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) =
      (Matrix.fromBlocks (JR (F := F) (AF F) JT) 0 0 (-JR (F := F) (AF F) JT)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [GlobalTheory.WeilSchrodinger.DblTargetF.dblG, JR, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Matrix.map_apply] <;> simp [dbl]
  have eJE : GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT =
      (Matrix.fromBlocks JT 0 0 (-JT)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  let mG := leviGL (cAF σ) hr hu
  have hmem : ∀ t, mG t ∈ HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := by
    intro t
    have h := leviGL_mem (cAF σ) hcc hr hJ hu t
    rw [← eJ] at h
    exact h
  let m₀ : GL (Fin n) (AF F ⊗[F] E) →* HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := mG.codRestrict _ hmem
  let m : GL (Fin n) (AF F ⊗[F] E) →* GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) :=
    { toFun := fun t => m₀ t
      map_one' := m₀.map_one
      map_mul' := m₀.map_mul }
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have hcont_c : Continuous (cAF (F := F) (E := E) σ) := GlobalTheory.HeisThetaF.continuous_cAF
  have hL : ∀ (f g : GL (Fin n) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), Continuous f → Continuous g →
      Continuous fun t => (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) (f t) (g t)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    intro f g hf hg
    refine Continuous.matrix_submatrix ?_ _ _
    simp only [L, sM]
    refine ((continuous_const.matrix_mul ?_).matrix_mul continuous_const)
    refine Continuous.matrix_fromBlocks hf continuous_const continuous_const ?_
    exact (continuous_const.matrix_mul ((hg.matrix_map hcont_c).matrix_transpose)).matrix_mul continuous_const
  have hmG : Continuous mG := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun t : GL (Fin n) (AF F ⊗[F] E) =>
        (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) t.1 (t⁻¹).1).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm
      exact hL _ _ Units.continuous_val Units.continuous_coe_inv
    · show Continuous fun t : GL (Fin n) (AF F ⊗[F] E) =>
        (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) (t⁻¹).1 t.1).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm
      exact hL _ _ Units.continuous_coe_inv Units.continuous_val
  have hm : Continuous m := by
    have : Continuous fun t => (⟨mG t, hmem t⟩ : HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) :=
      hmG.subtype_mk _
    exact this
  refine ⟨m, hm, ?_, ?_⟩
  · intro t
    exact leviGL_col (cAF σ) hr hu t
  · intro a
    let a' : GL (Fin n) (AF F ⊗[F] E) := Matrix.GeneralLinearGroup.map (incAF F E) a
    show ((m₀ a' : HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) : GL (Fin (n + n)) (AF F ⊗[F] E)) ∈
      HFin (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
    refine ⟨leviGL (σ : E →+* E) hrE2 huE a, ?_, ?_⟩
    · have h := leviGL_mem (σ : E →+* E) hccE hrE2 hJE huE a
      rw [← eJE] at h
      exact h
    · exact leviGL_map (inclR (F := F) (AF F)) (σ : E →+* E) (cAF σ) (fun x => rfl) hrE2 hr huE hu a
