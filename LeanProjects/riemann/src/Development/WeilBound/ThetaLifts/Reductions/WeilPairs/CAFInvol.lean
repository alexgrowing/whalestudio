import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacterIm
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

section Alg

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem levi_alg (c : R →+* R) (hcc : ∀ x, c (c x) = x) (r : R) (hr : 2 * r = 1) (J : Matrix ι ι R)
    (hJ : (J.map c)ᵀ = J) (hJu : IsUnit J.det) (a : R) (ha : c a = a) (t t' : Matrix ι ι R)
    (h1 : t * t' = 1) (h2 : t' * t = 1) (hs : a • (t - 1) = t - 1) :
    ∃ H H' : Matrix (ι ⊕ ι) (ι ⊕ ι) R, H * H' = 1 ∧ H' * H = 1 ∧
      (H.map c)ᵀ * Matrix.fromBlocks J 0 0 (-J) * H = Matrix.fromBlocks J 0 0 (-J) ∧
      H * Matrix.fromRows (1 : Matrix ι ι R) (1 : Matrix ι ι R) = Matrix.fromRows (1 : Matrix ι ι R) (1 : Matrix ι ι R) * t ∧
      a • (H - 1) = H - 1 ∧
      (∃ M : Matrix ι ι R, IsUnit M.det ∧
        H' * Matrix.fromRows (1 : Matrix ι ι R) (-1 : Matrix ι ι R) = Matrix.fromRows (1 : Matrix ι ι R) (-1 : Matrix ι ι R) * M) ∧
      H.det * c t.det = t.det := by
  have hcr : c r = r := by
    have := congrArg c hr
    rw [map_mul, map_ofNat, map_one] at this
    linear_combination r * this - c r * hr
  have hT : ∀ {κ : Type} [Fintype κ] (x y : Matrix κ κ R), ((x * y).map c)ᵀ = (y.map c)ᵀ * (x.map c)ᵀ := by
    intro κ _ x y
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hT1 : ((1 : Matrix ι ι R).map c)ᵀ = 1 := by
    rw [Matrix.map_one _ c.map_zero c.map_one, Matrix.transpose_one]
  have hTT : ∀ x : Matrix ι ι R, (((x.map c)ᵀ).map c)ᵀ = x := by
    intro x; ext i j; exact hcc _
  have j1 : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJu
  have j2 : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hJu
  obtain ⟨u, hu⟩ : ∃ u, u = (t.map c)ᵀ := ⟨_, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u', u' = (t'.map c)ᵀ := ⟨_, rfl⟩
  have u1 : u * u' = 1 := by rw [hu, hu', ← hT, h2, hT1]
  have u2 : u' * u = 1 := by rw [hu, hu', ← hT, h1, hT1]
  obtain ⟨s, hs1⟩ : ∃ s, s = J⁻¹ * u' * J := ⟨_, rfl⟩
  obtain ⟨s', hs2⟩ : ∃ s', s' = J⁻¹ * u * J := ⟨_, rfl⟩
  have s1 : s * s' = 1 := by
    rw [hs1, hs2]
    calc J⁻¹ * u' * J * (J⁻¹ * u * J) = J⁻¹ * (u' * (J * J⁻¹) * u) * J := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [j1, Matrix.mul_one, u2, Matrix.mul_one, j2]
  have s2 : s' * s = 1 := mul_eq_one_comm.1 s1
  have k1 : u * J * s = J := by
    rw [hs1]
    calc u * J * (J⁻¹ * u' * J) = u * (J * J⁻¹) * u' * J := by simp only [Matrix.mul_assoc]
      _ = J := by rw [j1, Matrix.mul_one, u1, Matrix.one_mul]
  have k2 : (s.map c)ᵀ * J * t = J := by
    have := congrArg (fun x : Matrix ι ι R => (x.map c)ᵀ) k1
    simp only [hT, hJ] at this
    rw [hu, hTT] at this
    rw [Matrix.mul_assoc, this]
  have a1 : a • (t' - 1) = t' - 1 := by
    have e : t' - 1 = -t' * (t - 1) := by rw [Matrix.mul_sub, Matrix.neg_mul, h2]; simp [sub_eq_add_neg, add_comm]
    rw [e, ← Matrix.mul_smul, hs]
  have a2 : a • (u' - 1) = u' - 1 := by
    ext i j
    have := congrArg c (congrFun (congrFun a1 j) i)
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, map_mul, map_sub, ha] at this ⊢
    have e : c ((1 : Matrix ι ι R) j i) = (1 : Matrix ι ι R) i j := congrFun (congrFun hT1 i) j
    rw [e] at this
    rw [hu']
    exact this
  have a3 : a • (s - 1) = s - 1 := by
    have e : s - 1 = J⁻¹ * (u' - 1) * J := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, j2, hs1]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, a2]
  have d1 : s.det * c t.det = 1 := by
    have e : c t.det = u.det := by
      rw [hu, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
    have := congrArg Matrix.det k1
    rw [Matrix.det_mul, Matrix.det_mul] at this
    refine hJu.mul_left_cancel ?_
    rw [e]
    linear_combination this
  obtain ⟨P, hP⟩ : ∃ P : Matrix (ι ⊕ ι) (ι ⊕ ι) R, P = Matrix.fromBlocks 1 1 1 (-1) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (ι ⊕ ι) (ι ⊕ ι) R, Q = r • P := ⟨_, rfl⟩
  have hrr : r • (1 : Matrix ι ι R) + r • 1 = 1 := by
    rw [← add_smul, ← two_mul, hr, one_smul]
  have p1 : P * Q = 1 := by
    rw [hQ, Matrix.mul_smul, hP, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, ← Matrix.fromBlocks_one]
    simp [hrr]
  have p2 : Q * P = 1 := mul_eq_one_comm.1 p1
  have pT : (P.map c)ᵀ = P := by
    rw [hP]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply, apply_ite c, eq_comm]
  have qT : (Q.map c)ᵀ = Q := by
    ext i j
    have := congrFun (congrFun pT i) j
    simp only [hQ, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hcr] at this ⊢
    rw [this]
  have c1 : P * Matrix.fromRows (1 : Matrix ι ι R) (0 : Matrix ι ι R) = Matrix.fromRows (1 : Matrix ι ι R) (1 : Matrix ι ι R) := by
    rw [hP, Matrix.fromBlocks_mul_fromRows]; simp
  have c2 : P * Matrix.fromRows (0 : Matrix ι ι R) (1 : Matrix ι ι R) = Matrix.fromRows (1 : Matrix ι ι R) (-1 : Matrix ι ι R) := by
    rw [hP, Matrix.fromBlocks_mul_fromRows]; simp
  have conj : ∀ X Y : Matrix (ι ⊕ ι) (ι ⊕ ι) R, X * Y = 1 → P * X * Q * (P * Y * Q) = 1 := by
    intro X Y h
    calc P * X * Q * (P * Y * Q) = P * (X * (Q * P) * Y) * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [p2, Matrix.mul_one, h, Matrix.mul_one, p1]
  refine ⟨P * Matrix.fromBlocks t 0 0 s * Q, P * Matrix.fromBlocks t' 0 0 s' * Q, conj _ _ ?_, conj _ _ ?_, ?_, ?_, ?_,
    ⟨s', ?_, ?_⟩, ?_⟩
  · rw [Matrix.fromBlocks_multiply, h1, s1]; simp
  · rw [Matrix.fromBlocks_multiply, h2, s2]; simp
  · have e1 : P * Matrix.fromBlocks J 0 0 (-J) * P = Matrix.fromBlocks 0 (J + J) (J + J) 0 := by
      rw [hP, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]; simp
    have e2 : ((Matrix.fromBlocks t 0 0 s).map c)ᵀ = Matrix.fromBlocks u 0 0 (s.map c)ᵀ := by
      rw [hu, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]; simp
    have e3 : Matrix.fromBlocks u 0 0 (s.map c)ᵀ * Matrix.fromBlocks 0 (J + J) (J + J) 0 * Matrix.fromBlocks t 0 0 s =
        Matrix.fromBlocks 0 (J + J) (J + J) 0 := by
      rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp [Matrix.mul_add, Matrix.add_mul, k1, k2]
    rw [hT, hT, pT, qT, e2]
    calc Q * (Matrix.fromBlocks u 0 0 (s.map c)ᵀ * P) * Matrix.fromBlocks J 0 0 (-J) *
          (P * Matrix.fromBlocks t 0 0 s * Q)
        = Q * (Matrix.fromBlocks u 0 0 (s.map c)ᵀ * (P * Matrix.fromBlocks J 0 0 (-J) * P) *
            Matrix.fromBlocks t 0 0 s) * Q := by simp only [Matrix.mul_assoc]
      _ = (Q * P) * Matrix.fromBlocks J 0 0 (-J) * (P * Q) := by
          rw [e1, e3, ← e1]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [p1, p2, Matrix.one_mul, Matrix.mul_one]
  · rw [← c1]
    calc P * Matrix.fromBlocks t 0 0 s * Q * (P * Matrix.fromRows (1 : Matrix ι ι R) (0 : Matrix ι ι R))
        = P * (Matrix.fromBlocks t 0 0 s * ((Q * P) * Matrix.fromRows (1 : Matrix ι ι R) (0 : Matrix ι ι R))) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [p2, Matrix.one_mul, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]; simp
  · have e : P * Matrix.fromBlocks t 0 0 s * Q - 1 = P * Matrix.fromBlocks (t - 1) 0 0 (s - 1) * Q := by
      have e0 : Matrix.fromBlocks (t - 1) 0 0 (s - 1) = Matrix.fromBlocks t 0 0 s - 1 := by
        rw [← Matrix.fromBlocks_one, sub_eq_add_neg (Matrix.fromBlocks t 0 0 s), Matrix.fromBlocks_neg,
          Matrix.fromBlocks_add]
        simp [sub_eq_add_neg]
      rw [e0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, p1]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.fromBlocks_smul, hs, a3, smul_zero]
  · exact Matrix.isUnit_det_of_left_inverse s1
  · rw [← c2]
    calc P * Matrix.fromBlocks t' 0 0 s' * Q * (P * Matrix.fromRows (0 : Matrix ι ι R) (1 : Matrix ι ι R))
        = P * (Matrix.fromBlocks t' 0 0 s' * ((Q * P) * Matrix.fromRows (0 : Matrix ι ι R) (1 : Matrix ι ι R))) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [p2, Matrix.one_mul, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]; simp
  · have e := congrArg Matrix.det p1
    rw [Matrix.det_mul, Matrix.det_one] at e
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
    linear_combination t.det * s.det * c t.det * e + t.det * d1

end Alg

theorem cAF_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) (z : AEF F E) : cAF σ (cAF σ z) = z := by
  have hs : ∀ (a : AF F) (x : E), cAF σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := fun _ _ => rfl
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => rw [hs, hs, GlobalTheory.SplitDetCharF.sig_invol h]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]

theorem exists_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E), IsHermND σ JT →
      ∀ e, IsSplitIdemF σ e → ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        (∀ i j, (e + cAF σ e) * (t.1 - 1) i j = (t.1 - 1) i j) →
      ∃ h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * dC F E nT = dC F E nT * t.1 ∧
        SuppAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h ∧
        (∃ M : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), IsUnit M.det ∧ ∀ (nS : ℕ) (y : WOF F E nS nT),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h⁻¹ * (aC F E nT * y) = aC F E nT * (M * y)) ∧
        ∃ x : (AF F ⊗[F] E)ˣ, IsDetAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h x ∧
          ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (m : ℕ), ResEtaF χ m → χ x = χ (Matrix.GeneralLinearGroup.det t) := by
  intro F E _ _ _ _ _ σ B hB n JT hT e he t ht
  have hc : IsCMExt F E σ := hB.cm
  have hcc := cAF_invol hc
  obtain ⟨r, hr⟩ : ∃ r : AEF F E, 2 * r = 1 := by
    have h := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (AF F ⊗[F] E))
    rw [map_ofNat] at h
    exact h.exists_right_inv
  have hJ : ((JR (F := F) (AF F) JT).map (cAF σ))ᵀ = JR (F := F) (AF F) JT := by
    ext i j
    show (1 : AF F) ⊗ₜ[F] σ (JT j i) = (1 : AF F) ⊗ₜ[F] JT i j
    rw [hT.1]
  have hu : IsUnit (JR (F := F) (AF F) JT).det := by
    have := ((Ne.isUnit hT.2).map (inclR (F := F) (AF F)))
    rwa [RingHom.map_det] at this
  have ha : cAF σ (e + cAF σ e) = e + cAF σ e := by rw [RingHom.map_add, hcc, add_comm]
  obtain ⟨H, H', g1, g2, g3, g4, g5, ⟨M, hM, g6⟩, g7⟩ := levi_alg (cAF σ) hcc r hr _ hJ hu _ ha t.1 (t⁻¹).1
    t.mul_inv t.inv_mul (by ext i j; exact ht i j)
  have eJ : JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) =
      (Matrix.fromBlocks (JR (F := F) (AF F) JT) 0 0 (-JR (F := F) (AF F) JT)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [GlobalTheory.WeilSchrodinger.DblTargetF.dblG, JR, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Matrix.map_apply] <;> simp [dbl]
  let G : GL (Fin (n + n)) (AF F ⊗[F] E) :=
    ⟨H.submatrix finSumFinEquiv.symm finSumFinEquiv.symm, H'.submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
      by rw [Matrix.submatrix_mul_equiv, g1, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, g2, Matrix.submatrix_one_equiv]⟩
  have hG : G ∈ HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := by
    show ((H.map (cAF σ))ᵀ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
      JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) *
      H.submatrix finSumFinEquiv.symm finSumFinEquiv.symm = JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
    rw [eJ, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, g3]
  obtain ⟨h, m1, m2⟩ : ∃ h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT),
      mtF σ _ h = H.submatrix finSumFinEquiv.symm finSumFinEquiv.symm ∧
      mtF σ _ h⁻¹ = H'.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := ⟨⟨G, hG⟩, rfl, rfl⟩
  have sub : ∀ (X : Matrix (Fin n ⊕ Fin n) (Fin n) (AEF F E)) (Y : Matrix (Fin n) (Fin n) (AEF F E)),
      (X * Y).submatrix (finSumFinEquiv (m := n) (n := n)).symm id = X.submatrix finSumFinEquiv.symm id * Y :=
    fun X Y => rfl
  have e1 : e * e = e := he.1
  have e2 : e * cAF σ e = 0 := he.2.1
  have e3 : cAF σ e * cAF σ e = cAF σ e := by rw [← RingHom.map_mul, e1]
  have hd : (1 - (e + cAF σ e)) * (t.1.det - 1) = 0 :=
    GlobalTheory.SplitDetCharF.mul_det_sub_one _ _ fun i j => by rw [sub_mul, one_mul, ht i j, sub_self]
  refine ⟨h, ?_, ?_, ⟨M, hM, fun nS y => ?_⟩,
    GlobalTheory.SplitDetCharF.cutDet σ _ e e1 h, ?_, fun χ m hχ => ?_⟩
  · rw [m1, dC, Matrix.submatrix_mul_equiv, ← sub]
    exact congrArg (fun X => Matrix.submatrix X finSumFinEquiv.symm id) g4
  · intro i j
    rw [m1, ← Matrix.submatrix_one_equiv (finSumFinEquiv (m := n) (n := n)).symm]
    exact congrFun (congrFun g5 (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  · rw [m2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, aC, Matrix.submatrix_mul_equiv, ← sub]
    exact congrArg (fun X => Matrix.submatrix X finSumFinEquiv.symm id * y) g6
  · exact add_comm _ _
  · let w : (AEF F E)ˣ := Units.map (GlobalTheory.SplitDetCharF.cut (cAF σ e) e3) (Matrix.GeneralLinearGroup.det t)
    let u : (AEF F E)ˣ := Units.map (GlobalTheory.SplitDetCharF.cut e e1) (Matrix.GeneralLinearGroup.det t)
    have hw : (w : AEF F E) = (1 - cAF σ e) + cAF σ e * t.1.det := rfl
    have hu' : (u : AEF F E) = (1 - e) + e * t.1.det := rfl
    have huw : Matrix.GeneralLinearGroup.det t = u * w := by
      refine Units.ext ?_
      rw [Units.val_mul, hw, hu', Matrix.GeneralLinearGroup.val_det_apply]
      linear_combination hd - (t.1.det - 1) ^ 2 * e2
    obtain ⟨w', hw'⟩ : IsUnit (cAF σ (w : AEF F E)) := w.isUnit.map (cAF σ)
    have hx : GlobalTheory.SplitDetCharF.cutDet σ _ e e1 h * w' = u := by
      refine Units.ext ?_
      rw [Units.val_mul, hw', hw, hu', GlobalTheory.SplitDetCharF.cutDet_val, m1, Matrix.det_submatrix_equiv_self,
        RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, hcc]
      linear_combination (H.det - 1) * (cAF σ t.1.det - 1) * e1 + e * g7
    have hy := GlobalTheory.SplitDetCharF.char_eq_of_mul_conj hc hχ w'⁻¹ w (by rw [← hw', Units.inv_mul])
    rw [huw, map_mul, ← hy, ← map_mul, ← hx, mul_inv_cancel_right]

end GlobalTheory.SplitLagrF

end
