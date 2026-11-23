import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorMatricesAtComplexPointStatement
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SuccMulSuccSubOneDivSucc
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

theorem adjugate_transpose_rev {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (h : A.det ≠ 0) :
    (A.transpose.submatrix Fin.rev id).adjugate = (sgRev n * A.det) • (A⁻¹.transpose.submatrix id Fin.rev) := by
  have hB : (A.transpose.submatrix Fin.rev id).det = sgRev n * A.det := by
    show (A.transpose.submatrix (Fin.revPerm : Equiv.Perm (Fin n)) id).det = _
    rw [Matrix.det_permute, Matrix.det_transpose, sgRev]
  have hI : (A.transpose.submatrix Fin.rev id)⁻¹ = A⁻¹.transpose.submatrix id Fin.rev := by
    show (A.transpose.submatrix (Fin.revPerm : Equiv.Perm (Fin n)) (Equiv.refl _))⁻¹ = _
    rw [Matrix.inv_submatrix_equiv, Matrix.transpose_nonsing_inv]
    rfl
  have hne : (A.transpose.submatrix Fin.rev id).det ≠ 0 := by
    rw [hB]
    refine mul_ne_zero ?_ h
    unfold sgRev
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h1 | h1 <;> rw [h1] <;> norm_num
  rw [← hI, ← hB, Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hne, one_smul]

end GlobalTheory.TwV.DelA

namespace GlobalTheory.TwV.DelA

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem posJ_blkJ (j : ℕ) (x : Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :
    posJ X D pos j ⟨x.1, x.2.1⟩ = pos (blkJ X j x) := by
  cases j <;> rfl

theorem levelIndex_row_val_eq (j : ℕ) (x : Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :
    ((idxJ X j x).2.2.1 : ℕ) = x.2.2.1 := by
  cases j <;> rfl

theorem levelIndex_col_val_eq (j : ℕ) (x : Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :
    ((idxJ X j x).2.2.2 : ℕ) = x.2.2.2 := by
  cases j <;> rfl

def kOdd {j : ℕ} (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (τ : D.what₂.Tau) : ℂ :=
  (zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det

theorem evD_ySub (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) {j : ℕ} (hN : RankTie X D j)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ)
    (hf : ∀ τ, (f' τ).det ≠ 0) (hd : ∀ τ, (dfr X D hN d f' τ).det ≠ 0) (v : X.Pl) (s : Fin (X.G.P.n' v))
    (a t : Fin (NN X.G.P.m X.t j)) :
    evD X D pos ι hN d f' (ySub X Kc j v s a t) =
      (if IsOddPos s then ι (kOdd X D pos hN d f' (pos ⟨v, s⟩)) else 1) *
        ι (zT X D pos (dfr X D hN d f') (pos ⟨v, s⟩) (Fin.cast hN.1.symm a) (Fin.cast hN.1.symm t)) := by
  obtain ⟨_, hE, hO⟩ := GlobalTheory.T.operatorMatrices_at_complexPoint X D pos Kc ι j hN d f' hf hd v s
  have hsym : IsOddPos (pos.symm (pos ⟨v, s⟩)).2 ↔ IsOddPos s := by
    have hb : ∀ b : (Σ v : X.Pl, Fin (X.G.P.n' v)), b = ⟨v, s⟩ → (IsOddPos b.2 ↔ IsOddPos s) := by
      rintro _ rfl; exact Iff.rfl
    exact hb _ (Equiv.symm_apply_apply _ _)
  by_cases ho : IsOddPos s
  · rw [if_pos ho, ySub_odd X Kc j v s ho]
    have h1 := RingHom.map_adjugate (evD X D pos ι hN d f') (YtMat X Kc j v s)
    simp only [RingHom.mapMatrix_apply] at h1
    have h2 := congrFun (congrFun h1 a) t
    rw [Matrix.map_apply] at h2
    rw [h2, hO ho, Matrix.adjugate_smul, Fintype.card_fin,
      show (Fin.cast hN.1.symm : Fin (NN X.G.P.m X.t j) → Fin (D.R.N j)) = ⇑(finCongr hN.1.symm) from rfl,
      Matrix.adjugate_submatrix_equiv_self]
    have h3 := RingHom.map_adjugate ι ((dfr X D hN d f' (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id)
    simp only [RingHom.mapMatrix_apply] at h3
    rw [← h3, adjugate_transpose_rev _ (hd _)]
    have hz : zT X D pos (dfr X D hN d f') (pos ⟨v, s⟩) = ((dfr X D hN d f' (pos ⟨v, s⟩))⁻¹).transpose.submatrix id Fin.rev := by
      unfold zT; rw [if_pos (hsym.2 ho)]
    have hpos : 1 ≤ D.R.N j := by have := rkS X D hN; omega
    have he : ((D.R.N j : ℤ) - 1) = ((NN X.G.P.m X.t j - 1 : ℕ) : ℤ) := by
      rw [← hN.1]; push_cast [Nat.cast_sub hpos]; ring
    rw [hz, kOdd, he, zpow_natCast]
    simp only [Matrix.smul_apply, Matrix.submatrix_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, mul_assoc]
  · rw [if_neg ho, one_mul]
    have h0 : ySub X Kc j v s = dyMat X Kc j v s := by unfold ySub; rw [if_neg ho]
    have hz : zT X D pos (dfr X D hN d f') (pos ⟨v, s⟩) = dfr X D hN d f' (pos ⟨v, s⟩) := by
      unfold zT; rw [if_neg (fun h => ho (hsym.1 h))]
    have h2 := congrFun (congrFun (hE ho) a) t
    rw [Matrix.map_apply] at h2
    rw [h0, h2, hz]
    rfl

end GlobalTheory.TwV.DelA

namespace GlobalTheory.TwV.DelA

theorem evD_subD : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → OddDeg X j G → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (subD X Kc j G) = ι ((∏ τ, if IsOddPos (pos.symm τ).2 then ((zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ ((D.R.N j : ℤ) * cT1 X D pos j τ - szT X D pos j τ) else 1) * valZ X D pos j (rkS X D hN) Gc (dfr X D hN d f')) := by
  intro p _ X D pos Kc _ _ ι j hN Gc G hG hO d f' hf hd
  let g : Var (X.Pj j) → ℂ := fun y => zT X D pos (dfr X D hN d f') (posJ X D pos j ⟨y.1, y.2.1⟩)
    (Fin.cast (rkS X D hN) y.2.2.1) (Fin.cast (rkS X D hN) y.2.2.2)
  let φ : (X.Pj j).Xsp →+* Kc := (evD X D pos ι hN d f').comp (subD X Kc j : (X.Pj j).Xsp →+* DA X Kc j)
  let ψ : (X.Pj j).Xsp →+* Kc := MvPolynomial.eval₂Hom (algebraMap X.G.Kf Kc) (fun y => ι (g y))
  have hR : ι (valZ X D pos j (rkS X D hN) Gc (dfr X D hN d f')) = ψ G := by
    show ι (MvPolynomial.eval g Gc) = MvPolynomial.eval₂ (algebraMap X.G.Kf Kc) (fun y => ι (g y)) G
    rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, RingHom.comp_id,
      ← MvPolynomial.eval_map, ← hG, MvPolynomial.eval_map]
    rfl
  have hC : ∀ a, φ (MvPolynomial.C a) = ψ (MvPolynomial.C a) := by
    intro a
    show evD X D pos ι hN d f' (subD X Kc j (MvPolynomial.C a)) = MvPolynomial.eval₂ _ _ (MvPolynomial.C a)
    rw [MvPolynomial.eval₂_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_apply,
      MvPolynomial.algebraMap_apply]
    simp [evD]
  have hX : ∀ x, φ (MvPolynomial.X x) =
      (if IsOddPos (blkJ X j x).2 then ι (kOdd X D pos hN d f' (pos (blkJ X j x))) else 1) * ψ (MvPolynomial.X x) := by
    intro x
    show evD X D pos ι hN d f' (subD X Kc j (MvPolynomial.X x)) = _ * MvPolynomial.eval₂ _ _ (MvPolynomial.X x)
    rw [subD_X, MvPolynomial.eval₂_X, evD_ySub X D pos Kc ι hN d f' hf hd]
    congr 2
    show _ = zT X D pos (dfr X D hN d f') (posJ X D pos j ⟨x.1, x.2.1⟩) _ _
    rw [posJ_blkJ]
    congr 1 <;> ext <;> simp [levelIndex_row_val_eq, levelIndex_col_val_eq]
  have key := ringHom_scale φ ψ
    (fun x => if IsOddPos (blkJ X j x).2 then ι (kOdd X D pos hN d f' (pos (blkJ X j x))) else 1) hC hX
    (ι (∏ τ, if IsOddPos (pos.symm τ).2 then ((zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ ((D.R.N j : ℤ) * cT1 X D pos j τ - szT X D pos j τ) else 1)) G ?_
  · rw [map_mul, hR]
    exact key
  · intro m hm
    let H : (Σ v : X.Pl, Fin (X.G.P.n' v)) → ℂ := fun b =>
      if IsOddPos b.2 then kOdd X D pos hN d f' (pos b) ^ ((D.R.N j : ℤ) * cMu X j b.1 b.2 - szMu X j b.1 b.2) else 1
    have hF : ∀ τ, (if IsOddPos (pos.symm τ).2 then ((zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ ((D.R.N j : ℤ) * cT1 X D pos j τ - szT X D pos j τ) else 1) = H (pos.symm τ) := by
      intro τ
      simp only [H, cT1, szT, Equiv.apply_symm_apply]
      rfl
    rw [Finset.prod_congr rfl (fun τ _ => hF τ), Fintype.prod_equiv pos.symm (fun τ => H (pos.symm τ)) H (fun _ => rfl),
      map_prod, ← Finset.prod_fiberwise Finset.univ (blkJ X j)]
    refine Finset.prod_congr rfl fun b _ => ?_
    have h2 : ∏ x ∈ Finset.univ.filter (fun x => blkJ X j x = b),
        (if IsOddPos (blkJ X j x).2 then ι (kOdd X D pos hN d f' (pos (blkJ X j x))) else 1) ^ m x =
        (if IsOddPos b.2 then ι (kOdd X D pos hN d f' (pos b)) else 1) ^
          (∑ x ∈ Finset.univ.filter (fun x => blkJ X j x = b), m x) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.1 hx).2]
    rw [h2]
    by_cases hb : IsOddPos b.2
    · simp only [H]
      rw [if_pos hb, if_pos hb, hN.1, ← hO m hm b hb, zpow_natCast, map_pow]
    · simp only [H]
      rw [if_neg hb, if_neg hb, one_pow, map_one]

end GlobalTheory.TwV.DelA
