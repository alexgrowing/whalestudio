import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorMatricesAtComplexPointStatement

noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem pow_toNat_split {K : Type} [Field K] {a : K} (ha : a ≠ 0) (e : ℤ) :
    a ^ e.toNat = a ^ (-e).toNat * a ^ e := by
  have h := Int.toNat_sub_toNat_neg e
  calc a ^ e.toNat = a ^ (-e).toNat * a ^ ((e.toNat : ℤ) - ((-e).toNat : ℤ)) := by
        rw [zpow_sub₀ ha, zpow_natCast, zpow_natCast]
        field_simp
    _ = _ := by rw [h]

theorem zT_det_ne {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, (f τ).det ≠ 0) (τ : D.what₂.Tau) :
    (zT X D pos f τ).det ≠ 0 := by
  unfold zT
  split_ifs
  · have h1 : (((f τ)⁻¹).transpose.submatrix id Fin.rev).det
        = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) * (((f τ)⁻¹).transpose).det := by
      exact Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin n)) (((f τ)⁻¹).transpose)
    rw [h1, Matrix.det_transpose, Matrix.det_nonsing_inv]
    refine mul_ne_zero (by simp) ?_
    rw [Ring.inverse_eq_inv']
    exact inv_ne_zero (hf τ)
  · exact hf τ

theorem det_rev_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (A.transpose.submatrix Fin.rev id).det = sgRev n * A.det := by
  have : (A.transpose.submatrix Fin.rev id).det = _ := Matrix.det_permute (Fin.revPerm : Equiv.Perm (Fin n)) A.transpose
  rw [this, Matrix.det_transpose, sgRev]

theorem evD_det {Kc : Type} [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) {j : ℕ} (hN : RankTie X D j)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n (DA X Kc j)) : evD X D pos ι hN d f' M.det = (M.map (evD X D pos ι hN d f')).det :=
  RingHom.map_det _ M

theorem det_map_cast {Kc : Type} [Field Kc] (ι : ℂ →+* Kc) {a b : ℕ} (h : a = b) (B : Matrix (Fin b) (Fin b) ℂ) :
    ((B.map ι).submatrix (Fin.cast h) (Fin.cast h)).det = ι B.det := by
  have : ((B.map ι).submatrix (Fin.cast h) (Fin.cast h)).det = (B.map ι).det :=
    Matrix.det_submatrix_equiv_self (finCongr h) (B.map ι)
  rw [this, RingHom.map_det]
  rfl

theorem evD_numD_denD : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (numD X Kc j) = evD X D pos ι hN d f' (denD X Kc j) * ι (∏ τ, if IsOddPos (pos.symm τ).2 then (zT X D pos f' τ).det ^ (cT1 X D pos j τ - szT X D pos j τ) * ((zT X D pos f' τ).det ^ (D.R.N j) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ (cT1 X D pos j τ - (D.R.N j : ℤ) * cT1 X D pos j τ + szT X D pos j τ) else (dfr X D hN d f' τ).det ^ (X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j)).toNat) := by
  intro p _ X D pos Kc _ _ ι j hN d f' hf hd
  classical
  have key := GlobalTheory.T.operatorMatrices_at_complexPoint X D pos Kc ι j hN d f' hf hd
  have e : ∀ G : D.what₂.Tau → ℂ, ∏ τ, G τ = ∏ v, ∏ s, G (pos ⟨v, s⟩) := fun G => by
    rw [← Equiv.prod_comp pos G, Fintype.prod_sigma]
  rw [e, map_prod]
  unfold numD denD
  simp only [map_prod]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [cT1, szT]
  rw [Equiv.symm_apply_apply]
  obtain ⟨k1, k2, k3⟩ := key v s
  by_cases hs : IsOddPos s
  · simp only [if_pos hs]
    have hY : evD X D pos ι hN d f' (YtMat X Kc j v s).det
        = ι ((zT X D pos f' (pos ⟨v, s⟩)).det ^ D.R.N j * sgRev (D.R.N j) * (dfr X D hN d f' (pos ⟨v, s⟩)).det) := by
      rw [evD_det, k3 hs, Matrix.det_smul, det_map_cast, det_rev_transpose, Fintype.card_fin,
        show NN X.G.P.m X.t j = D.R.N j from hN.1.symm]
      simp only [map_mul, map_pow]
      ring
    have ha : ι (zT X D pos f' (pos ⟨v, s⟩)).det ≠ 0 := (map_ne_zero ι).2 (zT_det_ne X D pos f' hf _)
    have hb : ι ((zT X D pos f' (pos ⟨v, s⟩)).det ^ D.R.N j * sgRev (D.R.N j) * (dfr X D hN d f' (pos ⟨v, s⟩)).det) ≠ 0 := by
      refine (map_ne_zero ι).2 (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (zT_det_ne X D pos f' hf _)) ?_) (hd _))
      simp [sgRev]
    rw [map_mul ι ((zT X D pos f' (pos ⟨v, s⟩)).det ^ _), map_zpow₀, map_zpow₀]
    rw [map_mul (evD X D pos ι hN d f'), map_mul (evD X D pos ι hN d f'), map_pow (evD X D pos ι hN d f'),
      map_pow (evD X D pos ι hN d f'), map_pow (evD X D pos ι hN d f'), map_pow (evD X D pos ι hN d f'), k1, hY,
      pow_toNat_split ha (exY X j v s), pow_toNat_split hb (exT X j v s)]
    have h1 : exY X j v s = cMu X j v s - szMu X j v s := rfl
    have h2 : exT X j v s = cMu X j v s - (D.R.N j : ℤ) * cMu X j v s + szMu X j v s := by
      rw [exT, show NN X.G.P.m X.t j = D.R.N j from hN.1.symm]
    rw [h1, h2]
    ring
  · simp only [if_neg hs]
    rw [map_one, one_mul, map_pow (evD X D pos ι hN d f'), evD_det, k2 hs, det_map_cast, map_pow]

end GlobalTheory.TwV.DelA
