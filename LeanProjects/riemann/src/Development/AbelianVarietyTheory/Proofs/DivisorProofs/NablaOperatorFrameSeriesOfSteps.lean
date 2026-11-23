import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

section NabAux

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

open Classical in

def colCoef {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ)
    (lam : Let cx) (ℓ : LtN Dw n) : k :=
  ∑ j : Fin n, if ℓ = ⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2, j⟩ then B lam.1.1.1 lam.1.2 j else 0

theorem sum_colCoef_smul {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ)
    (lam : Let cx) {M : Type} [AddCommGroup M] [Module k M] (x : LtN Dw n → M) :
    ∑ ℓ, colCoef B cx lam ℓ • x ℓ =
      ∑ j : Fin n, B lam.1.1.1 lam.1.2 j • x ⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2, j⟩ := by
  classical
  simp only [colCoef, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2, j⟩ : LtN Dw n)]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem polyP_eq_aeval {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) :
    polyP B cx = MvPolynomial.aeval (fun lam : Let cx => ∑ ℓ, MvPolynomial.C (colCoef B cx lam ℓ) *
      (MvPolynomial.X ℓ : MvPolynomial (LtN Dw n) k)) (polyH k cx) := by
  classical
  unfold polyP polyH
  rw [map_prod, ← Finset.prod_filter_of_ne (p := fun f => cx f ≠ 0)
    (fun f _ hf h0 => hf (by rw [h0, pow_zero])),
    Finset.prod_subtype (p := fun f => cx f ≠ 0) (F := inferInstance) _ (by simp)]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [MvPolynomial.aeval_rename, detPow, map_pow, AlgHom.map_det, ← Matrix.det_transpose]
  congr 2
  ext1 a b
  simp only [GlobalTheory.CombMinor.cMat, Matrix.transpose_apply, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply,
    MvPolynomial.aeval_X, Function.comp_apply, MvPolynomial.C_mul']
  rw [sum_colCoef_smul]

theorem map_polyP {k k' : Type} [Field k] [Field k'] (φ : k →+* k') {n : ℕ}
    (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) :
    MvPolynomial.map φ (polyP B cx) = polyP (fun f b j => φ (B f b j)) cx := by
  unfold polyP
  rw [map_prod]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext1 a b
  simp [GlobalTheory.CombMinor.cMat]

theorem subst_colCoef_expPt {k : Type} [Field k] {v : AddValuation k (WithTop ℝ)} {d n : ℕ} (G : LogFGL v d)
    (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) (u : Lt1 Dw → Fin d → k) (Φ : PS k n d) :
    subst (fun ℓ : LtN Dw n => ∑ lam : Let cx, colCoef B cx lam ℓ • (X lam : MvPowerSeries (Let cx) k))
      (subst (fun q : Fin n × Fin d => expPt G (fun e => ∑ ℓ : LtN Dw n,
        (if ℓ.2.2 = q.1 then u ⟨ℓ.1, ℓ.2.1⟩ e else 0) • (X ℓ : MvPowerSeries (LtN Dw n) k)) q.2) Φ) =
    subst (fun q : Fin n × Fin d => expPt G (fun e => ∑ lam : Let cx,
      (B lam.1.1.1 lam.1.2 q.1 * u ⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2⟩ e) •
        (X lam : MvPowerSeries (Let cx) k)) q.2) Φ := by
  have ht : HasSubst (fun ℓ : LtN Dw n => ∑ lam : Let cx, colCoef B cx lam ℓ •
      (X lam : MvPowerSeries (Let cx) k)) := hasSubst_of_constantCoeff_zero (by simp)
  have hw : ∀ (j : Fin n) (e : Fin d), constantCoeff (∑ ℓ : LtN Dw n,
      (if ℓ.2.2 = j then u ⟨ℓ.1, ℓ.2.1⟩ e else 0) • (X ℓ : MvPowerSeries (LtN Dw n) k)) = 0 := by
    intro j e
    rw [map_sum]
    exact Finset.sum_eq_zero fun ℓ _ => by rw [constantCoeff_smul, constantCoeff_X, smul_zero]
  have hs : HasSubst (fun q : Fin n × Fin d => expPt G (fun e => ∑ ℓ : LtN Dw n,
      (if ℓ.2.2 = q.1 then u ⟨ℓ.1, ℓ.2.1⟩ e else 0) • (X ℓ : MvPowerSeries (LtN Dw n) k)) q.2) :=
    hasSubst_of_constantCoeff_zero fun q => cc_expPt G (hw q.1) q.2
  refine (subst_comp_subst_apply hs ht Φ).trans (congrArg (fun s => subst s Φ) (funext fun q => ?_))
  refine (subst_expPt G ht (hw q.1) q.2).trans (congrArg (fun s => expPt G s q.2) (funext fun e => ?_))
  simp only [← coe_substAlgHom ht, map_sum, map_smul]
  simp only [coe_substAlgHom, subst_X ht, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have h := sum_colCoef_smul B cx lam
    (fun ℓ : LtN Dw n => if ℓ.2.2 = q.1 then u ⟨ℓ.1, ℓ.2.1⟩ e else 0)
  simp only [smul_eq_mul] at h
  rw [Finset.sum_congr rfl fun ℓ _ => mul_comm _ _, h]
  simp

end NabAux

theorem nabSt_of : InvDerSt → LinSt → FrameSt → NabSt := by
  intro hI hL hF E _ _ _ H Dw l Xo c _ T io y Ch p _ X cx n B k g
  let _ := io.toAlgebra
  let _ : Algebra T.Fr X.C := X.ιF.toAlgebra
  have hfr := (hF X.C (vX_vp X) (chD Ch.ch) T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch X) _ (gauge_chart Ch X) H.w0 n).2.1 k
  have hinv := hI X.C (vX_vp X) (chD Ch.ch) (lawX Ch X) (fgl Ch X).F_int n (LtN Dw n) (fun ℓ => ℓ.2.2)
    (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map X.ιF (polyT B cx)) (g * frameX Ch X n ^ k)
  have hP : MvPolynomial.map X.ιF (polyT B cx) = polyP (fun f b j => jX X (B f b j)) cx := map_polyP _ _ _
  unfold nabX nabValN
  rw [hfr]
  refine Eq.trans hinv ?_
  rw [hP, polyP_eq_aeval, hL]
  exact congrArg (derivAt0 (polyH X.C cx))
    (subst_colCoef_expPt (fgl Ch X) (fun f b j => jX X (B f b j)) cx (lieVec Ch X) (g * frameX Ch X n ^ k))

end GlobalTheory.IsoTriv
