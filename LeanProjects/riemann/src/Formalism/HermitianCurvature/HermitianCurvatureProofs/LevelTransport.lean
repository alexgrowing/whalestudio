import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsPlaceWithVectors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SiteTransport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm

open Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PTieB

section id

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rel_id (A : Pr V) : Rel (LinearMap.id : V →ₗ[ℂ] V) A A :=
  ⟨by rw [LinearMap.comp_id, LinearMap.id_comp], by rw [LinearMap.comp_id, LinearMap.id_comp]⟩

theorem mrel_id (M : Matrix (Fin 2) (Fin 2) (Pr V)) : MRel (LinearMap.id : V →ₗ[ℂ] V) M M := fun _ _ => rel_id _

end id

theorem pairAt_smul {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : Measure (Mt k r)) (a : ℝ≥0)
    (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    P5.pairAt (a • μ) Φ Ψ c = ((a : ℝ) : ℂ) * P5.pairAt μ Φ Ψ c := by
  unfold P5.pairAt
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem glue_zero' {r : ℕ} (c : Fin r → ℂ) (c'' : Fin (r - 0) → ℂ) :
    P5.glue (⟨0, by omega⟩ : Fin (r + 1)) c (PTie.shiftCf ⟨0, by omega⟩ c'') = c'' := by
  funext l
  simp [P5.glue, PTie.shiftCf]

theorem glue_step {r : ℕ} (j : ℕ) (hj : j + 1 ≤ r) (c : Fin r → ℂ) (c'' : Fin (r - (j + 1)) → ℂ)
    (hn : r - j = 1 + (r - (j + 1))) :
    P5.glue (⟨j, by omega⟩ : Fin (r + 1)) c
        (PTie.shiftCf ⟨j, by omega⟩ (fun l => consC (c ⟨j, by omega⟩) c'' (Fin.cast hn l))) =
      P5.glue (⟨j + 1, by omega⟩ : Fin (r + 1)) c (PTie.shiftCf ⟨j + 1, by omega⟩ c'') := by
  funext l
  unfold P5.glue PTie.shiftCf consC
  by_cases h1 : j + 1 ≤ l.val
  · rw [dif_pos (show j ≤ l.val by omega), dif_pos h1]
    simp only [Fin.val_cast]
    rw [dif_neg (by omega)]
    congr 1
  · by_cases h2 : j ≤ l.val
    · rw [dif_pos h2, dif_neg h1]
      simp only [Fin.val_cast]
      rw [dif_pos (by omega)]
      congr 1
      ext
      simp only
      omega
    · rw [dif_neg h2, dif_neg h1]

theorem castM_iota0 {k r : ℕ} (h : 0 + (r - 0) = r) (g : B.Mat k (r - 0)) :
    D.castM h (ιLev k 0 (r - 0) g) = g := by
  ext p q
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev, finCongr_symm, finCongr_apply,
    Fin.val_cast]
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

theorem step_cast {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k n ρ : ℕ} (hn : n = 1 + ρ)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn.symm (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn.symm (liftVec k 1 ρ zs'))
    (hzs : inWb k ρ zs) (hzs' : inWb k ρ zs')
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)}
    {πs : Mx k ρ → (Wp →L[ℂ] Wp)} {πs' : Mx k ρ → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn.symm (ιLev k 1 ρ y))) (hπ' : ∀ y, πs' y = π' (D.castM hn.symm (ιLev k 1 ρ y)))
    (X : ActualOps k n z z' π π') (Xs : ActualOps k ρ zs zs' πs πs')
    (L : R.LevelData (Pr (RadSp k n z z' π π')) n) (st : Fr.Start (Pr (RadSp k n z z' π π')))
    (Ls : R.LevelData (Pr (RadSp k ρ zs zs' πs πs')) ρ) (sts : Fr.Start (Pr (RadSp k ρ zs zs' πs πs')))
    (s : ℂ) (μ : Measure (Mt k n)) (μs : Measure (Mt k ρ))
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y)
    (hμ : B.IsHaarOn (Glev k n (Fin.last n)) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs)
    (hlaw : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k n z z' (Fin.last n) (Matrix.of x)) ∂μ =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k n z) (Tz k n z') ζ) * ψ ζ)
    (hlaws : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k ρ zs zs' (Fin.last ρ) (Matrix.of x)) ∂μs =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k ρ zs) (Tz k ρ zs') ζ) * ψ ζ)
    (t : ℂ) (ht : t ≠ 0) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k ρ zs zs' πs πs',
      (∀ Φ c g, (T Φ : Fn k ρ (Wq →L[ℂ] Wp)) c g =
        (Φ : Fn k n (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast hn l)) (D.castM hn.symm (ιLev k 1 ρ g))) ∧
      (∀ l : Fin ρ, Rel T (L.p ⟨l.val + 1, by omega⟩) (Ls.p l) ∧ Rel T (L.c ⟨l.val + 1, by omega⟩) (Ls.c l) ∧
        Rel T (L.ci ⟨l.val + 1, by omega⟩) (Ls.ci l)) ∧
      (∀ (m : ℕ) (hm : m ≤ ρ) (Y : ℂ),
        MRel T (P5.QQi L st ⟨m + 1, by omega⟩ Y) (P5.QQi Ls sts ⟨m, by omega⟩ Y)) ∧
      ∀ Φ Ψ c, P5.pairAt μs (T Φ) (T Ψ) c = P5.pairAt μ Φ Ψ (fun l => consC t c (Fin.cast hn l)) := by
  subst hn
  rw [P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  obtain rfl : πs = fun y => π (ιLev k 1 ρ y) := funext fun y => by rw [hπ, P.JCTx5.castM_rfl]
  obtain rfl : πs' = fun y => π' (ιLev k 1 ρ y) := funext fun y => by rw [hπ', P.JCTx5.castM_rfl]
  rw [tz_iota, tz_iota] at hlaw
  have hmap : μs.map (B2.levM k ρ) = μ := map_levM_eq hμ hμs _ (zWeight_fin _ _) hlaw hlaws
  refine ⟨trL ht zs zs' π π', fun Φ c g => ?_, fun l => site_ops ht hL hLs l,
    fun m hm Y => qqi_rel_n ht hzs hzs' hL hLs hst hsts m hm Y, fun Φ Ψ c => ?_⟩
  · rw [P.JCTx5.castM_rfl]; rfl
  · exact pairAt_tr ht hmap Φ Ψ c

end Formalism.FourierDecayAlt.P.PTieL

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
