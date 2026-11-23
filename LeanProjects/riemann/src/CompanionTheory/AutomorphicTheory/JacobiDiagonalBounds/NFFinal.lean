import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.NFModel
import CompanionTheory.AutomorphicTheory.NumberFieldModels.ModelPt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatrixUnitZeroZeroEqInsert
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatBdd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFModelNFg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

noncomputable section

theorem model_adm {P : M.Par} (hP : P.OK) {l0 : ℕ} (h1 : 1 ≤ l0) (h2 : l0 ≤ P.k) {w : List C.Letter}
    (hw : KB.CutWord P l0 w) : admitted (MA.startM P (MA.DQ P) l0) (D.positionted w) :=
  (Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (Wp := ℂ) (Wq := ℂ) P 0 0 0 0
    ⟨0, M.qC P, 0, 0, 0, {Y | ∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0}⟩ l0 hP h1 h2 rfl rfl w hw.1 hw.2).1

theorem model_nf {P : M.Par} {L : LevelData (MA.A P (MA.DQ P)) P.r} (hP : P.OK) (hM : MA.IsModelLevel P (MA.DQ P) L)
    {l0 : ℕ} (h1 : 1 ≤ l0) (h2 : l0 ≤ P.k) {w : List C.Letter} (hw : KB.CutWord P l0 w) (a : Ix (Fin w.length)) :
    (∀ b ∈ BB P L, ∀ f ∈ L.fns, Commute b f) ∧
      gM P l0 L (D.positionted w) a ∈ NFs L (BB P L) (L.Di ^ w.length) w.length := by
  have hTT : 0 ≤ P.TT := (mul_pos hP.T_pos hP.T'_pos).le
  have hLaw := analytic_laws P.r P.TT hTT
  have hS := level_star_holds P _ hLaw L hM
  have hst := start_admissible P hP _ hLaw l0 L hM
  have H := model_hyp hat_bounded_decay_holds hTT hM hS l0
  refine ⟨H.fn, ?_⟩
  have := word_nf word_recursion H (model_aHyp hM hS hst (sites_admissible P _ hLaw l0)) (D.positionted w)
    (model_adm hP h1 h2 hw) a
  rw [gM_eq hM]
  simpa only [D.positionted, List.length_ofFn] using this

theorem nfModelNFg_ok (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hP : P.OK)
    (hM : MA.IsModelLevel P (MA.DQ P) L) (l0 : ℕ) (h1 : 1 ≤ l0) (h2 : l0 ≤ P.k) (Y : Finset ℝ) (w : List C.Letter)
    (hw : TBB.AdmW P l0 Y w) (e : Wd.Ix (Fin w.length)) :
    ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (i i' : Fin m → ℕ) (h : Fin m → List (MA.A P (MA.DQ P))),
      (∀ j, b j ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ j, i j + i' j = w.length) ∧
      (∀ j, (h j).length = w.length ∧ ∀ a ∈ h j, a ∈ MA.hatSet P L) ∧
      ∑ e' : Wd.Ix (Fin w.length),
          (Fr.ofWord L (MA.startM P (MA.DQ P) l0) (D.positionted w)).F e e' *
            Wd.uw (MA.sites P (MA.DQ P)) (D.positionted w) e' =
        ∑ j, b j * L.Di ^ i j * L.Dbi ^ i' j * (h j).prod := by
  obtain ⟨m, b, u, hb, hu, e1⟩ := nfs_fin (model_nf hP hM h1 h2 hw.1 e).2
  exact ⟨m, b, fun _ => w.length, fun _ => 0, u, hb, fun _ => rfl, hu, by
    simp only [pow_zero, mul_one]; exact e1⟩

theorem model_pt {P : M.Par} {L : LevelData (MA.A P (MA.DQ P)) P.r} (hP : P.OK) (hM : MA.IsModelLevel P (MA.DQ P) L)
    {l0 : ℕ} (h1 : 1 ≤ l0) (h2 : l0 ≤ P.k) {w : List C.Letter} (hw : KB.CutWord P l0 w) (a : Ix (Fin w.length))
    (s : ℕ) :
    ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (u : Fin m → List (MA.A P (MA.DQ P))),
      (∀ j, b j ∈ Submonoid.closure (MA.bddSet P L)) ∧
      (∀ j, (u j).length = w.length ∧ ∀ x ∈ u j, x ∈ MA.hatSet P L) ∧
      ∀ f g : M.Ty P → MA.SmQ P.r P.TT,
        (∀ ρ q, MA.evQ P (g ρ) q = ((MA.Gq P q ^ s : ℝ) : ℂ) * MA.evQ P (f ρ) q) → ∀ (q : MA.Qp P.r P.TT) ρ,
        MA.evQ P (MA.actA P (gM P l0 L (D.positionted w) a) g ρ) q =
          ((MA.Gq P q ^ s : ℝ) : ℂ) * ((∏ l, q.1.1 l) * q.1.2)⁻¹ ^ w.length *
            ∑ j, MA.evQ P (MA.actA P (b j * (u j).prod) f ρ) q :=
  nf_pointwise (mul_pos hP.T_pos hP.T'_pos).le hM (model_nf hP hM h1 h2 hw a).1 (model_nf hP hM h1 h2 hw a).2 s

theorem normal_form_model_point : Formalism.MainStatements.NFTie.NFModelPt := by
  intro P L hP hM l0 h1 h2 w hw a s
  obtain ⟨m, b, u, hb, hu, h⟩ := model_pt hP hM h1 h2 hw a s
  refine ⟨m, b, u, m, Nat.cast_nonneg _, hb, hu, fun f g hg q => ?_⟩
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ _ => ?_
  have hG := (MA.Gq_pos P q).le
  have c1 : ‖∑ j, MA.evQ P (MA.actA P (b j * (u j).prod) f ρ) q‖ ^ 2 ≤
      (m : ℝ) * ∑ j, ‖MA.evQ P (MA.actA P (b j * (u j).prod) f ρ) q‖ ^ 2 := by
    refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2) ?_
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m)))
      (f := fun j => ‖MA.evQ P (MA.actA P (b j * (u j).prod) f ρ) q‖)
  rw [h f g hg q ρ, norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hG s),
    norm_pow, norm_inv, Complex.normSq_eq_norm_sq, ← pow_mul, ← pow_mul, mul_comm s 2, mul_comm w.length 2, pow_mul _ 2 w.length,
    inv_pow _ 2]
  calc _ ≤ MA.Gq P q ^ (2 * s) * (‖(∏ l, q.1.1 l) * q.1.2‖ ^ 2)⁻¹ ^ w.length *
        ((m : ℝ) * ∑ j, ‖MA.evQ P (MA.actA P (b j * (u j).prod) f ρ) q‖ ^ 2) :=
        mul_le_mul_of_nonneg_left c1 (by positivity)
    _ = _ := by ring

end

end Formalism.FourierDecayAlt.P.NormalFormRelations
