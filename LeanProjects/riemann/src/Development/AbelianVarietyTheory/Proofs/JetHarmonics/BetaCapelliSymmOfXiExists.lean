import Mathlib
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnergyReal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.XiExistsOfBesselXiIntegrable

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory.BetaSym

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity MeasureTheory
open scoped ContDiff ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem clause_bdd (D : RealPlaceData k r Wp Wq) {A : ℝ} (hA : 0 ≤ A) (hCC : CCIntegrable D A)
    (Θ : DiffOp k r Wp Wq) (hS : SmoothCoef (GV k r) Θ)
    (hP : ∀ T ∈ Θ, ∃ C : ℝ, ∀ (u v : List (Mat k r)) (g : Mat k r),
      ‖dLR u v T.coef g‖ ≤ C ∧ ‖dLR u v T.coefAdj g‖ ≤ C)
    (F F' : Mat k r → (Wq →L[ℂ] Wp)) (hF0 : InCC A (opOrder Θ + 5) F) (hF0' : InCC A (opOrder Θ + 5) F') :
    InCC A 5 (opApply Θ F) ∧ InCC A 5 (opAdj Θ F') ∧ IntClause D Θ F F' := by
  have hF : InCC (A + 0) (opOrder Θ + 5) F := by rwa [add_zero]
  have hF' : InCC (A + 0) (opOrder Θ + 5) F' := by rwa [add_zero]
  have hO : IsOpen (∅ : Set (Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ GV k r, g ∈ (∅ : Set (Mat k r)) ∨ g ∈ GV k r := fun g hg => Or.inr hg
  have hAd0 : 0 ≤ A + 0 := by linarith
  have hadj : ∀ T ∈ Θ, InCC A (opOrder Θ + 5) (ap T.coefAdj F') := by
    intro T hT
    obtain ⟨C, hC⟩ := hP T hT
    obtain ⟨c', hc'⟩ := hF'
    exact ⟨_, prodBound (C := C) hO hcov (sCkOn_mono le_top (hS T hT).2)
      (fun u v _ _ _ g _ _ => by rw [Real.rpow_zero, mul_one]; exact (hC u v g).2) hc'
      (fun g _ h => absurd h (Set.notMem_empty g))⟩
  refine ⟨?_, ?_, ?_⟩
  · refine InCC_opsum Θ (fun T => ap T.coef (Rw T.word F)) ?_
    intro T hT
    have hlen := word_le_order Θ hT
    obtain ⟨C, hC⟩ := hP T hT
    obtain ⟨c, hc⟩ : InCC (A + 0) 5 (Rw T.word F) :=
      InCC_Rw T.word_lie (sInCC_mono le_rfl (by omega) hF)
    exact ⟨_, prodBound (C := C) hO hcov (sCkOn_mono le_top (hS T hT).1)
      (fun u v _ _ _ g _ _ => by rw [Real.rpow_zero, mul_one]; exact (hC u v g).1) hc
      (fun g _ h => absurd h (Set.notMem_empty g))⟩
  · refine InCC_opsum Θ
      (fun T => fun g => ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (ap T.coefAdj F') g) ?_
    intro T hT
    have hlen := word_le_order Θ hT
    obtain ⟨c, hc⟩ : InCC A 5 (Rw T.word.reverse (ap T.coefAdj F')) :=
      InCC_Rw (fun X hX => T.word_lie X (List.mem_reverse.mp hX))
        (sInCC_mono le_rfl (by simp; omega) (hadj T hT))
    exact ⟨_, CCle_smul _ hc⟩
  · intro p hp T hT i j hij hj
    have hlen := word_le_order Θ hT
    set a : Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with hadef
    set b : Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hbdef
    have ha : a ∈ GV k r := gv_mul (gv_inv hp.1.1) (gv_inv hp.2.1.1)
    have hb : b ∈ GV k r := gv_mul hp.2.2.2.1 hp.2.2.1.1
    have hlie1 : ∀ X ∈ (T.word.take i).reverse, inLie k r X := fun X hX =>
      T.word_lie X (List.mem_of_mem_take (List.mem_reverse.mp hX))
    have hlie2 : ∀ X ∈ T.word.drop j, inLie k r X := fun X hX => T.word_lie X (List.mem_of_mem_drop hX)
    have hl1 : (T.word.take i).reverse.length ≤ opOrder Θ := by
      simp only [List.length_reverse, List.length_take]; omega
    have hl2 : (T.word.drop j).length ≤ opOrder Θ := by
      simp only [List.length_drop]; omega
    obtain ⟨K₁, hK₁⟩ : InCC A 0 (Rw (T.word.take i).reverse (ap T.coefAdj F')) :=
      InCC_Rw hlie1 (sInCC_mono le_rfl (by omega) (hadj T hT))
    obtain ⟨K₂, hK₂⟩ : InCC (A + 0) 0 (Rw ((T.word.drop j).map fun X => b⁻¹ * X * b) F) :=
      InCC_Rw (fun X hX => by
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
        exact lie_conj (hlie2 Y hY) hb) (sInCC_mono le_rfl (by simp only [List.length_map]; omega) hF)
    obtain ⟨cF, hcF⟩ := hF
    have hFk : CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) F := hcF.1
    set f₁ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.take i).reverse (ap T.coefAdj F') with hf₁
    set f₂ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.drop j) (rho D p F) with hf₂
    have hc₁ : ContinuousOn f₁ (GV k r) := CkOn_cont subset_rfl hK₁.1
    have hc₂ : ContinuousOn f₂ (GV k r) := by
      apply CkOn_cont subset_rfl
      rw [hf₂, ← Dw_wR, rho_eq_trn]
      apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) hlie2 x (by simpa [wL] using hx))
      apply CkOn_trn _ ha hb
      refine sCkOn_mono ?_ hFk
      simp only [wR, List.length_map, zero_add]
      exact_mod_cast (by omega : (T.word.drop j).length ≤ opOrder Θ + 5)
    have hb₂ : ∀ g ∈ GV k r, ‖f₂ g‖ ≤ ‖Lp D p‖ * K₂ := by
      intro g hg
      rw [hf₂, rho_eq_trn, Rw_trn _ ha hb _ hlie2
        (sCkOn_mono (by exact_mod_cast (by omega : (T.word.drop j).length ≤ opOrder Θ + 5)) hFk) g hg]
      exact ((Lp D p).le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (CC_bdd hAd0 hK₂ _ (gv_mul (gv_mul ha hg) hb)) (norm_nonneg _))
    set G : Mat k r → (Wq →L[ℂ] Wp) := fun g => ((‖f₂ g‖ : ℝ) : ℂ) • f₁ g with hG
    have hGn : ∀ g, ‖G g‖ = ‖f₁ g‖ * ‖f₂ g‖ := by
      intro g
      simp only [hG, norm_smul, Complex.norm_real, norm_norm]
      ring
    have hGc : ContinuousOn G (GV k r) := (Complex.continuous_ofReal.comp_continuousOn hc₂.norm).smul hc₁
    have hGm := aesm_of_continuousOn D hGc
    have hfin := hCC G (‖Lp D p‖ * K₂ * K₁) hGm (by
      intro g hg
      have h1 : gN g ^ A * ‖f₁ g‖ ≤ K₁ := hK₁.2 [] [] (by simp) (by simp) (by simp) g hg
      have h0 : 0 ≤ gN g ^ A * ‖f₁ g‖ := mul_nonneg (Real.rpow_nonneg (gN_pos hg).le _) (norm_nonneg _)
      calc gN g ^ A * ‖G g‖ = ‖f₂ g‖ * (gN g ^ A * ‖f₁ g‖) := by rw [hGn]; ring
        _ ≤ ‖Lp D p‖ * K₂ * K₁ := mul_le_mul (hb₂ g hg) h1 h0 ((norm_nonneg _).trans (hb₂ g hg)))
    have hint : Integrable (fun g : Mt k r => G (Matrix.of g)) D.μG := ⟨hGm, hfin⟩
    refine hint.norm.congr (Filter.Eventually.of_forall fun g => ?_)
    exact hGn _

theorem gv_stable (D : RealPlaceData k r Wp Wq) : IsStableOpen D (GV k r) :=
  ⟨⟨Set.univ, isOpen_univ, (Set.univ_inter _).symm⟩,
    fun _ hs _ hs' _ hg => gv_mul (gv_mul (Sset_sub hs) hg) (Sset_sub hs')⟩

theorem suppIn_gv (F : Mat k r → (Wq →L[ℂ] Wp)) : SuppIn (GV k r) F :=
  closure_minimal (fun _ hg => hg.1) gv_closed

end GlobalTheory.BetaSym

namespace GlobalTheory

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP.ER BetaSym
open scoped ComplexConjugate

theorem beta_capelli_symm_of_xiExists (hXi : B.XiExists) : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y A : ℝ) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → (B.CkOn ⊤ (B.GV k r) (F) ∧ ∀ m : ℕ, B.InCC (A) m (F)) → (B.CkOn ⊤ (B.GV k r) (F') ∧ ∀ m : ℕ, B.InCC (A) m (F')) → B.beta D (Q.CV k r (Y : ℂ) F) F' = B.beta D F (Q.CV k r (Y : ℂ) F') := by
  intro k r Wp Wq _ _ _ _ _ _ D Y A F F' hAB hF hF'
  have hA : 0 ≤ A := le_trans (by unfold B.AB; positivity) hAB
  have hAdj : CapAdj := capAdj_of_int (capAdjInt_of_scalar capacity_adjoint_scalar)
  set Θ := capTh k r Wp Wq 1 (Y : ℂ) with hΘ
  obtain ⟨hord, -, -, -, hApp⟩ := capacity_theta_facts k r Wp Wq D 1 (Y : ℂ) 1 0
  obtain ⟨_, _, _, _, _, h3, _⟩ := BXiAsm.any_of hXi k r Wp Wq D A hAB
  have hS : B.SmoothCoef (B.GV k r) Θ := by
    intro T hT
    obtain ⟨c, w, rfl⟩ := mem_capOp 1 _ hT
    exact ⟨ckOn_const' _, ckOn_const' _⟩
  have hCo : B.Commutes D (B.GV k r) Θ := by
    intro p hp f hf g hgG
    rw [hΘ, hord] at hf
    have hs' := B7.sgs_mem D hp hgG
    rw [hApp _ (B5.ckOn_rho D hp hf) g hgG, capelli_rho_commute k r Wp Wq D (Y : ℂ) f p hp hf g hgG]
    simp only [B.rho]
    rw [hApp f hf _ hs', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  have hP : ∀ T ∈ Θ, ∃ C : ℝ, ∀ (u v : List (B.Mat k r)) (g : B.Mat k r),
      ‖B.dLR u v T.coef g‖ ≤ C ∧ ‖B.dLR u v T.coefAdj g‖ ≤ C := by
    intro T hT
    obtain ⟨c, w, rfl⟩ := mem_capOp 1 _ hT
    refine ⟨‖c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖ + ‖conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖,
      fun u v g => ?_⟩
    have h1 := norm_dLR_const_le (c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) u v g
    have h2 := norm_dLR_const_le (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) u v g
    have n1 := norm_nonneg (c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    have n2 := norm_nonneg (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    exact ⟨by simp only [TLB.cTerm]; linarith, by simp only [TLB.cTerm]; linarith⟩
  obtain ⟨c1, c2, c3⟩ := clause_bdd D hA (matrix_coefficient_integrable_all k r Wp Wq D A hAB) Θ hS hP F F' (hF.2 _) (hF'.2 _)
  have h1 := h3 (B.GV k r) Θ (gv_stable D) hS hCo F F' (B5.ckOn_mono le_top hF.1) (B5.ckOn_mono le_top hF'.1)
    (suppIn_gv F) (suppIn_gv F') (hF.2 _) (hF'.2 _) c1 c2 c3
  have h0 : B.beta D (Q.CV k r (Y : ℂ) F) F' = B.beta D (B.opApply Θ F) F' :=
    beta_form_congr_holds k r Wp Wq D _ _ _ _
      (fun g hg => by rw [hApp F (B5.ckOn_mono le_top hF.1) g hg, one_smul]) (fun _ _ => rfl)
  have h2 : B.beta D F (B.opAdj Θ F') = B.beta D F (Q.CV k r (Y : ℂ) F') :=
    beta_form_congr_holds k r Wp Wq D _ _ _ _ (fun _ _ => rfl) (fun g hg => by
      rw [hΘ, hAdj k r Wp Wq 1 (Y : ℂ) F' hF'.1 g hg, map_one, Complex.conj_ofReal, one_smul])
  rw [h0, h1, h2]

theorem beta_capelli_symm_of_bessel : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y A : ℝ) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → (B.CkOn ⊤ (B.GV k r) (F) ∧ ∀ m : ℕ, B.InCC (A) m (F)) → (B.CkOn ⊤ (B.GV k r) (F') ∧ ∀ m : ℕ, B.InCC (A) m (F')) → B.beta D (Q.CV k r (Y : ℂ) F) F' = B.beta D F (Q.CV k r (Y : ℂ) F') :=
  fun h => beta_capelli_symm_of_xiExists (GlobalTheory.HCXi.xiExists_of_besselXiIntegrable h)

end GlobalTheory
