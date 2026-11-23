import Formalism.HermitianCurvature.HermitianCurvatureProofs.EHcChange
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem lie_sub {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X - Y) := by
  unfold inLie at *
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, sub_add_sub_comm, hX, hY, sub_zero]

theorem lie_add {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X + Y) := by
  unfold inLie at *
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]

theorem EHH {φ F : Mat k r → E} {U : Set (Mat k r)} {g : Mat k r} (hφ : CkOn 2 (GV k r) φ) (hU : IsOpen U)
    (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : ContDiffOn ℝ 2 F U) (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h)
    (a b c d : Fin (2 * r + k + 1)) :
    Q.EH k r a b (Q.EH k r c d φ) g =
      (fderiv ℝ F g (g * Xa k r a b * Xa k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xa k r a b) (g * Xa k r c d)) +
        Complex.I • (fderiv ℝ F g (g * Xa k r a b * Xb k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xa k r a b) (g * Xb k r c d)) +
      Complex.I • ((fderiv ℝ F g (g * Xb k r a b * Xa k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xb k r a b) (g * Xa k r c d)) +
        Complex.I • (fderiv ℝ F g (g * Xb k r a b * Xb k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xb k r a b) (g * Xb k r c d))) := by
  have hc : ContDiffOn ℝ (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) F U := by simpa using hF
  have hφ2 : CkOn ((1 : ℕ∞) + 1) (GV k r) φ := by
    have e : ((1 : ℕ∞) + 1) = 2 := by norm_num
    rw [e]; exact hφ
  have hφ1 : ∀ X : Mat k r, inLie k r X → CkOn 1 (GV k r) (Dx (false, X) φ) :=
    fun X hX => CkOn_Dx (x := (false, X)) hX hφ2
  have hop : ∀ X Y : Mat k r, inLie k r X → inLie k r Y →
      Dx (false, X) (Dx (false, Y) φ) g =
        fderiv ℝ (fderiv ℝ F) g (g * X) (g * Y) + fderiv ℝ F g (g * X * Y) :=
    fun X Y hX hY => Formalism.FourierDecayAlt.P.B4.op_op_ext false false hU hc hff hX hY hgU hg
  have hEcd : Q.EH k r c d φ = fun h => Dx (false, Xa k r c d) φ h + Complex.I • Dx (false, Xb k r c d) φ h :=
    EH_eq c d φ
  rw [EH_eq a b, hEcd]
  simp only
  rw [Dx_add (x := (false, Xa k r a b)) (Xa_lie a b) (hφ1 _ (Xa_lie c d)) (CkOn_smul _ (hφ1 _ (Xb_lie c d))) g hg,
    Dx_add (x := (false, Xb k r a b)) (Xb_lie a b) (hφ1 _ (Xa_lie c d)) (CkOn_smul _ (hφ1 _ (Xb_lie c d))) g hg,
    Dx_smul, Dx_smul]
  simp only
  rw [hop _ _ (Xa_lie a b) (Xa_lie c d), hop _ _ (Xa_lie a b) (Xb_lie c d), hop _ _ (Xb_lie a b) (Xa_lie c d),
    hop _ _ (Xb_lie a b) (Xb_lie c d)]
  simp only [smul_add]
  abel

theorem single_comm (a b c d : Fin (2 * r + k + 1)) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      ((if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) : Mat k r) := by
  split_ifs with h1 h2 h2
  all_goals
    first
    | (try subst h1); (try subst h2)
      simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, *]
    | ext i j
      simp_all [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, ite_mul, Finset.sum_ite_eq,
        Finset.sum_ite_eq']

theorem EH_HGl : HGl (Q.EH (E := E) k r) := by
  intro a b c d φ hφ g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := hφ g hg
  have hF2 : ContDiffOn ℝ 2 F U := by exact_mod_cast hF
  have hF' : HasFDerivAt F (fderiv ℝ F g) g :=
    ((hF2.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hgU)).hasFDerivAt
  have hsym : ∀ v w : Mat k r, fderiv ℝ (fderiv ℝ F) g v w = fderiv ℝ (fderiv ℝ F) g w v := by
    have hc : ContDiffOn ℝ (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) F U := by simpa using hF2
    have := (hc.contDiffAt (hU.mem_nhds hgU)).isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
    intro v w; exact this v w
  set A1 := Xa k r a b with hA1
  set A2 := Xb k r a b with hA2
  set C1 := Xa k r c d with hC1
  set C2 := Xb k r c d with hC2
  set D1 := fderiv ℝ F g with hD1
  set D2 := fderiv ℝ (fderiv ℝ F) g with hD2
  have hR : (if b = c then Q.EH k r a d φ g else 0) - (if d = a then Q.EH k r c b φ g else 0) =
      Psi D1 g (Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1) := by
    rw [single_comm, Psi_sub]
    congr 1
    · split_ifs
      · exact EH_psi hU hgU hg hF' hff a d
      · exact (Psi_zero D1 g).symm
    · split_ifs
      · exact EH_psi hU hgU hg hF' hff c b
      · exact (Psi_zero D1 g).symm
  have e1 : A1 + Complex.I • A2 = Matrix.single a b 1 := hp_decomp _
  have e2 : C1 + Complex.I • C2 = Matrix.single c d 1 := hp_decomp _
  have hbr : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      ((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2)) + Complex.I • ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2)) := by
    rw [← e1, ← e2]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (norm := module) hI • (A2 * C2 - C2 * A2)
  have hl1 : inLie k r ((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2)) :=
    lie_sub (lie_bracket (Xa_lie a b) (Xa_lie c d)) (lie_bracket (Xb_lie a b) (Xb_lie c d))
  have hl2 : inLie k r ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2)) :=
    lie_add (lie_bracket (Xa_lie a b) (Xb_lie c d)) (lie_bracket (Xb_lie a b) (Xa_lie c d))
  have hP : Psi D1 g (((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2)) + Complex.I • ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2))) =
      D1 (g * ((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2))) + Complex.I • D1 (g * ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2))) := by
    unfold Psi
    rw [(hp_of_parts hl1 hl2).1, (hp_of_parts hl1 hl2).2]
  rw [hR, hbr, hP, EHH hφ hU hgU hg hF2 hff a b c d, EHH hφ hU hgU hg hF2 hff c d a b]
  rw [← hA1, ← hA2, ← hC1, ← hC2, ← hD1, ← hD2]
  rw [hsym (g * C1) (g * A1), hsym (g * C2) (g * A1), hsym (g * C1) (g * A2), hsym (g * C2) (g * A2)]
  simp only [Matrix.mul_sub, Matrix.mul_add, map_sub, map_add, ← Matrix.mul_assoc]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (norm := module) hI • (D1 (g * A2 * C2) - D1 (g * C2 * A2))

theorem capAdInv : CapAdInv := by
  intro k r E _ _ y u f hy hf h hh
  have hyu := gv_unit hy
  have hQP : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv _ hyu
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  set e : Fin (Q.mdim k r 0) ≃ Fin (2 * r + k + 1) := finCongr hm with he
  have hpos : Q.posL k r 0 = ⇑e := by
    funext j; apply Fin.ext; simp [Q.posL, he]
  rw [hpos]
  exact ad_main (Q.EH k r) EH_HC EH_HL EH_HA EH_HS EH_HGl (EHc k r y) (EHc_HL hy) hQP
    (fun c d φ hφ g hg => EHc_change hy c d φ hφ g hg) e u f (by rw [hm]; exact hf) h hh

theorem cVRight : JF.CVRight := cvRight_of capAdInv

theorem cVRho : JF.CVRho := cvRho_of capAdInv

end Formalism.FourierDecayAlt.P.JFxE
