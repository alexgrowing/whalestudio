import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegBound

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.FrameInd

def Vc (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.of fun l i => gramVec k r z z' g i l

lemma herm_mulVec_mulVec {ι κ : Type*} [Fintype ι] [Fintype κ] (H : Matrix ι ι ℂ) (A : Matrix ι κ ℂ)
    (v w : κ → ℂ) : herm H (A *ᵥ v) (A *ᵥ w) = herm (Aᴴ * H * A) v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma gramM_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    gramM k r z z' g = (Vc k r z z' g)ᴴ * Hpk k r * Vc k r z z' g := by
  ext i j
  simp only [gramM, herm, Vc, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma Uperp_mat (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    Uperp k r z z' g = LinearMap.ker (Matrix.mulVecLin ((Vc k r z z' g)ᴴ * Hpk k r)) := rfl

lemma gramM_herm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    (gramM k r z z' g)ᴴ = gramM k r z z' g := by
  rw [gramM_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Formalism.QuantumDeterminants.GBasic.Hpk_herm, Matrix.mul_assoc]

lemma herm_Vc (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (c d : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    herm (Hpk k r) (Vc k r z z' g *ᵥ c) (Vc k r z z' g *ᵥ d) = herm (gramM k r z z' g) c d := by
  rw [herm_mulVec_mulVec, ← gramM_eq]

lemma Vc_mulVec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    Vc k r z z' g *ᵥ c = ∑ i, c i • gramVec k r z z' g i := by
  ext l
  simp [Vc, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

lemma Vc_inj (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hdet : (gramM k r z z' g).det ≠ 0) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ)
    (hc : Vc k r z z' g *ᵥ c = 0) : c = 0 := by
  have h1 : gramM k r z z' g *ᵥ c = 0 := by
    funext j
    have h2 := herm_Vc k r z z' g c (Pi.single j 1)
    rw [hc] at h2
    simp only [herm, Matrix.mulVec_zero, dotProduct_zero] at h2
    rw [Pi.zero_apply]
    have h3 : star (Pi.single j (1 : ℂ)) ⬝ᵥ (gramM k r z z' g *ᵥ c) = (gramM k r z z' g *ᵥ c) j := by
      simp [dotProduct, Pi.single_apply]
    rw [← h3, ← h2]
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1

theorem indep_of_det (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hdet : (gramM k r z z' g).det ≠ 0) : LinearIndependent ℂ (gramVec k r z z' g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h1 : Vc k r z z' g *ᵥ c = 0 := by rw [Vc_mulVec]; exact hc
  exact congrFun (Vc_inj k r z z' g hdet c h1) i

theorem finrank_Uperp_of_det (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hdet : (gramM k r z z' g).det ≠ 0) :
    Module.finrank ℂ (Uperp k r z z' g) = k - 1 := by
  obtain ⟨R, hR⟩ : ∃ R, R = (Vc k r z z' g)ᴴ * Hpk k r := ⟨_, rfl⟩
  have hRV : R * Vc k r z z' g = gramM k r z z' g := by rw [hR, gramM_eq]
  have hrk1 : (gramM k r z z' g).rank = 2 * r + 2 := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))]
    simp; ring
  have hrk2 : (gramM k r z z' g).rank ≤ R.rank := by rw [← hRV]; exact Matrix.rank_mul_le_left _ _
  have hrk3 : R.rank ≤ 2 * r + 2 := by
    have := Matrix.rank_le_card_height R
    simp at this; omega
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin R)
  have hrank : R.rank = Module.finrank ℂ (LinearMap.range (Matrix.mulVecLin R)) := rfl
  rw [Uperp_mat, ← hR]
  simp only [Module.finrank_fin_fun] at hrn
  omega

theorem det_ne (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hs : Std k r z z')
    (hp : PosPt k r z z' γ) : (gramM k r z z' γ).det ≠ 0 := by
  intro h0
  have h := Formalism.QuantumDeterminants.group_gram_holds k r z z' hs.2.1.1 hs.2.2.1 γ hp.1
  rw [h0, mul_zero] at h
  have : Gf k r z z' γ = 0 := by exact_mod_cast h
  linarith [hp.2]

end PI.FrameInd
