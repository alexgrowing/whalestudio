import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.FormF
variable {n : ℕ}

lemma map_star_mul (a b : Matrix (Fin n) (Fin n) ℂ) : (a * b).map star = a.map star * b.map star := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, star_sum, star_mul']

lemma map_star_star (a : Matrix (Fin n) (Fin n) ℂ) : (a.map star).map star = a := by
  ext i j
  simp

lemma map_star_one : (1 : Matrix (Fin n) (Fin n) ℂ).map star = 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

lemma map_star_ct (a : Matrix (Fin n) (Fin n) ℂ) : (a.map star)ᴴ = aᴴ.map star := by
  ext i j
  simp

lemma Jm_star (ε : Fin n → Bool) : (Jm ε).map star = Jm ε := by
  ext i j
  simp only [Matrix.map_apply, Formalism.REAL.Jm, Matrix.diagonal_apply]
  split_ifs <;> simp

lemma UJ_star {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ UJset ε) : g.map star ∈ UJset ε := by
  have h' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := h
  show (g.map star)ᴴ * Formalism.REAL.Jm ε * g.map star = Formalism.REAL.Jm ε
  have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) h'
  simp only [map_star_mul, Jm_star] at e
  rw [map_star_ct]
  exact e

lemma K_star {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) : g.map star ∈ Kset ε := by
  have h' : g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := h
  obtain ⟨hu, hc⟩ := h'
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hu ⊢
    have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) hu
    simp only [map_star_mul, map_star_one, Matrix.star_eq_conjTranspose] at e
    rw [Matrix.star_eq_conjTranspose, map_star_ct]
    exact e
  · have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) hc
    simpa only [map_star_mul, Jm_star] using e

lemma P_star {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X) : inP ε (X.map star) := by
  have h' : (Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0) ∧ X * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := h
  obtain ⟨hg, hp⟩ := h'
  show ((X.map star)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X.map star = 0) ∧
    X.map star * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X.map star)
  refine ⟨?_, ?_⟩
  · have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) hg
    have ha : ∀ M N : Matrix (Fin n) (Fin n) ℂ, (M + N).map star = M.map star + N.map star :=
      fun M N => by
        ext i j
        simp
    have hz : (0 : Matrix (Fin n) (Fin n) ℂ).map star = 0 := by
      ext i j
      simp
    simp only [ha, hz, map_star_mul, Jm_star] at e
    rw [map_star_ct]
    exact e
  · have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) hp
    have hn : ∀ M : Matrix (Fin n) (Fin n) ℂ, (-M).map star = -(M.map star) := fun M => by
      ext i j
      simp
    simpa only [hn, map_star_mul, Jm_star] using e

lemma exp_star (X : Matrix (Fin n) (Fin n) ℂ) :
    (NormedSpace.exp X).map star = NormedSpace.exp (X.map star) := by
  have e : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map star = Mᴴᵀ := fun M => by
    ext i j
    simp
  rw [e (NormedSpace.exp X), e X, Matrix.exp_transpose, Matrix.exp_conjTranspose]

lemma Phi_star (lam : Fin n → ℝ) (z : Matrix (Fin n) (Fin n) ℂ) : Phi lam (z.map star) = star (Phi lam z) := by
  have e : ∀ (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ), (M.map star).det = star M.det := by
    intro N M
    rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose Mᴴ]
    congr 1
  simp only [GlobalTheory.Dec.Phi, star_prod, star_zpow₀]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  congr 1
  simp only [Formalism.MainNotions.S.leadMinor]
  rw [← e]
  rfl

lemma K_UJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) : g ∈ UJset ε := by
  have h' : g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := h
  obtain ⟨hu, hc⟩ := h'
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.mp hu, Matrix.one_mul]

lemma one_K (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε := by
  refine ⟨one_mem _, ?_⟩
  rw [Matrix.one_mul, Matrix.mul_one]

lemma K_inv {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) : g⁻¹ = gᴴ := by
  have h' : g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := h
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp h'.1

lemma K_KC {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) : g ∈ KC ε := by
  have h' : g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := h
  exact ⟨⟨⟨g, star g, Matrix.mem_unitaryGroup_iff.mp h'.1, Matrix.mem_unitaryGroup_iff'.mp h'.1⟩, rfl⟩, h'.2⟩

lemma exp_posDef {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X) : (NormedSpace.exp X).PosDef := by
  have h' : (Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0) ∧ X * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := h
  obtain ⟨hg, hp⟩ := h'
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have h1 : Xᴴ * Formalism.REAL.Jm ε = X * Formalism.REAL.Jm ε := by
    rw [hp]
    exact eq_neg_of_add_eq_zero_left hg
  have hH : Xᴴ = X := by
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = X * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [h1]
      _ = X := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hYH : ((2⁻¹ : ℝ) • X)ᴴ = (2⁻¹ : ℝ) • X := by
    rw [Matrix.conjTranspose_smul, hH, star_trivial]
  have hYY : (2⁻¹ : ℝ) • X + (2⁻¹ : ℝ) • X = X := by
    rw [← add_smul]
    norm_num
  rw [← hYY, Formalism.REAL.exp_add_self]
  have hE := Formalism.REAL.exp_conjTranspose_of_hermitian hYH
  have hsq : NormedSpace.exp ((2⁻¹ : ℝ) • X) * NormedSpace.exp ((2⁻¹ : ℝ) • X) =
      (NormedSpace.exp ((2⁻¹ : ℝ) • X))ᴴ * NormedSpace.exp ((2⁻¹ : ℝ) • X) := by
    rw [hE]
  rw [hsq]
  apply Matrix.PosDef.conjTranspose_mul_self
  intro u v huv
  have e := congrArg (NormedSpace.exp (-((2⁻¹ : ℝ) • X))).mulVec huv
  simpa only [Matrix.mulVec_mulVec, Formalism.REAL.matrix_exp_neg_mul_exp, Matrix.one_mulVec] using e

lemma URep_K {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsURepOn (UJset ε) σ) : IsURepOn (Kset ε) σ := by
  obtain ⟨⟨h1, hm⟩, hi, hc⟩ := h
  exact ⟨⟨h1, fun a ha b hb => hm a (K_UJ ha) b (K_UJ hb)⟩, fun g hg v => hi g (K_UJ hg) v,
    fun v => (hc v).mono (fun g hg => K_UJ hg)⟩

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
lemma smooth_cont {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : SmoothOnG ε f) :
    ContinuousOn f (UJset ε) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := h g₀ hg₀
  have hFc : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hgU)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfF g₀ hgU hg₀)
  filter_upwards [inter_mem_nhdsWithin (UJset ε) (hU.mem_nhds hgU)] with g hg
  exact hfF g hg.2 hg.1

end GlobalTheory.Dec.FormF
