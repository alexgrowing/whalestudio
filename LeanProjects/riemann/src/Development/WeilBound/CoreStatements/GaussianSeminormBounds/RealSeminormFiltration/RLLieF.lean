import Mathlib
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieB
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieC

noncomputable section

open Complex Matrix Filter Topology
open scoped Real RealInnerProductSpace

namespace PositivityTheory.RL.Up

open GlobalTheory.RealWeil

theorem lie_of_exp_banach {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸]
    [StarModule ℝ 𝔸] (Z K : 𝔸) (h : ∀ t : ℝ, star (NormedSpace.exp (t • Z)) * K * NormedSpace.exp (t • Z) = K) :
    star Z * K + K * Z = 0 := by
  have hE := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0
  have hP := (hE.star.mul (hasDerivAt_const (0 : ℝ) K)).mul hE
  have hf : ((fun u : ℝ => star (NormedSpace.exp (u • Z))) * (fun _ : ℝ => K)) *
      (fun u : ℝ => NormedSpace.exp (u • Z)) = fun _ => K := by
    funext u
    simp only [Pi.mul_apply]
    exact h u
  rw [hf] at hP
  have e := hP.unique (hasDerivAt_const (0 : ℝ) K)
  simpa [NormedSpace.exp_zero] using e

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem lie_of_exp {𝕜 ι : Type} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] (Z K : Matrix ι ι 𝕜)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Z))ᴴ * K * NormedSpace.exp (t • Z) = K) : Zᴴ * K + K * Z = 0 := by
  exact @lie_of_exp_banach (Matrix ι ι 𝕜) _ _ _ _ ⟨continuous_id.matrix_conjTranspose⟩ _ Z K h

variable {l : Type} [Fintype l] [DecidableEq l]

theorem sympl_eq (w w' : l ⊕ l → ℝ) : sympl w w' = -(w ⬝ᵥ Matrix.J l ℝ *ᵥ w') := by
  simp [sympl, pPart, qPart, dotProduct, Fintype.sum_sum_type, Matrix.J, Matrix.fromBlocks_mulVec,
    PiLp.inner_apply, Finset.sum_sub_distrib, Matrix.neg_mulVec, Matrix.one_mulVec, Finset.sum_neg_distrib]
  simp only [mul_comm]
  ring

theorem mem_sp_of (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) (h : ∀ w w', sympl (A *ᵥ w) (A *ᵥ w') = sympl w w') :
    A ∈ Matrix.symplecticGroup l ℝ := by
  have key : ∀ v u : l ⊕ l → ℝ, (A *ᵥ v) ⬝ᵥ Matrix.J l ℝ *ᵥ (A *ᵥ u) = v ⬝ᵥ (Aᵀ * Matrix.J l ℝ * A) *ᵥ u := by
    intro v u
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  rw [SymplecticGroup.mem_iff']
  ext i j
  have e := h (Pi.single i 1) (Pi.single j 1)
  rw [sympl_eq, sympl_eq, neg_inj, key] at e
  simpa [Matrix.mulVec_single_one, Pi.single_apply, dotProduct, Matrix.mulVec] using e

theorem mem_lie_of (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (h : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) :
    X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  have := lie_of_exp X (Matrix.J l ℝ) fun t => by
    rw [conjTranspose_eq_transpose_of_trivial]
    exact SymplecticGroup.mem_iff'.1 (h t)
  rw [conjTranspose_eq_transpose_of_trivial] at this
  refine (mem_skewAdjointMatricesLieSubalgebra _ _).2 ((mem_skewAdjointMatricesSubmodule _ _).2 ?_)
  show Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -X
  rw [Matrix.mul_neg, eq_neg_iff_add_eq_zero, this]

variable {W β : Type} [Fintype W] [DecidableEq W] [Fintype β] [DecidableEq β]

def SG (K : W → Matrix β β ℂ) : Subgroup (W → Matrix β β ℂ)ˣ where
  carrier := {g | star g.1 * K * g.1 = K}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have ha' : star a.1 * K * a.1 = K := ha
    have hb' : star b.1 * K * b.1 = K := hb
    show star (a.1 * b.1) * K * (a.1 * b.1) = K
    calc _ = star b.1 * (star a.1 * K * a.1) * b.1 := by simp only [star_mul, mul_assoc]
      _ = K := by rw [ha', hb']
  inv_mem' := fun {a} ha => by
    have ha' : star a.1 * K * a.1 = K := ha
    show star a⁻¹.1 * K * a⁻¹.1 = K
    calc _ = star a⁻¹.1 * (star a.1 * K * a.1) * a⁻¹.1 := by rw [ha']
      _ = star (a.1 * a⁻¹.1) * K * (a.1 * a⁻¹.1) := by simp only [star_mul, mul_assoc]
      _ = K := by simp

def LG (K : W → Matrix β β ℂ) : Submodule ℝ (W → Matrix β β ℂ) where
  carrier := {Z | star Z * K + K * Z = 0}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    have ha' : star a * K + K * a = 0 := ha
    have hb' : star b * K + K * b = 0 := hb
    show star (a + b) * K + K * (a + b) = 0
    rw [star_add, add_mul, mul_add, add_add_add_comm, ha', hb', add_zero]
  smul_mem' := fun r a ha => by
    have ha' : star a * K + K * a = 0 := ha
    show star (r • a) * K + K * (r • a) = 0
    rw [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, ha', smul_zero]

theorem mid (M : Meta l) (K : W → Matrix β β ℂ) (hK : ∀ w, (K w)ᴴ = K w) (hu : ∀ w, IsUnit (K w).det)
    (ρ : (W → Matrix β β ℂ) →ₐ[ℝ] Matrix (l ⊕ l) (l ⊕ l) ℝ) (hρ : ∀ g : SG K, ρ g.1.1 ∈ Matrix.symplecticGroup l ℝ)
    (A : SG K →* (Sch l →L[ℂ] Sch l))
    (hA : ∀ (g : SG K) g', (M.pr g' : Matrix (l ⊕ l) (l ⊕ l) ℝ) = ρ g.1.1 → ∃ c : ℂ, A g = c • M.om g')
    (hw : ∀ (T : Sch l →L[ℂ] ℂ) f, Continuous fun g => T (A g f)) :
    ∃ c : W → ℂ, ∀ (Z : W → Matrix β β ℂ) (γ : ℝ → SG K), (∀ t w, (γ t).1.1 w = NormedSpace.exp (t • Z w)) →
      ∀ (T : Sch l →L[ℂ] ℂ) f, HasDerivAt (fun t => T (A (γ t) f))
        (T (quad (ρ Z) f + (∑ w, c w * (Z w).trace) • f)) 0 := by
  have hρc : Continuous ρ := ρ.toLinearMap.continuous_of_finiteDimensional
  let s : SG K →* Matrix.symplecticGroup l ℝ :=
    { toFun := fun g => ⟨ρ g.1.1, hρ g⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun a b => Subtype.ext (map_mul ρ _ _) }
  have hs : Continuous s := (hρc.comp (Units.continuous_val.comp continuous_subtype_val)).subtype_mk _
  obtain ⟨χ, hχ, hcore⟩ := core M s hs A (fun g g' h => hA g g' (congrArg Subtype.val h)) hw
  letI : NormedRing (Matrix β β ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix β β ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix β β ℂ) := FiniteDimensional.complete ℝ _
  letI : NormedAlgebra ℚ (Matrix β β ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedAlgebra ℚ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hpi : ∀ (Z : W → Matrix β β ℂ) w, NormedSpace.exp Z w = NormedSpace.exp (Z w) := fun Z w => Pi.coe_exp Z w
  have hS : ∀ Z ∈ LG K, expU Z ∈ SG K := fun Z hZ => funext fun w => by
    have := exp_preserves (Y := Z w) (J := K w) (congrFun hZ w)
    rw [← hpi] at this
    exact this
  have hexp : ∀ (Z : W → Matrix β β ℂ) (t : ℝ), ρ (NormedSpace.exp (t • Z)) = NormedSpace.exp (t • ρ Z) := fun Z t => by
    rw [← map_smul]
    exact NormedSpace.map_exp ρ hρc _
  have key : ∀ Z (h : Z ∈ LG K), ∃ z : ℂ, (∀ t : ℝ, χ ⟨expU (t • Z), hS _ ((LG K).smul_mem t h)⟩ = cexp (2 * z * t)) ∧
      ∀ (T : Sch l →L[ℂ] ℂ) f, HasDerivAt (fun t : ℝ => T (A ⟨expU (t • Z), hS _ ((LG K).smul_mem t h)⟩ f))
        (T (quad (ρ Z) f + z • f)) 0 := fun Z h =>
    hcore (fun t => ⟨expU (t • Z), hS _ ((LG K).smul_mem t h)⟩) ((continuous_expU Z).subtype_mk _)
      (Subtype.ext (by simp only [zero_smul]; exact expU_zero)) (fun a b => Subtype.ext (expU_add Z a b)) (ρ Z)
      (mem_lie_of _ fun t => by
        rw [← hexp]
        exact hρ ⟨expU (t • Z), hS _ ((LG K).smul_mem t h)⟩) (hexp Z)
  obtain ⟨ζ, hζ, hbr⟩ := char_lie (SG K) (LG K) hS (fun Z hZ Y hY => by
    have h1 : star (expU Z)⁻¹.1 * K * (expU Z)⁻¹.1 = K := (SG K).inv_mem (hS Z hZ)
    have h2 : star Y * K + K * Y = 0 := hY
    show star ((expU Z).1 * Y * (expU Z)⁻¹.1) * K + K * ((expU Z).1 * Y * (expU Z)⁻¹.1) = 0
    generalize expU Z = g at h1
    calc _ = star (g.1 * Y * g⁻¹.1) * (star g⁻¹.1 * K * g⁻¹.1) + (star g⁻¹.1 * K * g⁻¹.1) * (g.1 * Y * g⁻¹.1) := by
          rw [h1]
      _ = star g⁻¹.1 * (star Y * star (g⁻¹.1 * g.1) * K + K * (g⁻¹.1 * g.1) * Y) * g⁻¹.1 := by
          simp only [star_mul, mul_assoc, mul_add, add_mul]
      _ = 0 := by rw [Units.inv_mul, star_one, mul_one, mul_one, h2, mul_zero, zero_mul]) χ hχ
    fun Z h => (key Z h).imp' (fun z => 2 * z) fun _ h => h.1
  have tr : ∀ w, ∃ c : ℂ, ∀ Z : Matrix β β ℂ, Zᴴ * K w + K w * Z = 0 → ζ (Pi.single w Z) = c * Z.trace := fun w => by
    let τ : Matrix β β ℂ →ₗ[ℝ] Matrix β β ℂ :=
      { toFun := fun A => -((K w)⁻¹ * Aᴴ * K w)
        map_add' := fun A B => by simp [Matrix.mul_add, Matrix.add_mul, add_comm]
        map_smul' := fun r A => by simp }
    have h1 : (K w)⁻¹ * K w = 1 := Matrix.nonsing_inv_mul _ (hu w)
    have h2 : K w * (K w)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hu w)
    have hτ : ∀ Z, τ Z = Z ↔ Zᴴ * K w + K w * Z = 0 := fun Z => by
      show -((K w)⁻¹ * Zᴴ * K w) = Z ↔ _
      constructor
      · intro h
        conv_lhs => rw [← congrArg (K w * ·) h]
        simp [← Matrix.mul_assoc, h2]
      · intro h
        rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h]
        simp [← Matrix.mul_assoc, h1]
    have hm : ∀ Z, τ Z = Z → Pi.single w Z ∈ LG K := fun Z hZ => funext fun v => by
      by_cases h : v = w
      · subst h
        simpa [star_eq_conjTranspose] using (hτ Z).1 hZ
      · simp [h]
    obtain ⟨c, hc⟩ := real_form_trace τ (fun A => by simp [τ]) (fun A => by
      show -((K w)⁻¹ * (-((K w)⁻¹ * Aᴴ * K w))ᴴ * K w) = A
      simp only [conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hK,
        Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, h1, Matrix.mul_one]
      rw [← Matrix.mul_assoc, h1, Matrix.one_mul]) (ζ ∘ₗ LinearMap.single ℝ (fun _ : W => Matrix β β ℂ) w) fun X Y hX hY => by
      refine ⟨(hτ _).2 ?_, ?_⟩
      · have a1 := eq_neg_of_add_eq_zero_left ((hτ _).1 hX)
        have a2 := eq_neg_of_add_eq_zero_left ((hτ _).1 hY)
        simp only [conjTranspose_sub, conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, a1, a2,
          Matrix.mul_neg]
        simp only [← Matrix.mul_assoc, a1, a2, Matrix.neg_mul]
        abel
      · have := hbr _ (hm X hX) _ (hm Y hY)
        rw [← Pi.single_mul, ← Pi.single_mul, ← Pi.single_sub] at this
        exact this
    exact ⟨c, fun Z hZ => hc Z ((hτ Z).2 hZ)⟩
  choose c hc using tr
  refine ⟨fun w => c w / 2, fun Z γ hγ => ?_⟩
  have hZw : ∀ w, (Z w)ᴴ * K w + K w * Z w = 0 := fun w => lie_of_exp _ _ fun t => by
    rw [← hγ]
    exact congrFun (show star (γ t).1.1 * K * (γ t).1.1 = K from (γ t).2) w
  have hZ : Z ∈ LG K := funext hZw
  obtain ⟨z, h1, h2⟩ := key Z hZ
  have e : ∀ t, γ t = ⟨expU (t • Z), hS _ ((LG K).smul_mem t hZ)⟩ := fun t =>
    Subtype.ext (Units.ext (funext fun w => (hγ t w).trans (hpi (t • Z) w).symm))
  have e2 : z = ∑ w, c w / 2 * (Z w).trace := by
    have a : 2 * z = ζ Z := exp_mul_inj fun t => by rw [← h1, hζ Z hZ]
    have b : ζ Z = ∑ w, c w * (Z w).trace := by
      conv_lhs => rw [← Finset.univ_sum_single Z, map_sum]
      exact Finset.sum_congr rfl fun w _ => hc w _ (hZw w)
    rw [b] at a
    simp only [div_mul_eq_mul_div, ← Finset.sum_div, ← a]
    ring
  simp only [e, ← e2]
  exact h2

end PositivityTheory.RL.Up

end
