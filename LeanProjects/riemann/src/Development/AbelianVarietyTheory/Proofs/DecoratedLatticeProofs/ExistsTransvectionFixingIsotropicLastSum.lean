import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.TransvLast

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

theorem form_mulVec (S : HSp D) {k l : ℕ} (M : Mx D S.rank k) (N : Mx D S.rank l) (x : Fin k → AE D)
    (y : Fin l → AE D) :
    form S (M *ᵥ x) (N *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj N ⬝ (gA S ⬝ M)) *ᵥ x) := by
  have h : (fun i => cA D ((N *ᵥ y) i)) = N.map (cA D) *ᵥ (fun i => cA D (y i)) :=
    funext fun i => RingHom.map_mulVec (cA D) N y i
  rw [form, h, ← Matrix.vecMul_transpose (N.map (cA D)), ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  rfl

theorem conj_smul {n : ℕ} (c : AE D) (y : Fin n → AE D) :
    (fun i => cA D ((c • y) i)) = cA D c • fun i => cA D (y i) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]

theorem conj_ratV {n : ℕ} (z : Fin n → D.host.E) : (fun i => cA D (ratV z i)) = ratV (star z) :=
  funext fun i => GlobalTheory.DualPairCheck.cA_incA (z i)

theorem ratV_dotProduct {n : ℕ} (x y : Fin n → D.host.E) : ratV x ⬝ᵥ ratV y = incA D (x ⬝ᵥ y) := by
  simp only [dotProduct, map_sum, map_mul]
  rfl

theorem incA_inv_mul {x : D.host.E} (hx : x ≠ 0) : incA D x⁻¹ * incA D x = 1 := by
  rw [← map_mul, inv_mul_cancel₀ hx, map_one]

section Lemmas

variable {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

theorem hermSpaceAdelicForm_isotropic_anisotropic_zero (b : Fin ρ → AE D) (y : Fin V₀.rank → AE D) : form V (vecX d b) (d.j0 *ᵥ y) = 0 := by
  rw [vecX, form_mulVec, d.gram_0X, Matrix.zero_mulVec, dotProduct_zero]

theorem form_vecX_vecX (b b' : Fin ρ → AE D) : form V (vecX d b) (vecX d b') = 0 := by
  rw [vecX, vecX, form_mulVec, d.gram_XX, Matrix.zero_mulVec, dotProduct_zero]

theorem hermSpaceAdelicForm_anisotropic_isotropic_zero (y : Fin V₀.rank → AE D) (b : Fin ρ → AE D) : form V (d.j0 *ᵥ y) (vecX d b) = 0 := by
  rw [vecX, form_mulVec, d.wittDecomp_gram_X_anisotropic, Matrix.zero_mulVec, dotProduct_zero]

theorem hermSpaceAdelicForm_anisotropic_rational_smul (z : Fin V₀.rank → D.host.E) (c : AE D) :
    form V (d.j0 *ᵥ ratV z) (d.j0 *ᵥ (c • ratV z)) = cA D c * incA D (star z ⬝ᵥ V₀.gram *ᵥ z) := by
  rw [form_mulVec, d.gram_00, conj_smul, smul_dotProduct, conj_ratV, gA, ← GlobalTheory.MixPer.ratV_mulVec, ratV_dotProduct,
    smul_eq_mul]

theorem mt_jX_of_isTransv {w v : VA V} {u : GA D V} (hu : IsTransv V w v u)
    (hw : ∀ b, form V (vecX d b) w = 0) (hv : ∀ b, form V (vecX d b) v = 0) : mt V u ⬝ d.jX = d.jX := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  have h : act V u (vecX d (Pi.single i 1)) = transv V w v (vecX d (Pi.single i 1)) := hu _
  rw [transv, hv, hw, zero_smul, zero_smul, mul_zero, zero_smul, add_zero, sub_zero, sub_zero] at h
  rw [← Matrix.mulVec_mulVec]
  exact h

theorem mt_of_isTransv {S : HSp D} {w v y : VA S} {u : GA D S} (hu : IsTransv S w v u) (hy : form S y w = 0) :
    mt S u *ᵥ y = y + form S y v • w := by
  have h : act S u y = transv S w v y := hu _
  rw [transv, hy, zero_smul, mul_zero, zero_smul, sub_zero, sub_zero] at h
  exact h

theorem simpleSum_of {z : Fin V₀.rank → D.host.E} {u : GA D V} {c : Fin ρ → AE D} (s : AE D)
    (hX : mt V u ⬝ d.jX = d.jX) (hy : mt V u *ᵥ (d.j0 *ᵥ ratV z) = d.j0 *ᵥ ratV z + s • (d.jX *ᵥ c)) :
    simpleSum d z u = s * (ell D ρ ⬝ᵥ c) := by
  rw [simpleSum, blockX, hX, d.pX_jX, upSum_one, zero_add, coefX, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hy, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, d.pX_j0,
    d.pX_jX, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, dotProduct_smul, smul_eq_mul]

theorem mem_fixer_column {u : GA D V} (hX : mt V u ⬝ d.jX = d.jX) (i : Fin ρ) :
    u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i) := by
  rw [mem_fixer]
  ext k l
  have h := congrFun (congrFun hX k) i
  rw [Matrix.mul_apply] at h
  simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using h

theorem ell_dotProduct_last {j : Fin ρ} (hj : j.1 + 1 = ρ) {a : Fin ρ → D.host.E} (haj : a j = 1) :
    ell D ρ ⬝ᵥ ratVec a = 1 := by
  rw [dotProduct, Finset.sum_eq_single j]
  · simp [ell, hj, ratVec, haj]
  · intro i _ hij
    have : ¬ (i.1 + 1 = ρ) := fun h => hij (Fin.ext (Nat.add_right_cancel (h.trans hj.symm)))
    simp [ell, this]
  · intro h
    exact absurd (Finset.mem_univ j) h

end Lemmas

theorem exists_transv_simpleSum_last : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (z : Fin V₀.rank → D.host.E), star z ⬝ᵥ V₀.gram *ᵥ z ≠ 0 → ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → j.1 + 1 = ρ → ∀ s : AE D, ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum d z u = s := by
  intro D V V₀ ρ d z hz j a haj _ hj s
  refine ⟨d.j0 *ᵥ (cA D (s * incA D (star z ⬝ᵥ V₀.gram *ᵥ z)⁻¹) • ratV z), hermSpaceAdelicForm_isotropic_anisotropic_zero d _ _,
    fun i k _ => by rw [hermSpaceAdelicForm_isotropic_anisotropic_zero, zero_mul], fun u hu => ?_⟩
  have hX := mt_jX_of_isTransv d hu (fun b => form_vecX_vecX d b _) (fun b => hermSpaceAdelicForm_isotropic_anisotropic_zero d b _)
  have hy := mt_of_isTransv hu (hermSpaceAdelicForm_anisotropic_isotropic_zero d (ratV z) (ratVec a))
  rw [hermSpaceAdelicForm_anisotropic_rational_smul, cA_cA, mul_assoc, incA_inv_mul hz, mul_one] at hy
  exact ⟨fun i => mem_fixer_column d hX i.1, (simpleSum_of d s hX hy).trans (by rw [ell_dotProduct_last hj haj, mul_one])⟩

end GlobalTheory.TransvLast

end
