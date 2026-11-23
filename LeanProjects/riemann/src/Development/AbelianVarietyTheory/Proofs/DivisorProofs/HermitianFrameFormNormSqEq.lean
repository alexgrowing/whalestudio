import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormSqZero
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open scoped ComplexOrder

open GlobalTheory.HermFrame Filter Topology ComplexConjugate

namespace GlobalTheory.HermFrame

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem ddbar_mul_conj_mul_of_zero {s U : E → ℂ} {z : E} (hs : ContDiffAt ℂ 2 s z) (h0 : s z = 0)
    (hU : ContDiffAt ℝ 2 U z) (ξ η : E) :
    ddbar (fun x => s x * (conj (s x) * U x)) z ξ η = del s z ξ * (conj (del s z η) * U z) := by
  have hR : ContDiffAt ℝ 2 s z := hs.restrict_scalars ℝ
  have hc : ContDiffAt ℝ 2 (fun x => conj (s x)) z := Complex.conjCLE.contDiff.contDiffAt.comp z hR
  have hW : ContDiffAt ℝ 2 (fun x => conj (s x) * U x) z := hc.mul hU
  have he : (fun x => dbar (fun y => s y * (conj (s y) * U y)) x η) =ᶠ[𝓝 z]
      fun x => s x * dbar (fun y => conj (s y) * U y) x η := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt_two hs,
      eventually_differentiableAt_of_contDiffAt_two hW] with x h1 h2
    rw [dbar_mul (h1.restrictScalars ℝ) h2, dbar_eq_zero h1]
    simp
  rw [ddbar_eq_del_dbar (hR.mul hW), del_congr he,
    del_mul (hR.differentiableAt two_ne_zero) (differentiableAt_dbar_apply hW η),
    dbar_mul (hc.differentiableAt two_ne_zero) (hU.differentiableAt two_ne_zero), dbar_conj, h0]
  simp

open Matrix in

theorem extTrace_chg_of_block_eq_zero {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    {K A : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E} (h : MContDiffAt 1 K z)
    (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (hA : MContDiffAt 1 A z) (hu : IsUnit (A z).det)
    (hA0 : ∀ η, mdbar A z η = 0) (ht : (A z).toBlocks₂₁ = 0) (ξ η : E) :
    extTrace (fun x => chg (A x) (K x)) z ξ η = kappa *
      ((secondForm K z ξ + (mdel A z ξ).toBlocks₂₁ * (A z).toBlocks₁₁⁻¹) *
        adj (subGram (K z)) (quotGram (K z))
          (secondForm K z η + (mdel A z η).toBlocks₂₁ * (A z).toBlocks₁₁⁻¹)).trace := by
  have eA : A z = fromBlocks (A z).toBlocks₁₁ (A z).toBlocks₁₂ 0 (A z).toBlocks₂₂ := by
    rw [← ht, fromBlocks_toBlocks]
  have hd := hu
  rw [eA, det_fromBlocks_zero₂₁, IsUnit.mul_iff] at hd
  have hK := hp.self_of_nhds
  have hb (ξ : E) : secondForm (fun x => chg (A x) (K x)) z ξ =
      (A z).toBlocks₂₂⁻¹ * (secondForm K z ξ + (mdel A z ξ).toBlocks₂₁ * (A z).toBlocks₁₁⁻¹) *
        (A z).toBlocks₁₁ := by
    have e := congrArg (A z * ·) (conn_changeFrame h hK.det_pos.ne'.isUnit hA hu hA0 ξ)
    simp only [mul_nonsing_inv_cancel_left _ _ hu] at e
    have e₁ := congrArg toBlocks₂₁ e
    rw [← fromBlocks_toBlocks (conn _ z ξ), ← fromBlocks_toBlocks (conn K z ξ),
      ← fromBlocks_toBlocks (mdel A z ξ), eA] at e₁
    simp only [fromBlocks_multiply, fromBlocks_add, toBlocks_fromBlocks₂₁, Matrix.zero_mul,
      Matrix.mul_zero, zero_add, add_zero] at e₁
    rw [secondForm_eq, secondForm_eq, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_assoc,
      nonsing_inv_mul _ hd.1, Matrix.mul_one]
    first
      | (rw [← e₁, nonsing_inv_mul_cancel_left _ _ hd.2]; rfl)
      | (rw [add_comm, ← e₁, nonsing_inv_mul_cancel_left _ _ hd.2]; rfl)
  have hp' : ∀ᶠ x in 𝓝 z, (chg (A x) (K x)).PosDef := by
    filter_upwards [hp, hA.eventually_isUnit hu] with x h₁ h₂
    exact posDef_chg ((isUnit_iff_isUnit_det _).2 h₂) h₁
  rw [extTrace_eq (K := fun x => chg (A x) (K x))
    ((hA.transpose.mul h).mul hA.conjTranspose.transpose) hp',
    secondFormAdj, hb, hb, ← trace_mul_adj_chg hd.1 hd.2 (subGram (K z)),
    ← subGram_chg _ (A z).toBlocks₁₂ (A z).toBlocks₂₂,
    ← quotGram_chg (A z).toBlocks₁₂ _ hd.1 (posDef_subGram hK).det_pos.ne'.isUnit, ← eA]

end

theorem chg_mul_sub_form {K A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ} (hK : K.IsHermitian) :
    chg A K (.inl 0) (.inl 0) * K (.inl 0) (.inl 0) -
      ((‖form K (Pi.single (Sum.inl 0) 1) (fun i => A i (Sum.inl 0))‖ ^ 2 : ℝ) : ℂ) =
    A (.inr 0) (.inl 0) * (conj (A (.inr 0) (.inl 0)) *
      (K (.inl 0) (.inl 0) * K (.inr 0) (.inr 0) - K (.inl 0) (.inr 0) * K (.inr 0) (.inl 0))) := by
  have h1 : conj (K (.inl 0) (.inl 0)) = K (.inl 0) (.inl 0) := hK.apply _ _
  have h2 : conj (K (.inl 0) (.inr 0)) = K (.inr 0) (.inl 0) := hK.apply _ _
  rw [Complex.ofReal_pow, ← Complex.mul_conj', chg_apply, form_eq_sum, form_eq_sum]
  simp [Fintype.sum_sum_type, h1, h2]
  ring

end GlobalTheory.HermFrame

namespace GlobalTheory.LineForm

theorem ofValues_mul_ofValues_eq_zero {n : ℕ} (u u' w w' : ReciprocityTheory.L2DbarEstimates.V n → ℂ) (c : ℂ) :
    ((ofValues (fun ξ η => c * (u ξ * u' η)) : Ev n) : Alt n) *
      (((ofValues (fun ξ η => u ξ * w' η) : Ev n) : Alt n) +
        ((ofValues (fun ξ η => w ξ * u' η) : Ev n) : Alt n)) = 0 := by
  have e : ((ofValues (fun ξ η => c * (u ξ * u' η)) : Ev n) : Alt n) =
      c • ((ofValues (fun ξ η => u ξ * u' η) : Ev n) : Alt n) := by
    simp only [ofValues, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, Finset.smul_sum, smul_smul]
  rw [e, coe_ofValues_mul, coe_ofValues_mul, coe_ofValues_mul]
  generalize (∑ a, u (GlobalTheory.GoodMetric.coordVec a) • Pi.single (Sum.inl a) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = x
  generalize (∑ a, w (GlobalTheory.GoodMetric.coordVec a) • Pi.single (Sum.inl a) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = x'
  generalize (∑ b, u' (GlobalTheory.GoodMetric.coordVec b) • Pi.single (Sum.inr b) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = y
  generalize (∑ b, w' (GlobalTheory.GoodMetric.coordVec b) • Pi.single (Sum.inr b) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = y'
  have h := Subalgebra.mem_center_iff.1 (ι_mul_ι_mem_center x y) (ExteriorAlgebra.ι ℂ x)
  have h' := Subalgebra.mem_center_iff.1 (ι_mul_ι_mem_center x' y) (ExteriorAlgebra.ι ℂ y)
  rw [smul_mul_assoc, mul_add, ← mul_assoc _ (ExteriorAlgebra.ι ℂ x), ← h, ← mul_assoc (ExteriorAlgebra.ι ℂ x),
    ExteriorAlgebra.ι_sq_zero, mul_assoc (ExteriorAlgebra.ι ℂ x), h', mul_assoc (ExteriorAlgebra.ι ℂ x'),
    ExteriorAlgebra.ι_sq_zero]
  simp

theorem coe_ofValues_sub_eq {n : ℕ} {α β γ δ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n → ℂ}
    (h : ∀ ξ η, α ξ η = β ξ η + (γ ξ η + δ ξ η)) :
    ((ofValues α : Ev n) : Alt n) - ((ofValues β : Ev n) : Alt n) =
      ((ofValues γ : Ev n) : Alt n) + ((ofValues δ : Ev n) : Alt n) := by
  simp only [ofValues, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, Subalgebra.coe_add, h, add_smul,
    Finset.sum_add_distrib, add_sub_cancel_left]

theorem ddc_sinSq_mul_extTrace_sub : ∀ (n : ℕ) (K A : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n → ℝ) (z : ReciprocityTheory.L2DbarEstimates.V n),
    GlobalTheory.HermFrame.MContDiffAt 2 K z → (∀ᶠ x in nhds z, (K x).PosDef) → (∀ a b, AnalyticAt ℂ (fun x => A x a b) z) → IsUnit (A z).det → v z = 1 →
    (∀ᶠ x in nhds z, ‖GlobalTheory.HermFrame.form (K x) (Pi.single (Sum.inl 0) 1) (fun i => A x i (Sum.inl 0))‖ ^ 2 =
      v x * (GlobalTheory.HermFrame.chg (A x) (K x) (Sum.inl 0) (Sum.inl 0)).re * (K x (Sum.inl 0) (Sum.inl 0)).re) →
    ((ofValues (GlobalTheory.HermFrame.ddc (fun x => 1 - v x) z) : Ev n) : Alt n) *
      (((ofValues (GlobalTheory.HermFrame.extTrace (fun x => GlobalTheory.HermFrame.chg (A x) (K x)) z) : Ev n) : Alt n) -
        ((ofValues (GlobalTheory.HermFrame.extTrace K z) : Ev n) : Alt n)) = 0 := by
  intro n K A v z hK hp hA hu hv he
  have hA2 : MContDiffAt 2 A z := fun a b => ((hA a b).contDiffAt (n := 2)).restrict_scalars ℝ
  have hA1 : MContDiffAt 1 A z := fun a b => (hA2 a b).of_le (by norm_num)
  have hK1 : MContDiffAt 1 K z := fun a b => (hK a b).of_le (by norm_num)
  have hC : MContDiffAt 2 (fun x => chg (A x) (K x)) z :=
    (hA2.transpose.mul hK).mul hA2.conjTranspose.transpose
  have hp' : ∀ᶠ x in 𝓝 z, (chg (A x) (K x)).PosDef := by
    filter_upwards [hp, hA1.eventually_isUnit hu] with x h₁ h₂
    exact posDef_chg ((Matrix.isUnit_iff_isUnit_det _).2 h₂) h₁
  set s : ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun x => A x (.inr 0) (.inl 0) with hs
  set U : ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun x =>
    (K x (.inl 0) (.inl 0) * K x (.inr 0) (.inr 0) - K x (.inl 0) (.inr 0) * K x (.inr 0) (.inl 0)) *
      (chg (A x) (K x) (.inl 0) (.inl 0) * K x (.inl 0) (.inl 0))⁻¹ with hU
  have hne : chg (A z) (K z) (.inl 0) (.inl 0) * K z (.inl 0) (.inl 0) ≠ 0 :=
    mul_ne_zero (hp'.self_of_nhds.diag_pos).ne' (hp.self_of_nhds.diag_pos).ne'
  have hU2 : ContDiffAt ℝ 2 U z :=
    (((hK _ _).mul (hK _ _)).sub ((hK _ _).mul (hK _ _))).mul (((hC _ _).mul (hK _ _)).inv hne)
  have hev : (fun x => ((1 - v x : ℝ) : ℂ)) =ᶠ[𝓝 z] fun x => s x * (conj (s x) * U x) := by
    filter_upwards [hp, hp', he] with x h₁ h₂ h₃
    have e := chg_mul_sub_form (A := A x) h₁.isHermitian
    have n₁ := (h₁.diag_pos (i := .inl 0))
    have n₂ := (h₂.diag_pos (i := .inl 0))
    have r₁ : ((K x (.inl 0) (.inl 0)).re : ℂ) = K x (.inl 0) (.inl 0) :=
      Complex.ext rfl (by simpa using (Complex.lt_def.1 n₁).2)
    have r₂ : ((chg (A x) (K x) (.inl 0) (.inl 0)).re : ℂ) = chg (A x) (K x) (.inl 0) (.inl 0) :=
      Complex.ext rfl (by simpa using (Complex.lt_def.1 n₂).2)
    rw [h₃, Complex.ofReal_mul, Complex.ofReal_mul, r₁, r₂] at e
    have n₁' := n₁.ne'
    have n₂' := n₂.ne'
    simp only [hs, hU]
    rw [← mul_assoc (conj _), ← mul_assoc, ← e]
    push_cast
    field_simp
  have hUz : U z ≠ 0 := by
    refine mul_ne_zero ?_ (inv_ne_zero hne)
    have := hp.self_of_nhds.det_pos.ne'
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv.symm, Matrix.det_fin_two] at this
    exact this
  have hs0 : s z = 0 := by
    have := hev.self_of_nhds
    simp only [hv, sub_self, Complex.ofReal_zero] at this
    simpa [hUz] using this.symm
  have e1 : ddc (fun x => 1 - v x) z = fun ξ η => (kappa * U z) * (del s z ξ * conj (del s z η)) := by
    funext ξ η
    rw [ddc, leviForm, ddbar_congr hev, ddbar_mul_conj_mul_of_zero (hA _ _).contDiffAt hs0 hU2]
    ring
  have hA0 : ∀ η, mdbar A z η = 0 := fun η => Matrix.ext fun i j =>
    congr($(dbar_eq_zero (hA i j).differentiableAt) η)
  have ht : (A z).toBlocks₂₁ = 0 := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact hs0
  set c : ℂ := kappa * ((subGram (K z)).transpose⁻¹ 0 0 * quotGram (K z) 0 0) with hc
  set d : ℂ := (A z).toBlocks₁₁⁻¹ 0 0 with hd
  rw [e1, coe_ofValues_sub_eq (γ := fun ξ η => del s z ξ *
      (c * d * conj (secondForm K z η 0 0 + del s z η * d)))
    (δ := fun ξ η => (c * conj d * secondForm K z ξ 0 0) * conj (del s z η)) fun ξ η => ?_]
  · exact ofValues_mul_ofValues_eq_zero _ (fun η => conj (del s z η)) _ _ _
  · have m (ξ) : (mdel A z ξ).toBlocks₂₁ 0 0 = del s z ξ := rfl
    rw [extTrace_chg_of_block_eq_zero hK1 hp hA1 hu hA0 ht, extTrace_eq hK1 hp, secondFormAdj]
    simp only [adj, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_one, Matrix.add_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, m, ← hd, hc, Complex.star_def, map_add, map_mul]
    ring

end GlobalTheory.LineForm
