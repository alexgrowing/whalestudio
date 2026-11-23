import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.LogNormEstimates
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.HeightBoundSetup

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

noncomputable section

namespace GlobalTheory.CuspGeo.TrReal

variable (I : AutInst)

def signMap : (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) where
  toFun x := fun v => Formalism.REAL.Jm (I.ε v) *ᵥ x v
  map_add' x y := by funext v; simp [mulVec_add]
  map_smul' r x := by funext v; simp [mulVec_smul]

theorem signMap_signMap (x) : signMap I (signMap I x) = x := by
  funext v
  simp [signMap, mulVec_mulVec, Formalism.REAL.Jm_mul_self]

theorem hform_eq_hf (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J x y = CompanionTheory.D.gk.RF.hf I.J x y := by
  simp [Formalism.UG.hform, CompanionTheory.D.gk.RF.hf, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem pair_vec (y : I.Ginf) (u u' : Fin I.n → I.E) :
    2 * ∑ v, ∑ i, (star (vec I y u v i) * signMap I (vec I y u') v i).re = (trForm I u u' : ℝ) := by
  rw [trForm, CompanionTheory.D.gk.RF.PE.trace_eq I (fun v a => CompanionTheory.D.gk.RF.phi_star I v a), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Complex.re_sum, hform_eq_hf, ← CompanionTheory.D.gk.RF.hf_atV_atV, ← CompanionTheory.D.gk.RF.PE.hf_uMat (y v)⁻¹]
  rfl

section
variable {I} {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))

def signMat : Matrix (Fin N) (Fin N) ℝ :=
  LinearMap.toMatrix' (ρ.toLinearMap ∘ₗ signMap I ∘ₗ ρ.symm.toLinearMap)

theorem signMat_mulVec (x) : signMat ρ *ᵥ ρ x = ρ (signMap I x) := by
  simp [signMat, LinearMap.toMatrix'_mulVec]

theorem signMat_sq : signMat ρ * signMat ρ = 1 := by
  rw [signMat, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
  congr 1
  ext w
  simp [signMap_signMap]

theorem mul_apply_dot (A X : Matrix (Fin N) (Fin N) ℝ) (i j) :
    (Aᵀ * X * A) i j = (fun k => A k i) ⬝ᵥ (X *ᵥ fun l => A l j) := by
  rw [dotProduct_mulVec, Matrix.mul_apply]
  simp [vecMul, dotProduct, Matrix.mul_apply]

theorem gm_pair (hρ : IsRealCoord I ρ) (c : ℕ) (y : I.Ginf) (e : Fin N → Fin I.n → I.E) (i j) :
    ((gm I ρ y e)ᵀ * ((2 * c : ℝ) • signMat ρ) * gm I ρ y e) i j = c * (trForm I (e i) (e j) : ℝ) := by
  rw [mul_apply_dot]
  have h1 : (fun k => gm I ρ y e k i) = ρ (vec I y (e i)) := rfl
  have h2 : (fun k => gm I ρ y e k j) = ρ (vec I y (e j)) := rfl
  rw [h1, h2, smul_mulVec, dotProduct_smul, signMat_mulVec, hρ, ← pair_vec I y (e i) (e j), smul_eq_mul]
  ring

theorem adj_formula (G X : Matrix (Fin N) (Fin N) ℝ) (a : ℝ) (ha : a ≠ 0) (hX : X * X = a • 1) :
    G * adjugate (Gᵀ * X * G) * Gᵀ = ((Gᵀ * X * G).det / a) • X := by
  have hadj : adjugate X = (X.det / a) • X := by
    calc adjugate X = adjugate X * (a⁻¹ • (X * X)) := by rw [hX, smul_smul, inv_mul_cancel₀ ha, one_smul, Matrix.mul_one]
      _ = (a⁻¹ • (adjugate X * X)) * X := by rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [adjugate_mul, smul_smul, Matrix.smul_mul, Matrix.one_mul, div_eq_inv_mul]
  rw [adjugate_mul_distrib, adjugate_mul_distrib, hadj, det_mul, det_mul, det_transpose]
  have e1 : G * (adjugate G * (((X.det / a) • X) * adjugate Gᵀ)) * Gᵀ =
      (G * adjugate G) * ((X.det / a) • X) * (adjugate Gᵀ * Gᵀ) := by simp only [Matrix.mul_assoc]
  rw [e1, mul_adjugate, adjugate_mul, det_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  congr 1
  ring
end

section Rat

theorem hform_dot (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J x y = (fun i => starRingEnd I.E (x i)) ⬝ᵥ (I.J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem trForm_sum_right {ι : Type} [Fintype ι] (x : Fin I.n → I.E) (q : ι → ℚ) (y : ι → Fin I.n → I.E) :
    trForm I x (∑ j, q j • y j) = ∑ j, q j * trForm I x (y j) := by
  simp only [trForm, hform_dot, mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul, map_sum, map_smul,
    smul_eq_mul]

theorem trForm_sum_left {ι : Type} [Fintype ι] (x : Fin I.n → I.E) (q : ι → ℚ) (y : ι → Fin I.n → I.E) :
    trForm I (∑ j, q j • y j) x = ∑ j, q j * trForm I (y j) x := by
  have e : (fun i => starRingEnd I.E ((∑ j, q j • y j) i)) = ∑ j, q j • fun i => starRingEnd I.E (y j i) := by
    funext i
    simp [Finset.sum_apply, map_sum, map_rat_smul]
  simp only [trForm, hform_dot, e, sum_dotProduct, smul_dotProduct, map_sum, map_smul, smul_eq_mul]

theorem trForm_smul_left (x u : Fin I.n → I.E) (q : ℚ) : trForm I (q • u) x = q * trForm I u x := by
  have := trForm_sum_left I x (fun _ : Fin 1 => q) (fun _ => u)
  simpa using this

theorem intVec_of_basis {N : ℕ} {e : Fin N → Fin I.n → I.E} (he : IsZBasis I e) (i) : IntVec I (e i) :=
  (he.2 (e i)).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩

theorem trForm_int (c : ℕ) (hc : ∀ a b, IsIntegral ℤ ((c : I.E) * I.J a b)) {u u' : Fin I.n → I.E}
    (hu : IntVec I u) (hu' : IntVec I u') : ∃ z : ℤ, (z : ℚ) = c * trForm I u u' := by
  have e1 : (c : ℚ) * trForm I u u' = Algebra.trace ℚ I.E ((c : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J u u') := by
    rw [trForm, ← smul_eq_mul, ← map_smul, Algebra.smul_def, map_natCast]
  have hint : IsIntegral ℤ ((c : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J u u') := by
    rw [Formalism.UG.hform, Finset.mul_sum]
    refine IsIntegral.sum _ fun a _ => ?_
    rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun b _ => ?_
    have : (c : I.E) * (starRingEnd I.E (u a) * I.J a b * u' b) = starRingEnd I.E (u a) * ((c : I.E) * I.J a b) * u' b := by ring
    rw [this]
    exact ((map_isIntegral_int (starRingEnd I.E) (hu a)).mul (hc a b)).mul (hu' b)
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (L := ℚ) hint)
  exact ⟨z, by rw [e1, ← hz]; simp⟩

end Rat

section Det
variable {I} {N : ℕ}

theorem det_ne_zero {e : Fin N → Fin I.n → I.E} (he : IsZBasis I e) (c : ℕ) (hc1 : 1 ≤ c)
    (B : Matrix (Fin N) (Fin N) ℤ) (hB : ∀ i j, (B i j : ℚ) = c * trForm I (e i) (e j)) : B.det ≠ 0 := by
  intro h0
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  set x : Fin I.n → I.E := ∑ j, ((z j : ℚ)) • e j with hxdef
  have hx0 : x ≠ 0 := by
    intro hx
    apply hz0
    have e0 : ∑ j, z j • e j = 0 := by rw [← hx, hxdef]; simp [Int.cast_smul_eq_zsmul]
    funext j
    exact Fintype.linearIndependent_iff.1 he.1 z e0 j
  have hc0 : (c : ℚ) ≠ 0 := by positivity
  have hxe : ∀ i, trForm I (e i) x = 0 := by
    intro i
    have h1 := congrFun hz i
    simp only [mulVec, dotProduct, Pi.zero_apply] at h1
    have h2 : ((∑ j, B i j * z j : ℤ) : ℚ) = 0 := by rw [h1]; simp
    push_cast at h2
    simp only [hB] at h2
    rw [hxdef, trForm_sum_right]
    have : (c : ℚ) * ∑ j, (z j : ℚ) * trForm I (e i) (e j) = 0 := by
      rw [Finset.mul_sum, ← h2]; exact Finset.sum_congr rfl fun j _ => by ring
    exact (mul_eq_zero.1 this).resolve_left hc0
  have hJx : I.J *ᵥ x ≠ 0 := fun h => I.J_det (Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx0, h⟩)
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hJx
  set y0 : Fin I.n → I.E := Pi.single k (star ((I.J *ᵥ x) k))⁻¹ with hy0def
  have hh : Formalism.UG.hform (starRingEnd I.E) I.J y0 x = 1 := by
    rw [hform_dot]
    have e2 : (fun i => starRingEnd I.E (y0 i)) = Pi.single k ((I.J *ᵥ x) k)⁻¹ := by
      funext i
      by_cases h : i = k
      · subst h; simp [hy0def, star_inv₀, starRingEnd_apply, star_star]
      · simp [hy0def, Pi.single_apply, h]
    rw [e2]
    simp [dotProduct, Pi.single_apply]
    exact inv_mul_cancel₀ (by simpa using hk)
  have hy0 : trForm I y0 x = Module.finrank ℚ I.E := by
    rw [trForm, hh, ← map_one (algebraMap ℚ I.E), Algebra.trace_algebraMap]; simp
  obtain ⟨d, hd, hdi⟩ := CompanionTheory.D.gk.RF.PE.exists_den y0
  obtain ⟨w, hw⟩ := (he.2 (fun i => (d : I.E) * y0 i)).1 hdi
  have e3 : (fun i => (d : I.E) * y0 i) = (d : ℚ) • y0 := by
    funext i; rw [Pi.smul_apply, Rat.smul_def]; simp
  have h4 : trForm I ((d : ℚ) • y0) x = 0 := by
    rw [← e3, hw]
    have : (∑ i, w i • e i) = ∑ i, ((w i : ℚ)) • e i := by simp [Int.cast_smul_eq_zsmul]
    rw [this, trForm_sum_left]; simp [hxe]
  rw [trForm_smul_left, hy0] at h4
  have hf : (Module.finrank ℚ I.E : ℚ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hd0 : (d : ℚ) ≠ 0 := by positivity
  exact mul_ne_zero hd0 hf h4

theorem change_basis {e e' : Fin N → Fin I.n → I.E} (he : IsZBasis I e) (he' : ∀ i, IntVec I (e' i)) (c : ℕ)
    (B B' : Matrix (Fin N) (Fin N) ℤ) (hB : ∀ i j, (B i j : ℚ) = c * trForm I (e i) (e j))
    (hB' : ∀ i j, (B' i j : ℚ) = c * trForm I (e' i) (e' j)) : ∃ Z : Matrix (Fin N) (Fin N) ℤ, B' = Z * B * Zᵀ := by
  choose Z hZ using fun i => (he.2 (e' i)).1 (he' i)
  refine ⟨Matrix.of fun i k => Z i k, Matrix.ext fun i j => Int.cast_injective (α := ℚ) ?_⟩
  rw [hB', hZ i, hZ j]
  have hq : ∀ i, ∑ k, Z i k • e k = ∑ k, ((Z i k : ℚ)) • e k := fun i => by simp [Int.cast_smul_eq_zsmul]
  rw [hq, hq, trForm_sum_left]
  simp only [trForm_sum_right]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  push_cast
  simp only [hB, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

end Det

theorem det_eq {N : ℕ} {e e' : Fin N → Fin I.n → I.E} (he : IsZBasis I e) (he' : IsZBasis I e') (c : ℕ) (hc1 : 1 ≤ c)
    (B B' : Matrix (Fin N) (Fin N) ℤ) (hB : ∀ i j, (B i j : ℚ) = c * trForm I (e i) (e j))
    (hB' : ∀ i j, (B' i j : ℚ) = c * trForm I (e' i) (e' j)) : B'.det = B.det := by
  obtain ⟨Z, hZ⟩ := change_basis he (intVec_of_basis I he') c B B' hB hB'
  obtain ⟨W, hW⟩ := change_basis he' (intVec_of_basis I he) c B' B hB' hB
  have h0 := det_ne_zero he c hc1 B hB
  have e1 : B'.det = Z.det * B.det * Z.det := by rw [hZ, det_mul, det_mul, det_transpose]
  have e2 : B.det = W.det * B'.det * W.det := by rw [hW, det_mul, det_mul, det_transpose]
  have e3 : Z.det * (Z.det * W.det * W.det) = 1 := by
    refine mul_left_cancel₀ h0 ?_
    calc B.det * (Z.det * (Z.det * W.det * W.det)) = W.det * (Z.det * B.det * Z.det) * W.det := by ring
      _ = B.det * 1 := by rw [← e1, ← e2, mul_one]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one e3 with h | h <;> rw [e1, h] <;> ring

theorem trace_form_real_coord : ∀ (I : AutInst) (N : ℕ) (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)),
    IsRealCoord I ρ → ∃ (X : Matrix (Fin N) (Fin N) ℝ) (μ : ℝ) (c : ℕ), μ ≠ 0 ∧ 1 ≤ c ∧
      ∀ (y : I.Ginf) (e : Fin N → Fin I.n → I.E), IsZBasis I e → ∃ B B' : Matrix (Fin N) (Fin N) ℤ,
        B.map (Int.cast : ℤ → ℝ) = (gm I ρ y e)ᵀ * X * gm I ρ y e ∧
        gm I ρ y e * B'.map (Int.cast : ℤ → ℝ) * (gm I ρ y e)ᵀ = μ • X ∧
        ∀ i j, (B i j : ℚ) = c * trForm I (e i) (e j) := by
  intro I N ρ hρ
  classical
  obtain ⟨c, hc1, hc⟩ := CompanionTheory.D.gk.RF.PE.exists_den fun p : Fin I.n × Fin I.n => I.J p.1 p.2
  have hcJ : ∀ a b, IsIntegral ℤ ((c : I.E) * I.J a b) := fun a b => hc (a, b)
  set X : Matrix (Fin N) (Fin N) ℝ := (2 * c : ℝ) • signMat ρ with hXdef
  have ha : (4 * (c : ℝ) ^ 2) ≠ 0 := by
    have : (1 : ℝ) ≤ c := by exact_mod_cast hc1
    positivity
  have hX : X * X = (4 * (c : ℝ) ^ 2) • 1 := by
    rw [hXdef, Matrix.smul_mul, Matrix.mul_smul, signMat_sq, smul_smul]
    congr 1
    ring
  have hBex : ∀ e : Fin N → Fin I.n → I.E, IsZBasis I e →
      ∃ B : Matrix (Fin N) (Fin N) ℤ, ∀ i j, (B i j : ℚ) = c * trForm I (e i) (e j) := fun e he => by
    choose z hz using fun i j => trForm_int I c hcJ (intVec_of_basis I he i) (intVec_of_basis I he j)
    exact ⟨Matrix.of z, fun i j => hz i j⟩
  let Δ : ℝ := if h : ∃ e : Fin N → Fin I.n → I.E, IsZBasis I e then
    ((hBex h.choose h.choose_spec).choose.det : ℝ) else 4 * (c : ℝ) ^ 2
  have hΔ : Δ ≠ 0 := by
    simp only [Δ]
    split_ifs with h
    · exact_mod_cast det_ne_zero h.choose_spec c hc1 _ (hBex h.choose h.choose_spec).choose_spec
    · exact ha
  refine ⟨X, Δ / (4 * (c : ℝ) ^ 2), c, div_ne_zero hΔ ha, hc1, fun y e he => ?_⟩
  obtain ⟨B, hB⟩ := hBex e he
  have hBr : B.map (Int.cast : ℤ → ℝ) = (gm I ρ y e)ᵀ * X * gm I ρ y e := by
    ext i j
    rw [hXdef, gm_pair ρ hρ c y e i j, Matrix.map_apply]
    have := congrArg (Rat.cast : ℚ → ℝ) (hB i j)
    push_cast at this
    exact this
  refine ⟨B, adjugate B, hBr, ?_, hB⟩
  have hex : ∃ e : Fin N → Fin I.n → I.E, IsZBasis I e := ⟨e, he⟩
  have hΔe : Δ = (B.det : ℝ) := by
    simp only [Δ, dif_pos hex]
    exact_mod_cast det_eq I he hex.choose_spec c hc1 B _ hB (hBex hex.choose hex.choose_spec).choose_spec
  have hadj : (adjugate B).map (Int.cast : ℤ → ℝ) = adjugate (B.map (Int.cast : ℤ → ℝ)) :=
    (Int.castRingHom ℝ).map_adjugate B
  rw [hadj, hBr, adj_formula _ X _ ha hX, ← hBr, hΔe]
  congr 2
  exact ((Int.castRingHom ℝ).map_det B).symm

end GlobalTheory.CuspGeo.TrReal

end
