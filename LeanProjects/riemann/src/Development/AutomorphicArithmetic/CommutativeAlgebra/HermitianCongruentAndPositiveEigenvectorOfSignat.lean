import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ComplexUniformizationSigOne
import Development.AutomorphicArithmetic.RealSpanData.RealData
import Development.AutomorphicArithmetic.RealSpanData.JSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianCongrOfPositiveIndexEq

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private theorem form_re_eq {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (H *ᵥ x)).re = ∑ i, hH.eigenvalues i *
      Complex.normSq ((star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ x) i) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hspec : H = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    have h0 := hH.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h0
  have hsy : star (star U *ᵥ x) = star x ᵥ* U := by
    rw [star_mulVec, ← star_eq_conjTranspose, star_star]
  have hL : star x ⬝ᵥ (H *ᵥ x) =
      star (star U *ᵥ x) ⬝ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (star U *ᵥ x)) := by
    rw [hsy, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← hspec]
  rw [hL, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mulVec_diagonal]
  simp only [Function.comp_apply, Pi.star_apply, RCLike.star_def, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  simp [Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem finrank_le_of_coord {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (p : Fin n → Prop)
    [Fintype {i // p i}] (W : Submodule ℂ (Fin n → ℂ)) (h : ∀ x ∈ W, (∀ i, p i → (U *ᵥ x) i = 0) → x = 0) :
    Module.finrank ℂ W ≤ Fintype.card {i // p i} := by
  let f : W →ₗ[ℂ] ({i // p i} → ℂ) :=
    { toFun := fun x i => (U *ᵥ (x : Fin n → ℂ)) i.1
      map_add' := fun x y => by
        ext i
        simp [mulVec_add]
      map_smul' := fun c x => by
        ext i
        simp [mulVec_smul] }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    apply h x x.2
    intro i hi
    exact congrFun hx ⟨i, hi⟩
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_pi] at h1

private theorem sig_eq_finrank {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (A B : Submodule ℂ (Fin n → ℂ)) (hAB : Module.finrank ℂ A + Module.finrank ℂ B = n)
    (hA : ∀ x ∈ A, x ≠ 0 → 0 < (star x ⬝ᵥ (H *ᵥ x)).re)
    (hB : ∀ x ∈ B, x ≠ 0 → (star x ⬝ᵥ (H *ᵥ x)).re < 0) :
    sigPosH hH = Module.finrank ℂ A := by
  set U : Matrix (Fin n) (Fin n) ℂ := star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hA' : Module.finrank ℂ A ≤ Fintype.card {i // 0 < hH.eigenvalues i} := by
    apply finrank_le_of_coord U (fun i => 0 < hH.eigenvalues i) A
    intro x hx hz
    by_contra hne
    have h1 := hA x hx hne
    rw [form_re_eq hH x] at h1
    have h2 : ∑ i, hH.eigenvalues i * Complex.normSq ((U *ᵥ x) i) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      by_cases hi : 0 < hH.eigenvalues i
      · rw [hz i hi]
        simp
      · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hi) (Complex.normSq_nonneg _)
    linarith
  have hB' : Module.finrank ℂ B ≤ Fintype.card {i // ¬ 0 < hH.eigenvalues i} := by
    apply finrank_le_of_coord U (fun i => ¬ 0 < hH.eigenvalues i) B
    intro x hx hz
    by_contra hne
    have h1 := hB x hx hne
    rw [form_re_eq hH x] at h1
    have h2 : 0 ≤ ∑ i, hH.eigenvalues i * Complex.normSq ((U *ᵥ x) i) := by
      apply Finset.sum_nonneg
      intro i _
      by_cases hi : 0 < hH.eigenvalues i
      · exact mul_nonneg hi.le (Complex.normSq_nonneg _)
      · rw [hz i hi]
        simp
    linarith
  have hc : Fintype.card {i // ¬ 0 < hH.eigenvalues i} =
      n - Fintype.card {i // 0 < hH.eigenvalues i} := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
  have hle : Fintype.card {i // 0 < hH.eigenvalues i} ≤ n := by
    simpa using Fintype.card_subtype_le (fun i => 0 < hH.eigenvalues i)
  have hs : sigPosH hH = Fintype.card {i // 0 < hH.eigenvalues i} := by
    unfold sigPosH
    exact Fintype.card_congr' rfl
  rw [hs]
  omega

theorem UpperTheory.hermitian_congruent_and_positive_eigenvector_of_signature :
    ∀ (n δ : ℕ) (H K J : Matrix (Fin n) (Fin n) ℂ) (e : ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian), (e = Complex.I ∨ e = -Complex.I) → J * J = -1 → ((-e) • (H * J)).PosDef → Matrix.trace J = e * (2 * (δ : ℂ) - (n : ℂ)) → K.det ≠ 0 → sigPosH hK = δ → (∃ Z : GL (Fin n) ℂ, H = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * K * (Z : Matrix (Fin n) (Fin n) ℂ)) ∧ (0 < δ → ∃ z : Fin n → ℂ, J *ᵥ z = e • z ∧ 0 < (star z ⬝ᵥ (H *ᵥ z)).re) := by
  intro n δ H K J e hH hK he hJJ hM htr hKdet hKsig
  have he2 : e * e = -1 := by
    rcases he with rfl | rfl <;> simp
  set E : Matrix (Fin n) (Fin n) ℂ := e • J with hEdef
  have hEE : E * E = 1 := by
    rw [hEdef, smul_mul_smul_comm, he2, hJJ, neg_smul, smul_neg, one_smul, neg_neg]
  have hJE : J = (-e) • E := by
    rw [hEdef, smul_smul, neg_mul, he2, neg_neg, one_smul]
  set P : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (1 - E) with hPdef
  have h2 : (1 - E) * (1 - E) = (2 : ℂ) • (1 - E) := by
    rw [sub_mul, mul_sub, mul_sub, _root_.one_mul, _root_.mul_one, _root_.one_mul, hEE, two_smul]
    abel
  have hPP : P * P = P := by
    rw [hPdef, smul_mul_smul_comm, h2, smul_smul]
    norm_num
  have hEP : E * P = -P := by
    rw [hPdef, Matrix.mul_smul, mul_sub, _root_.mul_one, hEE, ← smul_neg, neg_sub]
  set f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := Matrix.toLin' P with hfdef
  have hidem : IsIdempotentElem f := by
    show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hPP]
  have hJrange : ∀ x ∈ LinearMap.range f, J *ᵥ x = e • x := by
    rintro x ⟨y, rfl⟩
    rw [hfdef, Matrix.toLin'_apply, hJE, smul_mulVec, mulVec_mulVec, hEP, neg_mulVec,
      smul_neg, ← neg_smul, neg_neg]
  have hJker : ∀ x ∈ LinearMap.ker f, J *ᵥ x = (-e) • x := by
    intro x hx
    rw [LinearMap.mem_ker, hfdef, Matrix.toLin'_apply, hPdef, smul_mulVec, sub_mulVec,
      one_mulVec, smul_eq_zero] at hx
    have hx' : x = E *ᵥ x := by
      rcases hx with h | h
      · norm_num at h
      · exact (sub_eq_zero.1 h)
    rw [hJE, smul_mulVec, ← hx']
  have hform : ∀ x c, J *ᵥ x = c • x → ((-e) • (H * J)) *ᵥ x = ((-e) * c) • (H *ᵥ x) := by
    intro x c hx
    rw [smul_mulVec, ← mulVec_mulVec, hx, mulVec_smul, smul_smul]
  have hApos : ∀ x ∈ LinearMap.range f, x ≠ 0 → 0 < (star x ⬝ᵥ (H *ᵥ x)).re := by
    intro x hx hx0
    have h0 := hM.re_dotProduct_pos hx0
    rw [hform x e (hJrange x hx), neg_mul, he2, neg_neg, one_smul] at h0
    simpa using h0
  have hBneg : ∀ x ∈ LinearMap.ker f, x ≠ 0 → (star x ⬝ᵥ (H *ᵥ x)).re < 0 := by
    intro x hx hx0
    have h0 := hM.re_dotProduct_pos hx0
    rw [hform x (-e) (hJker x hx), neg_mul_neg, he2, neg_one_smul, dotProduct_neg] at h0
    have h1 : 0 < -(star x ⬝ᵥ (H *ᵥ x)).re := by simpa using h0
    linarith
  have hAB : Module.finrank ℂ (LinearMap.range f) + Module.finrank ℂ (LinearMap.ker f) = n := by
    rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]
  have htrP : P.trace = (δ : ℂ) := by
    rw [hPdef, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one, hEdef, Matrix.trace_smul, htr,
      Fintype.card_fin, smul_eq_mul, smul_eq_mul]
    linear_combination (-(2 * (δ : ℂ) - (n : ℂ)) / 2) * he2
  have hrank : Module.finrank ℂ (LinearMap.range f) = δ := by
    have h0 := (LinearMap.IsIdempotentElem.isProj_range f hidem).trace
    rw [hfdef, Matrix.trace_toLin'_eq, htrP] at h0
    exact_mod_cast h0.symm
  have hsig : sigPosH hH = δ := by
    rw [sig_eq_finrank hH _ _ hAB hApos hBneg, hrank]
  have hHdet : H.det ≠ 0 := by
    intro h0
    have hd := hM.det_pos
    rw [Matrix.det_smul, Matrix.det_mul, h0, zero_mul, mul_zero] at hd
    exact lt_irrefl _ hd
  refine ⟨?_, ?_⟩
  · obtain ⟨Z, hZ⟩ := HermCongruence.congr_of_sigPosH_eq K H hK hH hKdet hHdet (by rw [hKsig, hsig])
    exact ⟨Z, hZ⟩
  · intro hδ
    have hpos : 0 < Module.finrank ℂ (LinearMap.range f) := hrank ▸ hδ
    obtain ⟨⟨z, hzA⟩, hz0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
    have hz0' : z ≠ 0 := fun h => hz0 (Subtype.ext h)
    exact ⟨z, hJrange z hzA, hApos z hzA hz0'⟩
