import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PeriodsLactSymplectic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableNormSiegelThetaSeriesTerms
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEq
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsWeilOfSymplecticStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CanonicalThetaExponentSymplecticInvariantStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LactMulFrame

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.UnAct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem exists_mem_dom (X : Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show FD.gram τ.1 X.Gm (mat (fun τ => P τ) τ) = FD.gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0

omit [NumberField E] [IsCMField E] in

theorem lact_one' {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  change (1 : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

omit [NumberField E] [IsCMField E] in

theorem lact_mul' {Ψ : Finset (E →+* ℂ)} (γ' γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ' * γ) x = lact γ' (lact γ x) := by
  first
  | exact @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame
  | exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame
  | (apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame ..)

theorem isUn_mul {γ' γ : GL (Fin r) E} (h' : IsUn X γ') (h : IsUn X γ) : IsUn X (γ' * γ) := by
  intro u v
  rw [Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, h', h]

theorem tauMat_mem (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    tauMat X bas idx x ∈ Siegel (Fin g) :=
  ⟨tauMat_isSymm idx hs hx, tauMat_im_posDef idx hs hx⟩

theorem eq_of_thA_eq (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {φ ψ : TF n g}
    (hφ : IsSB φ) (hψ : IsSB ψ) (h : thA X bas idx φ x = thA X bas idx ψ x) : φ = ψ := by
  refine eq_of_thS_eq _ _ φ ψ hφ hψ _ (tauMat_mem idx hs hx) fun ζ => ?_
  have h1 := congrFun h fun k => perMat X bas idx Sum.inl x *ᵥ ζ k
  simp only [thA, mulVec_mulVec, hMat_mul_perMat idx hs hx, one_mulVec] at h1
  exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ (isUnit_det_hMat idx hs hx).ne_zero)
    (Complex.exp_ne_zero _)) h1

theorem thA_add (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {φ ψ : TF n g}
    (hφ : IsSB φ) (hψ : IsSB ψ) :
    thA X bas idx (φ + ψ) x = thA X bas idx φ x + thA X bas idx ψ x := by
  funext z
  have h1 := (SiegelSum.summable_norm_thetaTerm _ _ φ hφ _ (tauMat_mem idx hs hx)
    fun k => hMat X bas idx x *ᵥ z k).of_norm
  have h2 := (SiegelSum.summable_norm_thetaTerm _ _ ψ hψ _ (tauMat_mem idx hs hx)
    fun k => hMat X bas idx x *ᵥ z k).of_norm
  simp only [thA, thS, Pi.add_apply, add_mul]
  rw [h1.tsum_add h2, mul_add]

theorem thA_smul (x : Frame X.Ψ r) (a : ℂ) (φ : TF n g) :
    thA X bas idx (a • φ) x = a • thA X bas idx φ x := by
  funext z
  simp only [thA, thS, Pi.smul_apply, smul_eq_mul, mul_assoc a, tsum_mul_left]
  ring

theorem exists_weil (hs : IsSympl X bas) (hn : Even n) {γ : GL (Fin r) E} (hγ : IsUn X γ) :
    ∃ ω : TF n g → TF n g, ∀ φ, IsSB φ → IsSB (ω φ) ∧
      (∀ x ∈ X.dom, thA X bas idx (ω φ) (lact γ x) = thA X bas idx φ x) ∧
      ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  obtain ⟨σ, hσ, h⟩ := periods_lact_symplectic E r X g bas idx n hs hn γ hγ
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_weil_of_symplectic' (Fin n) (Fin g) σ (by simpa using hn) hσ
  refine ⟨ω, fun φ hφ => ⟨(hω φ hφ).1, fun x hx => ?_, (hω φ hφ).2.2⟩⟩
  obtain ⟨-, hτ, h1, h2⟩ := h x hx
  funext z
  have h3 := (hω φ hφ).2.1 _ hτ fun k => hMat X bas idx x *ᵥ z k
  have h4 := Finset.sum_congr (s₁ := Finset.univ) rfl fun (k : Fin n) _ =>
    GlobalTheory.T.canonicalThetaExponent_symplectic_invariant _ σ hσ _ hτ (hMat X bas idx x *ᵥ z k)
  have hd := (GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle _ σ hσ _ hτ).1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h4
  have h5 (k) : hMat X bas idx (lact γ x) *ᵥ z k =
      (hMat X bas idx x *ᵥ z k) ᵥ* (spDen σ (tauMat X bas idx x))⁻¹ := by
    rw [h2, ← mulVec_mulVec, mulVec_transpose]
  have h6 : (hMat X bas idx (lact γ x)).det =
      (spDen σ (tauMat X bas idx x)).det⁻¹ * (hMat X bas idx x).det := by
    rw [h2, det_mul, det_transpose, det_nonsing_inv, Ring.inverse_eq_inv']
  simp only [thA, h5, imInv_eq, h1, h6]
  rw [h3, ← h4, Fintype.card_fin, mul_add, Complex.exp_add, mul_pow, inv_pow]
  have h7 := pow_ne_zero (n / 2) hd
  rw [show ∀ t : ℂ, (π : ℂ) / 2 * (2 * I * t) = π * I * t from fun t => by ring]
  field_simp

theorem wG_eq (hs : IsSympl X bas) {γ : GL (Fin r) E} (hγ : IsUn X γ) {φ ψ : TF n g}
    (hψ : IsSB ψ) (h : ∀ x ∈ X.dom, thA X bas idx ψ (lact γ x) = thA X bas idx φ x) :
    wG X bas idx γ φ = ψ := by
  have he : ∃ ψ : TF n g, IsSB ψ ∧ ∀ x ∈ X.dom, thA X bas idx ψ (lact γ x) = thA X bas idx φ x :=
    ⟨ψ, hψ, h⟩
  obtain ⟨x, hx⟩ := exists_mem_dom X
  rw [wG, dif_pos he]
  exact eq_of_thA_eq idx hs (hγ.lact_mem hx) he.choose_spec.1 hψ
    ((he.choose_spec.2 x hx).trans (h x hx).symm)

theorem herm_lact (hs : IsSympl X bas) {γ : GL (Fin r) E} (hγ : IsUn X γ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (u v : Fin g → ℂ) :
    (hMat X bas idx (lact γ x) *ᵥ u) ⬝ᵥ imInv X bas idx (lact γ x) *ᵥ
        star (hMat X bas idx (lact γ x) *ᵥ v) =
      (hMat X bas idx x *ᵥ u) ⬝ᵥ imInv X bas idx x *ᵥ star (hMat X bas idx x *ᵥ v) := by
  obtain ⟨σ, hσ, h⟩ := periods_lact_symplectic E r X g bas idx 0 hs Even.zero γ hγ
  obtain ⟨hx', hτ, h1, h2⟩ := h x hx
  obtain ⟨hd, -, -, h3, -⟩ := GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle _ σ hσ _ hτ
  have h4 : imInv X bas idx x = (spDen σ (tauMat X bas idx x))⁻¹ * imInv X bas idx (lact γ x) *
      ((spDen σ (tauMat X bas idx x))⁻¹)ᴴ := by
    rw [← (imInv_isSymm idx hs hx).eq, ← (imInv_isSymm idx hs hx').eq, imInv_eq, imInv_eq, ← h3, h1,
      Matrix.mul_inv_rev, Matrix.mul_inv_rev, transpose_mul, transpose_mul,
      ← transpose_nonsing_inv (spDen _ _), transpose_transpose, conjTranspose_nonsing_inv,
      transpose_nonsing_inv (Matrix.map (spDen _ _) _)]
    rfl
  rw [h4, h2, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, mulVec_transpose, star_vecMul,
    ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec _ (spDen _ _)⁻¹]

end GlobalTheory.SW.UnAct

namespace GlobalTheory.SW

open UnAct

theorem wG_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∀ φ : TF n g, IsSB φ → IsSB (wG X bas idx γ φ) ∧ (∀ x ∈ X.dom, thA X bas idx (wG X bas idx γ φ) (lact γ x) = thA X bas idx φ x) ∧ (∀ ψ, IsSB ψ → ip (wG X bas idx γ φ) (wG X bas idx γ ψ) = ip φ ψ ∧ wG X bas idx γ (φ + ψ) = wG X bas idx γ φ + wG X bas idx γ ψ ∧ ∀ x ∈ X.dom, thA X bas idx φ x = thA X bas idx ψ x → φ = ψ) ∧ (∀ a : ℂ, wG X bas idx γ (a • φ) = a • wG X bas idx γ φ) ∧ wG X bas idx 1 φ = φ ∧ (∀ γ', IsUn X γ' → wG X bas idx (γ' * γ) φ = wG X bas idx γ' (wG X bas idx γ φ)) ∧ ∀ y : Matrix (Fin n) (Fin r) E, wG X bas idx γ (heisG X bas y φ) = heisG X bas (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) (wG X bas idx γ φ) := by
  intro E _ _ _ r X g bas idx n hs hn
  have key : ∀ γ, IsUn X γ → ∀ φ : TF n g, IsSB φ → IsSB (wG X bas idx γ φ) ∧
      (∀ x ∈ X.dom, thA X bas idx (wG X bas idx γ φ) (lact γ x) = thA X bas idx φ x) ∧
      ∀ ψ, IsSB ψ → ip (wG X bas idx γ φ) (wG X bas idx γ ψ) = ip φ ψ := by
    intro γ hγ φ hφ
    obtain ⟨ω, hω⟩ := exists_weil idx hs hn hγ
    have e : ∀ ψ, IsSB ψ → wG X bas idx γ ψ = ω ψ := fun ψ hψ =>
      wG_eq idx hs hγ (hω ψ hψ).1 (hω ψ hψ).2.1
    rw [e φ hφ]
    exact ⟨(hω φ hφ).1, (hω φ hφ).2.1, fun ψ hψ => by rw [e ψ hψ]; exact (hω φ hφ).2.2 ψ hψ⟩
  intro γ hγ φ hφ
  obtain ⟨k1, k2, k3⟩ := key γ hγ φ hφ
  refine ⟨k1, k2, fun ψ hψ => ⟨k3 ψ hψ, ?_, fun x hx => eq_of_thA_eq idx hs hx hφ hψ⟩,
    fun a => ?_, ?_, fun γ' hγ' => ?_, fun y => ?_⟩
  · obtain ⟨l1, l2, -⟩ := key γ hγ ψ hψ
    refine wG_eq idx hs hγ (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ k1 l1).1 fun x hx => ?_
    rw [thA_add idx hs (hγ.lact_mem hx) k1 l1, thA_add idx hs hx hφ hψ, k2 x hx, l2 x hx]
  · refine wG_eq idx hs hγ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ k1 k1).2.1 a) fun x hx => ?_
    rw [thA_smul, thA_smul, k2 x hx]
  · exact wG_eq idx hs (fun u v => by simp) hφ fun x _ => by rw [lact_one']
  · obtain ⟨l1, l2, -⟩ := key γ' hγ' _ k1
    refine wG_eq idx hs (isUn_mul hγ' hγ) l1 fun x hx => ?_
    rw [lact_mul', l2 _ (hγ.lact_mem hx), k2 x hx]
  · obtain ⟨-, -, -, hH⟩ := heisG_laws E r X g bas idx n hs hn
    refine wG_eq idx hs hγ (hH _ _ k1).1 fun x hx => ?_
    funext z
    have hy (k) : per X (lact γ x) ((y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) k) = per X x (y k) := by
      rw [← per_lact x hγ]
      congr 1
      funext i
      simp only [mul_apply, transpose_apply, mulVec, dotProduct, mul_comm]
    rw [(hH _ _ k1).2.2.2.2 _ (hγ.lact_mem hx), (hH _ _ hφ).2.2.2.2 _ hx, k2 x hx]
    simp only [hy, herm_lact idx hs hγ hx]

end GlobalTheory.SW
