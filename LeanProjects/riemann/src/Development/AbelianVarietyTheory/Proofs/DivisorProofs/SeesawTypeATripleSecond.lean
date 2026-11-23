import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEtaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementForm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.StabLawA

open Matrix

theorem form_herm {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {N : ℕ}
    {J : Matrix (Fin N) (Fin N) E} (hh : ∀ i j, σ (J j i) = J i j) (a b : Fin N → E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J a b = σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b a) := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hh]; ring

theorem det_ne_of_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n r s : ℕ}
    (B : Base F E) (J : Matrix (Fin n) (Fin n) E) (h : ∀ w, HasSig (J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  obtain ⟨hrs, A, hA⟩ := h w
  have hM : (J.map (B.emb w).1).det ≠ 0 := by
    let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
    let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
    have h1 : A'ᵀ * J.map (B.emb w).1 * A'.map star =
        (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
      rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
    have h2 : (A'ᵀ * J.map (B.emb w).1 * A'.map star).det ≠ 0 := by
      rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
      simp [Matrix.det_neg]
    intro h0
    apply h2
    rw [Matrix.det_mul, Matrix.det_mul, h0]; simp
  intro h0; apply hM
  have e := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e
  rw [← e, h0, map_zero]

theorem cA_inclR' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.includeRight_apply]

set_option maxHeartbeats 1000000 in

theorem exists_levi_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (hσ : ∀ x, σ (σ x) = x)
    (hh : ∀ i j, σ (Y.J j i) = Y.J i j) (hn : n = n₁ + 2) (hxx : form σ Y.J H.x H.x = 0) (hyy : form σ Y.J H.y H.y = 0)
    (hxy : form σ Y.J H.x H.y = 1) (horth : ∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0)
    (hgram : H.ιᵀ * Y.J * H.ι.map σ = Y₁.J) (hdet : Y₁.J.det ≠ 0) (h₁ : UA σ Y₁.J) :
    ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) H 1 h₁ m := by
  subst hn
  set XY : Matrix (Fin (n₁ + 2)) (Fin 2) E := Matrix.of fun r t => ![H.x, H.y] t r with hXY
  set Q : Matrix (Fin (n₁ + 2)) (Fin n₁ ⊕ Fin 2) E := fromCols H.ι XY with hQ
  set S₂ : Matrix (Fin 2) (Fin 2) E := !![0, 1; 1, 0] with hS₂
  have hyx : form σ Y.J H.y H.x = 1 := by rw [form_herm hσ hh, hxy, map_one]
  have horth' : ∀ i, form σ Y.J (fun r => H.ι r i) H.x = 0 ∧ form σ Y.J (fun r => H.ι r i) H.y = 0 := by
    intro i
    have e : (fun r => H.ι r i) = H.ι *ᵥ Pi.single i 1 := by
      funext r; simp [mulVec, dotProduct, Pi.single_apply]
    rw [e]; exact horth _
  have hK : Qᵀ * Y.J * Q.map σ = fromBlocks Y₁.J 0 0 S₂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [fromBlocks_apply₁₁, ← hgram, GlobalTheory.LeviPlaneSection.gram_apply, GlobalTheory.LeviPlaneSection.gram_apply]; rfl
    · rw [fromBlocks_apply₁₂, GlobalTheory.LeviPlaneSection.gram_apply]
      fin_cases j
      · simpa [Q, XY] using (horth' i).1
      · simpa [Q, XY] using (horth' i).2
    · rw [fromBlocks_apply₂₁, GlobalTheory.LeviPlaneSection.gram_apply, form_herm hσ hh]
      fin_cases i
      · simp [Q, XY, (horth' j).1]
      · simp [Q, XY, (horth' j).2]
    · rw [fromBlocks_apply₂₂, GlobalTheory.LeviPlaneSection.gram_apply]
      fin_cases i <;> fin_cases j <;> simp [Q, XY, S₂, hxx, hyy, hxy, hyx]
  have hdetK : (fromBlocks Y₁.J 0 0 S₂).det ≠ 0 := by
    rw [det_fromBlocks_zero₂₁]; simp [S₂, Matrix.det_fin_two_of, hdet]
  have hKu : IsUnit (fromBlocks Y₁.J 0 0 S₂).det := isUnit_iff_ne_zero.2 hdetK
  set R : Matrix (Fin n₁ ⊕ Fin 2) (Fin (n₁ + 2)) E := ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J).map σ with hR
  have h0 : (fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ = 1 := by
    have : (fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ = (fromBlocks Y₁.J 0 0 S₂)⁻¹ * (Qᵀ * Y.J * Q.map σ) := by
      simp only [Matrix.mul_assoc]
    rw [this, hK, nonsing_inv_mul _ hKu]
  have hQQ : (Q.map σ).map (σ : E →+* E) = Q := by ext i j; simp [hσ]
  have hRQ : R * Q = 1 := by
    calc R * Q = ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J).map (σ : E →+* E) * (Q.map σ).map (σ : E →+* E) := by
          rw [hQQ]; rfl
      _ = ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ).map (σ : E →+* E) := Matrix.map_mul.symm
      _ = 1 := by rw [h0]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hQR : Q * R = 1 := (mul_eq_one_comm_of_equiv finSumFinEquiv).1 hRQ
  set f : E →+* AE F E := inclR (F := F) (AF F) with hf
  have hRQA : R.map f * Q.map f = 1 := by rw [← Matrix.map_mul, hRQ, Matrix.map_one f (map_zero f) (map_one f)]
  have hQRA : Q.map f * R.map f = 1 := by rw [← Matrix.map_mul, hQR, Matrix.map_one f (map_zero f) (map_one f)]
  have hcf : ∀ {a b : Type} (X : Matrix a b E), (X.map f).map (cA σ) = (X.map σ).map f := fun X => by
    ext i j; exact cA_inclR' σ _
  have hKA : (Q.map f)ᵀ * incM F Y.J * (Q.map f).map (cA σ).toRingHom = fromBlocks (incM F Y₁.J) 0 0 (S₂.map f) := by
    change (Q.map f)ᵀ * Y.J.map f * (Q.map f).map (cA σ) = fromBlocks (Y₁.J.map f) 0 0 (S₂.map f)
    rw [hcf, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hK, fromBlocks_map]
    simp
  let φ := GlobalTheory.LeviPlaneSection.conjHom hRQA hQRA
  have hmem : Units.map φ h₁.1 ∈ UG (cA σ) (incM F Y.J) := by
    show (GlobalTheory.LeviPlaneSection.conjM (Q.map f) (R.map f) (h₁.1 : Matrix _ _ (AE F E)))ᵀ * incM F Y.J *
      (GlobalTheory.LeviPlaneSection.conjM (Q.map f) (R.map f) (h₁.1 : Matrix _ _ (AE F E))).map (cA σ) = incM F Y.J
    exact GlobalTheory.LeviPlaneSection.conjM_unitary (cA σ).toRingHom hKA hQRA h₁.2
  let m : UA σ Y.J := ⟨Units.map φ h₁.1, hmem⟩
  have hmat : mat m = GlobalTheory.LeviPlaneSection.conjM (Q.map f) (R.map f) (mat h₁) := rfl
  refine ⟨m, ?_⟩
  have hMQ : mat m * Q.map f = Q.map f * fromBlocks (mat h₁) 0 0 (1 : Matrix (Fin 2) (Fin 2) (AE F E)) := by
    rw [hmat]; unfold GlobalTheory.LeviPlaneSection.conjM; rw [Matrix.mul_assoc, hRQA, Matrix.mul_one]
  have hcol : ∀ t : Fin 2, mat m *ᵥ (fun r => f (XY r t)) = fun r => f (XY r t) := by
    intro t
    have e1 : (fun r => f (XY r t)) = Q.map f *ᵥ Pi.single (Sum.inr t) 1 := by
      funext r; simp [Q, mulVec, dotProduct, Pi.single_apply]
    have e2 : fromBlocks (mat h₁) 0 0 (1 : Matrix (Fin 2) (Fin 2) (AE F E)) *ᵥ Pi.single (Sum.inr t) 1 =
        Pi.single (Sum.inr t) 1 := by
      ext i; rcases i with i | i <;> simp [mulVec, dotProduct, Pi.single_apply, one_apply, Fintype.sum_sum_type]
    rw [e1, mulVec_mulVec, hMQ, ← mulVec_mulVec, e2]
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_one, one_smul]; exact hcol 0
  · rw [inv_one, Units.val_one, map_one, one_smul]; exact hcol 1
  · have e3 : incM F H.ι = Q.map f * fromRows (1 : Matrix (Fin n₁) (Fin n₁) (AE F E)) (0 : Matrix (Fin 2) (Fin n₁) (AE F E)) := by
      ext r k; simp [incM, Q, mul_apply, Fintype.sum_sum_type, one_apply, hf]
    have e4 : fromBlocks (mat h₁) 0 0 (1 : Matrix (Fin 2) (Fin 2) (AE F E)) *
        fromRows (1 : Matrix (Fin n₁) (Fin n₁) (AE F E)) (0 : Matrix (Fin 2) (Fin n₁) (AE F E)) =
        fromRows (1 : Matrix (Fin n₁) (Fin n₁) (AE F E)) (0 : Matrix (Fin 2) (Fin n₁) (AE F E)) * mat h₁ := by
      ext i k; rcases i with i | i <;> simp [mul_apply, Fintype.sum_sum_type, one_apply]
    rw [e3, ← Matrix.mul_assoc, hMQ, Matrix.mul_assoc, e4, Matrix.mul_assoc]

theorem resEtaPow_div' {R E : Type} [CommRing R] [CommRing E] [Algebra R E] [Invertible (2 : R)] {K : Subgroup Rˣ}
    {χ₁ χ₂ : Eˣ →* Circle} {m n : ℕ} (h₁ : ResEtaPow K χ₁ m) (h₂ : ResEtaPow K χ₂ n) :
    ResEtaPow K (χ₁ / χ₂) (m + n) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h₁ x, h₂ x]
  split_ifs
  · simp
  · have h : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [div_eq_iff (pow_ne_zero _ (by norm_num)), pow_add, mul_assoc, h, mul_one]

theorem isHecke_div' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {χ₁ χ₂ : Chr F E}
    (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) :=
  ⟨h₁.1.div' h₂.1, fun x => by rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x]; exact div_self' 1⟩

theorem incM_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem vecMulVec_mul_transpose {R : Type} [CommRing R] {k l p : ℕ} (a : Fin k → R) (b : Fin p → R)
    (M : Matrix (Fin l) (Fin p) R) : Matrix.vecMulVec a b * Mᵀ = Matrix.vecMulVec a (M *ᵥ b) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

end GlobalTheory.StabLawA

open GlobalTheory.StabLawA in

theorem GlobalTheory.StabLawA.evalA_stab_law : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (k : UA σ G.V.J) (l : (AE F E)ˣ) (g₁ : UA σ G₁.V.J), mat k *ᵥ incV F H.x = (l : AE F E) • incV F H.x → (∀ z : Fin b → AE F E, ∃ a : AE F E, mat k *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat g₁ *ᵥ z) + a • incV F H.x) →
      ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), e (om (k, 1) Ψ) = (((X.β / X.α) l : ℂ) * (((absE F E l : ℝ) ^ (((b + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ)) • om₁ (g₁, 1) (e Ψ) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' cfg T T₁ e hev k l g₁ hkx hkι Ψ hΨ
  have P : IsPair B G.M X.β (X.β / X.α) om (b + 2 - G.p) G.p _ _ :=
    ⟨T.base, T.geo.hV, T.geo.hW, T.geo.hM, T.chars.heckeβ, GlobalTheory.StabLawA.isHecke_div' T.chars.heckeβ T.chars.heckeα,
      T.chars.resβ, GlobalTheory.StabLawA.resEtaPow_div' T.chars.resβ T.chars.resα, T.weil⟩
  have P₁ : IsPair B G₁.M X.β (X.β / X.α) om₁ (b - G₁.p) G₁.p _ _ :=
    ⟨T₁.base, T₁.geo.hV, T₁.geo.hW, T₁.geo.hM, T₁.chars.heckeβ, GlobalTheory.StabLawA.isHecke_div' T₁.chars.heckeβ T₁.chars.heckeα,
      T₁.chars.resβ, GlobalTheory.StabLawA.resEtaPow_div' T₁.chars.resβ T₁.chars.resα, T₁.weil⟩

  obtain ⟨Ma, hMa⟩ := GlobalTheory.T.exists_good_schrodinger_model F E σ B T.base (b + 2) (b + a') G.V G₁.W _ _ _ _ T.geo.hV T₁.geo.hW
  obtain ⟨oma, hwa⟩ := GlobalTheory.T.hecke_characters_restriction_eta hKP.base F E σ B T.base (b + 2) (b + a') G.V G₁.W _ _ _ _ T.geo.hV T₁.geo.hW Ma hMa
    X.β (X.β / X.α) T.chars.heckeβ (GlobalTheory.StabLawA.isHecke_div' T.chars.heckeβ T.chars.heckeα) T.chars.resβ
    (GlobalTheory.StabLawA.resEtaPow_div' T₁.chars.resβ T₁.chars.resα)
  have Pa : IsPair B Ma X.β (X.β / X.α) oma (b + 2 - G.p) G.p _ _ :=
    ⟨T.base, T.geo.hV, T₁.geo.hW, hMa, T.chars.heckeβ, GlobalTheory.StabLawA.isHecke_div' T.chars.heckeβ T.chars.heckeα,
      T.chars.resβ, GlobalTheory.StabLawA.resEtaPow_div' T₁.chars.resβ T₁.chars.resα, hwa⟩

  obtain ⟨e₁, he₁⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hKP.base).1 F E σ B (b + 2) (b + 2 + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P
    (b + a') G.V G₁.W H' 0 (b + 1) Ma rfl cfg.hH' hMa).1
  obtain ⟨⟨e₂, he₂⟩, law₂⟩ := GlobalTheory.T.adapted_plane_first_variable hKP.base F E σ B (b + 2) (b + a') G.V G₁.W Ma X.β (X.β / X.α) oma _ _ _ _ Pa
    b G₁.V H 0 (b + 1) G₁.M om₁ _ _ cfg.hH P₁

  have heisC : ∀ (z : Matrix (Fin b) (Fin (b + a')) (AE F E)), ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      (e₂ ∘ₗ e₁) (G.M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = G₁.M.co.rho B.ψ z ((e₂ ∘ₗ e₁) Φ) := by
    intro z Φ hΦ
    have h1 := he₁.Heisenberg₂ (incM F H.ι * z) Φ hΦ
    have h2 := he₂.Heisenberg₂ z (e₁ Φ) (he₁.maps Φ hΦ)
    rw [GlobalTheory.StabLawA.incM_one', Matrix.one_mul] at h1
    rw [GlobalTheory.StabLawA.incM_one', Matrix.transpose_one, Matrix.mul_one] at h2
    simp only [LinearMap.comp_apply]
    rw [h1, h2]
  have invC : ∀ u ∈ isoA H H', ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      (e₂ ∘ₗ e₁) (G.M.co.rho B.ψ u Φ) = (e₂ ∘ₗ e₁) Φ := by
    intro u hu Φ hΦ
    simp only [LinearMap.comp_apply]
    rcases hu with hu | ⟨z, rfl⟩
    · rw [he₁.inv u hu Φ hΦ]
    · have h1 := he₁.Heisenberg₂ (Matrix.vecMulVec (incV F H.x) z) Φ hΦ
      rw [GlobalTheory.StabLawA.incM_one', Matrix.one_mul, GlobalTheory.StabLawA.vecMulVec_mul_transpose] at h1
      rw [h1, he₂.inv _ ⟨z, rfl⟩ _ (he₁.maps Φ hΦ)]
  obtain ⟨c, hc⟩ := GlobalTheory.T.pair_double_descent hKP.base F E σ B (b + 2) (b + 2 + a') b (b + a') G.V G.W G₁.V G₁.W G.M X.β (X.β / X.α) om
    _ _ _ _ P H H' 0 (b + 1) 0 (b + 1) G₁.M cfg.hH cfg.hH' T₁.geo.hM e hev (e₂ ∘ₗ e₁) heisC invC
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.pair_double_descent_models hKP.base F E σ B (b + 2) (b + 2 + a') b (b + a') G.V G.W G₁.V G₁.W G.M X.β (X.β / X.α) om
    _ _ _ _ P H H' 0 (b + 1) 0 (b + 1) Ma oma _ _ G₁.M cfg.hH cfg.hH' Pa T₁.geo.hM e₁ e₂ he₁ he₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne
    have := hc Φ₀ hΦ₀
    rw [zero_smul, LinearMap.comp_apply] at this
    exact this

  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.LeviTorusH.sigma_invol T.base.cm
  obtain ⟨mt, hmt⟩ := GlobalTheory.LeviTorusH.exists_levi hKP.base F E σ B (b + 2) (b + a') G.V G₁.W Ma X.β (X.β / X.α) oma _ _ _ _ Pa
    b G₁.V H 0 (b + 1) G₁.M om₁ _ _ cfg.hH P₁ l
  obtain ⟨mg, hmg⟩ := exists_levi_one G.V G₁.V H hσ T.geo.hV.herm cfg.hH.rank cfg.hH.xx cfg.hH.yy cfg.hH.xy cfg.hH.orth
    cfg.hH.gram (det_ne_of_sig B G₁.V.J T₁.geo.hV.sig) g₁
  set m := mt * mg with hm
  have hmul : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (x y : UA σ J), mat (x * y) = mat x * mat y := fun _ _ => rfl
  have hone : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, mat (1 : UA σ J) = 1 := rfl
  have hL : IsLevi (W₁ := G₁.V) H l g₁ m := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hm, hmul, ← Matrix.mulVec_mulVec, hmg.1, Units.val_one, one_smul, hmt.1]
    · rw [hm, hmul, ← Matrix.mulVec_mulVec, hmg.2.1, inv_one, Units.val_one, map_one, one_smul, hmt.2.1]
    · rw [hm, hmul, Matrix.mul_assoc, hmg.2.2, ← Matrix.mul_assoc, hmt.2.2, hone, Matrix.mul_one]
  have hinvL : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (x : UA σ J), mat x⁻¹ * mat x = 1 := fun x => by
    rw [← hmul, inv_mul_cancel, hone]
  have hinvR : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (x : UA σ J), mat x * mat x⁻¹ = 1 := fun x => by
    rw [← hmul, mul_inv_cancel, hone]
  have hmx : mat m⁻¹ *ᵥ incV F H.x = ((l⁻¹ : (AE F E)ˣ) : AE F E) • incV F H.x := by
    have h := congrArg (fun v => ((l⁻¹ : (AE F E)ˣ) : AE F E) • (mat m⁻¹ *ᵥ v)) hL.1
    simp only [Matrix.mulVec_mulVec, hinvL, Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, Units.inv_mul,
      one_smul] at h
    exact h.symm
  have hmι : mat m⁻¹ * incM F H.ι = incM F H.ι * mat g₁⁻¹ := by
    calc mat m⁻¹ * incM F H.ι = mat m⁻¹ * (incM F H.ι * (mat g₁ * mat g₁⁻¹)) := by rw [hinvR, Matrix.mul_one]
      _ = mat m⁻¹ * (mat m * incM F H.ι) * mat g₁⁻¹ := by rw [hL.2.2]; simp only [Matrix.mul_assoc]
      _ = incM F H.ι * mat g₁⁻¹ := by rw [← Matrix.mul_assoc, hinvL, Matrix.one_mul]
  have hu : k * m⁻¹ ∈ unip σ G.V H := by
    apply Subgroup.subset_closure
    refine ⟨?_, fun z => ?_⟩
    · rw [hmul, ← Matrix.mulVec_mulVec, hmx, Matrix.mulVec_smul, hkx, smul_smul, Units.inv_mul, one_smul]
    · obtain ⟨a, ha⟩ := hkι (mat g₁⁻¹ *ᵥ z)
      refine ⟨a, ?_⟩
      have e1 : mat m⁻¹ *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat g₁⁻¹ *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, hmι, ← Matrix.mulVec_mulVec]
      have e2 : mat g₁ *ᵥ (mat g₁⁻¹ *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, hinvR, Matrix.one_mulVec]
      rw [hmul, ← Matrix.mulVec_mulVec, e1, ha, e2]
  have hk : k = (k * m⁻¹) * m := by rw [mul_assoc, inv_mul_cancel, mul_one]

  have hpres : om (k, 1) Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := (T.weil.isUSplitting).pres _ _ hΨ
  have hL1 : IsLevi (W₁ := G₁.W) H' 1 (1 : UA σ G₁.W.J) (1 : UA σ G.W.J) := by
    refine ⟨?_, ?_, ?_⟩
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _)
      simp
  have key : e₂ (e₁ (om (k, 1) Ψ)) = (((X.β / X.α) l : ℂ) * (((absE F E l : ℝ) ^ (((b + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ)) •
      om₁ (g₁, 1) (e₂ (e₁ Ψ)) := by
    have h1 := GlobalTheory.T.adapted_plane_second_variable hKP.base F E σ B (b + 2) (b + 2 + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P (b + a') G₁.W H'
      0 (b + 1) Ma oma _ _ cfg.hH' Pa e₁ he₁ k 1 1 1 hL1 1 (Subgroup.one_mem _) Ψ hΨ
    have h2 := law₂ e₂ he₂ 1 l g₁ m hL (k * m⁻¹) hu (e₁ Ψ) (he₁.maps Ψ hΨ)
    simp only [one_mul, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] at h1
    rw [← hk] at h2
    rw [h1, h2]
  calc e (om (k, 1) Ψ) = c⁻¹ • (c • e (om (k, 1) Ψ)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = c⁻¹ • ((((X.β / X.α) l : ℂ) * (((absE F E l : ℝ) ^ (((b + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ)) • om₁ (g₁, 1) (c • e Ψ)) := by
        rw [← hc _ hpres, ← hc _ hΨ]
        simp only [LinearMap.comp_apply]
        rw [key]
    _ = _ := by rw [map_smul, smul_comm _ c, smul_smul, inv_mul_cancel₀ hc0, one_smul]
