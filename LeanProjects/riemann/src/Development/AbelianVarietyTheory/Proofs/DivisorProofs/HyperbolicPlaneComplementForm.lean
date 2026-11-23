import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.LeviPlaneSection

open Matrix

section Alg

variable {S : Type*} [CommRing S] {m : Type*} [Fintype m] [DecidableEq m] {k : ℕ}

def conjM (Q : Matrix m (Fin k ⊕ Fin 2) S) (R : Matrix (Fin k ⊕ Fin 2) m S) (a : Matrix (Fin k) (Fin k) S) :
    Matrix m m S :=
  Q * fromBlocks a (0 : Matrix (Fin k) (Fin 2) S) 0 (1 : Matrix (Fin 2) (Fin 2) S) * R

theorem conjM_mul {Q : Matrix m (Fin k ⊕ Fin 2) S} {R : Matrix (Fin k ⊕ Fin 2) m S} (hRQ : R * Q = 1)
    (a b : Matrix (Fin k) (Fin k) S) : conjM Q R a * conjM Q R b = conjM Q R (a * b) := by
  have h : fromBlocks a 0 0 1 * (R * Q) * fromBlocks b 0 0 (1 : Matrix (Fin 2) (Fin 2) S) = fromBlocks (a * b) 0 0 1 := by
    rw [hRQ, Matrix.mul_one, fromBlocks_multiply]; simp
  unfold conjM
  rw [← h]; simp only [Matrix.mul_assoc]

theorem conjM_one {Q : Matrix m (Fin k ⊕ Fin 2) S} {R : Matrix (Fin k ⊕ Fin 2) m S} (hQR : Q * R = 1) :
    conjM Q R (1 : Matrix (Fin k) (Fin k) S) = 1 := by
  unfold conjM; rw [fromBlocks_one, Matrix.mul_one, hQR]

def conjHom {Q : Matrix m (Fin k ⊕ Fin 2) S} {R : Matrix (Fin k ⊕ Fin 2) m S} (hRQ : R * Q = 1) (hQR : Q * R = 1) :
    Matrix (Fin k) (Fin k) S →* Matrix m m S where
  toFun := conjM Q R
  map_one' := conjM_one hQR
  map_mul' a b := (conjM_mul hRQ a b).symm

theorem conjM_map {T : Type*} [CommRing T] (f : S →+* T) (Q : Matrix m (Fin k ⊕ Fin 2) S) (R : Matrix (Fin k ⊕ Fin 2) m S)
    (a : Matrix (Fin k) (Fin k) S) : (conjM Q R a).map f = conjM (Q.map f) (R.map f) (a.map f) := by
  simp [conjM, Matrix.map_mul, fromBlocks_map]

theorem conjM_unitary (c : S →+* S) {Q : Matrix m (Fin k ⊕ Fin 2) S} {R : Matrix (Fin k ⊕ Fin 2) m S} {J : Matrix m m S}
    {J₁ : Matrix (Fin k) (Fin k) S} {S₂ : Matrix (Fin 2) (Fin 2) S}
    (hK : Qᵀ * J * Q.map c = fromBlocks J₁ 0 0 S₂) (hQR : Q * R = 1) {a : Matrix (Fin k) (Fin k) S}
    (ha : aᵀ * J₁ * a.map c = J₁) : (conjM Q R a)ᵀ * J * (conjM Q R a).map c = J := by
  have h1 : Rᵀ * Qᵀ = 1 := by rw [← transpose_mul, hQR, transpose_one]
  have h2 : Q.map c * R.map c = 1 := by rw [← Matrix.map_mul, hQR, Matrix.map_one c (map_zero c) (map_one c)]
  have hmid : (fromBlocks a 0 0 (1 : Matrix (Fin 2) (Fin 2) S))ᵀ * fromBlocks J₁ 0 0 S₂ *
      (fromBlocks a 0 0 (1 : Matrix (Fin 2) (Fin 2) S)).map c = fromBlocks J₁ 0 0 S₂ := by
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp [ha, Matrix.map_one c (map_zero c) (map_one c)]
  calc (conjM Q R a)ᵀ * J * (conjM Q R a).map c
      = Rᵀ * ((fromBlocks a 0 0 (1 : Matrix (Fin 2) (Fin 2) S))ᵀ * (Qᵀ * J * Q.map c) *
          (fromBlocks a 0 0 (1 : Matrix (Fin 2) (Fin 2) S)).map c) * R.map c := by
        simp only [conjM, transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    _ = Rᵀ * Qᵀ * J * (Q.map c * R.map c) := by rw [hK, hmid, ← hK]; simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

end Alg

section Forms

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem gram_apply (σ : E →ₐ[F] E) {N : ℕ} {ι₁ ι₂ : Type*} (J : Matrix (Fin N) (Fin N) E) (A : Matrix (Fin N) ι₁ E)
    (B : Matrix (Fin N) ι₂ E) (i : ι₁) (j : ι₂) :
    (Aᵀ * J * B.map σ) i j = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (fun r => A r i) (fun r => B r j) := by
  simp only [Matrix.mul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, mulVec, transpose_apply, map_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem form_skew {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {N : ℕ} {J : Matrix (Fin N) (Fin N) E}
    (hsk : ∀ i j, σ (J j i) = -J i j) (a b : Fin N → E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J a b = -σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b a) := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsk]; ring

end Forms

theorem cA_inclR' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.includeRight_apply]

theorem continuous_unitsMap {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
    (φ : M →* N) (hφ : Continuous φ) : Continuous (Units.map φ) :=
  Units.continuous_iff.2 ⟨hφ.comp Units.continuous_val,
    (hφ.comp Units.continuous_coe_inv).congr fun x => (Units.coe_map_inv φ x).symm⟩

set_option maxHeartbeats 1000000 in

theorem leviSection : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), (∀ x, σ (σ x) = x) →
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y₁.J.det ≠ 0 →
    ∃ M : UA σ Y₁.J → UA σ Y.J, Continuous M ∧ (∀ h₁, IsLevi (W₁ := Y₁) H 1 h₁ (M h₁)) ∧
      ∀ γ ∈ ratU σ Y₁.J, M γ ∈ ratU σ Y.J := by
  intro F E _ _ _ _ _ σ n n₁ Y Y₁ H hσ hsk hn hxx hyy hxy horth hgram hdet
  subst hn
  set XY : Matrix (Fin (n₁ + 2)) (Fin 2) E := Matrix.of fun r t => ![H.x, H.y] t r with hXY
  set Q : Matrix (Fin (n₁ + 2)) (Fin n₁ ⊕ Fin 2) E := fromCols H.ι XY with hQ
  set S₂ : Matrix (Fin 2) (Fin 2) E := !![0, 1; -1, 0] with hS₂
  have hyx : form σ Y.J H.y H.x = -1 := by rw [form_skew hσ hsk, hxy, map_one]
  have horth' : ∀ i, form σ Y.J (fun r => H.ι r i) H.x = 0 ∧ form σ Y.J (fun r => H.ι r i) H.y = 0 := by
    intro i
    have e : (fun r => H.ι r i) = H.ι *ᵥ Pi.single i 1 := by
      funext r; simp [mulVec, dotProduct, Pi.single_apply]
    rw [e]; exact horth _
  have hK : Qᵀ * Y.J * Q.map σ = fromBlocks Y₁.J 0 0 S₂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [fromBlocks_apply₁₁, ← hgram, gram_apply, gram_apply]; rfl
    · rw [fromBlocks_apply₁₂, gram_apply]
      fin_cases j
      · simpa [Q, XY] using (horth' i).1
      · simpa [Q, XY] using (horth' i).2
    · rw [fromBlocks_apply₂₁, gram_apply, form_skew hσ hsk]
      fin_cases i
      · simp [Q, XY, (horth' j).1]
      · simp [Q, XY, (horth' j).2]
    · rw [fromBlocks_apply₂₂, gram_apply]
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
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hRQA : R.map f * Q.map f = 1 := by rw [← Matrix.map_mul, hRQ, Matrix.map_one f (map_zero f) (map_one f)]
  have hQRA : Q.map f * R.map f = 1 := by rw [← Matrix.map_mul, hQR, Matrix.map_one f (map_zero f) (map_one f)]
  have hcf : ∀ {a b : Type} (X : Matrix a b E), (X.map f).map (cA σ) = (X.map σ).map f := fun X => by
    ext i j; exact cA_inclR' σ _
  have hKA : (Q.map f)ᵀ * incM F Y.J * (Q.map f).map (cA σ).toRingHom = fromBlocks (incM F Y₁.J) 0 0 (S₂.map f) := by
    change (Q.map f)ᵀ * Y.J.map f * (Q.map f).map (cA σ) = fromBlocks (Y₁.J.map f) 0 0 (S₂.map f)
    rw [hcf, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hK, fromBlocks_map]
    simp
  let φ := conjHom hRQA hQRA
  have hmem : ∀ h : UA σ Y₁.J, Units.map φ h.1 ∈ UG (cA σ) (incM F Y.J) := by
    intro h
    show (conjM (Q.map f) (R.map f) (h.1 : Matrix _ _ (AE F E)))ᵀ * incM F Y.J *
      (conjM (Q.map f) (R.map f) (h.1 : Matrix _ _ (AE F E))).map (cA σ) = incM F Y.J
    exact conjM_unitary (cA σ).toRingHom hKA hQRA h.2
  let Mf : UA σ Y₁.J → UA σ Y.J := fun h => ⟨Units.map φ h.1, hmem h⟩
  have hmat : ∀ h, mat (Mf h) = conjM (Q.map f) (R.map f) (mat h) := fun h => rfl
  refine ⟨Mf, ?_, ?_, ?_⟩
  · have hφ : Continuous φ := by
      change Continuous fun a => conjM (Q.map f) (R.map f) a
      unfold conjM
      exact (continuous_const.matrix_mul (continuous_id.matrix_fromBlocks continuous_const continuous_const
        continuous_const)).matrix_mul continuous_const
    exact Continuous.subtype_mk ((continuous_unitsMap φ hφ).comp continuous_subtype_val) _
  · intro h
    have hMQ : mat (Mf h) * Q.map f = Q.map f * fromBlocks (mat h) 0 0 (1 : Matrix (Fin 2) (Fin 2) (AE F E)) := by
      rw [hmat]; unfold conjM; rw [Matrix.mul_assoc, hRQA, Matrix.mul_one]
    have hcol : ∀ t : Fin 2, mat (Mf h) *ᵥ (fun r => f (XY r t)) = fun r => f (XY r t) := by
      intro t
      have e1 : (fun r => f (XY r t)) = Q.map f *ᵥ Pi.single (Sum.inr t) 1 := by
        funext r; simp [Q, mulVec, dotProduct, Pi.single_apply]
      have e2 : fromBlocks (mat h) 0 0 (1 : Matrix (Fin 2) (Fin 2) (AE F E)) *ᵥ Pi.single (Sum.inr t) 1 =
          Pi.single (Sum.inr t) 1 := by
        ext i; rcases i with i | i <;> simp [mulVec, dotProduct, Pi.single_apply, one_apply, Fintype.sum_sum_type]
      rw [e1, mulVec_mulVec, hMQ, ← mulVec_mulVec, e2]
    refine ⟨?_, ?_, ?_⟩
    · rw [Units.val_one, one_smul]; exact hcol 0
    · rw [inv_one, Units.val_one, map_one, one_smul]; exact hcol 1
    · have e3 : incM F H.ι = Q.map f * fromRows (1 : Matrix (Fin n₁) (Fin n₁) (AE F E)) (0 : Matrix (Fin 2) (Fin n₁) (AE F E)) := by
        ext r k; simp [incM, Q, mul_apply, Fintype.sum_sum_type, one_apply, hf]
      have e4 : fromBlocks (mat h) 0 0 (1 : Matrix (Fin 2) (Fin 2) (AE F E)) *
          fromRows (1 : Matrix (Fin n₁) (Fin n₁) (AE F E)) (0 : Matrix (Fin 2) (Fin n₁) (AE F E)) =
          fromRows (1 : Matrix (Fin n₁) (Fin n₁) (AE F E)) (0 : Matrix (Fin 2) (Fin n₁) (AE F E)) * mat h := by
        ext i k; rcases i with i | i <;> simp [mul_apply, Fintype.sum_sum_type, one_apply]
      rw [e3, ← Matrix.mul_assoc, hMQ, Matrix.mul_assoc, e4, Matrix.mul_assoc]
  · intro γ hγ
    rw [ratU, Subgroup.mem_subgroupOf] at hγ ⊢
    obtain ⟨g, hg⟩ := hγ
    refine ⟨Units.map (conjHom hRQ hQR) g, ?_⟩
    have hgv : (g : Matrix (Fin n₁) (Fin n₁) E).map f = mat γ := by
      ext a b; rw [Matrix.map_apply, ← Matrix.GeneralLinearGroup.map_apply, hg]; rfl
    apply Matrix.GeneralLinearGroup.ext; intro i j
    rw [Matrix.GeneralLinearGroup.map_apply]
    change f (conjM Q R (g : Matrix _ _ E) i j) = conjM (Q.map f) (R.map f) (mat γ) i j
    rw [← hgv, ← conjM_map]; rfl

end GlobalTheory.LeviPlaneSection

end
