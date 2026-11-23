import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMono
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open Matrix

noncomputable section
namespace GlobalTheory.ThK.GLTwo.LiftUnip
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open GlobalTheory.StdPar
open GlobalTheory.SiegelSet (adMat)

omit [NumberField E] in
theorem mat_inv_mul' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  unfold mat
  rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]

omit [NumberField E] in
theorem mat_mul_inv' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  unfold mat
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]

theorem iff_of_lift {R : Type} [CommRing R] {n n₁ : ℕ} (P Q : Matrix (Fin n) (Fin n) R) (P₁ Q₁ : Matrix (Fin n₁) (Fin n₁) R)
    (x : Fin n → R) (ι : Matrix (Fin n) (Fin n₁) R) (hQP : Q * P = 1) (hPQ₁ : P₁ * Q₁ = 1)
    (hx : P *ᵥ x = x) (hι : ∀ z, ∃ a : R, P *ᵥ (ι *ᵥ z) = a • x + ι *ᵥ (P₁ *ᵥ z))
    (A : Submodule R (Fin n₁ → R)) (hA : ∀ y, y ∈ A ↔ P₁ *ᵥ y ∈ A) (w : Fin n → R) :
    (∃ (c : R) (z : Fin n₁ → R), z ∈ A ∧ w = c • x + ι *ᵥ z) ↔
      ∃ (c : R) (z : Fin n₁ → R), z ∈ A ∧ P *ᵥ w = c • x + ι *ᵥ z := by
  constructor
  · rintro ⟨c, z, hz, rfl⟩
    obtain ⟨a, ha⟩ := hι z
    exact ⟨c + a, P₁ *ᵥ z, (hA z).1 hz, by rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx, ha, add_smul, add_assoc]⟩
  · rintro ⟨c, z, hz, hw⟩
    obtain ⟨a, ha⟩ := hι (Q₁ *ᵥ z)
    have hz' : P₁ *ᵥ (Q₁ *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, hPQ₁, Matrix.one_mulVec]
    rw [hz'] at ha
    have hQx : Q *ᵥ x = x := calc
      Q *ᵥ x = Q *ᵥ (P *ᵥ x) := by rw [hx]
      _ = x := by rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
    have hQι : Q *ᵥ (ι *ᵥ z) = ι *ᵥ (Q₁ *ᵥ z) - a • x := by
      have e : ι *ᵥ z = P *ᵥ (ι *ᵥ (Q₁ *ᵥ z)) - a • x := by rw [ha]; abel
      rw [e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec, Matrix.mulVec_smul, hQx]
    refine ⟨c - a, Q₁ *ᵥ z, (hA _).2 (by rw [hz']; exact hz), ?_⟩
    calc w = Q *ᵥ (P *ᵥ w) := by rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
      _ = _ := by rw [hw, Matrix.mulVec_add, Matrix.mulVec_smul, hQx, hQι, sub_smul]; abel

omit [NumberField E] in
theorem col_zero {n r : ℕ} {X' : Matrix (Fin n) (Fin (r + 1)) E} {x : Fin n → E} (h0 : ∀ k, X' k 0 = x k) :
    (adMat F X')ᵀ 0 = incV F x := funext fun k => by
  simp [adMat, incV, h0]

omit [NumberField E] in
theorem col_succ {n n₁ r : ℕ} {X' : Matrix (Fin n) (Fin (r + 1)) E} {Xf : Matrix (Fin n₁) (Fin r) E}
    {ι : Matrix (Fin n) (Fin n₁) E} (hs : ∀ k (i : Fin r), X' k i.succ = (ι * Xf) k i) (i : Fin r) :
    (adMat F X')ᵀ i.succ = incM F ι *ᵥ (adMat F Xf)ᵀ i := funext fun k => by
  simp [adMat, incM, hs, Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum]

omit [NumberField E] in

theorem mem_colSpan_lift {n n₁ r : ℕ} {X' : Matrix (Fin n) (Fin (r + 1)) E} {Xf : Matrix (Fin n₁) (Fin r) E}
    {x : Fin n → E} {ι : Matrix (Fin n) (Fin n₁) E} (h0 : ∀ k, X' k 0 = x k)
    (hs : ∀ k (i : Fin r), X' k i.succ = (ι * Xf) k i) (I : Set (Fin r)) (w : Fin n → AE F E) :
    w ∈ colSpan F X' (insert 0 (Fin.succ '' I)) ↔
      ∃ (c : AE F E) (z : Fin n₁ → AE F E), z ∈ colSpan F Xf I ∧ w = c • incV F x + incM F ι *ᵥ z := by
  have e : (fun i => (adMat F X')ᵀ i) '' insert 0 (Fin.succ '' I) =
      insert (incV F x) ((incM F ι).mulVecLin '' ((fun i => (adMat F Xf)ᵀ i) '' I)) := by
    rw [Set.image_insert_eq, Set.image_image, Set.image_image, col_zero h0]
    congr 1
    exact Set.image_congr fun i _ => col_succ hs i
  rw [colSpan, e, Submodule.span_insert, Submodule.span_image, Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z', hz', rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hz'
    exact ⟨c, z, hz, rfl⟩
  · rintro ⟨c, z, hz, rfl⟩
    exact ⟨c • incV F x, Submodule.mem_span_singleton.2 ⟨c, rfl⟩, _, Submodule.mem_map_of_mem hz, rfl⟩

omit [NumberField E] in
theorem mem_colSpan_succ {n n₁ r : ℕ} {X' : Matrix (Fin n) (Fin (r + 1)) E} {Xf : Matrix (Fin n₁) (Fin r) E}
    {ι : Matrix (Fin n) (Fin n₁) E} (hs : ∀ k (i : Fin r), X' k i.succ = (ι * Xf) k i) (j : Fin r) {w : Fin n → AE F E}
    (hw : w ∈ colSpan F X' {j.succ}) : ∃ z, z ∈ colSpan F Xf {j} ∧ w = incM F ι *ᵥ z := by
  rw [colSpan, Set.image_singleton, Submodule.mem_span_singleton] at hw
  obtain ⟨c, rfl⟩ := hw
  refine ⟨c • (adMat F Xf)ᵀ j, Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl, rfl⟩), ?_⟩
  rw [col_succ hs, Matrix.mulVec_smul]

omit [NumberField E] in
theorem mem_colSpan_zero {n r : ℕ} {X' : Matrix (Fin n) (Fin (r + 1)) E} {x : Fin n → E} (h0 : ∀ k, X' k 0 = x k)
    {w : Fin n → AE F E} (hw : w ∈ colSpan F X' {0}) : ∃ c : AE F E, w = c • incV F x := by
  rw [colSpan, Set.image_singleton, Submodule.mem_span_singleton, col_zero h0] at hw
  obtain ⟨c, rfl⟩ := hw
  exact ⟨c, rfl⟩

theorem set_zero {r : ℕ} (S' : Finset (Fin r)) :
    {i : Fin (r + 1) | ∃ k ∈ insert 0 (S'.map (Fin.succEmb r)), i ≤ k ∧ k < 0} = ∅ := by
  ext i; simp

theorem set_succ {r : ℕ} (S' : Finset (Fin r)) (j : Fin r) :
    {i : Fin (r + 1) | ∃ k ∈ insert 0 (S'.map (Fin.succEmb r)), i ≤ k ∧ k < j.succ} =
      insert 0 (Fin.succ '' {i | ∃ k ∈ S', i ≤ k ∧ k < j}) := by
  ext i
  cases i using Fin.cases with
  | zero => simp [Fin.succ_pos]
  | succ i => simp [Fin.succ_ne_zero, Fin.succ_le_succ_iff, Fin.succ_lt_succ_iff]

theorem set_last {r : ℕ} (S' : Finset (Fin r)) :
    {i : Fin (r + 1) | ∃ k ∈ insert 0 (S'.map (Fin.succEmb r)), i ≤ k} =
      insert 0 (Fin.succ '' {i | ∃ k ∈ S', i ≤ k}) := by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp [Fin.succ_ne_zero, Fin.succ_le_succ_iff]

omit [NumberField E] in
theorem T_apply {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (c₀ : E)
    (C : Matrix (Fin n) (Fin m) E) (v : Fin n → E) (i : Fin m) :
    ((Formalism.UG.cT (σ : E →+* E) C * (c₀ • J.map σ)) *ᵥ v) i = c₀ * σ (form σ J (fun l => C l i) v) := by
  simp only [Formalism.UG.cT, form, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, hσ, Finset.sum_mul, Finset.mul_sum, AlgHom.coe_toRingHom,
    RingHom.coe_coe]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField E] in
theorem form_lift {σ : E →ₐ[F] E} {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E}
    {ι : Matrix (Fin n) (Fin n₁) E} (hJ₁ : ιᵀ * J * ι.map σ = J₁) (u u' : Fin n₁ → E) :
    form σ J (ι *ᵥ u) (ι *ᵥ u') = form σ J₁ u u' := by
  have e : (fun i => σ ((ι *ᵥ u') i)) = ι.map σ *ᵥ fun i => σ (u' i) := funext fun i => by
    simp [Matrix.mulVec, dotProduct, map_sum]
  simp only [form]
  rw [e, ← hJ₁, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem perp_lift {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n n₁ r : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {J₁ : Matrix (Fin n₁) (Fin n₁) E} {x y : Fin n → E} {ι : Matrix (Fin n) (Fin n₁) E} (hsk : ∀ i j, σ (J j i) = -J i j)
    (hxx : form σ J x x = 0) (hxy : form σ J x y = 1)
    (hι : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (hJ₁ : ιᵀ * J * ι.map σ = J₁)
    {c₀ : E} (hc₀ : c₀ ≠ 0) {X' : Matrix (Fin n) (Fin (r + 1)) E} {Xf : Matrix (Fin n₁) (Fin r) E}
    (h0 : ∀ k, X' k 0 = x k) (hs : ∀ k (i : Fin r), X' k i.succ = (ι * Xf) k i) (K₁ : Set (Fin r))
    (α β : AE F E) (z : Fin n₁ → AE F E)
    (hw : α • incV F x + β • incV F y + incM F ι *ᵥ z ∈ colPerp σ (c₀ • J.map σ) X' (insert 0 (Fin.succ '' K₁))) :
    β = 0 ∧ z ∈ colPerp σ (c₀ • J₁.map σ) Xf K₁ := by
  set T := Formalism.UG.cT (σ : E →+* E) X' * (c₀ • J.map σ) with hT
  set T₁ := Formalism.UG.cT (σ : E →+* E) Xf * (c₀ • J₁.map σ) with hT₁
  have hcol0 : (fun l => X' l 0) = x := funext h0
  have hcols : ∀ i, (fun l => X' l i.succ) = ι *ᵥ fun l => Xf l i := fun i => funext fun k => by
    rw [hs]; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have Tι : ∀ i j, (T * ι) i j = (T *ᵥ (ι *ᵥ Pi.single j 1)) i := fun i j => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]; rfl
  have t0x : (T *ᵥ x) 0 = 0 := by rw [hT, T_apply hσ, hcol0, hxx, map_zero, mul_zero]
  have t0y : (T *ᵥ y) 0 = c₀ := by rw [hT, T_apply hσ, hcol0, hxy, map_one, mul_one]
  have t0ι : ∀ j, (T * ι) 0 j = 0 := fun j => by
    rw [Tι, hT, T_apply hσ, hcol0, GlobalTheory.LeviPlaneSection.form_skew hσ hsk, (hι _).1, map_zero, neg_zero, map_zero, mul_zero]
  have tsx : ∀ i : Fin r, (T *ᵥ x) i.succ = 0 := fun i => by rw [hT, T_apply hσ, hcols, (hι _).1, map_zero, mul_zero]
  have tsy : ∀ i : Fin r, (T *ᵥ y) i.succ = 0 := fun i => by rw [hT, T_apply hσ, hcols, (hι _).2, map_zero, mul_zero]
  have tsι : ∀ (i : Fin r) (j : Fin n₁), (T * ι) i.succ j = T₁ i j := fun i j => by
    rw [Tι, hT, T_apply hσ, hcols, form_lift hJ₁, ← T_apply hσ J₁ c₀ Xf, Matrix.mulVec_single_one]; rfl
  have hv : adMat F T *ᵥ (α • incV F x + β • incV F y + incM F ι *ᵥ z) =
      α • incV F (T *ᵥ x) + β • incV F (T *ᵥ y) + incM F (T * ι) *ᵥ z := by
    have ev : ∀ v : Fin n → E, adMat F T *ᵥ incV F v = incV F (T *ᵥ v) := fun v => funext fun i =>
      (RingHom.map_mulVec (inclR (F := F) (AF F)) T v i).symm
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ev, ev]
    congr 2
    exact (Matrix.map_mul).symm
  simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply, Matrix.mulVecLin_apply,
    LinearMap.proj_apply] at hw ⊢
  refine ⟨?_, fun i hi => ?_⟩
  · have h := hw 0 (Set.mem_insert _ _)
    rw [hv] at h
    have e3 : (incM F (T * ι) *ᵥ z) 0 = 0 := by simp [Matrix.mulVec, dotProduct, incM, t0ι]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, incV, t0x, t0y, map_zero, mul_zero, zero_add, e3, add_zero] at h
    have hu : inclR (F := F) (AF F) c₀ * inclR (F := F) (AF F) c₀⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hc₀, map_one]
    calc β = β * inclR (F := F) (AF F) c₀ * inclR (F := F) (AF F) c₀⁻¹ := by rw [mul_assoc, hu, mul_one]
      _ = 0 := by rw [h, zero_mul]
  · have h := hw i.succ (Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩)
    rw [hv] at h
    have e3 : (incM F (T * ι) *ᵥ z) i.succ = (adMat F T₁ *ᵥ z) i := by
      simp only [Matrix.mulVec, dotProduct, incM, adMat, Matrix.map_apply, tsι]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, incV, tsx, tsy, map_zero, mul_zero, zero_add, e3] at h
    exact h

theorem mem_unip_of_lift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ (g : UA σ W.J) (h₁ : UA σ W₁.J), mat g *ᵥ incV F H.x = incV F H.x → (∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat g *ᵥ (incM F H.ι *ᵥ z) = a • incV F H.x + incM F H.ι *ᵥ (mat h₁ *ᵥ z)) → GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀ h₁ ∈ GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S' → GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ g ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r))) := by
  intro F E _ _ _ _ _ σ _ hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ _ r Xf Yf _ X' Y' _ hX0 _ hXs S' g h₁ hgx hgι hh₁
  have hs : ∀ k (i : Fin r), X' k i.succ = (H.ι * Xf) k i := fun k i => (hXs k i).1
  have hP : IsHypPlane σ H W W₁ := ⟨hn, hxx, hyy, hxy, hι, hJ₁⟩
  have hd : W₁.J.det ≠ 0 := fun h0 => hN₁.2 (by
    have e : (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero])
  have hM : (matHom (AF F) σ (c₀ • W.J.map σ) (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ g)).1 = mat g := rfl
  have key : ∀ A : Submodule (AE F E) (Fin n₁ → AE F E), (∀ y, y ∈ A ↔ mat h₁ *ᵥ y ∈ A) → ∀ w,
      (∃ (c : AE F E) (z : Fin n₁ → AE F E), z ∈ A ∧ w = c • incV F H.x + incM F H.ι *ᵥ z) ↔
      ∃ (c : AE F E) (z : Fin n₁ → AE F E), z ∈ A ∧ mat g *ᵥ w = c • incV F H.x + incM F H.ι *ᵥ z :=
    fun A hA w => iff_of_lift (mat g) (mat g⁻¹) (mat h₁) (mat h₁⁻¹) _ _ (mat_inv_mul' g) (mat_mul_inv' h₁) hgx hgι A hA w
  obtain ⟨hh1, hh2⟩ := hh₁
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun j => ?_, ?_, ?_⟩
  · cases j using Fin.cases with
    | zero =>
      rw [set_zero, show colSpan F X' (∅ : Set (Fin (r + 1))) = ⊥ by simp [colSpan]]
      refine ⟨fun y => ?_, fun y hy => ?_⟩
      · rw [hM, Submodule.mem_bot, Submodule.mem_bot]
        refine ⟨fun h => by rw [h, Matrix.mulVec_zero], fun h => ?_⟩
        calc y = mat g⁻¹ *ᵥ (mat g *ᵥ y) := by rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
          _ = 0 := by rw [h, Matrix.mulVec_zero]
      · obtain ⟨c, rfl⟩ := mem_colSpan_zero hX0 hy
        rw [hM, Submodule.mem_bot, Matrix.mulVec_smul, hgx, sub_self]
    | succ j =>
      have hj := Subgroup.mem_iInf.1 hh1 j
      rw [set_succ]
      refine ⟨fun y => ?_, fun y hy => ?_⟩
      · rw [hM, mem_colSpan_lift hX0 hs, mem_colSpan_lift hX0 hs]
        exact key _ hj.1 y
      · obtain ⟨z, hz, rfl⟩ := mem_colSpan_succ hs j hy
        obtain ⟨a, ha⟩ := hgι z
        rw [hM, mem_colSpan_lift hX0 hs]
        exact ⟨a, mat h₁ *ᵥ z - z, hj.2 z hz, by rw [ha, Matrix.mulVec_sub]; abel⟩
  · rw [set_last]
    intro y
    rw [hM, mem_colSpan_lift hX0 hs, mem_colSpan_lift hX0 hs]
    exact key _ hh2.1 y
  · rw [set_last]
    intro y hy
    obtain ⟨α, β, z, rfl⟩ := hP.decompA hσ hsk hd y
    obtain ⟨hβ, hz⟩ := perp_lift hσ hsk hxx hxy hι hJ₁ hc₀ hX0 hs _ α β z hy
    obtain ⟨a, ha⟩ := hgι z
    rw [hM, mem_colSpan_lift hX0 hs]
    refine ⟨a, mat h₁ *ᵥ z - z, hh2.2 z hz, ?_⟩
    rw [hβ, zero_smul, add_zero, Matrix.mulVec_add, Matrix.mulVec_smul, hgx, ha, Matrix.mulVec_sub]
    abel

end GlobalTheory.ThK.GLTwo.LiftUnip

end
