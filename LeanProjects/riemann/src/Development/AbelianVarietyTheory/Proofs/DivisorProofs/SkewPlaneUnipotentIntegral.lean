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

open Formalism.UG (cT)

namespace GlobalTheory.StdPar.PlaneStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n n₁ r : ℕ} {H : Plane E n n₁}

theorem dot_incV (a b : Fin n → E) : incV F a ⬝ᵥ incV F b = inclR (F := F) (AF F) (a ⬝ᵥ b) := by
  simp [incV, dotProduct, map_sum, map_mul]

theorem col_zero {X' : Matrix (Fin n) (Fin (r + 1)) E} (hX0 : ∀ k, X' k 0 = H.x k) :
    (GlobalTheory.SiegelSet.adMat F X')ᵀ 0 = incV F H.x := by
  ext k; simp [GlobalTheory.SiegelSet.adMat, incV, hX0]

theorem col_succ {X' : Matrix (Fin n) (Fin (r + 1)) E} {Xf : Matrix (Fin n₁) (Fin r) E}
    (hXs : ∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i) (i : Fin r) :
    (GlobalTheory.SiegelSet.adMat F X')ᵀ i.succ = incM F H.ι *ᵥ (GlobalTheory.SiegelSet.adMat F Xf)ᵀ i := by
  ext k
  simp [GlobalTheory.SiegelSet.adMat, incM, hXs, Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem mem_colSpan_insert {X' : Matrix (Fin n) (Fin (r + 1)) E} {Xf : Matrix (Fin n₁) (Fin r) E}
    (hX0 : ∀ k, X' k 0 = H.x k) (hXs : ∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i) (I : Set (Fin r))
    (y : Fin n → AE F E) :
    y ∈ colSpan F X' (insert 0 (Fin.succ '' I)) ↔
      ∃ b : AE F E, ∃ w ∈ colSpan F Xf I, y = b • incV F H.x + incM F H.ι *ᵥ w := by
  have e : (fun i => (GlobalTheory.SiegelSet.adMat F X')ᵀ i) '' (Fin.succ '' I) =
      (incM F H.ι).mulVecLin '' ((fun i => (GlobalTheory.SiegelSet.adMat F Xf)ᵀ i) '' I) := by
    rw [Set.image_image, Set.image_image]
    refine Set.image_congr fun i _ => ?_
    exact col_succ hXs i
  rw [colSpan, Set.image_insert_eq, Submodule.span_insert, e, Submodule.span_image, Submodule.mem_sup]
  simp only [Submodule.mem_span_singleton, Submodule.mem_map, col_zero hX0]
  constructor
  · rintro ⟨_, ⟨b, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨b, w, hw, rfl⟩
  · rintro ⟨b, w, hw, rfl⟩
    exact ⟨_, ⟨b, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩

theorem mem_colSpan_succ {X' : Matrix (Fin n) (Fin (r + 1)) E} {Xf : Matrix (Fin n₁) (Fin r) E}
    (hXs : ∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i) (j : Fin r) {z : Fin n₁ → AE F E}
    (hz : z ∈ colSpan F Xf {j}) : incM F H.ι *ᵥ z ∈ colSpan F X' {j.succ} := by
  rw [colSpan, Set.image_singleton, Submodule.mem_span_singleton] at hz ⊢
  obtain ⟨c, rfl⟩ := hz
  exact ⟨c, by rw [col_succ hXs, Matrix.mulVec_smul]⟩

theorem form_mulVec (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E) (a b : Fin n₁ → E) :
    form σ J (ι *ᵥ a) (ι *ᵥ b) = form σ (ιᵀ * J * ι.map σ) a b := by
  have e : (fun i => σ ((ι *ᵥ b) i)) = ι.map σ *ᵥ fun i => σ (b i) := by
    funext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp only [form, e, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, ← Matrix.vecMul_vecMul]

theorem entry (hσ : ∀ x, σ (σ x) = x) {m : ℕ} (J : Matrix (Fin n) (Fin n) E) (C : Matrix (Fin n) (Fin m) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (c : E) (i : Fin m) (k : Fin n₁) :
    (cT (σ : E →+* E) C * (c • J.map σ) * ι) i k = c * σ (form σ J (fun l => C l i) (fun l => ι l k)) := by
  simp only [cT, form, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, map_sum, map_mul, hσ, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  simp only [RingHom.coe_coe]
  ring

theorem eq_zero_of_add {W : Matrix (Fin n) (Fin n) E} (hxy : form σ W H.x H.y = 1)
    (hι : ∀ u, form σ W (H.ι *ᵥ u) H.x = 0 ∧ form σ W (H.ι *ᵥ u) H.y = 0) {W₁ : Matrix (Fin n₁) (Fin n₁) E}
    (hJ₁ : H.ιᵀ * W * H.ι.map σ = W₁) (hd : W₁.det ≠ 0) {b : AE F E} {w : Fin n₁ → AE F E}
    (h : b • incV F H.x + incM F H.ι *ᵥ w = 0) : b = 0 ∧ w = 0 := by
  set v : Fin n → E := W *ᵥ fun i => σ (H.y i) with hv
  have h1 : incV F H.x ⬝ᵥ incV F v = 1 := by rw [dot_incV]; exact (congrArg _ hxy).trans (map_one _)
  have hvι : v ᵥ* H.ι = 0 := by
    funext k
    have := (hι (Pi.single k 1)).2
    simp only [form, Matrix.mulVec_single_one] at this
    rw [dotProduct_comm] at this
    simpa [Matrix.vecMul, dotProduct, Matrix.transpose_apply, mul_comm] using this
  have h2 : (incM F H.ι *ᵥ w) ⬝ᵥ incV F v = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec]
    have : incV F v ᵥ* incM F H.ι = 0 := by
      funext k
      have := congrFun hvι k
      simp only [Matrix.vecMul, dotProduct, incV, incM, Matrix.map_apply, Pi.zero_apply] at this ⊢
      rw [← map_zero (inclR (F := F) (AF F)), ← this, map_sum]
      simp [map_mul]
    rw [this, zero_dotProduct]
  have hb : b = 0 := by
    have := congrArg (· ⬝ᵥ incV F v) h
    simpa [add_dotProduct, smul_dotProduct, h1, h2] using this
  refine ⟨hb, ?_⟩
  rw [hb, zero_smul, zero_add] at h
  have hM : (incM F H.ι)ᵀ * incM F W * incM F (H.ι.map σ) = incM F W₁ := by
    rw [← hJ₁]; simp only [incM, Matrix.transpose_map, Matrix.map_mul]
  have hw : w ᵥ* incM F W₁ = 0 := by
    rw [← hM, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, h, Matrix.zero_vecMul,
      Matrix.zero_vecMul]
  have hu : IsUnit (incM F W₁).det := by
    have e := RingHom.map_det (inclR (F := F) (AF F)) W₁
    rw [RingHom.mapMatrix_apply] at e
    simp only [incM]
    rw [← e]
    exact (Ne.isUnit hd).map _
  calc w = w ᵥ* (incM F W₁ * (incM F W₁)⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
    _ = 0 := by rw [← Matrix.vecMul_vecMul, hw, Matrix.zero_vecMul]

theorem mem_colPerp (hσ : ∀ x, σ (σ x) = x) {W : Matrix (Fin n) (Fin n) E} (hsk : ∀ i j, σ (W j i) = -W i j)
    (hι : ∀ u, form σ W (H.ι *ᵥ u) H.x = 0 ∧ form σ W (H.ι *ᵥ u) H.y = 0) {W₁ : Matrix (Fin n₁) (Fin n₁) E}
    (hJ₁ : H.ιᵀ * W * H.ι.map σ = W₁) (c : E) {X' : Matrix (Fin n) (Fin (r + 1)) E} {Xf : Matrix (Fin n₁) (Fin r) E}
    (hX0 : ∀ k, X' k 0 = H.x k) (hXs : ∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i) (K : Set (Fin r))
    {z : Fin n₁ → AE F E} (hz : z ∈ colPerp σ (c • W₁.map σ) Xf K) :
    incM F H.ι *ᵥ z ∈ colPerp σ (c • W.map σ) X' (insert 0 (Fin.succ '' K)) := by
  have row0 : ∀ k, (cT (σ : E →+* E) X' * (c • W.map σ) * H.ι) 0 k = 0 := fun k => by
    rw [entry hσ, GlobalTheory.LeviPlaneSection.form_skew hσ hsk]
    have e1 : (fun l => X' l 0) = H.x := funext hX0
    have e2 : (fun l => H.ι l k) = H.ι *ᵥ Pi.single k 1 := by rw [Matrix.mulVec_single_one]; rfl
    rw [e1, e2, (hι _).1, map_zero, neg_zero, map_zero, mul_zero]
  have what₂ : ∀ i k, (cT (σ : E →+* E) X' * (c • W.map σ) * H.ι) i.succ k = (cT (σ : E →+* E) Xf * (c • W₁.map σ)) i k :=
      fun i k => by
    rw [← Matrix.mul_one (cT (σ : E →+* E) Xf * (c • W₁.map σ)), entry hσ, entry hσ]
    have e1 : (fun l => X' l i.succ) = H.ι *ᵥ (fun l => Xf l i) := by
      funext l; rw [hXs]; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have e2 : (fun l => H.ι l k) = H.ι *ᵥ (fun l => (1 : Matrix (Fin n₁) (Fin n₁) E) l k) := by
      funext l; simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
    rw [e1, e2, form_mulVec hσ, hJ₁]
  simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_proj, Function.eval, Matrix.mulVecLin_apply] at hz ⊢
  intro i hi
  have e : GlobalTheory.SiegelSet.adMat F (cT (σ : E →+* E) X' * (c • W.map σ)) *ᵥ (incM F H.ι *ᵥ z) =
      GlobalTheory.SiegelSet.adMat F (cT (σ : E →+* E) X' * (c • W.map σ) * H.ι) *ᵥ z := by
    rw [Matrix.mulVec_mulVec]; simp only [GlobalTheory.SiegelSet.adMat, incM, Matrix.map_mul]
  rw [e]
  rcases hi with rfl | ⟨i, hi, rfl⟩
  · simp only [Matrix.mulVec, dotProduct, GlobalTheory.SiegelSet.adMat, Matrix.map_apply, row0, map_zero, zero_mul,
      Finset.sum_const_zero]
  · have := hz i hi
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.SiegelSet.adMat, Matrix.map_apply, what₂] at this ⊢
    exact this

theorem idx_lt (S' : Finset (Fin r)) (j : Fin r) :
    {i : Fin (r + 1) | ∃ k ∈ insert 0 (S'.map (Fin.succEmb r)), i ≤ k ∧ k < j.succ} =
      insert 0 (Fin.succ '' {i | ∃ k ∈ S', i ≤ k ∧ k < j}) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Set.mem_setOf_eq, Set.mem_insert_iff, true_or, iff_true]
    exact ⟨0, Finset.mem_insert_self _ _, le_rfl, Fin.succ_pos j⟩
  · simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.succ_ne_zero, false_or, Set.mem_image,
      Fin.succ_inj, exists_eq_right, Finset.mem_insert, Finset.mem_map, Fin.coe_succEmb]
    constructor
    · rintro ⟨k, hk, hik, hkj⟩
      rcases hk with rfl | ⟨k, hk, rfl⟩
      · exact absurd hik (not_le.2 (Fin.succ_pos i))
      · exact ⟨k, hk, Fin.succ_le_succ_iff.1 hik, Fin.succ_lt_succ_iff.1 hkj⟩
    · rintro ⟨k, hk, hik, hkj⟩
      exact ⟨k.succ, Or.inr ⟨k, hk, rfl⟩, Fin.succ_le_succ_iff.2 hik, Fin.succ_lt_succ_iff.2 hkj⟩

theorem idx_le (S' : Finset (Fin r)) :
    {i : Fin (r + 1) | ∃ k ∈ insert 0 (S'.map (Fin.succEmb r)), i ≤ k} =
      insert 0 (Fin.succ '' {i | ∃ k ∈ S', i ≤ k}) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Set.mem_setOf_eq, Set.mem_insert_iff, true_or, iff_true]
    exact ⟨0, Finset.mem_insert_self _ _, le_rfl⟩
  · simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.succ_ne_zero, false_or, Set.mem_image,
      Fin.succ_inj, exists_eq_right, Finset.mem_insert, Finset.mem_map, Fin.coe_succEmb]
    constructor
    · rintro ⟨k, hk, hik⟩
      rcases hk with rfl | ⟨k, hk, rfl⟩
      · exact absurd hik (not_le.2 (Fin.succ_pos i))
      · exact ⟨k, hk, Fin.succ_le_succ_iff.1 hik⟩
    · rintro ⟨k, hk, hik⟩
      exact ⟨k.succ, Or.inr ⟨k, hk, rfl⟩, Fin.succ_le_succ_iff.2 hik⟩

theorem unip_of_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ (g : UA σ W.J) (h₁ : UA σ W₁.J), GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ g ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r))) → (∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat g *ᵥ (incM F H.ι *ᵥ z) = a • incV F H.x + incM F H.ι *ᵥ (mat h₁ *ᵥ z)) → GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀ h₁ ∈ GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S' := by
  intro F E _ _ _ _ _ σ _ hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN r Xf Yf hWf X' Y' hW' hX0 hY0 hXs S' g h₁
    hg hgh
  have hd : W₁.J.det ≠ 0 := by
    intro h0
    apply hN₁.2
    have e : (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  have hX0' : ∀ k, X' k 0 = H.x k := hX0
  have hXs' : ∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i := fun k i => (hXs k i).1
  have eg : ((matHom (AF F) σ (c₀ • W.J.map σ)) (SquareIntegrability.toGAd hσ W.J hc₀ g)).1 = mat g := by
    rw [matHom_apply, SquareIntegrability.toGAd_mat]; rfl
  have eh : ((matHom (AF F) σ (c₀ • W₁.J.map σ)) (SquareIntegrability.toGAd hσ W₁.J hc₀ h₁)).1 = mat h₁ := by
    rw [matHom_apply, SquareIntegrability.toGAd_mat]; rfl
  have tr : ∀ (I : Set (Fin r)) (a : AE F E) (w : Fin n₁ → AE F E),
      a • incV F H.x + incM F H.ι *ᵥ w ∈ colSpan F X' (insert 0 (Fin.succ '' I)) ↔ w ∈ colSpan F Xf I := by
    intro I a w
    rw [mem_colSpan_insert hX0' hXs']
    constructor
    · rintro ⟨b, w', hw', e⟩
      have h0 : (a - b) • incV F H.x + incM F H.ι *ᵥ (w - w') = 0 := by
        rw [sub_smul, Matrix.mulVec_sub]
        linear_combination (norm := skip) e
        abel
      have := (eq_zero_of_add hxy hι hJ₁ hd h0).2
      rwa [sub_eq_zero.1 this]
    · intro hw
      exact ⟨a, w, hw, rfl⟩
  have tr0 : ∀ (I : Set (Fin r)) (w : Fin n₁ → AE F E),
      incM F H.ι *ᵥ w ∈ colSpan F X' (insert 0 (Fin.succ '' I)) ↔ w ∈ colSpan F Xf I := fun I w => by
    simpa using tr I 0 w
  have hg1 := Subgroup.mem_iInf.1 hg.1
  have hg2 := hg.2
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨fun z => ?_, fun z hz => ?_⟩, ⟨fun z => ?_, fun z hz => ?_⟩⟩
  · have gj : ∀ y, y ∈ colSpan F X' (insert 0 (Fin.succ '' {i | ∃ k ∈ S', i ≤ k ∧ k < j})) ↔
        mat g *ᵥ y ∈ colSpan F X' (insert 0 (Fin.succ '' {i | ∃ k ∈ S', i ≤ k ∧ k < j})) := fun y => by
      have := (hg1 j.succ).1 y
      rwa [eg, idx_lt] at this
    obtain ⟨a, ha⟩ := hgh z
    rw [eh, ← tr0, gj, ha, tr]
  · have gj : ∀ y ∈ colSpan F X' {j.succ},
        mat g *ᵥ y - y ∈ colSpan F X' (insert 0 (Fin.succ '' {i | ∃ k ∈ S', i ≤ k ∧ k < j})) := fun y hy => by
      have := (hg1 j.succ).2 y hy
      rwa [eg, idx_lt] at this
    obtain ⟨a, ha⟩ := hgh z
    have := gj _ (mem_colSpan_succ hXs' j hz)
    rw [ha, add_sub_assoc, ← Matrix.mulVec_sub, tr] at this
    rwa [eh]
  · have gK : ∀ y, y ∈ colSpan F X' (insert 0 (Fin.succ '' {i | ∃ k ∈ S', i ≤ k})) ↔
        mat g *ᵥ y ∈ colSpan F X' (insert 0 (Fin.succ '' {i | ∃ k ∈ S', i ≤ k})) := fun y => by
      have := hg2.1 y
      rwa [eg, idx_le] at this
    obtain ⟨a, ha⟩ := hgh z
    rw [eh, ← tr0, gK, ha, tr]
  · have gK : ∀ y ∈ colPerp σ (c₀ • W.J.map σ) X' (insert 0 (Fin.succ '' {i | ∃ k ∈ S', i ≤ k})),
        mat g *ᵥ y - y ∈ colSpan F X' (insert 0 (Fin.succ '' {i | ∃ k ∈ S', i ≤ k})) := fun y hy => by
      have := hg2.2 y (by rwa [idx_le])
      rwa [eg, idx_le] at this
    obtain ⟨a, ha⟩ := hgh z
    have := gK _ (mem_colPerp hσ hsk hι hJ₁ c₀ hX0' hXs' _ hz)
    rw [ha, add_sub_assoc, ← Matrix.mulVec_sub, tr] at this
    rwa [eh]

end GlobalTheory.StdPar.PlaneStep
