import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip

noncomputable section

namespace GlobalTheory.LiftCentral

section Gen
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem vmv_mul_vmv (a b c d : n → R) :
    Matrix.vecMulVec a b * Matrix.vecMulVec c d = (b ⬝ᵥ c) • Matrix.vecMulVec a d := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, dotProduct, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem vmv_mul {k : Type} [Fintype k] (a : n → R) (b : n → R) (M : Matrix n k R) :
    Matrix.vecMulVec a b * M = Matrix.vecMulVec a (b ᵥ* M) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem mul_vmv (a b : n → R) (M : Matrix n n R) :
    M * Matrix.vecMulVec a b = Matrix.vecMulVec (M *ᵥ a) b := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem vmv_neg (a b : n → R) : Matrix.vecMulVec a (-b) = -Matrix.vecMulVec a b := by
  ext i j; simp [Matrix.vecMulVec_apply]

end Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def trv (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (f : E) :
    Matrix (Fin n) (Fin n) E :=
  1 - f • Matrix.vecMulVec x (J *ᵥ fun i => σ (x i))

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : Fin n → E}

theorem trv_mul (hxx : form σ J x x = 0) (f g : E) : trv σ J x f * trv σ J x g = trv σ J x (f + g) := by
  have hAA : Matrix.vecMulVec x (J *ᵥ fun i => σ (x i)) * Matrix.vecMulVec x (J *ᵥ fun i => σ (x i)) = 0 := by
    rw [vmv_mul_vmv, dotProduct_comm]
    change form σ J x x • _ = _
    rw [hxx, zero_smul]
  simp only [trv, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hAA, smul_zero, add_smul]
  module

theorem trv_zero : trv σ J x 0 = 1 := by simp [trv]

theorem trv_unitary (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = -J i j) (hxx : form σ J x x = 0) {f : E}
    (hf : σ f = f) : (trv σ J x f)ᵀ * J * (trv σ J x f).map σ = J := by
  set c : Fin n → E := J *ᵥ fun i => σ (x i) with hc
  have hsc : (fun i => σ (c i)) = -(x ᵥ* J) := by
    ext j
    simp only [hc, Matrix.mulVec, dotProduct, map_sum, Pi.neg_apply, Matrix.vecMul]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul, hσ, hJ]; ring
  have hT : (trv σ J x f)ᵀ = 1 - f • Matrix.vecMulVec c x := by
    simp [trv, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_vecMulVec, hc]
  have hM : (trv σ J x f).map σ = 1 - f • Matrix.vecMulVec (fun i => σ (x i)) (fun i => σ (c i)) := by
    ext i j
    simp [trv, Matrix.one_apply, Matrix.vecMulVec_apply, apply_ite σ, hf, hc]
  set V := Matrix.vecMulVec c (x ᵥ* J) with hV
  have h1 : Matrix.vecMulVec c x * J = V := vmv_mul _ _ _
  have h2 : J * Matrix.vecMulVec (fun i => σ (x i)) (fun i => σ (c i)) = -V := by
    rw [mul_vmv, hsc, vmv_neg]
  have h3 : V * Matrix.vecMulVec (fun i => σ (x i)) (fun i => σ (c i)) = 0 := by
    rw [vmv_mul_vmv, ← Matrix.dotProduct_mulVec]
    change form σ J x x • _ = _
    rw [hxx, zero_smul]
  rw [hT, hM, sub_mul, one_mul, smul_mul_assoc, h1]
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h2, h3, smul_zero, smul_neg]
  module

end GlobalTheory.LiftCentral

namespace GlobalTheory.LiftCentral

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_swap_skew {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hσ : ∀ e, σ (σ e) = e)
    (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin n → E) : form σ J y x = -σ (form σ J x y) := by
  simp only [form, Matrix.mulVec, dotProduct, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem basQ_isUnit {σ : E →ₐ[F] E} {B : Base F E} {m : ℕ} {W : Spc F E (m + 2)} {r s : ℕ} (hW : W.IsSkew σ B r s)
    {W₁ : Spc F E m} {H : Plane E (m + 2) m} {i₀ i₁ : ℕ} (hH : H.IsAdapted σ B W W₁ i₀ i₁) : IsUnit (basQ H) := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  have hL : (W.L : Set (Fin (m + 2) → E)) ⊆ LinearMap.range (Matrix.mulVecLin (basQ H)) := by
    intro z hz
    obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
    refine ⟨fun i => Sum.elim (Sum.elim (fun _ => s) u) (fun _ => t) (ixE m i), ?_⟩
    ext q
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, basQ, Matrix.submatrix_apply, id]
    rw [(ixE m).sum_comp (fun j => basP H q j * Sum.elim (Sum.elim (fun _ => s) u) (fun _ => t) j)]
    simp [Fintype.sum_sum_type, basP, Matrix.mulVec, dotProduct, mul_comm]
  have htop : Submodule.span E (W.L : Set (Fin (m + 2) → E)) = ⊤ := by
    haveI := hW.lat
    exact Submodule.IsLattice.span_eq_top
  intro z
  have hz : z ∈ LinearMap.range (Matrix.mulVecLin (basQ H)) := by
    have h := Submodule.span_le.2 hL
    rw [htop] at h
    exact h Submodule.mem_top
  obtain ⟨v, hv⟩ := hz
  exact ⟨v, hv⟩

end GlobalTheory.LiftCentral

namespace GlobalTheory.LiftCentral

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem heis_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ} (a w : Fin m → R) (α : R) :
    (Heisenberg₂ a w α).map φ = Heisenberg₂ (fun k => φ (a k)) (fun k => φ (w k)) (φ α) := by
  ext ((i | i) | i) ((j | j) | j) <;> simp [Heisenberg₂, Matrix.one_apply, Matrix.fromBlocks, apply_ite φ]

theorem trv_mul_basQ {σ : E →ₐ[F] E} {B : Base F E} {m : ℕ} {W : Spc F E (m + 2)} {r s : ℕ} (hσ : ∀ e, σ (σ e) = e)
    (hW : W.IsSkew σ B r s) {W₁ : Spc F E m} {H : Plane E (m + 2) m} {i₀ i₁ : ℕ} (hH : H.IsAdapted σ B W W₁ i₀ i₁)
    (f : E) : trv σ W.J H.x f * basQ H = basQ H * (Heisenberg₂ 0 0 f).submatrix (ixE m) (ixE m) := by
  have hyx : form σ W.J H.y H.x = -1 := by rw [form_swap_skew hσ hW.skew, hH.xy, map_one]
  have hι : ∀ k, form σ W.J (fun q => H.ι q k) H.x = 0 := by
    intro k
    have h := (hH.orth (Pi.single k 1)).1
    rwa [Matrix.mulVec_single_one] at h
  have hcol : ∀ i, ((W.J *ᵥ fun i => σ (H.x i)) ᵥ* basQ H) ((ixE m).symm i) = form σ W.J (fun q => basP H q i) H.x := by
    intro i
    simp only [Matrix.vecMul, form, basQ, Matrix.submatrix_apply, id, Equiv.apply_symm_apply]
    exact dotProduct_comm _ _
  have hR : ∀ q i, (basQ H * (Heisenberg₂ 0 0 f).submatrix (ixE m) (ixE m)) q ((ixE m).symm i) =
      ∑ i', basP H q i' * Heisenberg₂ 0 0 f i' i := by
    intro q i
    simp only [Matrix.mul_apply, basQ, Matrix.submatrix_apply, id, Equiv.apply_symm_apply]
    exact (ixE m).sum_comp (fun i' => basP H q i' * Heisenberg₂ 0 0 f i' i)
  have hL : ∀ q i, (basQ H) q ((ixE m).symm i) = basP H q i := by
    intro q i; simp [basQ]
  rw [trv, sub_mul, one_mul, smul_mul_assoc, vmv_mul]
  ext q j
  obtain ⟨i, rfl⟩ := (ixE m).symm.surjective j
  rw [hR, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, hcol, hL]
  rcases i with ((i | k) | i)
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    simp [hH.xx, Fintype.sum_sum_type, Heisenberg₂, Matrix.fromBlocks, basP, Matrix.one_apply]
  · simp [hι, Fintype.sum_sum_type, Heisenberg₂, Matrix.fromBlocks, basP, Matrix.one_apply]
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    simp [hyx, Fintype.sum_sum_type, Heisenberg₂, Matrix.fromBlocks, basP, Matrix.one_apply]
    ring

end GlobalTheory.LiftCentral

namespace GlobalTheory.LiftCentral

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR' (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem exists_rat_heis_center : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (B : Base F E) {m : ℕ} (W : Spc F E (m + 2)) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (W₁ : Spc F E m) (H : Plane E (m + 2) m) (i₀ i₁ : ℕ), H.IsAdapted σ B W W₁ i₀ i₁ → ∀ f : E, σ f = f → ∃ γ ∈ ratU σ W.J, crd H γ = Heisenberg₂ 0 0 (inclR (F := F) (AF F) f) := by
  intro F E _ _ _ _ _ σ hσ B m W r s hW W₁ H i₀ i₁ hH f hf
  have hxx : form σ W.J H.x H.x = 0 := hH.xx
  let g : GL (Fin (m + 2)) E := ⟨trv σ W.J H.x f, trv σ W.J H.x (-f),
    by rw [trv_mul hxx, add_neg_cancel, trv_zero], by rw [trv_mul hxx, neg_add_cancel, trv_zero]⟩
  have hg : (g : Matrix (Fin (m + 2)) (Fin (m + 2)) E)ᵀ * W.J * (g : Matrix (Fin (m + 2)) (Fin (m + 2)) E).map σ = W.J :=
    trv_unitary hσ hW.skew hxx hf
  let γ : UA σ W.J := ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) g, by
    show ((g : Matrix (Fin (m + 2)) (Fin (m + 2)) E).map (inclR (F := F) (AF F)))ᵀ * W.J.map (inclR (F := F) (AF F)) *
      ((g : Matrix (Fin (m + 2)) (Fin (m + 2)) E).map (inclR (F := F) (AF F))).map (cA σ) = W.J.map (inclR (F := F) (AF F))
    rw [Matrix.map_map, show (cA σ ∘ inclR (F := F) (AF F)) = inclR (F := F) (AF F) ∘ σ from funext (cA_inclR' σ),
      ← Matrix.map_map, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hg]⟩
  have hmat : mat γ = (trv σ W.J H.x f).map (inclR (F := F) (AF F)) := rfl
  refine ⟨γ, Subgroup.mem_subgroupOf.2 ⟨g, rfl⟩, ?_⟩
  have hP : IsUnit (incM F (basQ H)).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (basQ_isUnit hW hH)).map _
  have key : mat γ * incM F (basQ H) = incM F (basQ H) * incM F ((Heisenberg₂ 0 0 f).submatrix (ixE m) (ixE m)) := by
    rw [hmat, incM, incM, ← Matrix.map_mul, ← Matrix.map_mul, trv_mul_basQ hσ hW hH]
  unfold crd
  rw [Matrix.mul_assoc, key, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
  have h0 : (0 : Fin m → AE F E) = fun k => inclR (F := F) (AF F) ((0 : Fin m → E) k) := by ext; simp
  rw [h0, ← heis_map (inclR (F := F) (AF F)) 0 0 f]
  ext i j
  simp [incM]

end GlobalTheory.LiftCentral
