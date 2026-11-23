import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChangeGen

open Matrix GlobalTheory.SympChange

variable {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]

def upM (T : Matrix κ κ K) : Matrix (κ ⊕ κ) (κ ⊕ κ) K := fromBlocks 1 T 0 1

theorem weylM_mem : (weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ Submonoid.closure (gens (F := K) (κ := κ)) :=
  Submonoid.subset_closure (Or.inr rfl)

theorem leviM_mem (A : Matrix κ κ K) (h : IsUnit A.det) :
    leviM A ∈ Submonoid.closure (gens (F := K) (κ := κ)) :=
  Submonoid.subset_closure (Or.inl (Or.inl ⟨A, h, rfl⟩))

theorem unipM_mem (S : Matrix κ κ K) (h : Sᵀ = S) :
    unipM S ∈ Submonoid.closure (gens (F := K) (κ := κ)) :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨S, h, rfl⟩))

theorem upM_eq (T : Matrix κ κ K) :
    upM T = weylM * unipM (-T) * (weylM * weylM * weylM) := by
  simp [upM, weylM, unipM, fromBlocks_multiply]

theorem upM_mem (T : Matrix κ κ K) (h : Tᵀ = T) :
    upM T ∈ Submonoid.closure (gens (F := K) (κ := κ)) := by
  rw [upM_eq]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ weylM_mem (unipM_mem _ (by rw [transpose_neg, h])))
    (Submonoid.mul_mem _ (Submonoid.mul_mem _ weylM_mem weylM_mem) weylM_mem)

theorem isSymp_mul {G H : Matrix (κ ⊕ κ) (κ ⊕ κ) K} (hG : IsSymp G) (hH : IsSymp H) :
    IsSymp (G * H) := by
  unfold IsSymp at *
  calc (G * H)ᵀ * weylM * (G * H) = Hᵀ * (Gᵀ * weylM * G) * H := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = weylM := by rw [hG, hH]

theorem isSymp_upM (T : Matrix κ κ K) (h : Tᵀ = T) : IsSymp (upM T) := by
  simp [IsSymp, upM, weylM, fromBlocks_transpose, fromBlocks_multiply, h]

theorem weyl_sq : (weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * weylM = -1 := by
  simp [weylM, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem exists_sym_isUnit (a c : Matrix κ κ K) (hs : aᵀ * c = cᵀ * a)
    (hinj : ∀ x, a *ᵥ x = 0 → c *ᵥ x = 0 → x = 0) :
    ∃ T : Matrix κ κ K, Tᵀ = T ∧ IsUnit (a + T * c).det := by
  classical
  let P : Finset κ → Prop := fun s => ∀ y, (∀ i ∉ s, (a *ᵥ y) i = 0) → a *ᵥ y = 0
  have hP0 : P ∅ := fun y hy => funext fun i => hy i (Finset.notMem_empty i)
  obtain ⟨s, hs_mem, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) Finset.card
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, hP0⟩⟩
  have hsP : P s := (Finset.mem_filter.1 hs_mem).2
  have key : ∀ z : κ → K, (∀ i ∈ s, z i = 0) → (∀ y, z ⬝ᵥ (a *ᵥ y) = 0) → z = 0 := by
    intro z hzs hzo
    funext j
    by_cases hj : j ∈ s
    · exact hzs j hj
    · have hnot : ¬ P (insert j s) := by
        intro hP'
        have := hmax (insert j s) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hP'⟩)
        rw [Finset.card_insert_of_notMem hj] at this
        omega
      simp only [P, not_forall] at hnot
      obtain ⟨y, hy, hne⟩ := hnot
      have hvj : (a *ᵥ y) j ≠ 0 := by
        intro h0
        apply hne
        apply hsP y
        intro i hi
        by_cases hij : i = j
        · rw [hij]; exact h0
        · exact hy i (by simp [hij, hi])
      have hsum : z ⬝ᵥ (a *ᵥ y) = z j * (a *ᵥ y) j := by
        unfold dotProduct
        apply Finset.sum_eq_single j
        · intro i _ hij
          by_cases his : i ∈ s
          · rw [hzs i his, zero_mul]
          · rw [hy i (by simp [hij, his]), mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have h0 := hzo y
      rw [hsum] at h0
      exact (mul_eq_zero.1 h0).resolve_right hvj
  set T : Matrix κ κ K := diagonal fun i => if i ∈ s then 1 else 0 with hTdef
  have hTe : ∀ w : κ → K, ∀ i, (T *ᵥ w) i = (if i ∈ s then 1 else 0) * w i := fun w i => by
    simp [hTdef, mulVec_diagonal]
  have hx : ∀ x, (a + T * c) *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [add_mulVec, ← mulVec_mulVec] at hx
    have hx2 : ∀ i, (a *ᵥ x) i + (if i ∈ s then 1 else 0) * (c *ᵥ x) i = 0 := fun i => by
      rw [← hTe]; exact congrFun hx i
    have hax : a *ᵥ x = 0 := hsP x (fun i hi => by
      have := hx2 i
      rwa [if_neg hi, zero_mul, add_zero] at this)
    have hcs : ∀ i ∈ s, (c *ᵥ x) i = 0 := fun i hi => by
      have := hx2 i
      rwa [if_pos hi, one_mul, hax, Pi.zero_apply, zero_add] at this
    have horth : ∀ y, (c *ᵥ x) ⬝ᵥ (a *ᵥ y) = 0 := fun y => by
      calc (c *ᵥ x) ⬝ᵥ (a *ᵥ y) = x ⬝ᵥ ((cᵀ * a) *ᵥ y) := by
            rw [← mulVec_mulVec, dotProduct_mulVec x cᵀ, vecMul_transpose]
        _ = x ⬝ᵥ ((aᵀ * c) *ᵥ y) := by rw [hs]
        _ = (a *ᵥ x) ⬝ᵥ (c *ᵥ y) := by
            rw [← mulVec_mulVec, dotProduct_mulVec x aᵀ, vecMul_transpose]
        _ = 0 := by rw [hax, zero_dotProduct]
    exact hinj x hax (key _ hcs horth)
  refine ⟨T, by simp [hTdef], isUnit_iff_ne_zero.2 fun hdet => ?_⟩
  obtain ⟨v, hv, hmv⟩ := exists_mulVec_eq_zero_iff.2 hdet
  exact hv (hx v hmv)

theorem symp_blocks {a b c d : Matrix κ κ K} (h : IsSymp (fromBlocks a b c d)) :
    aᵀ * c = cᵀ * a ∧ aᵀ * d = 1 + cᵀ * b ∧ bᵀ * d = dᵀ * b := by
  simp only [IsSymp, weylM, fromBlocks_transpose, fromBlocks_multiply] at h
  obtain ⟨h11, h12, -, h22⟩ := fromBlocks_inj.1 h
  simp at h11 h12 h22
  refine ⟨(neg_add_eq_zero.1 h11).symm, ?_, (neg_add_eq_zero.1 h22).symm⟩
  rw [← h12]; abel

theorem mem_of_isUnit {a b c d : Matrix κ κ K} (h : IsSymp (fromBlocks a b c d)) (ha : IsUnit a.det) :
    fromBlocks a b c d ∈ Submonoid.closure (gens (F := K) (κ := κ)) := by
  obtain ⟨e1, e2, e3⟩ := symp_blocks h
  have haa : a * a⁻¹ = 1 := mul_nonsing_inv a ha
  have hai : a⁻¹ * a = 1 := nonsing_inv_mul a ha
  have hT1 : a⁻¹ᵀ * aᵀ = 1 := by rw [← transpose_mul, haa, transpose_one]
  have hT2 : aᵀ * a⁻¹ᵀ = 1 := by rw [← transpose_mul, hai, transpose_one]
  set Y := c * a⁻¹ with hYdef
  have hY : Yᵀ = Y := by
    rw [hYdef, transpose_mul]
    calc a⁻¹ᵀ * cᵀ = a⁻¹ᵀ * cᵀ * (a * a⁻¹) := by rw [haa, Matrix.mul_one]
      _ = a⁻¹ᵀ * (cᵀ * a) * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = a⁻¹ᵀ * (aᵀ * c) * a⁻¹ := by rw [e1]
      _ = (a⁻¹ᵀ * aᵀ) * c * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = c * a⁻¹ := by rw [hT1, Matrix.one_mul]
  have hd : d = a⁻¹ᵀ + Y * b := by
    calc d = (a⁻¹ᵀ * aᵀ) * d := by rw [hT1, Matrix.one_mul]
      _ = a⁻¹ᵀ * (aᵀ * d) := by rw [Matrix.mul_assoc]
      _ = a⁻¹ᵀ + (a⁻¹ᵀ * cᵀ) * b := by rw [e2, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]
      _ = a⁻¹ᵀ + Y * b := by rw [← transpose_mul, ← hYdef, hY]
  set X := a⁻¹ * b with hXdef
  have hX : Xᵀ = X := by
    have e3' := e3
    rw [hd, Matrix.mul_add, transpose_add, Matrix.add_mul, transpose_mul, hY, transpose_transpose] at e3'
    simp only [← Matrix.mul_assoc] at e3'
    rw [hXdef, transpose_mul]
    exact add_right_cancel e3'
  have hG : fromBlocks a b c d = unipM Y * leviM a * upM X := by
    simp only [unipM, leviM, upM, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
    congr 1
    · rw [hXdef, ← Matrix.mul_assoc, haa, Matrix.one_mul]
    · rw [hYdef, Matrix.mul_assoc, hai, Matrix.mul_one]
    · rw [hd, hXdef, hYdef, add_comm]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc a a⁻¹ b, haa, Matrix.one_mul]
  rw [hG]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (unipM_mem _ hY) (leviM_mem _ ha)) (upM_mem _ hX)

theorem mem_closure_gens : ∀ (K : Type) [Field K] [CharZero K] (κ : Type) [Fintype κ] [DecidableEq κ]
    (G : Matrix (κ ⊕ κ) (κ ⊕ κ) K),
    GlobalTheory.SympChange.IsSymp G → G ∈ Submonoid.closure (GlobalTheory.SympChange.gens (F := K) (κ := κ)) := by
  intro K _ _ κ _ _ G hG
  rw [← fromBlocks_toBlocks G] at hG ⊢
  set a := G.toBlocks₁₁
  set b := G.toBlocks₁₂
  set c := G.toBlocks₂₁
  set d := G.toBlocks₂₂
  obtain ⟨e1, -, -⟩ := symp_blocks hG

  have hL : (-(weylM * (fromBlocks a b c d)ᵀ * weylM)) * fromBlocks a b c d = 1 := by
    have h := hG
    unfold IsSymp at h
    have e : weylM * (fromBlocks a b c d)ᵀ * weylM * fromBlocks a b c d
        = weylM * ((fromBlocks a b c d)ᵀ * weylM * fromBlocks a b c d) := by simp only [Matrix.mul_assoc]
    rw [Matrix.neg_mul, e, h, weyl_sq, neg_neg]
  have hinj : ∀ x, a *ᵥ x = 0 → c *ᵥ x = 0 → x = 0 := by
    intro x hax hcx
    have hv : fromBlocks a b c d *ᵥ Sum.elim x 0 = 0 := by
      rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, hax, hcx, mulVec_zero, mulVec_zero]
      simp
    have h0 : Sum.elim x (0 : κ → K) = 0 := by
      rw [← Matrix.one_mulVec (Sum.elim x 0), ← hL, ← mulVec_mulVec, hv, mulVec_zero]
    funext i
    exact congrFun h0 (Sum.inl i)
  obtain ⟨T, hT, hu⟩ := exists_sym_isUnit a c e1 hinj
  have hH : upM T * fromBlocks a b c d = fromBlocks (a + T * c) (b + T * d) c d := by
    simp [upM, fromBlocks_multiply]
  have hHs : IsSymp (fromBlocks (a + T * c) (b + T * d) c d) := hH ▸ isSymp_mul (isSymp_upM T hT) hG
  have hinv : upM (-T) * upM T = (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) := by
    simp [upM, fromBlocks_multiply]
  have : fromBlocks a b c d = upM (-T) * fromBlocks (a + T * c) (b + T * d) c d := by
    rw [← hH, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  rw [this]
  exact Submonoid.mul_mem _ (upM_mem _ (by rw [transpose_neg, hT])) (mem_of_isUnit hHs hu)

end GlobalTheory.SympChangeGen
