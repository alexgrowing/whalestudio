import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition

open Matrix Formalism.REAL
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Dec.IwKC

variable {n : ℕ}

theorem diag_mul_lo {a b : Matrix (Fin n) (Fin n) ℂ} (ha : IsLo a) (hb : IsLo b) (i : Fin n) :
    (a * b) i i = a i i * b i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hb k i h, mul_zero]
    · rw [ha i k h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem lo_iff {a : Matrix (Fin n) (Fin n) ℂ} : IsLo a ↔ a.IsLowerTriangular := by
  constructor
  · intro h i j hij
    exact h i j (OrderDual.toDual_lt_toDual.mp hij)
  · intro h i j hij
    exact h (OrderDual.toDual_lt_toDual.mpr hij)

theorem lo_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : IsLo a) (hb : IsLo b) : IsLo (a * b) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge i k with h | h
  · rw [ha i k h, zero_mul]
  · rw [hb k j (lt_of_le_of_lt h hij), mul_zero]

theorem lo_inv {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsLo a) (hu : IsUnit a) : IsLo a⁻¹ := by
  rw [lo_iff] at ha ⊢
  have := hu.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular ha

theorem isUnit_iff_lo {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsLo a) : IsUnit a ↔ ∀ i, a i i ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    Matrix.det_of_isLowerTriangular a (lo_iff.mp ha), Finset.prod_ne_zero_iff]
  simp

theorem chol_unique {b b' : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b) (hb' : IsLo b')
    (hp : ∀ i, 0 < b i i) (hp' : ∀ i, 0 < b' i i) (h : bᴴ * b = b'ᴴ * b') : b = b' := by
  have hu : IsUnit b.det :=
    (Matrix.isUnit_iff_isUnit_det b).mp ((isUnit_iff_lo hb).2 fun i => (hp i).ne')
  have hu' : IsUnit b'.det :=
    (Matrix.isUnit_iff_isUnit_det b').mp ((isUnit_iff_lo hb').2 fun i => (hp' i).ne')
  have hbi : IsLo b⁻¹ := lo_inv hb ((Matrix.isUnit_iff_isUnit_det b).mpr hu)
  have hbi' : IsLo b'⁻¹ := lo_inv hb' ((Matrix.isUnit_iff_isUnit_det b').mpr hu')

  have hCl : IsLo (b' * b⁻¹) := lo_mul hb' hbi
  have hEl : IsLo (b * b'⁻¹) := lo_mul hb hbi'
  have hCE : b' * b⁻¹ = (b * b'⁻¹)ᴴ := by
    have h2 : (b'⁻¹)ᴴ * (b'ᴴ * b') * b⁻¹ = (b'⁻¹)ᴴ * (bᴴ * b) * b⁻¹ := by rw [h]
    have hl : (b'⁻¹)ᴴ * (b'ᴴ * b') * b⁻¹ = b' * b⁻¹ := by
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu',
        Matrix.conjTranspose_one, Matrix.one_mul]
    have hr : (b'⁻¹)ᴴ * (bᴴ * b) * b⁻¹ = (b * b'⁻¹)ᴴ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
        Matrix.conjTranspose_mul]
    rw [← hl, h2, hr]
  have hinv : ∀ i, b⁻¹ i i * b i i = 1 := fun i => by
    rw [← diag_mul_lo hbi hb i, Matrix.nonsing_inv_mul _ hu, Matrix.one_apply_eq]
  have hinv' : ∀ i, b'⁻¹ i i * b' i i = 1 := fun i => by
    rw [← diag_mul_lo hbi' hb' i, Matrix.nonsing_inv_mul _ hu', Matrix.one_apply_eq]
  have hC1 : b' * b⁻¹ = 1 := by
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [hCl i j hij, Matrix.one_apply_ne hij.ne]
    · have e1 : (b' * b⁻¹) i i = b' i i * b⁻¹ i i := diag_mul_lo hb' hbi i
      have e2 : (b' * b⁻¹) i i = star (b i i * b'⁻¹ i i) := by
        rw [hCE, Matrix.conjTranspose_apply, diag_mul_lo hb hbi' i]
      obtain ⟨r, hr, hx⟩ : ∃ r : ℝ, 0 < r ∧ b i i = r := by
        obtain ⟨h1, h2⟩ := Complex.pos_iff.mp (hp i)
        exact ⟨(b i i).re, h1, Complex.ext (by simp) (by simp [← h2])⟩
      obtain ⟨r', hr', hx'⟩ : ∃ r : ℝ, 0 < r ∧ b' i i = r := by
        obtain ⟨h1, h2⟩ := Complex.pos_iff.mp (hp' i)
        exact ⟨(b' i i).re, h1, Complex.ext (by simp) (by simp [← h2])⟩
      have hu1 : b⁻¹ i i = ((r⁻¹ : ℝ) : ℂ) := by
        rw [eq_inv_of_mul_eq_one_left (hinv i), hx, Complex.ofReal_inv]
      have hu1' : b'⁻¹ i i = ((r'⁻¹ : ℝ) : ℂ) := by
        rw [eq_inv_of_mul_eq_one_left (hinv' i), hx', Complex.ofReal_inv]
      rw [hx', hu1] at e1
      rw [hx, hu1'] at e2
      have key : r' * r⁻¹ = r * r'⁻¹ := by
        have e3 := e1.symm.trans e2
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.star_def, Complex.conj_ofReal] at e3
        exact_mod_cast e3
      have hsq : r' * r' = r * r := by
        field_simp at key
        nlinarith [key]
      have hrr : r' = r := by
        rcases mul_self_eq_mul_self_iff.mp hsq with h3 | h3
        · exact h3
        · linarith
      rw [e1, hrr, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one,
        Matrix.one_apply_eq]
    · rw [hCE, Matrix.conjTranspose_apply, hEl j i hij, star_zero, Matrix.one_apply_ne hij.ne']
  calc b = 1 * b := (Matrix.one_mul b).symm
    _ = b' * b⁻¹ * b := by rw [hC1]
    _ = b' := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem exists_lo (g : Matrix (Fin n) (Fin n) ℂ) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, IsLo R ∧ Rᴴ * R = gᴴ * g := by
  classical
  let f : (Fin n)ᵒᵈ → EuclideanSpace ℂ (Fin n) :=
    fun i => WithLp.toLp 2 (fun k => g k (OrderDual.ofDual i))
  have hd : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n)ᵒᵈ := by simp
  let B := InnerProductSpace.gramSchmidtOrthonormalBasis hd f
  refine ⟨Matrix.of fun a c => inner ℂ (B (OrderDual.toDual a)) (f (OrderDual.toDual c)), ?_, ?_⟩
  · intro a c hac
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hd f (OrderDual.toDual_lt_toDual.mpr hac)
  · ext i j
    have hf : inner ℂ (f (OrderDual.toDual i)) (f (OrderDual.toDual j)) = (gᴴ * g) i j := by
      simp [f, PiLp.inner_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [← hf, ← B.sum_inner_mul_inner]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    refine Fintype.sum_equiv OrderDual.toDual _ _ (fun a => ?_)
    rw [← inner_conj_symm (B (OrderDual.toDual a)) (f (OrderDual.toDual i)), Complex.star_def,
      Complex.conj_conj]

theorem exists_chol {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) :
    ∃ b : Matrix (Fin n) (Fin n) ℂ, IsLo b ∧ (∀ i, 0 < b i i) ∧ bᴴ * b = gᴴ * g := by
  obtain ⟨R, hR, hRg⟩ := exists_lo g
  have hRu : IsUnit R := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    have hg' : g.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det g).mp hg)
    have h1 : (Rᴴ * R).det ≠ 0 := by
      rw [hRg, Matrix.det_mul, Matrix.det_conjTranspose]
      exact mul_ne_zero (star_ne_zero.mpr hg') hg'
    rw [Matrix.det_mul] at h1
    exact right_ne_zero_of_mul h1
  have hne : ∀ i, R i i ≠ 0 := (isUnit_iff_lo hR).1 hRu
  let d : Fin n → ℂ := fun i => ((‖R i i‖ : ℝ) : ℂ) / R i i
  have hd : ∀ i, star (d i) * d i = 1 := by
    intro i
    rw [Complex.star_def, Complex.conj_mul']
    have : ‖d i‖ = 1 := by
      simp only [d, norm_div, Complex.norm_real, norm_norm]
      exact div_self (norm_ne_zero_iff.mpr (hne i))
    rw [this]
    simp
  refine ⟨Matrix.diagonal d * R, ?_, ?_, ?_⟩
  · intro i j hij
    rw [Matrix.diagonal_mul, hR i j hij, mul_zero]
  · intro i
    rw [Matrix.diagonal_mul]
    simp only [d]
    rw [div_mul_cancel₀ _ (hne i)]
    exact Complex.zero_lt_real.mpr (norm_pos_iff.mpr (hne i))
  · have hDD : (Matrix.diagonal d)ᴴ * Matrix.diagonal d = 1 := by
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact hd i
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal d)ᴴ, hDD,
      Matrix.one_mul, hRg]

theorem gram_unitary_mul {k b : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (k * b)ᴴ * (k * b) = bᴴ * b := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ,
    ← Matrix.star_eq_conjTranspose k, Matrix.mem_unitaryGroup_iff'.mp hk, Matrix.one_mul]

theorem decomp_unique {k k' b b' : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hk' : k' ∈ Matrix.unitaryGroup (Fin n) ℂ) (hb : IsLo b) (hb' : IsLo b')
    (hp : ∀ i, 0 < b i i) (hp' : ∀ i, 0 < b' i i) (h : k * b = k' * b') : k = k' ∧ b = b' := by
  have hg : bᴴ * b = b'ᴴ * b' := by
    rw [← gram_unitary_mul hk, h, gram_unitary_mul hk']
  have hbb : b = b' := chol_unique hb hb' hp hp' hg
  subst hbb
  refine ⟨?_, rfl⟩
  have hu : IsUnit b.det :=
    (Matrix.isUnit_iff_isUnit_det b).mp ((isUnit_iff_lo hb).2 fun i => (hp i).ne')
  calc k = k * b * b⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = k' * b * b⁻¹ := by rw [h]
    _ = k' := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem exists_decomp (ε : Fin n → Bool) {y : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ KC ε) :
    ∃ k b : Matrix (Fin n) (Fin n) ℂ, k ∈ Kset ε ∧ b ∈ KC ε ∧ IsLo b ∧ (∀ l, 0 < b l l) ∧ y = k * b := by
  obtain ⟨hyu, hyJ⟩ := hy
  obtain ⟨b, hb, hp, hbg⟩ := exists_chol hyu
  have hbd : IsUnit b.det :=
    (Matrix.isUnit_iff_isUnit_det b).mp ((isUnit_iff_lo hb).2 fun i => (hp i).ne')
  have hJJ : Jm ε * Jm ε = 1 := Jm_mul_self ε
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTranspose ε
  let s : Fin n → ℂ := fun a => if ε a then 1 else -1
  have hJ : Jm ε = Matrix.diagonal s := rfl
  have hs : ∀ a, s a * s a = 1 := fun a => by by_cases h : ε a <;> simp [s, h]

  have hc : IsLo (Jm ε * b * Jm ε) := by
    intro i j hij
    rw [hJ, Matrix.mul_diagonal, Matrix.diagonal_mul, hb i j hij, mul_zero, zero_mul]
  have hcd : ∀ l, (Jm ε * b * Jm ε) l l = b l l := by
    intro l
    rw [hJ, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm (s l), mul_assoc, hs, mul_one]
  have hyJh : Jm ε * yᴴ = yᴴ * Jm ε := by
    have e := congrArg Matrix.conjTranspose hyJ
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh] at e
  have hcg : (Jm ε * b * Jm ε)ᴴ * (Jm ε * b * Jm ε) = bᴴ * b := by
    simp only [Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Jm ε) (Jm ε), hJJ, Matrix.one_mul, ← Matrix.mul_assoc bᴴ b, hbg,
      Matrix.mul_assoc yᴴ, hyJ, ← Matrix.mul_assoc yᴴ, ← hyJh, Matrix.mul_assoc (Jm ε) yᴴ,
      ← Matrix.mul_assoc (Jm ε) (Jm ε), hJJ, Matrix.one_mul]
  have hbc : b = Jm ε * b * Jm ε :=
    chol_unique hb hc hp (fun l => by rw [hcd]; exact hp l) hcg.symm
  have hbJ : b * Jm ε = Jm ε * b := by
    calc b * Jm ε = Jm ε * b * Jm ε * Jm ε := by rw [← hbc]
      _ = Jm ε * b := by rw [Matrix.mul_assoc _ (Jm ε), hJJ, Matrix.mul_one]
  have hbiJ : b⁻¹ * Jm ε = Jm ε * b⁻¹ := by
    have e : b⁻¹ * (b * Jm ε) * b⁻¹ = b⁻¹ * (Jm ε * b) * b⁻¹ := by rw [hbJ]
    rw [← Matrix.mul_assoc b⁻¹ b, Matrix.nonsing_inv_mul _ hbd, Matrix.one_mul,
      Matrix.mul_assoc b⁻¹, Matrix.mul_assoc (Jm ε), Matrix.mul_nonsing_inv _ hbd,
      Matrix.mul_one] at e
    exact e.symm
  refine ⟨y * b⁻¹, b, ⟨?_, ?_⟩, ⟨(Matrix.isUnit_iff_isUnit_det b).mpr hbd, hbJ⟩, hb, hp, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc yᴴ, ← hbg, Matrix.mul_assoc bᴴ,
      Matrix.mul_nonsing_inv _ hbd, Matrix.mul_one, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ hbd, Matrix.conjTranspose_one]
  · rw [Matrix.mul_assoc, hbiJ, ← Matrix.mul_assoc, hyJ, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hbd, Matrix.mul_one]

theorem continuous_of_closed_graph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {f : X → Y} (h : IsClosed {p : X × Y | p.2 = f p.1}) : Continuous f := by
  refine continuous_iff_isClosed.mpr fun C hC => ?_
  have e : f ⁻¹' C = Prod.fst '' ({p : X × Y | p.2 = f p.1} ∩ Prod.snd ⁻¹' C) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x, f x), ⟨rfl, hx⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hpC⟩, rfl⟩
      show f p.1 ∈ C
      rw [← (show p.2 = f p.1 from hp)]
      exact hpC
  rw [e]
  exact isClosedMap_fst_of_compactSpace _ (h.inter (hC.preimage continuous_snd))

end GlobalTheory.Dec.IwKC

namespace GlobalTheory.Dec

open IwKC

theorem iwasawaKC : IwasawaKC := by
  intro n ε
  classical
  have := Complex.orderClosedTopology
  have key : ∀ y ∈ KC ε, ∃ k b : Matrix (Fin n) (Fin n) ℂ,
      k ∈ Kset ε ∧ b ∈ KC ε ∧ IsLo b ∧ (∀ l, 0 < b l l) ∧ y = k * b :=
    fun y hy => exists_decomp ε hy
  choose! κ β hκ using key
  have hβ : ∀ y ∈ KC ε, β y = (κ y)ᴴ * y := by
    intro y hy
    obtain ⟨hk, -, -, -, hy'⟩ := hκ y hy
    have hu : star (κ y) * κ y = 1 := Matrix.mem_unitaryGroup_iff'.mp hk.1
    rw [show (κ y)ᴴ * y = (κ y)ᴴ * (κ y * β y) by rw [← hy'], ← Matrix.mul_assoc,
      ← Matrix.star_eq_conjTranspose, hu, Matrix.one_mul]
  have unitK : ∀ k ∈ Kset ε, IsUnit k := fun k hk =>
    (Matrix.isUnit_iff_isUnit_det k).2 (IsUnit.of_mul_eq_one (star k).det
      (by rw [← Matrix.det_mul, Matrix.mem_unitaryGroup_iff.mp hk.1, Matrix.det_one]))
  have unitKh : ∀ k ∈ Kset ε, IsUnit kᴴ := fun k hk =>
    (Matrix.isUnit_iff_isUnit_det kᴴ).2 (IsUnit.of_mul_eq_one k.det
      (by rw [← Matrix.det_mul, ← Matrix.star_eq_conjTranspose,
        Matrix.mem_unitaryGroup_iff'.mp hk.1, Matrix.det_one]))

  have hKc : IsCompact (Kset ε) := by
    have hB := isCompact_univ_pi fun _ : Fin n =>
      isCompact_univ_pi fun _ : Fin n => isCompact_closedBall (0 : ℂ) 1
    refine IsCompact.of_isClosed_subset hB ?_ ?_
    · have e : Kset ε = {g : Matrix (Fin n) (Fin n) ℂ | star g * g = 1 ∧ g * star g = 1} ∩
          {g | g * Jm ε = Jm ε * g} := by
        ext g
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨⟨Matrix.mem_unitaryGroup_iff'.mp h1, Matrix.mem_unitaryGroup_iff.mp h1⟩, h2⟩
        · rintro ⟨⟨h1, -⟩, h2⟩
          exact ⟨Matrix.mem_unitaryGroup_iff'.mpr h1, h2⟩
      rw [e, Set.ofPred_and]
      exact ((isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
        (isClosed_eq (continuous_id.mul continuous_star) continuous_const)).inter
        (isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id))
    · intro g hg
      exact Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j =>
        mem_closedBall_zero_iff.mpr (entry_norm_bound_of_unitary hg.1 i j)
  have : CompactSpace (Kset ε) := isCompact_iff_compactSpace.mp hKc

  let F : KC ε → Kset ε := fun y => ⟨κ y, (hκ y y.2).1⟩
  have hT : IsClosed {m : Matrix (Fin n) (Fin n) ℂ | IsLo m ∧ ∀ l, 0 ≤ m l l} := by
    have e : {m : Matrix (Fin n) (Fin n) ℂ | IsLo m ∧ ∀ l, 0 ≤ m l l} =
        (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), {m : Matrix (Fin n) (Fin n) ℂ | m i j = 0}) ∩
          ⋂ l : Fin n, {m : Matrix (Fin n) (Fin n) ℂ | 0 ≤ m l l} := by
      ext m
      simp [IsLo]
    rw [e]
    exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (continuous_id.matrix_elem i j) continuous_const).inter
      (isClosed_iInter fun l => isClosed_le continuous_const (continuous_id.matrix_elem l l))
  have hcm : Continuous fun p : KC ε × Kset ε =>
      ((p.2 : Matrix (Fin n) (Fin n) ℂ)ᴴ * (p.1 : Matrix (Fin n) (Fin n) ℂ)) :=
    ((continuous_subtype_val.comp continuous_snd).matrix_conjTranspose).matrix_mul
      (continuous_subtype_val.comp continuous_fst)
  have hgraph : IsClosed {p : KC ε × Kset ε | p.2 = F p.1} := by
    have e : {p : KC ε × Kset ε | p.2 = F p.1} =
        (fun p : KC ε × Kset ε => ((p.2 : Matrix (Fin n) (Fin n) ℂ)ᴴ * (p.1 : Matrix (Fin n) (Fin n) ℂ))) ⁻¹'
          {m : Matrix (Fin n) (Fin n) ℂ | IsLo m ∧ ∀ l, 0 ≤ m l l} := by
      ext ⟨⟨y, hy⟩, ⟨k, hk⟩⟩
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      constructor
      · intro hp
        have hk' : k = κ y := congrArg Subtype.val hp
        rw [hk', ← hβ y hy]
        obtain ⟨-, -, hb, hpos, -⟩ := hκ y hy
        exact ⟨hb, fun l => (hpos l).le⟩
      · rintro ⟨hlo, hnn⟩
        have hyk : y = k * (kᴴ * y) := by
          rw [← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp hk.1,
            Matrix.one_mul]
        have hub : IsUnit (kᴴ * y) := (unitKh k hk).mul hy.1
        have hne := (isUnit_iff_lo hlo).1 hub
        have hpos : ∀ l, 0 < (kᴴ * y) l l := fun l => lt_of_le_of_ne (hnn l) (hne l).symm
        obtain ⟨hk1, -, hb1, hp1, hy1⟩ := hκ y hy
        have := (decomp_unique hk1.1 hk.1 hb1 hlo hp1 hpos (hy1.symm.trans hyk)).1
        exact Subtype.ext this.symm
    rw [e]
    exact hT.preimage hcm
  have hF : Continuous F := continuous_of_closed_graph hgraph
  have hcont : ContinuousOn κ (KC ε) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_subtype_val.comp hF
  refine ⟨κ, β, fun y hy => hκ y hy, hcont, ?_, ?_⟩
  · refine ContinuousOn.congr ?_ hβ
    exact (continuous_id.matrix_conjTranspose.comp_continuousOn hcont).mul continuousOn_id
  · intro k hk b hbK hb hp
    have hkb : k * b ∈ KC ε := by
      refine ⟨(unitK k hk).mul hbK.1, ?_⟩
      rw [Matrix.mul_assoc, hbK.2, ← Matrix.mul_assoc, hk.2, Matrix.mul_assoc]
    obtain ⟨hk', -, hb', hp', he⟩ := hκ _ hkb
    exact decomp_unique hk'.1 hk.1 hb' hb hp' hp he.symm

end GlobalTheory.Dec
