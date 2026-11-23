import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.HkC

def lA (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] := C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)

def lB (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] := C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)

theorem polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), C (p.coeff i) * (lA g ^ i * lB g ^ (w - i)) := by
  rw [slP, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, lcoeff_apply, LinearMap.toSpanSingleton_apply, ← C_mul']
  rfl

theorem polySlash_monomial (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (k : ℕ) (c : ℂ) (hk : k ≤ w) :
    slP w g (monomial k c) = C c * (lA g ^ k * lB g ^ (w - k)) := by
  rw [polySlash_apply, Finset.sum_eq_single k]
  · simp
  · intro i _ hik; simp [coeff_monomial, Ne.symm hik]
  · intro h; simp at h; omega

theorem mem_degLT_iff {w : ℕ} {p : ℂ[X]} : p ∈ degreeLT ℂ (w + 1) ↔ p.natDegree ≤ w := by
  rw [mem_degreeLT]
  by_cases hp : p = 0
  · subst hp; simp
  · rw [degree_eq_natDegree hp]; norm_cast; omega

theorem natDegree_lA (g : Matrix (Fin 2) (Fin 2) ℤ) : (lA g).natDegree ≤ 1 := natDegree_linear_le
theorem natDegree_lB (g : Matrix (Fin 2) (Fin 2) ℤ) : (lB g).natDegree ≤ 1 := natDegree_linear_le

theorem natDegree_slP_le (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) : (slP w g p).natDegree ≤ w := by
  rw [polySlash_apply]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have hi' : i ≤ w := by simp at hi; omega
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_mul_le.trans ?_
  have h1 := natDegree_pow_le_of_le i (natDegree_lA g)
  have h2 := natDegree_pow_le_of_le (w - i) (natDegree_lB g)
  omega

theorem polySlash_mul (h : Matrix (Fin 2) (Fin 2) ℤ) (m n : ℕ) (q r : ℂ[X]) (hq : q.natDegree ≤ m)
    (hr : r.natDegree ≤ n) : slP (m + n) h (q * r) = slP m h q * slP n h r := by
  have eq := as_sum_range' q (m + 1) (by omega)
  have er := as_sum_range' r (n + 1) (by omega)
  rw [polySlash_apply m h q, polySlash_apply n h r, Finset.sum_mul_sum]
  conv_lhs => rw [eq, er, Finset.sum_mul_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun t ht => ?_
  simp only [Finset.mem_range] at hs ht
  rw [monomial_mul_monomial, polySlash_monomial _ _ _ _ (by omega)]
  have e : m + n - (s + t) = (m - s) + (n - t) := by omega
  rw [e, C_mul, pow_add, pow_add]; ring

theorem polySlash_pow (h : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) (q : ℂ[X]) (hq : q.natDegree ≤ m) :
    ∀ k : ℕ, slP (m * k) h (q ^ k) = (slP m h q) ^ k := by
  intro k
  induction k with
  | zero => simp [polySlash_apply]
  | succ k ih =>
    rw [pow_succ, pow_succ, Nat.mul_succ,
      polySlash_mul h (m * k) m (q ^ k) q ((natDegree_pow_le_of_le k hq).trans (le_of_eq (mul_comm _ _))) hq, ih]

theorem polySlash_one_num (g h : Matrix (Fin 2) (Fin 2) ℤ) : slP 1 h (lA g) = lA (g * h) := by
  have c0 : (lA g).coeff 0 = ((g 0 1 : ℤ) : ℂ) := by rw [lA, coeff_add, coeff_C_mul_X, coeff_C]; simp
  have c1 : (lA g).coeff 1 = ((g 0 0 : ℤ) : ℂ) := by rw [lA, coeff_add, coeff_C_mul_X, coeff_C]; simp
  rw [polySlash_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, c0, c1]
  simp only [lA, lB, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  simp only [C_add, C_mul]
  ring

theorem polySlash_one_denom (g h : Matrix (Fin 2) (Fin 2) ℤ) : slP 1 h (lB g) = lB (g * h) := by
  have c0 : (lB g).coeff 0 = ((g 1 1 : ℤ) : ℂ) := by rw [lB, coeff_add, coeff_C_mul_X, coeff_C]; simp
  have c1 : (lB g).coeff 1 = ((g 1 0 : ℤ) : ℂ) := by rw [lB, coeff_add, coeff_C_mul_X, coeff_C]; simp
  rw [polySlash_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, c0, c1]
  simp only [lA, lB, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  simp only [C_add, C_mul]
  ring

theorem polySlash_comp (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) (hp : p.natDegree ≤ w) :
    slP w h (slP w g p) = slP w (g * h) p := by
  conv_lhs => rw [as_sum_range' p (w + 1) (by omega)]
  conv_rhs => rw [as_sum_range' p (w + 1) (by omega)]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [polySlash_monomial _ _ _ _ (by omega), polySlash_monomial _ _ _ _ (by omega), C_mul', map_smul, C_mul']
  congr 1
  obtain ⟨j, rfl⟩ : ∃ j, w = k + j := ⟨w - k, by omega⟩
  rw [Nat.add_sub_cancel_left,
    polySlash_mul h k j _ _ ((natDegree_pow_le_of_le k (natDegree_lA g)).trans (by omega))
      ((natDegree_pow_le_of_le j (natDegree_lB g)).trans (by omega))]
  have hA := polySlash_pow h 1 (lA g) (natDegree_lA g) k
  have hB := polySlash_pow h 1 (lB g) (natDegree_lB g) j
  rw [one_mul] at hA hB
  rw [hA, hB, polySlash_one_num, polySlash_one_denom]

theorem polySlash_map (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (q : ℂ[X]) :
    (slP w g q).map (starRingEnd ℂ) = slP w g (q.map (starRingEnd ℂ)) := by
  rw [polySlash_apply, polySlash_apply]
  simp [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, lA, lB, coeff_map]

end GlobalTheory.HeckeFamilyMatrices.HkC

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.HkC

variable {Γ : Subgroup SL(2, ℤ)} {α : Matrix (Fin 2) (Fin 2) ℤ} {ι : Type} {δ : ι → Matrix (Fin 2) (Fin 2) ℤ}

theorem matm (a b : Γ) : mat ↑(a * b) = mat ↑a * mat ↑b := rfl

theorem det_mat (γ : SL(2, ℤ)) : (mat γ).det = 1 := γ.2

theorem det_rep (hD : IsDCReps Γ α δ) (i : ι) : (δ i).det = α.det := by
  obtain ⟨γ1, γ2, h⟩ := hD.1 i
  rw [h, Matrix.det_mul, Matrix.det_mul, det_mat, det_mat]; ring

theorem cancel_right {M N D : Matrix (Fin 2) (Fin 2) ℤ} (hD : D.det ≠ 0) (h : M * D = N * D) : M = N := by
  have h2 : M * (D * D.adjugate) = N * (D * D.adjugate) := by rw [← mul_assoc, h, mul_assoc]
  rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_smul, mul_one, mul_one] at h2
  exact smul_right_injective _ hD h2

theorem rep_uniq (hD : IsDCReps Γ α δ) (hα : α.det ≠ 0) {a b : Γ} {j k : ι}
    (h : mat a * δ j = mat b * δ k) : j = k ∧ a = b := by
  obtain ⟨γ1, γ2, hj⟩ := hD.1 j
  obtain ⟨i, _, hi⟩ := hD.2 (a * γ1) γ2
  have e1 : mat ↑(a * γ1) * α * mat γ2 = mat a * δ j := by rw [hj, matm]; simp only [mul_assoc]
  have hjk : j = k := (hi j ⟨a, e1⟩).trans (hi k ⟨b, e1.trans h⟩).symm
  subst hjk
  refine ⟨rfl, ?_⟩
  have := cancel_right (by rw [det_rep hD]; exact hα) h
  exact Subtype.ext (Subtype.ext this)

theorem rep_exists [Fintype ι] (hD : IsDCReps Γ α δ) (hα : α.det ≠ 0) (γ : Γ) :
    ∃ π : Equiv.Perm ι, ∃ g : ι → Γ, ∀ i, δ i * mat γ = mat (g i) * δ (π i) := by
  have hx : ∀ i, ∃ j, ∃ g : Γ, δ i * mat γ = mat g * δ j := by
    intro i
    obtain ⟨γ1, γ2, hi⟩ := hD.1 i
    obtain ⟨j, ⟨g, hg⟩, _⟩ := hD.2 γ1 (γ2 * γ)
    exact ⟨j, g, by rw [hi, ← hg, matm]; simp only [mul_assoc]⟩
  choose f g hfg using hx
  have hinj : Function.Injective f := by
    intro i k hik
    have h1 := hfg i
    have h2 := hfg k
    rw [hik] at h1
    have hγ : (mat γ).det ≠ 0 := by rw [det_mat]; norm_num
    have e : mat ↑(g k * (g i)⁻¹) * δ i = mat ↑(1 : Γ) * δ k := by
      apply cancel_right hγ
      calc mat ↑(g k * (g i)⁻¹) * δ i * mat γ = mat (g k) * mat ↑(g i)⁻¹ * (δ i * mat γ) := by
              rw [matm]; simp only [mul_assoc]
        _ = mat (g k) * mat ↑(g i)⁻¹ * (mat (g i) * δ (f k)) := by rw [h1]
        _ = mat (g k) * mat ↑((g i)⁻¹ * g i) * δ (f k) := by rw [matm]; simp only [mul_assoc]
        _ = mat (g k) * δ (f k) := by simp
        _ = δ k * mat γ := h2.symm
        _ = mat ↑(1 : Γ) * δ k * mat γ := by simp
    exact (rep_uniq hD hα e).1
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), g, hfg⟩

theorem hk_apply [Fintype ι] (w : ℕ) (hD : IsDCReps Γ α δ) (hα : α.det ≠ 0) (z : Γ → ℂ[X]) (γ : Γ)
    (π : Equiv.Perm ι) (g : ι → Γ) (hg : ∀ i, δ i * mat γ = mat (g i) * δ (π i)) :
    hk Γ w δ z γ = ∑ i, slP w (δ (π i)) (z (g i)) := by
  have hex : ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i) :=
    ⟨π, fun i => ⟨g i, hg i⟩⟩
  rw [hk, LinearMap.pi_apply, dif_pos hex, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, LinearMap.proj_apply]
  have e := ((hex.choose_spec i).choose_spec).symm.trans (hg i)
  obtain ⟨h1, h2⟩ := rep_uniq hD hα e
  rw [h2, h1]

end GlobalTheory.HeckeFamilyMatrices.HkC

namespace GlobalTheory.HeckeFamilyMatrices.HkC

theorem hk_cocycle_coboundary_conj : ∀ (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (ι : Type) [Fintype ι]
    (α : Matrix (Fin 2) (Fin 2) ℤ) (δ : ι → Matrix (Fin 2) (Fin 2) ℤ), 0 < α.det → IsDCReps Γ α δ →
    (∀ z ∈ Z1 Γ w, hk Γ w δ z ∈ Z1 Γ w) ∧ (∀ z ∈ B1 Γ w, hk Γ w δ z ∈ B1 Γ w) ∧
      ∀ z, cj (hk Γ w δ z) = hk Γ w δ (cj z) := by
  intro Γ w ι _ α δ hpos hD
  have hα : α.det ≠ 0 := hpos.ne'
  refine ⟨?_, ?_, ?_⟩
  · rintro z ⟨hz1, hz2⟩
    refine ⟨fun γ => ?_, fun γ γ' => ?_⟩
    · obtain ⟨π, g, hg⟩ := rep_exists hD hα γ
      rw [hk_apply w hD hα z γ π g hg]
      exact Submodule.sum_mem _ fun i _ => mem_degLT_iff.2 (natDegree_slP_le _ _ _)
    · obtain ⟨π1, g1, hg1⟩ := rep_exists hD hα γ
      obtain ⟨π2, g2, hg2⟩ := rep_exists hD hα γ'
      have hg : ∀ i, δ i * mat ↑(γ * γ') = mat ↑(g1 i * g2 (π1 i)) * δ ((π1.trans π2) i) := by
        intro i
        rw [matm, matm, ← mul_assoc, hg1, mul_assoc, hg2, ← mul_assoc]
        rfl
      rw [hk_apply w hD hα z _ _ _ hg, hk_apply w hD hα z γ π1 g1 hg1, hk_apply w hD hα z γ' π2 g2 hg2,
        map_sum]
      simp only [hz2, map_add, Finset.sum_add_distrib, Equiv.trans_apply]
      have hs := Equiv.sum_comp π1 (fun j => slP w (δ (π2 j)) (z (g2 j)))
      rw [hs, add_left_inj]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [polySlash_comp _ _ _ _ (mem_degLT_iff.1 (hz1 _)), polySlash_comp _ _ _ _ (mem_degLT_iff.1 (hz1 _)),
        ← hg2 (π1 i)]
  · rintro z ⟨⟨p, hp⟩, rfl⟩
    have hp' : p.natDegree ≤ w := mem_degLT_iff.1 hp
    refine ⟨⟨∑ i, slP w (δ i) p, Submodule.sum_mem _ fun i _ => mem_degLT_iff.2 (natDegree_slP_le _ _ _)⟩, ?_⟩
    funext γ
    obtain ⟨π, g, hg⟩ := rep_exists hD hα γ
    rw [hk_apply w hD hα _ γ π g hg]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.id_apply, map_sub, Finset.sum_sub_distrib, map_sum]
    have hs := Equiv.sum_comp π (fun j => slP w (δ j) p)
    rw [hs, sub_left_inj]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [polySlash_comp _ _ _ _ hp', polySlash_comp _ _ _ _ hp', hg]
  · intro z
    funext γ
    simp only [cj, hk, LinearMap.pi_apply]
    split_ifs with h
    · simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, Polynomial.map_sum, polySlash_map]
      rfl
    · simp

end GlobalTheory.HeckeFamilyMatrices.HkC
