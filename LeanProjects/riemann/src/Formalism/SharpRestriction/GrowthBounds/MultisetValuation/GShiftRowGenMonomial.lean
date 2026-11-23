import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
import Formalism.SharpRestriction.GrowthBounds.DataG

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

section Grade

variable {r : ℕ} (ht : Fin r → ℤ)

def htW (n : ℕ) : Fin r × Fin n → ℤ := fun v => ht v.1

def GShift {R : Type*} [CommRing R] {n : ℕ} (P : Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ δ : ℤ) : Prop :=
  ∀ k : ℕ, IsWeightedHomogeneous (htW ht n) (P.coeff k) (μ + k * δ)

variable {ht}

theorem gShift_mul {R : Type*} [CommRing R] {n : ℕ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' δ : ℤ}
    (hP : GShift ht P μ δ) (hQ : GShift ht Q μ' δ) : GShift ht (P * Q) (μ + μ') δ := by
  intro k
  rw [Polynomial.coeff_mul]
  apply IsWeightedHomogeneous.sum
  intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h := (hP x.1).mul (hQ x.2)
  convert h using 1
  rw [← hx]
  push_cast
  ring

theorem gShift_one {R : Type*} [CommRing R] {n : ℕ} (δ : ℤ) :
    GShift ht (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 δ := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs with h
  · have hk : k = 0 := by omega
    subst hk
    intro d hd
    rw [MvPolynomial.coeff_one] at hd
    split_ifs at hd with h0
    · subst h0
      simp
    · exact absurd rfl hd
  · intro d hd
    exact absurd (MvPolynomial.coeff_zero d) hd

theorem gShift_pow {R : Type*} [CommRing R] {n : ℕ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ δ : ℤ}
    (hP : GShift ht P μ δ) (e : ℕ) : GShift ht (P ^ e) (e • μ) δ := by
  induction e with
  | zero =>
    rw [pow_zero, zero_smul]
    exact gShift_one δ
  | succ e ih =>
    rw [pow_succ, succ_nsmul]
    exact gShift_mul ih hP

theorem gShift_prod {R : Type*} [CommRing R] {n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → ℤ) (δ : ℤ)
    (h : ∀ i ∈ s, GShift ht (P i) (μ i) δ) : GShift ht (∏ i ∈ s, P i) (∑ i ∈ s, μ i) δ := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty, Finset.sum_empty]
    exact gShift_one δ
  · intro i s hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact gShift_mul (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem gShift_algebraMap {R : Type*} [CommRing R] {n : ℕ} (c : R) (δ : ℤ) :
    GShift ht (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 δ := by
  intro k
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs with h
  · subst h
    intro d hd
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C] at hd
    split_ifs at hd with h0
    · subst h0
      simp
    · exact absurd rfl hd
  · intro d hd
    exact absurd (MvPolynomial.coeff_zero d) hd

theorem gShift_gen {R : Type*} [CommRing R] {n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    GShift ht (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (htW ht n v) (ht a - ht b) := by
  intro k
  have hX : ∀ u : Fin r × Fin n, IsWeightedHomogeneous (htW ht n) (X u : MvPolynomial (Fin r × Fin n) R) (ht u.1) :=
    fun u => isWeightedHomogeneous_X R (htW ht n) u
  have h0 : ∀ m : ℤ, IsWeightedHomogeneous (htW ht n) (0 : MvPolynomial (Fin r × Fin n) R) m :=
    fun m d hd => absurd (MvPolynomial.coeff_zero d) hd
  split_ifs with hb
  · rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.X_mul_C, Polynomial.coeff_C_mul_X]
    by_cases hk0 : k = 0
    · subst hk0
      simp only [↓reduceIte, zero_ne_one, add_zero, Nat.cast_zero, zero_mul]
      exact hX v
    · by_cases hk1 : k = 1
      · subst hk1
        simp only [one_ne_zero, ↓reduceIte, zero_add, Nat.cast_one, one_mul]
        convert hX (a, v.2) using 1
        simp only [htW]
        rw [hb]
        ring
      · rw [if_neg hk0, if_neg hk1, add_zero]
        exact h0 _
  · rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_zero, add_zero]
    split_ifs with hk0
    · subst hk0
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact hX v
    · exact h0 _

theorem gShift_rowGen_monomial (R : Type*) [CommRing R] {n : ℕ} (a b : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    GShift ht (rowGen R a b (monomial d c)) (Finsupp.weight (htW ht n) d) (ht a - ht b) := by
  unfold rowGen
  rw [aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]
  refine gShift_mul (gShift_algebraMap c _) ?_
  unfold Finsupp.prod Finsupp.sum
  exact gShift_prod _ _ _ _ fun v _ => gShift_pow (gShift_gen a b v) _

theorem g_rowDiv_shift (R : Type*) [CommRing R] {n : ℕ} (H : ℤ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (htW ht n) f H) :
    IsWeightedHomogeneous (htW ht n) (rowDiv R a b k f) (H + k * (ht a - ht b)) := by
  unfold rowDiv
  conv => enter [2, 1, 2]; rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have := gShift_rowGen_monomial (ht := ht) R a b d (coeff d f) k
  rwa [hf (mem_support_iff.mp hd)] at this

theorem g_weight {n : ℕ} (d : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (htW ht n) d = ∑ a : Fin r, ht a * ((Finsupp.weight (rowW r n) d a : ℕ) : ℤ) := by
  refine Finsupp.induction_linear d ?_ ?_ ?_
  · simp
  · intro f g hf hg
    rw [map_add, hf, hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_add, Pi.add_apply, Nat.cast_add, mul_add]
  · intro v k
    simp only [Finsupp.weight_apply, Finsupp.sum_single_index, zero_smul, implies_true]
    rw [Finset.sum_eq_single v.1]
    · simp [htW, rowW]
      try ring
    · intro b _ hb
      simp [rowW, Pi.single_apply, hb]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem g_of_rowW {R : Type*} [CommRing R] {n : ℕ} {f : MvPolynomial (Fin r × Fin n) R} {μ : Fin r → ℕ}
    (hf : IsWeightedHomogeneous (rowW r n) f μ) :
    IsWeightedHomogeneous (htW ht n) f (∑ a : Fin r, ht a * (μ a : ℤ)) := by
  intro d hd
  rw [g_weight, hf hd]

theorem g_applyWord (R : Type) [CommRing R] {n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (w : List (Fin r × Fin r × ℕ)) :
    ∃ z : ℤ, IsWeightedHomogeneous (htW ht n) (applyWord R w (hw R hn ν)) z := by
  induction w with
  | nil => exact ⟨_, g_of_rowW (hwRowWeight R r n hn ν hν)⟩
  | cons x w ih =>
    obtain ⟨z, hz⟩ := ih
    exact ⟨_, g_rowDiv_shift R z x.1 x.2.1 x.2.2 _ hz⟩

end Grade

theorem dom_dualWeyl (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) (k : ℕ) :
    ∀ d ∈ f.support, (∑ a : Fin r with a.val < k, rowDeg d a) ≤ ∑ t : Fin n with t.val < k, ν t := by
  classical
  rw [standardMonomialSpanDomain R r n ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hx
    intro d hd
    have := (bidetDominance R r n K sz hsz I d hd).1 k
    rwa [hsh] at this
  | zero => intro d hd; simp at hd
  | add x y _ _ hx hy =>
    intro d hd
    rcases Finset.mem_union.1 (support_add hd) with h | h
    · exact hx d h
    · exact hy d h
  | smul a x _ hx =>
    intro d hd
    exact hx d (support_smul hd)

section Diag

def piR {k n : ℕ} (r : ℕ) (d : Fin k × Fin n →₀ ℕ) : ℕ := ∑ a : Fin k with a.val < r, rowDeg d a

private theorem finsupp_weight_rowW_eq_rowDeg {k n : ℕ} (d : Fin k × Fin n →₀ ℕ) (a : Fin k) :
    Finsupp.weight (rowW k n) d a = rowDeg d a := by
  refine Finsupp.induction_linear d ?_ ?_ ?_
  · simp [rowDeg]
  · intro f g hf hg
    rw [map_add, Pi.add_apply, hf, hg]
    simp only [rowDeg, Finsupp.add_apply, Finset.sum_add_distrib]
  · intro v c
    simp only [Finsupp.weight_apply, Finsupp.sum_single_index, zero_smul, implies_true]
    simp only [rowDeg, rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Finsupp.single_apply]
    by_cases h : a = v.1
    · subst h
      rw [Finset.sum_eq_single v.2]
      · simp
      · intro s _ hs
        rw [if_neg]
        intro hv
        exact hs (congrArg Prod.snd hv).symm
      · intro hs
        exact absurd (Finset.mem_univ _) hs
    · rw [if_neg h, mul_zero]
      refine (Finset.sum_eq_zero fun s _ => ?_).symm
      rw [if_neg]
      intro hv
      exact h (congrArg Prod.fst hv).symm

theorem weight_ind {k n : ℕ} (r : ℕ) (d : Fin k × Fin n →₀ ℕ) :
    Finsupp.weight (htW (fun a : Fin k => if a.val < r then (1 : ℤ) else 0) n) d = (piR r d : ℤ) := by
  rw [g_weight]
  unfold piR
  push_cast
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [finsupp_weight_rowW_eq_rowDeg]
  split_ifs <;> simp

theorem diag_monomial {K : Type} [Field K] {k n : ℕ} (r : ℕ) (c : K) (d : Fin k × Fin n →₀ ℕ) (x : K) :
    rowAct K (lb_D k r c) (monomial d x) = (c⁻¹) ^ (piR r d) • monomial d x := by
  have hD : RowActDiagWeight := by
    first
    | exact rowActDiagWeight
    | exact row_action_diagonal_weight
    | exact Formalism.GradedWeylDivisibility.rowActDiagWeight
  have hH : IsWeightedHomogeneous (rowW k n) (monomial d x) (Finsupp.weight (rowW k n) d) :=
    isWeightedHomogeneous_monomial _ _ _ rfl
  unfold lb_D
  rw [hD K k n _ _ _ hH]
  congr 1
  unfold piR
  rw [← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [finsupp_weight_rowW_eq_rowDeg]
  split_ifs <;> simp

theorem diag_const {K : Type} [Field K] {k n : ℕ} (r : ℕ) (c : K) (G : MvPolynomial (Fin k × Fin n) K) (π0 : ℕ)
    (h : ∀ d ∈ G.support, piR r d = π0) : rowAct K (lb_D k r c) G = (c⁻¹) ^ π0 • G := by
  conv_lhs => rw [G.as_sum]
  rw [map_sum]
  conv_rhs => rw [G.as_sum]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [diag_monomial, h d hd]

theorem weyl_diag (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] (k r : ℕ) (ν : Fin k → ℕ)
    (hν : Antitone ν) (w : O) (hw : algebraMap O Kf w ≠ 0) (f : MvPolynomial (Fin k × Fin k) O)
    (hf : f ∈ weyl O k k le_rfl ν) :
    (algebraMap O Kf w) ^ (∑ t : Fin k with t.val < r, ν t) •
        rowAct Kf (lb_D k r (algebraMap O Kf w)) (map (algebraMap O Kf) f) ∈
      Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap (weyl O k k le_rfl ν) := by
  classical
  set c : Kf := algebraMap O Kf w with hc
  set N : ℕ := ∑ t : Fin k with t.val < r, ν t with hN
  have hmap : ∀ f : MvPolynomial (Fin k × Fin k) O,
      (mapAlgHom (Algebra.ofId O Kf)).toLinearMap f = map (algebraMap O Kf) f := fun f => rfl
  let T : MvPolynomial (Fin k × Fin k) O →ₗ[O] MvPolynomial (Fin k × Fin k) Kf :=
    ((LinearMap.lsmul Kf _ (c ^ N)).restrictScalars O) ∘ₗ
      ((rowAct Kf (n := k) (lb_D k r c)).toLinearMap.restrictScalars O) ∘ₗ
      (mapAlgHom (Algebra.ofId O Kf)).toLinearMap
  have key : weyl O k k le_rfl ν ≤
      (Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap (weyl O k k le_rfl ν)).comap T := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨wd, rfl⟩
    set Wd := applyWord O wd (Formalism.GradedWeylDivisibility.hw O (le_refl k) ν) with hWd
    have hWmem : Wd ∈ weyl O k k le_rfl ν := Submodule.subset_span ⟨wd, rfl⟩
    show c ^ N • rowAct Kf (lb_D k r c) (map (algebraMap O Kf) Wd) ∈
      Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap (weyl O k k le_rfl ν)
    by_cases h0 : Wd = 0
    · rw [h0, map_zero, map_zero, smul_zero]
      exact Submodule.zero_mem _
    · obtain ⟨d, hd⟩ := ne_zero_iff.mp h0
      obtain ⟨z, hz⟩ := g_applyWord (ht := fun a : Fin k => if a.val < r then (1 : ℤ) else 0) O (le_refl k) ν hν wd
      have hπ : ∀ d' ∈ (map (algebraMap O Kf) Wd).support, piR r d' = piR r d := by
        intro d' hd'
        have h1 : coeff d' Wd ≠ 0 := by
          intro h
          rw [mem_support_iff, coeff_map, h, map_zero] at hd'
          exact hd' rfl
        have e1 := hz h1
        have e2 := hz hd
        rw [weight_ind] at e1 e2
        exact_mod_cast e1.trans e2.symm
      have hle : piR r d ≤ N :=
        dom_dualWeyl O k k ν Wd (weylLeDual O k k le_rfl ν hν hWmem) r d (mem_support_iff.2 hd)
      rw [diag_const r c _ _ hπ, smul_smul]
      refine ⟨w ^ (N - piR r d) • Wd, Submodule.smul_mem _ _ hWmem, ?_⟩
      rw [map_smul, hmap, ← algebraMap_smul Kf (w ^ (N - piR r d)), map_pow, ← hc]
      congr 1
      have h4 : c ^ N = c ^ (N - piR r d) * c ^ (piR r d) := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      rw [h4, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hw), mul_one]
  exact key hf

end Diag

section Pos

theorem mem_deltaL {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {k : ℕ} {ν : Fin k → ℕ}
    {g : Matrix (Fin k) (Fin k) Kf} {F : MvPolynomial (Fin k × Fin k) Kf} :
    F ∈ deltaL O Kf k ν g ↔ ∃ f ∈ weyl O k k le_rfl ν, map (algebraMap O Kf) f = rowAct Kf g F := by
  unfold deltaL
  rw [Submodule.mem_comap, Submodule.mem_map]
  first
  | rfl
  | simp [MvPolynomial.mapAlgHom_apply]

theorem dl_P (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] (m r : ℕ)
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (w : O) (hw : algebraMap O Kf w ≠ 0) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (hF : F ∈ deltaLTw O Kf m lam g) :
    (algebraMap O Kf w ^ (∑ i : Fin (m + 1) with i.val < r, lam i)) • F ∈
      deltaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w)) := by
  classical
  set c : Kf := algebraMap O Kf w with hc
  set ν : Fin (m + 1) → ℕ := nuOf lam with hν
  set e : ℤ := lam (Fin.last m) with he
  have hνa : Antitone ν := by
    intro x y hxy
    simp only [hν, nuOf]
    exact Int.toNat_le_toNat (sub_le_sub_right (hlam hxy) _)
  obtain ⟨F0, hF0, rfl⟩ := hF
  obtain ⟨f, hf, hfe⟩ := mem_deltaL.1 hF0
  set Nν : ℕ := ∑ t : Fin (m + 1) with t.val < r, ν t with hNν
  set A : ℤ := ∑ i : Fin (m + 1) with i.val < r, lam i with hA
  obtain ⟨f1, hf1, hf1e⟩ := weyl_diag O Kf (m + 1) r ν hνa w hw f hf
  refine ⟨c ^ Nν • F0, mem_deltaL.2 ⟨f1, hf1, ?_⟩, ?_⟩
  · have h5 := rowActMul Kf (m + 1) (m + 1) (lb_D (m + 1) r c) g
    have h6 : rowAct Kf (g * lb_D (m + 1) r c) F0 = rowAct Kf (lb_D (m + 1) r c) (rowAct Kf g F0) := by
      rw [← h5]
      rfl
    rw [map_smul, h6, ← hfe]
    exact hf1e
  · show (g * lb_D (m + 1) r c).det ^ (-e) • (c ^ Nν • F0) = c ^ A • (g.det ^ (-e) • F0)
    rw [smul_smul, smul_smul]
    congr 1
    set ρ : ℕ := (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card with hρ
    have h1 : (g * lb_D (m + 1) r c).det = g.det * (c⁻¹) ^ ρ := by
      rw [Matrix.det_mul, lb_D, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const,
        Finset.prod_const_one, mul_one]
    have h3 : A = (Nν : ℤ) + ρ * e := by
      rw [hA, hNν, hρ]
      push_cast
      rw [Finset.card_eq_sum_ones]
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      have : 0 ≤ lam a - lam (Fin.last m) := sub_nonneg.2 (hlam (Fin.le_last a))
      simp only [hν, nuOf, Int.toNat_of_nonneg this, he]
      ring
    have h5 : ((c⁻¹) ^ ρ) ^ (-e) = c ^ ((ρ : ℤ) * e) := by
      rw [inv_pow, inv_zpow, zpow_neg, inv_inv, ← zpow_natCast c ρ, ← zpow_mul]
    rw [h1, h3, mul_zpow, h5, zpow_add₀ hw, zpow_natCast]
    ring

theorem dl_indep (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g h : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (hs : colSpan O g = colSpan O h) : deltaLTw O Kf m lam g ≤ deltaLTw O Kf m lam h := by
  classical
  have hcol : ∀ (g h : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf), colSpan O g = colSpan O h →
      ∃ U : Matrix (Fin (m + 1)) (Fin (m + 1)) O, h = g * U.map (algebraMap O Kf) := by
    intro g h hs
    have h1 : ∀ j, ∃ c : Fin (m + 1) → O, ∑ i, c i • (fun a => g a i) = fun a => h a j := by
      intro j
      have hm : (fun a => h a j) ∈ colSpan O g := by
        rw [hs]; exact Submodule.subset_span ⟨j, rfl⟩
      exact (Submodule.mem_span_range_iff_exists_fun O).1 hm
    choose c hc using h1
    refine ⟨fun i j => c j i, ?_⟩
    ext a j
    have h2 := congrFun (hc j) a
    rw [Matrix.mul_apply, ← h2, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    show c j i • g a i = g a i * algebraMap O Kf (c j i)
    rw [Algebra.smul_def, mul_comm]
  obtain ⟨U, hU⟩ := hcol g h hs
  obtain ⟨U', hU'⟩ := hcol h g hs.symm
  have hdU : ∀ V : Matrix (Fin (m + 1)) (Fin (m + 1)) O,
      (V.map (algebraMap O Kf)).det = algebraMap O Kf V.det :=
    fun V => (RingHom.map_det (algebraMap O Kf) V).symm
  have hdet : U.det * U'.det = 1 := by
    apply hinj
    have h1 : g.det * (algebraMap O Kf U.det * algebraMap O Kf U'.det) = g.det * 1 := by
      conv_rhs => rw [mul_one, hU', hU, Matrix.det_mul, Matrix.det_mul, hdU, hdU]
      ring
    rw [map_mul, map_one]
    exact mul_left_cancel₀ hg.ne_zero h1
  let u : Oˣ := ⟨U.det, U'.det, hdet, by rw [mul_comm]; exact hdet⟩
  set e : ℤ := lam (Fin.last m) with he
  have hz : algebraMap O Kf ((u ^ e : Oˣ) : O) = (algebraMap O Kf U.det) ^ e := by
    calc algebraMap O Kf ((u ^ e : Oˣ) : O)
        = ((Units.map (algebraMap O Kf : O →* Kf) (u ^ e) : Kfˣ) : Kf) := rfl
      _ = (((Units.map (algebraMap O Kf : O →* Kf) u) ^ e : Kfˣ) : Kf) := by rw [map_zpow]
      _ = ((Units.map (algebraMap O Kf : O →* Kf) u : Kfˣ) : Kf) ^ e := Units.val_zpow_eq_zpow_val _ _
      _ = (algebraMap O Kf U.det) ^ e := rfl
  have hUne : algebraMap O Kf U.det ≠ 0 := by
    intro h0
    have := congrArg (algebraMap O Kf) hdet
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  let UU : GL (Fin (m + 1)) O := Matrix.nonsingInvUnit U u.isUnit
  intro F hF
  obtain ⟨F0, hF0, rfl⟩ := hF
  obtain ⟨f, hf, hfe⟩ := mem_deltaL.1 hF0
  have hst : rowAct O U f ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf lam) := by
    have := Formalism.UG.P.weyl_module_GL_stable O (m + 1) (m + 1) le_rfl (nuOf lam) UU⁻¹ f hf
    unfold Formalism.UG.dwAct at this
    rw [inv_inv] at this
    exact this
  refine ⟨(algebraMap O Kf U.det) ^ e • F0,
    mem_deltaL.2 ⟨((u ^ e : Oˣ) : O) • rowAct O U f, Submodule.smul_mem _ _ hst, ?_⟩, ?_⟩
  · have h4 : rowAct Kf (U.map (algebraMap O Kf)) (rowAct Kf g F0) = rowAct Kf h F0 := by
      have h5 := rowActMul Kf (m + 1) (m + 1) (U.map (algebraMap O Kf)) g
      rw [hU, ← h5]
      rfl
    rw [map_smul (rowAct Kf h), ← h4, ← hfe, ← ldtwist_map_rowAct, ← hz, algebraMap_smul]
    exact (map_smul (mapAlgHom (Algebra.ofId O Kf)).toLinearMap ((u ^ e : Oˣ) : O) (rowAct O U f))
  · show h.det ^ (-e) • ((algebraMap O Kf U.det) ^ e • F0) = g.det ^ (-e) • F0
    rw [smul_smul, hU, Matrix.det_mul, hdU, mul_zpow, mul_assoc, ← zpow_add₀ hUne, neg_add_cancel, zpow_zero, mul_one]

theorem dl_pos (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m r : ℕ) (lam : Fin (m + 1) → ℤ)
    (w : O) (hw : algebraMap O Kf w ≠ 0) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (hF : F ∈ Dl0 O m lam (colSpan O g)) :
    (algebraMap O Kf w ^ (∑ i : Fin (m + 1) with i.val < r, lam i)) • F ∈
      Dl0 O m lam (colSpan O (g * lb_D (m + 1) r (algebraMap O Kf w))) := by
  have hgD : IsUnit (g * lb_D (m + 1) r (algebraMap O Kf w)).det := by
    rw [Matrix.det_mul]; exact hg.mul (lb_D_det _ _ _ hw)
  unfold Dl0 at hF ⊢
  by_cases hlam : Antitone lam
  · rw [if_pos hlam] at hF ⊢
    have h1 : F ∈ deltaLTw O Kf m lam g := (iInf₂_le g ⟨hg, rfl⟩ : _ ≤ deltaLTw O Kf m lam g) hF
    have h2 := dl_P O Kf m r lam hlam w hw g F h1
    exact (le_iInf₂ fun h hh => dl_indep O Kf hinj m lam _ h hgD hh.2 :
      deltaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w)) ≤ _) h2
  · rw [if_neg hlam] at hF ⊢
    rw [Submodule.mem_bot] at hF ⊢
    rw [hF, smul_zero]

end Pos

end Formalism.MainNotions.FormalGroupSystem.Pf
