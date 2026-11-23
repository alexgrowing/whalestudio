import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudADef
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudIso
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsTwoWeightIff
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CcDualWtAnti
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Tensor
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

section Gen

variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

private theorem rowAct_mul_lemma_0 {k n : ℕ} (g h : Matrix (Fin k) (Fin k) K) (F : MvPolynomial (Fin k × Fin n) K) :
    rowAct K g (rowAct K h F) = rowAct K (h * g) F := by
  have e : (rowAct K (n := n) g).comp (rowAct K (n := n) h) = rowAct K (n := n) (h * g) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, rowAct, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => ?_))
    ring
  exact AlgHom.congr_fun e F

private theorem mem_nablaLTw_lemma (m : ℕ) (lam : Fin (m + 1) → ℤ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hg : IsUnit g.det) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :
    F ∈ nablaLTw O K m lam g ↔ g.det ^ (lam (Fin.last m)) • rowAct K g F ∈ intO O (m + 1) (nuOf lam) := by
  have hd : g.det ≠ 0 := hg.ne_zero
  constructor
  · intro hF
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hF
    have hy' : rowAct K g y ∈ intO O (m + 1) (nuOf lam) := hy
    show g.det ^ (lam (Fin.last m)) • rowAct K g (g.det ^ (-lam (Fin.last m)) • y) ∈ intO O (m + 1) (nuOf lam)
    rw [map_smul, smul_smul, ← zpow_add₀ hd, add_neg_cancel, zpow_zero, one_smul]
    exact hy'
  · intro hF
    refine Submodule.mem_map.mpr ⟨g.det ^ (lam (Fin.last m)) • F, ?_, ?_⟩
    · show rowAct K g (g.det ^ (lam (Fin.last m)) • F) ∈ intO O (m + 1) (nuOf lam)
      rw [map_smul]
      exact hF
    · show g.det ^ (-lam (Fin.last m)) • (g.det ^ (lam (Fin.last m)) • F) = F
      rw [smul_smul, ← zpow_add₀ hd, neg_add_cancel, zpow_zero, one_smul]

private theorem colSpan_le_lemma_2 {k : ℕ} (g g' : Matrix (Fin k) (Fin k) K) (h : colSpan O g' ≤ colSpan O g) :
    ∃ A : Matrix (Fin k) (Fin k) O, g' = g * A.map (algebraMap O K) := by
  have hc : ∀ c : Fin k, ∃ a : Fin k → O, ∑ b, a b • (fun i => g i b) = fun i => g' i c := by
    intro c
    exact (Submodule.mem_span_range_iff_exists_fun O).mp (h (Submodule.subset_span ⟨c, rfl⟩))
  choose a ha using hc
  refine ⟨Matrix.of fun b c => a c b, ?_⟩
  ext i c
  rw [Matrix.mul_apply, ← congrFun (ha c) i, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp [Algebra.smul_def, mul_comm]

private theorem step_lemma_3 (hinj : Function.Injective (algebraMap O K)) (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) (hsp : colSpan O g = colSpan O g')
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
    (hF : g.det ^ (lam (Fin.last m)) • rowAct K g F ∈ intO O (m + 1) (nuOf lam)) :
    g'.det ^ (lam (Fin.last m)) • rowAct K g' F ∈ intO O (m + 1) (nuOf lam) := by
  obtain ⟨A, hA⟩ := colSpan_le_lemma_2 (O := O) g g' (le_of_eq hsp.symm)
  obtain ⟨B, hB⟩ := colSpan_le_lemma_2 (O := O) g' g (le_of_eq hsp)
  have h1 : g * (A * B).map (algebraMap O K) = g * 1 := by
    rw [Matrix.map_mul, ← Matrix.mul_assoc, ← hA, ← hB, Matrix.mul_one]
  have h2 : (A * B).map (algebraMap O K) = 1 := by
    have h3 := congrArg (fun M => g⁻¹ * M) h1
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg, Matrix.one_mul] using h3
  have hAB : A * B = 1 := by
    ext i j
    apply hinj
    have h4 := congrFun (congrFun h2 i) j
    rw [Matrix.map_apply] at h4
    rw [h4, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hAB' : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hdet : IsUnit A.det := ⟨⟨A.det, B.det, hAB', by rw [mul_comm]; exact hAB'⟩, rfl⟩
  obtain ⟨u, hu⟩ := hdet
  obtain ⟨z, hz, hzF⟩ := Submodule.mem_map.mp hF
  subst hA
  rw [Matrix.det_mul, mul_zpow, ← rowAct_mul_lemma_0 (A.map (algebraMap O K)) g F, mul_comm (g.det ^ _),
    ← smul_smul, ← map_smul, ← hzF]
  have e1 : (A.map (algebraMap O K)).det = algebraMap O K A.det := by
    rw [RingHom.map_det]
    rfl
  have e2 : (algebraMap O K (u : O)) ^ (lam (Fin.last m)) = algebraMap O K ((u ^ (lam (Fin.last m)) : Oˣ) : O) := by
    have e3 : ((Units.map (algebraMap O K).toMonoidHom u : Kˣ) : K) = algebraMap O K (u : O) := rfl
    rw [← e3, ← Units.val_zpow_eq_zpow_val, ← map_zpow]
    rfl
  rw [e1, ← hu, e2, algebraMap_smul K]
  apply Submodule.smul_mem
  refine Submodule.mem_map.mpr ⟨rowAct O A z, dualWeylRowStable O (m + 1) (m + 1) (nuOf lam) A z hz, ?_⟩
  show map (algebraMap O K) (rowAct O A z) = rowAct K (A.map (algebraMap O K)) (map (algebraMap O K) z)
  rw [la_rowAct_map]

theorem mem_invariant_sections_iff_integral (hinj : Function.Injective (algebraMap O K)) (m : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :
    F ∈ H0 O m lam (colSpan O g) ↔ g.det ^ (lam (Fin.last m)) • rowAct K g F ∈ intO O (m + 1) (nuOf lam) := by
  simp only [H0, if_pos hlam, Submodule.mem_iInf]
  constructor
  · intro h
    exact (mem_nablaLTw_lemma (O := O) m lam g hg F).mp (h g ⟨hg, rfl⟩)
  · intro h g' hg'
    exact (mem_nablaLTw_lemma (O := O) m lam g' hg'.1 F).mpr (step_lemma_3 hinj m lam g g' hg hg'.2 F h)

theorem intO_le (k : ℕ) (ν : Fin k → ℕ) (x : MvPolynomial (Fin k × Fin k) K) (hx : x ∈ intO O k ν) :
    x ∈ dualWeyl K k k ν := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  exact dualWeylMap O K (algebraMap O K) k k ν y hy

theorem rowAct_rowAct {k n : ℕ} (g h : Matrix (Fin k) (Fin k) K) (F : MvPolynomial (Fin k × Fin n) K) :
    rowAct K g (rowAct K h F) = rowAct K (h * g) F := rowAct_mul_lemma_0 g h F

theorem rowAct_inv_cancel {k n : ℕ} (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin k × Fin n) K) : rowAct K g (rowAct K g⁻¹ F) = F := by
  rw [rowAct_rowAct, Matrix.nonsing_inv_mul g hg, tn_rowAct_one]

theorem rowAct_cancel_inv {k n : ℕ} (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin k × Fin n) K) : rowAct K g⁻¹ (rowAct K g F) = F := by
  rw [rowAct_rowAct, Matrix.mul_nonsing_inv g hg, tn_rowAct_one]

theorem rowAct_D {k : ℕ} (c : K) (f : MvPolynomial (Fin (k + 1) × Fin (k + 1)) K) (d : ℕ) (h : Row0 f d) :
    rowAct K (lb_D (k + 1) 1 c) f = (c⁻¹) ^ d • f := by
  have hX : ∀ v : Fin (k + 1) × Fin (k + 1),
      (∑ b : Fin (k + 1), C (lb_D (k + 1) 1 c v.1 b) * X (b, v.2) : MvPolynomial (Fin (k + 1) × Fin (k + 1)) K)
        = C (if v.1 = 0 then c⁻¹ else 1) * X v := by
    intro v
    rw [Finset.sum_eq_single v.1]
    · simp [lb_D, Fin.val_eq_zero_iff]
    · intro b _ hb
      simp [lb_D, Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  have hP : ∀ u : Fin (k + 1) × Fin (k + 1) →₀ ℕ,
      (∏ v : Fin (k + 1) × Fin (k + 1), (if v.1 = 0 then c⁻¹ else 1) ^ (u v)) = (c⁻¹) ^ rowDeg u 0 := by
    intro u
    rw [Fintype.prod_prod_type, Finset.prod_eq_single (0 : Fin (k + 1))]
    · simp [rowDeg, Finset.prod_pow_eq_pow_sum]
    · intro a _ ha
      simp [ha]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  have hmono : ∀ (u : Fin (k + 1) × Fin (k + 1) →₀ ℕ) (a : K),
      rowAct K (lb_D (k + 1) 1 c) (monomial u a) = (c⁻¹) ^ rowDeg u 0 • monomial u a := by
    intro u a
    simp only [rowAct, aeval_monomial, hX, algebraMap_eq]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [mul_pow, Finset.prod_mul_distrib]
    rw [show (∏ v : Fin (k + 1) × Fin (k + 1), (C (if v.1 = 0 then c⁻¹ else 1) : MvPolynomial (Fin (k + 1) × Fin (k + 1)) K) ^ (u v))
        = C (∏ v : Fin (k + 1) × Fin (k + 1), (if v.1 = 0 then c⁻¹ else 1) ^ (u v)) by
      rw [map_prod]
      exact Finset.prod_congr rfl (fun v _ => (map_pow C _ _).symm)]
    rw [hP, show (∏ v : Fin (k + 1) × Fin (k + 1), (X v : MvPolynomial (Fin (k + 1) × Fin (k + 1)) K) ^ (u v)) = monomial u 1 by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]]
    rw [smul_monomial, C_mul_monomial, C_mul_monomial, smul_eq_mul]
    congr 1
    ring
  rw [f.as_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  rw [hmono, h u (mem_support_iff.mp hu)]

theorem det_lb_D (k : ℕ) (c : K) : (lb_D (k + 1) 1 c).det = c⁻¹ := by
  simp [lb_D, Matrix.det_diagonal, Fin.prod_univ_succ]

theorem scal_id (D c : K) (hD : D ≠ 0) (hc : c ≠ 0) (r n : ℕ) :
    (D * c⁻¹) ^ (-(r : ℤ)) * c ^ n * D ^ r * (c⁻¹) ^ (n + r) = 1 := by
  rw [zpow_neg, zpow_natCast, mul_pow, inv_pow, pow_add]
  field_simp
  simp only [one_div, inv_pow]
  field_simp

theorem core_id {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (hg : IsUnit g.det) (c : K) (hc : c ≠ 0) (r n : ℕ)
    (x0 : MvPolynomial (Fin (k + 1) × Fin (k + 1)) K) (hR : Row0 x0 (n + r)) :
    (g * lb_D (k + 1) 1 c).det ^ (-(r : ℤ)) •
      rowAct K (g * lb_D (k + 1) 1 c) (c ^ n • (g.det ^ r • rowAct K g⁻¹ x0)) = x0 := by
  have hd : g.det ≠ 0 := hg.ne_zero
  rw [map_smul, map_smul, ← rowAct_rowAct (lb_D (k + 1) 1 c) g, rowAct_inv_cancel g hg, rowAct_D c x0 (n + r) hR,
    smul_smul, smul_smul, smul_smul]
  convert one_smul K x0 using 2
  rw [Matrix.det_mul, det_lb_D, ← scal_id g.det c hd hc r n]

theorem nuOf_anti {m : ℕ} (mu : Fin (m + 1) → ℤ) (h : Antitone mu) : Antitone (nuOf mu) := by
  intro a b hab
  show (mu b - mu (Fin.last m)).toNat ≤ (mu a - mu (Fin.last m)).toNat
  apply Int.toNat_le_toNat
  have := h hab
  linarith

theorem highest_weight_first_entry (k : ℕ) (ν : Fin (k + 1) → ℕ) (hν : Antitone ν) : Row0 (hw K (le_refl (k + 1)) ν) (ν 0) := by
  intro u hu
  have h := hwRowWeight K (k + 1) (k + 1) (le_refl _) ν hν hu
  have key : (Finsupp.weight (rowW (k + 1) (k + 1)) u) 0 = rowDeg u 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rowDeg]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (0 : Fin (k + 1))]
    · simp [rowW]
    · intro a _ ha
      simp [rowW, Pi.single_apply, Ne.symm ha]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  rw [← key, h]
  simp [rowNu]

private theorem map_hw_lemma_4 {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ} (hn : n ≤ r)
    (ν : Fin n → ℕ) : map φ (hw R hn ν) = hw S hn ν := by
  unfold hw lpMinor
  rw [map_prod]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [map_pow, RingHom.map_det]
  congr 2
  ext p q
  simp [RingHom.mapMatrix_apply]

theorem hw_int (k : ℕ) (ν : Fin k → ℕ) (hν : Antitone ν) : hw K (le_refl k) ν ∈ intO O k ν := by
  refine Submodule.mem_map.mpr ⟨hw O (le_refl k) ν, hwMem O k k (le_refl k) ν hν, ?_⟩
  show map (algebraMap O K) (hw O (le_refl k) ν) = hw K (le_refl k) ν
  exact map_hw_lemma_4 (algebraMap O K) (le_refl k) ν

private theorem eval_hw_lemma_5 {R : Type} [CommRing R] (k : ℕ) (ν : Fin k → ℕ) :
    eval (fun v : Fin k × Fin k => if v.1 = v.2 then (1 : R) else 0) (hw R (le_refl k) ν) = 1 := by
  unfold hw lpMinor
  rw [map_prod]
  refine Finset.prod_eq_one (fun s _ => ?_)
  rw [map_pow, RingHom.map_det]
  convert one_pow (M := R) _
  convert Matrix.det_one
  all_goals try infer_instance
  ext p q
  simp [RingHom.mapMatrix_apply, Matrix.one_apply]

theorem hw_prim [IsLocalRing O] (hinj : Function.Injective (algebraMap O K)) (w : O)
    (hw' : w ∈ IsLocalRing.maximalIdeal O) (k : ℕ) (ν : Fin k → ℕ) :
    ¬ ∃ y ∈ intO O k ν, hw K (le_refl k) ν = w • y := by
  rintro ⟨y, hy, hxy⟩
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  have h1 := congrArg (eval (fun v : Fin k × Fin k => if v.1 = v.2 then (1 : K) else 0)) hxy
  rw [eval_hw_lemma_5, ← algebraMap_smul K w, smul_eval] at h1
  have h2 : eval (fun v : Fin k × Fin k => if v.1 = v.2 then (1 : K) else 0)
      ((mapAlgHom (Algebra.ofId O K)).toLinearMap z)
      = algebraMap O K (eval (fun v : Fin k × Fin k => if v.1 = v.2 then (1 : O) else 0) z) := by
    show eval _ (map (algebraMap O K) z) = _
    rw [eval_map, show eval (fun v : Fin k × Fin k => if v.1 = v.2 then (1 : O) else 0) z
      = eval₂ (RingHom.id O) (fun v : Fin k × Fin k => if v.1 = v.2 then (1 : O) else 0) z from rfl,
      eval₂_comp_left, RingHom.comp_id]
    congr 1
    funext v
    simp only [Function.comp_apply]
    split_ifs <;> simp
  rw [h2, ← map_mul] at h1
  have h3 : (1 : O) = w * eval (fun v : Fin k × Fin k => if v.1 = v.2 then (1 : O) else 0) z :=
    hinj (by rw [map_one]; exact h1)
  have hu : IsUnit w := ⟨⟨w, _, h3.symm, by rw [mul_comm]; exact h3.symm⟩, rfl⟩
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal w).mp hw')) hu

end Gen

theorem caLast_ne_zero (m : ℕ) : Fin.last (m + 1) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp at this

theorem wtPQ_zero (m a b : ℕ) : wtPQ m a b 0 = a := by simp [wtPQ]

theorem wtPQ_last (m a b : ℕ) : wtPQ (m + 1) a b (Fin.last (m + 1)) = -(b : ℤ) := by
  simp [wtPQ]

theorem lo_val (mm ccl P Q : ℕ) (lam : Fin (mm + 1 + 1) → ℤ) (h0 : lam 0 = (P : ℤ) + ccl)
    (hl : lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl)) (i : Fin (mm + 1 + 1)) :
    (lam - wtPQ (mm + 1) P Q) i = if i = 0 then (ccl : ℤ) else if i = Fin.last (mm + 1) then -(ccl : ℤ) else lam i := by
  rw [Pi.sub_apply]
  unfold wtPQ
  split_ifs with h1 h2
  · rw [h1, h0]; ring
  · rw [h2, hl]; ring
  · ring

theorem caLo_anti (mm ccl P Q : ℕ) (lam : Fin (mm + 1 + 1) → ℤ) (hlam : Antitone lam) (h0 : lam 0 = (P : ℤ) + ccl)
    (hl : lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl))
    (hmid : ∀ i : Fin (mm + 1 + 1), 0 < i.val → i.val < mm + 1 → |lam i| ≤ ccl) :
    Antitone (lam - wtPQ (mm + 1) P Q) := by
  intro a b hab
  rw [lo_val mm ccl P Q lam h0 hl a, lo_val mm ccl P Q lam h0 hl b]
  have hlv : (Fin.last (mm + 1)).val = mm + 1 := Fin.val_last _
  have hab' : a.val ≤ b.val := hab
  have hc : (0 : ℤ) ≤ (ccl : ℤ) := Int.natCast_nonneg _
  have hbl' := b.isLt
  have hal' := a.isLt
  by_cases ha0 : a = 0
  · subst ha0
    rw [if_pos rfl]
    split_ifs with hb0 hbl
    · exact le_refl _
    · linarith
    · have hb1 : 0 < b.val := Nat.pos_of_ne_zero (fun h => hb0 (Fin.ext h))
      have hb2 : b.val < mm + 1 := by
        have : b.val ≠ mm + 1 := fun h => hbl (Fin.ext (h.trans hlv.symm))
        omega
      exact le_trans (le_abs_self _) (hmid b hb1 hb2)
  · by_cases hal : a = Fin.last (mm + 1)
    · have hb : b = Fin.last (mm + 1) := by
        apply Fin.ext
        rw [hal] at hab'
        omega
      subst hal
      subst hb
      exact le_refl _
    · have ha1 : 0 < a.val := Nat.pos_of_ne_zero (fun h => ha0 (Fin.ext h))
      have ha2 : a.val < mm + 1 := by
        have : a.val ≠ mm + 1 := fun h => hal (Fin.ext (h.trans hlv.symm))
        omega
      rw [if_neg ha0, if_neg hal]
      split_ifs with hb0 hbl
      · exfalso
        have : b.val = 0 := by rw [hb0]; rfl
        omega
      · linarith [neg_abs_le (lam a), hmid a ha1 ha2]
      · exact hlam hab

end Formalism.MainNotions.flipOneThree.Pf

end
