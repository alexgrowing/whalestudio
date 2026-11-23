import Development.EtaleCohomology.EtaleTrace.LCoverCut

noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.StepPf

lemma eval₂_mul_left {k R σ : Type} [CommSemiring k] [CommSemiring R] (f : k →+* R) (x : σ → R) (r : R)
    {m : ℕ} {F : MvPolynomial σ k} (hF : F.IsHomogeneous m) :
    eval₂ f (fun j => r * x j) F = r ^ m * eval₂ f x F := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = m := by
    have := hF (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

lemma jet_sub {k K : Type} [Field k] [Field K] [Algebra k K] (a b : K) (c : k) :
    ((a - algebraMap k K c * b), KaehlerDifferential.D k K (a - algebraMap k K c * b)) =
      (a, KaehlerDifferential.D k K a) - (algebraMap k K c) • (b, KaehlerDifferential.D k K b) := by
  ext
  · simp [Algebra.smul_def]
  · simp [Derivation.leibniz]

lemma exists_c {k K : Type} [Field k] [Infinite k] [Field K] [Algebra k K] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) k) (hF0 : F ≠ 0) (a : Fin (n + 1) → K) (j0 : Fin (n + 1)) (ha : a j0 ≠ 0) :
    ∃ c : Fin (n + 1) → k, eval c F ≠ 0 ∧ c (Fin.last n) ≠ 0 ∧ ∑ j, a j * algebraMap k K (c j) ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k K, φ (a j0) ≠ 0 := by
    by_contra h
    push Not at h
    exact ha ((Module.forall_dual_apply_eq_zero_iff k (a j0)).mp h)
  set G : MvPolynomial (Fin (n + 1)) k := ∑ j, C (φ (a j)) * X j with hGdef
  have hG : ∀ c, eval c G = φ (∑ j, a j * algebraMap k K (c j)) := by
    intro c
    simp only [hGdef, map_sum, map_mul, eval_C, eval_X]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (a j), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have hG0 : G ≠ 0 := by
    intro h
    have := hG (Pi.single j0 1)
    rw [h] at this
    simp [Pi.single_apply] at this
    exact hφ this.symm
  have hP : F * X (Fin.last n) * G ≠ 0 := mul_ne_zero (mul_ne_zero hF0 (X_ne_zero _)) hG0
  obtain ⟨c, hc⟩ : ∃ c, eval c (F * X (Fin.last n) * G) ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (MvPolynomial.funext fun x => by simpa using h x)
  simp only [map_mul, eval_X] at hc
  refine ⟨c, ?_, ?_, ?_⟩
  · exact left_ne_zero_of_mul (left_ne_zero_of_mul hc)
  · exact right_ne_zero_of_mul (left_ne_zero_of_mul hc)
  · intro h0
    apply right_ne_zero_of_mul hc
    rw [hG, h0, map_zero]

theorem Step_of : LateralTheory.EtaleTrace.Cov.Step := by
  intro k K _ _ _ _ n v m F hF0 hFh hFv hli
  obtain ⟨a, ha, j0, hj0⟩ := Fintype.not_linearIndependent_iff.mp hli
  obtain ⟨c, hcF, hcl, hcs⟩ := exists_c F hF0 a j0 hj0
  set e : k := (c (Fin.last n))⁻¹ with he
  set d : Fin (n + 1) → k := fun j => e * c j with hd
  have hdl : d (Fin.last n) = 1 := inv_mul_cancel₀ hcl
  have hdF : eval d F ≠ 0 := by
    have h := eval₂_mul_left (RingHom.id k) c e hFh
    change eval₂ (RingHom.id k) d F ≠ 0
    rw [show (fun j => e * c j) = d from rfl] at h
    rw [h]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hcl)) hcF
  set s : K := ∑ j, a j * algebraMap k K (d j) with hsdef
  have hs0 : s ≠ 0 := by
    have : s = algebraMap k K e * ∑ j, a j * algebraMap k K (c j) := by
      simp only [hsdef, hd, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    exact mul_ne_zero ((map_ne_zero _).mpr (inv_ne_zero hcl)) hcs
  set w : Fin n → K := fun j => v j.castSucc - algebraMap k K (d j.castSucc) * v (Fin.last n) with hw
  have hjw : ∀ j, LateralTheory.EtaleTrace.Cov.jet k w j =
      LateralTheory.EtaleTrace.Cov.jet k v j.castSucc - algebraMap k K (d j.castSucc) • LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n) := by
    intro j
    exact jet_sub _ _ _
  have h1 : ∀ j : Fin n, LateralTheory.EtaleTrace.Cov.jet k v j.castSucc =
      LateralTheory.EtaleTrace.Cov.jet k w j + algebraMap k K (d j.castSucc) • LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n) := by
    intro j; rw [hjw]; abel
  have hlast : s • LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n) = -(∑ j : Fin n, a j.castSucc • LateralTheory.EtaleTrace.Cov.jet k w j) := by
    have hs : s = ∑ j : Fin n, a j.castSucc * algebraMap k K (d j.castSucc) + a (Fin.last n) := by
      rw [hsdef, Fin.sum_univ_castSucc, hdl, map_one, mul_one]
    rw [Fin.sum_univ_castSucc] at ha
    simp_rw [h1, smul_add, Finset.sum_add_distrib, smul_smul] at ha
    rw [hs, add_smul, Finset.sum_smul, eq_neg_iff_add_eq_zero, ← ha]
    abel
  refine ⟨w, ?_, ?_, ?_⟩
  · intro j
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) ?_
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [hjw]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    · have hL : LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n) ∈ Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k w)) := by
        have : LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n) = s⁻¹ • (s • LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n)) := by
          rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
        rw [this, hlast]
        refine Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.sum_mem _ fun j _ => ?_))
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      induction j using Fin.lastCases with
      | last => exact hL
      | cast j =>
        rw [h1]
        exact Submodule.add_mem _ (Submodule.subset_span ⟨j, rfl⟩) (Submodule.smul_mem _ _ hL)
  · intro O hO hk ⟨i, hvi, hvO⟩
    let ι : k →+* O := (algebraMap k K).codRestrict O hk
    let U : Fin (n + 1) → O := fun j => ⟨v j / v i, hvO j⟩
    have hUF : eval₂ ι U F = 0 := by
      apply Subtype.val_injective
      have h := eval₂_comp_left O.subtype ι U F
      change O.subtype (eval₂ ι U F) = 0
      rw [h]
      have h2 : O.subtype.comp ι = algebraMap k K := by ext x; rfl
      have h3 : (O.subtype ∘ U) = fun j => (v i)⁻¹ * v j := by
        funext j; simp [U, div_eq_inv_mul]
      rw [h2, h3, eval₂_mul_left _ _ _ hFh, ← aeval_def, hFv, mul_zero]
    let W : Fin n → O := fun l => U l.castSucc - ι (d l.castSucc) * U (Fin.last n)
    have hWv : ∀ l, (W l : K) = w l / v i := by
      intro l
      simp only [W, U, ι, hw, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, RingHom.codRestrict_apply]
      ring
    by_contra hcon
    push Not at hcon
    have hWm : ∀ l, IsLocalRing.residue O (W l) = 0 := by
      intro l
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      have hval : w l / v i * (y : K) = 1 := by
        rw [← hWv]
        exact congrArg Subtype.val hy
      have hwl : w l ≠ 0 := by
        intro h0; rw [h0, zero_div, zero_mul] at hval; exact zero_ne_one hval
      obtain ⟨j, hj⟩ := hcon l hwl
      apply hj
      have : v j / w l = v j / v i * (y : K) := by
        rw [eq_comm, eq_div_iff hwl]
        calc v j / v i * (y : K) * w l = v j * (w l / v i * (y : K)) := by ring
          _ = v j := by rw [hval, mul_one]
      rw [this]
      exact O.mul_mem (hvO j) y.2
    set π := IsLocalRing.residue O
    set t := π (U (Fin.last n))
    have hπU : (fun j => π (U j)) = fun j => t * (π.comp ι) (d j) := by
      funext j
      induction j using Fin.lastCases with
      | last => rw [hdl, map_one, mul_one]
      | cast l =>
        have := hWm l
        simp only [W, map_sub, map_mul, sub_eq_zero] at this
        rw [this, RingHom.comp_apply, mul_comm]
    have hmain : t ^ m * (π.comp ι) (eval d F) = 0 := by
      have h := eval₂_comp_left π ι U F
      rw [hUF, map_zero] at h
      have h' : (π ∘ U) = fun j => t * (π.comp ι) (d j) := hπU
      rw [h', eval₂_mul_left _ _ _ hFh] at h
      have h4 := eval₂_comp_left (π.comp ι) (RingHom.id k) d F
      rw [RingHom.comp_id] at h4
      rw [h]
      exact congrArg (t ^ m * ·) h4
    have hne : (π.comp ι) (eval d F) ≠ 0 := (map_ne_zero _).mpr hdF
    have ht : t = 0 := pow_eq_zero_iff'.mp ((mul_eq_zero.mp hmain).resolve_right hne) |>.1
    have hUi : π (U i) = 0 := by
      have := congrFun hπU i
      rw [this, ht, zero_mul]
    have : U i = 1 := Subtype.ext (by simp [U, div_self hvi])
    rw [this, map_one] at hUi
    exact one_ne_zero hUi

end LateralTheory.EtaleTrace.StepPf
