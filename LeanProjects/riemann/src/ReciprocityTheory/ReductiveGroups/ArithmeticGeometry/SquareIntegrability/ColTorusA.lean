import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PolyDerivMonomialOne

namespace ReciprocityTheory.ChartRestriction.G.I2

open Metric

theorem ct_iter_cauchy {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (F : V → ℂ) (hF : ∀ m : ℕ, ContDiff ℂ m F) (ρ M : ℝ) (hρ : 0 < ρ) :
    ∀ (k : ℕ) (x : Fin k → V) (x₀ : V), (∀ j, ‖x j‖ ≤ 1) →
    (∀ y, ‖y - x₀‖ ≤ k * ρ → ‖F y‖ ≤ M) →
    ‖iteratedFDeriv ℂ k F x₀ x‖ ≤ M / ρ ^ k
  | 0, x, x₀, _, hM => by
    have := hM x₀ (by simp)
    have hx : x = 0 := Subsingleton.elim _ _
    simpa [iteratedFDeriv_zero_apply] using this
  | k + 1, x, x₀, hx, hM => by
    set e : V := x 0 with he
    set v : Fin k → V := Fin.tail x with hv
    set A := iteratedFDeriv ℂ k F with hA
    have hD : Differentiable ℂ A :=
      (hF (k + 1)).differentiable_iteratedFDeriv (m := k)
        (by exact_mod_cast Nat.lt_succ_self k)
    set g : ℂ → ℂ := fun w => A (x₀ + w • e) v with hg
    have hpath : ∀ w0 : ℂ, HasDerivAt (fun w : ℂ => x₀ + w • e) e w0 := by
      intro w0
      have := ((hasDerivAt_id w0).smul_const e).const_add x₀
      simpa using this
    have hgd : ∀ w0 : ℂ, HasDerivAt g (fderiv ℂ A (x₀ + w0 • e) e v) w0 := by
      intro w0
      have h1 := (hD (x₀ + w0 • e)).hasFDerivAt.comp_hasDerivAt w0 (hpath w0)
      have h2 := (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => V) ℂ v).hasFDerivAt.comp_hasDerivAt w0 h1
      simpa [Function.comp_def] using h2
    have hgdiff : Differentiable ℂ g := fun w0 => (hgd w0).differentiableAt
    have hderiv : deriv g 0 = iteratedFDeriv ℂ (k + 1) F x₀ x := by
      rw [(hgd 0).deriv, iteratedFDeriv_succ_apply_left, zero_smul, add_zero]
    have hsph : ∀ w ∈ sphere (0 : ℂ) ρ, ‖g w‖ ≤ M / ρ ^ k := by
      intro w hw
      have hw' : ‖w‖ = ρ := by simpa using hw
      have hwe : ‖w • e‖ ≤ ρ := by
        rw [norm_smul, hw']; simpa using mul_le_mul_of_nonneg_left (hx 0) hρ.le
      have := ct_iter_cauchy F hF ρ M hρ k v (x₀ + w • e) (fun j => hx _) (by
        intro y hy
        apply hM y
        calc ‖y - x₀‖ = ‖(y - (x₀ + w • e)) + w • e‖ := by congr 1; abel
          _ ≤ ‖y - (x₀ + w • e)‖ + ‖w • e‖ := norm_add_le _ _
          _ ≤ k * ρ + ρ := add_le_add hy hwe
          _ = ((k + 1 : ℕ) : ℝ) * ρ := by push_cast; ring)
      simpa [hg, hA, hv] using this
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hgdiff.diffContOnCl hsph
    rw [hderiv] at hc
    rw [pow_succ, ← div_div]
    exact hc

end ReciprocityTheory.ChartRestriction.G.I2

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex

theorem ct_iter_cexp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ℓ : V →L[ℂ] ℂ) (n : ℕ) :
    iteratedFDeriv ℂ n (fun w => cexp (ℓ w)) =
      fun v => cexp (ℓ v) • (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap
        (fun _ => ℓ) := by
  induction n with
  | zero =>
    funext v
    ext x
    simp [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  | succ n ih =>
    funext v
    ext x
    rw [iteratedFDeriv_succ_apply_left, ih]
    have hd : HasFDerivAt (fun w => cexp (ℓ w) •
        (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap (fun _ => ℓ))
        ((cexp (ℓ v) • ℓ).smulRight
          ((ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap (fun _ => ℓ))) v :=
      (ℓ.hasFDerivAt.cexp).smul_const _
    rw [hd.fderiv]
    simp [ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn, Fin.prod_univ_succ, Fin.tail]
    all_goals ring

theorem ct_iter_cexp_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ℓ : V →L[ℂ] ℂ) (n : ℕ) (v : V) (x : Fin n → V) :
    iteratedFDeriv ℂ n (fun w => cexp (ℓ w)) v x = cexp (ℓ v) * ∏ k, ℓ (x k) := by
  rw [ct_iter_cexp]
  simp [ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]

theorem ct_iter_mul_jet_one {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f g : V → ℂ) (hf : ContDiff ℂ (⊤ : ℕ∞) f) (hg : ContDiff ℂ (⊤ : ℕ∞) g) (c : ℕ)
    (h0 : g 0 = 1) (hjet : ∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j g 0 = 0) :
    iteratedFDeriv ℂ c (fun v => f v * g v) 0 = iteratedFDeriv ℂ c f 0 := by
  have hle : ∀ k : ℕ, ((k : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    intro k
    first
      | exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
      | exact WithTop.coe_le_coe.2 le_top
  have hhC : ContDiff ℂ (⊤ : ℕ∞) (fun v => g v - 1) := hg.sub contDiff_const
  have hz : ∀ k ≤ c, iteratedFDeriv ℂ k (fun v => g v - 1) 0 = 0 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · ext x
      simp [iteratedFDeriv_zero_apply, h0]
    · have e : (fun v => g v - 1) = g - fun _ => (1 : ℂ) := rfl
      rw [e]
      first
        | rw [iteratedFDeriv_sub_apply (hg.of_le (hle k)).contDiffAt contDiff_const.contDiffAt]
        | rw [iteratedFDeriv_sub_apply (hg.of_le (hle k)) contDiff_const]
      rw [hjet k hk0 hk, iteratedFDeriv_const_of_ne (by omega)]
      simp
  have hsplit : (fun v => f v * g v) = (fun v => f v) + (fun v => f v * (g v - 1)) := by
    funext v
    simp only [Pi.add_apply]
    ring
  have hfh : ContDiff ℂ (⊤ : ℕ∞) (fun v => f v * (g v - 1)) := hf.mul hhC
  rw [hsplit]
  first
    | rw [iteratedFDeriv_add_apply (hf.of_le (hle c)).contDiffAt (hfh.of_le (hle c)).contDiffAt]
    | rw [iteratedFDeriv_add_apply (hf.of_le (hle c)) (hfh.of_le (hle c))]
  have hb := norm_iteratedFDeriv_mul_le hf hhC (0 : V) (n := c) (hle c)
  have h0' : iteratedFDeriv ℂ c (fun v => f v * (g v - 1)) 0 = 0 := by
    rw [← norm_le_zero_iff]
    refine hb.trans (le_of_eq (Finset.sum_eq_zero fun i hi => ?_))
    rw [hz (c - i) (Nat.sub_le _ _), norm_zero, mul_zero]
  rw [h0', add_zero]

end ReciprocityTheory.ChartRestriction.G.I2

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex

noncomputable section

section

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem ct_itD_contDiff {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) (l : List W) :
    ContDiff ℂ (⊤ : ℕ∞) (fun y => itD f l y) := by
  unfold itD
  have h : ContDiff ℂ (⊤ : ℕ∞) (iteratedFDeriv ℂ l.length f) := by
    refine contDiff_infty.2 fun m => hf.iteratedFDeriv_right ?_
    first
      | exact_mod_cast (le_top : ((m + l.length : ℕ) : ℕ∞) ≤ ⊤)
      | exact WithTop.coe_le_coe.2 le_top
      | simp
  exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin l.length => W) ℂ _).contDiff.comp h

theorem ct_itD_cons_cons {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) (a b : W) (l : List W) (z : W) :
    itD f (a :: b :: l) z = fderiv ℂ (fderiv ℂ (fun y => itD f l y)) z a b := by
  have hg := ct_itD_contDiff hf l
  have h1 := contDiff_infty_iff_fderiv.1 hg
  have h2 := (contDiff_infty_iff_fderiv.1 h1.2).1
  rw [itD_cons hf]
  have hc : (fun y => itD f (b :: l) y) =
      (ContinuousLinearMap.apply ℂ ℂ b) ∘ fderiv ℂ (fun y => itD f l y) := by
    funext y
    exact itD_cons hf b l y
  rw [hc, fderiv_comp z (ContinuousLinearMap.differentiableAt _) (h2 z), ContinuousLinearMap.fderiv]
  rfl

theorem ct_itD_perm {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) {l₁ l₂ : List W} (h : l₁.Perm l₂) :
    (fun y => itD f l₁ y) = fun y => itD f l₂ y := by
  induction h with
  | nil => rfl
  | @cons x l₁ l₂ _ ih =>
    funext y
    rw [itD_cons hf, itD_cons hf, ih]
  | @swap x y l =>
    funext z
    rw [ct_itD_cons_cons hf, ct_itD_cons_cons hf]
    have hg := ct_itD_contDiff hf l
    have hs : IsSymmSndFDerivAt ℂ (fun y => itD f l y) z := by
      refine hg.contDiffAt.isSymmSndFDerivAt ?_
      try simp only [minSmoothness_of_isRCLikeNormedField]
      first
        | exact WithTop.coe_le_coe.2 le_top
        | exact (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
        | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
        | norm_num
        | decide
    exact hs y x
  | @trans l₁ l₂ l₃ _ _ ih1 ih2 => rw [ih1, ih2]

end

theorem ct_iter_eq_itD_ofFn {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (F : W → ℂ) (x : W)
    (j : ℕ) (w : Fin j → W) : iteratedFDeriv ℂ j F x w = itD F (List.ofFn w) x := by
  have gen : ∀ (n₁ n₂ : ℕ) (h : n₁ = n₂) (v₁ : Fin n₁ → W) (v₂ : Fin n₂ → W),
      (∀ i, v₁ i = v₂ (i.cast h)) → iteratedFDeriv ℂ n₁ F x v₁ = iteratedFDeriv ℂ n₂ F x v₂ := by
    intro n₁ n₂ h v₁ v₂ hv
    subst h
    exact congrArg _ (funext fun i => hv i)
  unfold itD
  refine gen _ _ (by simp) _ _ fun i => ?_
  simp

theorem ct_iter_single_eq_polyDeriv {ι : Type} [Fintype ι] [DecidableEq ι] (F : EuclideanSpace ℂ ι → ℂ)
    (hF : ContDiff ℂ (⊤ : ℕ∞) F) (j : ℕ) (v : Fin j → ι) :
    iteratedFDeriv ℂ j F 0 (fun k => EuclideanSpace.single (v k) (1 : ℂ)) =
      polyDeriv (MvPolynomial.monomial (Multiset.toFinsupp (↑(List.ofFn v) : Multiset ι)) (1 : ℂ))
        (fun i => EuclideanSpace.single i (1 : ℂ)) F 0 := by
  rw [ct_iter_eq_itD_ofFn, polyDeriv_monomial_one, pdTerm_eq_itD, Multiset.toFinsupp_toMultiset]
  have hl : (List.ofFn fun k => EuclideanSpace.single (v k) (1 : ℂ)) =
      (List.ofFn v).map (fun i => EuclideanSpace.single i (1 : ℂ)) := by
    rw [List.map_ofFn]
    rfl
  have hp : (List.ofFn fun k => EuclideanSpace.single (v k) (1 : ℂ)).Perm
      (((↑(List.ofFn v) : Multiset ι).toList).map fun i => EuclideanSpace.single i (1 : ℂ)) := by
    rw [hl]
    exact List.Perm.map _ (Multiset.coe_eq_coe.1 (Multiset.coe_toList _)).symm
  exact congrFun (ct_itD_perm hF hp) 0

theorem ct_degree_toFinsupp_ofFn {ι : Type} [DecidableEq ι] (j : ℕ) (v : Fin j → ι) :
    (Multiset.toFinsupp (↑(List.ofFn v) : Multiset ι)).degree = j := by
  have h := Finsupp.card_toMultiset (Multiset.toFinsupp (↑(List.ofFn v) : Multiset ι))
  rw [Multiset.toFinsupp_toMultiset, Multiset.coe_card, List.length_ofFn] at h
  refine Eq.trans ?_ h.symm
  first
    | rfl
    | simp [Finsupp.degree, Finsupp.sum]
    | simp [Finsupp.degree_eq_sum, Finsupp.sum]

open Classical in

theorem ct_jet_one_iter {ι : Type} [Fintype ι] (β : EuclideanSpace ℂ ι → ℂ)
    (hβ : ContDiff ℂ (⊤ : ℕ∞) β) (c : ℕ)
    (hjet : ∀ α : ι →₀ ℕ, α.degree ≤ c →
      polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) β 0 =
        polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1)
          (fun v : EuclideanSpace ℂ ι => MvPolynomial.eval (fun i => v i) (1 : MvPolynomial ι ℂ)) 0) :
    β 0 = 1 ∧ ∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j β 0 = 0 := by
  have hone : ContDiff ℂ (⊤ : ℕ∞)
      (fun w : EuclideanSpace ℂ ι => MvPolynomial.eval (fun i => w i) (1 : MvPolynomial ι ℂ)) := by
    simp only [map_one]
    exact contDiff_const
  have key : ∀ j (v : Fin j → ι), j ≤ c →
      iteratedFDeriv ℂ j β 0 (fun k => EuclideanSpace.single (v k) (1 : ℂ)) =
        iteratedFDeriv ℂ j
          (fun w : EuclideanSpace ℂ ι => MvPolynomial.eval (fun i => w i) (1 : MvPolynomial ι ℂ)) 0
          (fun k => EuclideanSpace.single (v k) (1 : ℂ)) := by
    intro j v hj
    rw [ct_iter_single_eq_polyDeriv β hβ j v, ct_iter_single_eq_polyDeriv _ hone j v]
    exact hjet _ (by rw [ct_degree_toFinsupp_ofFn]; exact hj)
  refine ⟨?_, fun j hj1 hjc => ?_⟩
  · have h := key 0 Fin.elim0 (Nat.zero_le _)
    simpa [iteratedFDeriv_zero_apply] using h
  · have hz : ∀ v : Fin j → ι,
        iteratedFDeriv ℂ j β 0 (fun k => EuclideanSpace.single (v k) (1 : ℂ)) = 0 := by
      intro v
      rw [key j v hjc]
      simp only [map_one]
      rw [iteratedFDeriv_const_of_ne (by omega)]
      rfl
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    refine Module.Basis.ext_multilinear (fun _ => (EuclideanSpace.basisFun ι ℂ).toBasis) ?_
    intro v
    simpa using hz v

end

end ReciprocityTheory.ChartRestriction.G.I2
