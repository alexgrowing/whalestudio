import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar

open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

namespace GlobalTheory.HilbTensorRep

section Abstract

variable {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℂ (H i)] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {tens : (∀ i, H i) → Hs}

omit [Fintype ι] [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] in

theorem ext_vec (hd : Dense (Submodule.span ℂ (Set.range tens) : Set Hs)) {u u' : Hs}
    (h : ∀ y, ⟪tens y, u⟫_ℂ = ⟪tens y, u'⟫_ℂ) : u = u' := by
  have key : (innerSL ℂ (u - u') : Hs →L[ℂ] ℂ) = 0 := by
    refine ContinuousLinearMap.ext_on hd ?_
    rintro _ ⟨y, rfl⟩
    rw [innerSL_apply_apply, zero_apply]
    rw [inner_eq_zero_symm, inner_sub_right, h y, sub_self]
  have h0 : ⟪u - u', u - u'⟫_ℂ = 0 := by
    have := congrArg (fun L : Hs →L[ℂ] ℂ => L (u - u')) key
    simpa only [innerSL_apply_apply, zero_apply] using this
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)

omit [Fintype ι] [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] in

theorem ext_op (hd : Dense (Submodule.span ℂ (Set.range tens) : Set Hs)) {A A' : Hs →L[ℂ] Hs}
    (h : ∀ x, A (tens x) = A' (tens x)) : A = A' := ContinuousLinearMap.ext_on hd (by rintro _ ⟨x, rfl⟩; exact h x)

theorem norm_tens (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) (x : ∀ i, H i) :
    ‖tens x‖ = ∏ i, ‖x i‖ := by
  have h1 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (tens x)
  rw [hi, Finset.prod_congr rfl (fun i _ => inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x i)),
    Finset.prod_pow] at h1
  have h2 : ‖tens x‖ ^ 2 = (∏ i, ‖x i‖) ^ 2 := by
    exact_mod_cast h1.symm
  exact (pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    two_ne_zero).mp h2

theorem continuous_tens (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) :
    Continuous tens := by
  rw [continuous_iff_continuousAt]
  intro x0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hf : ∀ x, ‖tens x - tens x0‖ = Real.sqrt ((∏ i, ‖x i‖) ^ 2
      - 2 * RCLike.re (∏ i, ⟪x i, x0 i⟫_ℂ) + (∏ i, ‖x0 i‖) ^ 2) := by
    intro x
    rw [← norm_tens hi x, ← norm_tens hi x0, ← hi, ← norm_sub_sq (𝕜 := ℂ),
      Real.sqrt_sq (norm_nonneg _)]
  have hc : Continuous fun x : (∀ i, H i) => Real.sqrt ((∏ i, ‖x i‖) ^ 2
      - 2 * RCLike.re (∏ i, ⟪x i, x0 i⟫_ℂ) + (∏ i, ‖x0 i‖) ^ 2) := by
    refine Real.continuous_sqrt.comp (Continuous.add (Continuous.sub ?_ ?_) continuous_const)
    · exact (continuous_finsetProd _ fun i _ => (continuous_apply i).norm).pow 2
    · exact continuous_const.mul (RCLike.continuous_re.comp
        (continuous_finsetProd _ fun i _ => (continuous_apply i).inner continuous_const))
  have h := hc.tendsto x0
  rw [← hf x0, sub_self, norm_zero] at h
  exact h.congr fun x => (hf x).symm

variable [DecidableEq ι]

theorem inner_update (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) (v : ι)
    (y x : ∀ i, H i) (a : H v) :
    ⟪tens y, tens (Function.update x v a)⟫_ℂ
      = ⟪y v, a⟫_ℂ * ∏ i ∈ Finset.univ.erase v, ⟪y i, x i⟫_ℂ := by
  rw [hi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi' => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi')]

theorem exists_continuousLinearMap_tens_update (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range tens) : Set Hs)) (v : ι) (x : ∀ i, H i) :
    ∃ L : H v →L[ℂ] Hs, ∀ a, L a = tens (Function.update x v a) := by
  have hadd : ∀ a b : H v, tens (Function.update x v (a + b))
      = tens (Function.update x v a) + tens (Function.update x v b) := by
    intro a b
    refine ext_vec hd fun y => ?_
    rw [inner_add_right, inner_update hi, inner_update hi, inner_update hi, inner_add_right, add_mul]
  have hsmul : ∀ (c : ℂ) (a : H v), tens (Function.update x v (c • a))
      = c • tens (Function.update x v a) := by
    intro c a
    refine ext_vec hd fun y => ?_
    rw [inner_smul_right, inner_update hi, inner_update hi, inner_smul_right, mul_assoc]
  let f : H v →ₗ[ℂ] Hs :=
    { toFun := fun a => tens (Function.update x v a)
      map_add' := hadd
      map_smul' := hsmul }
  refine ⟨f.mkContinuous (∏ i ∈ Finset.univ.erase v, ‖x i‖) fun a => ?_, fun a => rfl⟩
  show ‖tens (Function.update x v a)‖ ≤ _
  rw [norm_tens hi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v),
    Function.update_self, mul_comm]
  refine le_of_eq (congrArg (· * ‖a‖) (Finset.prod_congr rfl fun i hi' => ?_))
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi')]

omit [Fintype ι] [DecidableEq ι] in
theorem exists_unit (v : ι) : ∃ e : H v, ∀ a b : H v, ⟪b, a⟫_ℂ = ⟪b, a⟫_ℂ * ⟪e, e⟫_ℂ := by
  by_cases h : ∃ w : H v, w ≠ 0
  · obtain ⟨w, hw⟩ := h
    obtain ⟨e, he⟩ : ∃ e : H v, ‖e‖ = 1 := ⟨_, norm_smul_inv_norm (𝕜 := ℂ) hw⟩
    refine ⟨e, fun a b => ?_⟩
    rw [inner_self_eq_norm_sq_to_K, he]
    simp
  · simp only [not_exists, not_not] at h
    refine ⟨0, fun a b => ?_⟩
    rw [h b]
    simp

variable {G : ι → Type} [∀ i, Group (G i)] {π : ∀ i, G i →* (H i →L[ℂ] H i)}
  {σs : (∀ i, G i) → (Hs →L[ℂ] Hs)}

omit [Fintype ι] [DecidableEq ι] in
theorem inner_inv_loc (hn : ∀ i g a, ‖π i g a‖ = ‖a‖) (i : ι) (g : G i) (a b : H i) :
    ⟪b, π i g⁻¹ a⟫_ℂ = ⟪π i g b, a⟫_ℂ := by
  have hpres : ∀ x y : H i, ⟪π i g x, π i g y⟫_ℂ = ⟪x, y⟫_ℂ :=
    (LinearMap.norm_map_iff_inner_map_map (π i g)).mp (hn i g)
  have hinv : π i g (π i g⁻¹ a) = a := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one,
      one_apply_eq_self]
  rw [← hpres b (π i g⁻¹ a), hinv]

omit [DecidableEq ι] in
theorem inner_inv (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range tens) : Set Hs))
    (hs : ∀ g x, σs g (tens x) = tens fun i => π i (g i) (x i))
    (hn : ∀ i g a, ‖π i g a‖ = ‖a‖) (g : ∀ i, G i) (a b : Hs) :
    ⟪b, σs g⁻¹ a⟫_ℂ = ⟪σs g b, a⟫_ℂ := by
  have h1 : ∀ y x, ⟪tens y, σs g⁻¹ (tens x)⟫_ℂ = ⟪σs g (tens y), tens x⟫_ℂ := by
    intro y x
    rw [hs, hs, hi, hi]
    exact Finset.prod_congr rfl fun i _ => inner_inv_loc hn i (g i) (x i) (y i)
  have h2 : ∀ y c, ⟪tens y, σs g⁻¹ c⟫_ℂ = ⟪σs g (tens y), c⟫_ℂ := by
    intro y
    have hL : (innerSL ℂ (tens y)).comp (σs g⁻¹) = innerSL ℂ (σs g (tens y)) := by
      refine ContinuousLinearMap.ext_on hd ?_
      rintro _ ⟨x, rfl⟩
      rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, innerSL_apply_apply]
      exact h1 y x
    intro c
    have := congrArg (fun L : Hs →L[ℂ] ℂ => L c) hL
    simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using this
  have hL : innerSL ℂ (σs g⁻¹ a) = (innerSL ℂ a).comp (σs g) := by
    refine ContinuousLinearMap.ext_on hd ?_
    rintro _ ⟨y, rfl⟩
    rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, innerSL_apply_apply,
      ← inner_conj_symm (σs g⁻¹ a) (tens y), h2 y a, inner_conj_symm]
  have h3 : ⟪σs g⁻¹ a, b⟫_ℂ = ⟪a, σs g b⟫_ℂ := by
    have := congrArg (fun L : Hs →L[ℂ] ℂ => L b) hL
    simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using this
  rw [← inner_conj_symm b (σs g⁻¹ a), h3, inner_conj_symm]

theorem commutant_scalar [∀ i, CompleteSpace (H i)] [CompleteSpace Hs]
    (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range tens) : Set Hs))
    (hs : ∀ g x, σs g (tens x) = tens fun i => π i (g i) (x i))
    (hn : ∀ i g a, ‖π i g a‖ = ‖a‖)
    (hirr : ∀ i, ∀ S : Submodule ℂ (H i), IsClosed (S : Set (H i)) →
      (∀ g, ∀ v ∈ S, π i g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (T : Hs →L[ℂ] Hs) (hT : ∀ g u, σs g (T u) = T (σs g u)) :
    ∃ c : ℂ, T = c • (1 : Hs →L[ℂ] Hs) := by
  choose e he using fun v => exists_unit (H := H) v
  have hposition : ∀ (v : ι) (g : ∀ i, G i), (∀ i, i ≠ v → g i = 1) → ∀ (z : ∀ i, H i) (a : H v),
      σs g (tens (Function.update z v a)) = tens (Function.update z v (π v (g v) a)) := by
    intro v g hg z a
    rw [hs]
    congr 1
    funext i
    by_cases hiv : i = v
    · subst hiv
      simp only [Function.update_self]
    · rw [Function.update_of_ne hiv, Function.update_of_ne hiv, hg i hiv, map_one,
        one_apply_eq_self]
  have key : ∀ (v : ι) (y x : ∀ i, H i) (a b : H v),
      ⟪tens (Function.update y v b), T (tens (Function.update x v a))⟫_ℂ
        = ⟪b, a⟫_ℂ * ⟪tens (Function.update y v (e v)), T (tens (Function.update x v (e v)))⟫_ℂ := by
    intro v y x a b
    obtain ⟨Lx, hLx⟩ := exists_continuousLinearMap_tens_update hi hd v x
    obtain ⟨Ly, hLy⟩ := exists_continuousLinearMap_tens_update hi hd v y
    obtain ⟨K, hK⟩ : ∃ K : H v →L[ℂ] H v, K = (ContinuousLinearMap.adjoint Ly).comp (T.comp Lx) :=
      ⟨_, rfl⟩
    have hKin : ∀ a b, ⟪b, K a⟫_ℂ
        = ⟪tens (Function.update y v b), T (tens (Function.update x v a))⟫_ℂ := by
      intro a b
      rw [hK, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_right, hLy, hLx]
    have hcomm : ∀ h : G v, π v h * K = K * π v h := by
      intro h
      refine ContinuousLinearMap.ext fun a => ext_inner_left ℂ fun b => ?_
      have hg1 : ∀ i, i ≠ v → (Pi.mulSingle v h : ∀ i, G i) i = 1 := fun i hiv =>
        Pi.mulSingle_eq_of_ne hiv h
      have hg2 : ∀ i, i ≠ v → (Pi.mulSingle v h : ∀ i, G i)⁻¹ i = 1 := fun i hiv => by
        rw [Pi.inv_apply, Pi.mulSingle_eq_of_ne hiv h, inv_one]
      have e1 := hposition v _ hg1 x a
      have e2 := hposition v _ hg2 y b
      rw [Pi.mulSingle_eq_same] at e1
      rw [Pi.inv_apply, Pi.mulSingle_eq_same] at e2
      rw [mul_apply_eq_comp, mul_apply_eq_comp]
      have l1 : ⟪b, π v h (K a)⟫_ℂ = ⟪π v h⁻¹ b, K a⟫_ℂ := by
        simpa only [inv_inv] using inner_inv_loc hn v h⁻¹ (K a) b
      have l2 : ⟪tens (Function.update y v b),
            σs (Pi.mulSingle v h) (T (tens (Function.update x v a)))⟫_ℂ
          = ⟪σs (Pi.mulSingle v h)⁻¹ (tens (Function.update y v b)),
            T (tens (Function.update x v a))⟫_ℂ := by
        simpa only [inv_inv] using inner_inv hi hd hs hn (Pi.mulSingle v h)⁻¹
          (T (tens (Function.update x v a))) (tens (Function.update y v b))
      rw [l1, hKin, hKin, ← e2, ← e1, ← hT, l2]
    obtain ⟨c, hc⟩ := GlobalTheory.hilbert_schur (H v) (G v) (π v) (hn v) (hirr v) K hcomm
    rw [← hKin, ← hKin, hc]
    simp only [smul_apply, one_apply_eq_self, inner_smul_right]
    linear_combination c * he v a b
  have hF : ∀ (s : Finset ι) (y x : ∀ i, H i), (∀ i, i ∉ s → y i = e i ∧ x i = e i) →
      ⟪tens y, T (tens x)⟫_ℂ = (∏ i ∈ s, ⟪y i, x i⟫_ℂ) * ⟪tens e, T (tens e)⟫_ℂ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y x hyx
      have hy : y = e := funext fun i => (hyx i (Finset.notMem_empty i)).1
      have hx : x = e := funext fun i => (hyx i (Finset.notMem_empty i)).2
      rw [hy, hx, Finset.prod_empty, one_mul]
    | insert j s hj ih =>
      intro y x hyx
      have h1 := key j y x (x j) (y j)
      rw [Function.update_eq_self, Function.update_eq_self] at h1
      rw [h1, ih (Function.update y j (e j)) (Function.update x j (e j)), Finset.prod_insert hj,
        mul_assoc]
      · congr 2
        refine Finset.prod_congr rfl fun i his => ?_
        have hij : i ≠ j := fun hij => hj (hij ▸ his)
        rw [Function.update_of_ne hij, Function.update_of_ne hij]
      · intro i his
        by_cases hij : i = j
        · subst hij
          simp only [Function.update_self, and_self]
        · rw [Function.update_of_ne hij, Function.update_of_ne hij]
          exact hyx i (fun hmem => (Finset.mem_insert.mp hmem).elim hij his)
  refine ⟨⟪tens e, T (tens e)⟫_ℂ, ext_op hd fun x => ext_vec hd fun y => ?_⟩
  rw [hF Finset.univ y x (fun i hi' => absurd (Finset.mem_univ i) hi'),
    smul_apply, one_apply_eq_self, inner_smul_right, hi, mul_comm]

omit [DecidableEq ι] in

theorem tensor_rep [∀ i, CompleteSpace (H i)] [CompleteSpace Hs] [∀ i, TopologicalSpace (G i)]
    (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range tens) : Set Hs))
    (hs : ∀ g x, σs g (tens x) = tens fun i => π i (g i) (x i))
    (hn : ∀ i g a, ‖π i g a‖ = ‖a‖) (hc : ∀ i a, Continuous fun g => π i g a)
    (hirr : ∀ i, ∀ S : Submodule ℂ (H i), IsClosed (S : Set (H i)) →
      (∀ g, ∀ v ∈ S, π i g v ∈ S) → S = ⊥ ∨ S = ⊤) :
    σs 1 = 1 ∧ (∀ g h, σs (g * h) = σs g * σs h) ∧ (∀ g u, ‖σs g u‖ = ‖u‖) ∧
      (∀ u, Continuous fun g => σs g u) ∧ ∀ S : Submodule ℂ Hs, IsClosed (S : Set Hs) →
        (∀ g, ∀ u ∈ S, σs g u ∈ S) → S = ⊥ ∨ S = ⊤ := by
  classical
  have h1 : σs 1 = 1 := ext_op hd fun x => by
    rw [hs, one_apply_eq_self]
    congr 1
    funext i
    rw [Pi.one_apply, map_one, one_apply_eq_self]
  have hmul : ∀ g h, σs (g * h) = σs g * σs h := fun g h => ext_op hd fun x => by
    rw [mul_apply_eq_comp, hs h x, hs g, hs (g * h)]
    congr 1
    funext i
    rw [Pi.mul_apply, map_mul, mul_apply_eq_comp]
  have hnorm : ∀ g u, ‖σs g u‖ = ‖u‖ := by
    intro g u
    have hk : σs g⁻¹ (σs g u) = u := by
      rw [← mul_apply_eq_comp, ← hmul, inv_mul_cancel, h1,
        one_apply_eq_self]
    have h2 : ⟪σs g u, σs g u⟫_ℂ = ⟪u, u⟫_ℂ := by
      rw [← inner_inv hi hd hs hn g (σs g u) u, hk]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
    have h3 : ‖σs g u‖ ^ 2 = ‖u‖ ^ 2 := by exact_mod_cast h2
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3
  have hcont_span : ∀ w ∈ Submodule.span ℂ (Set.range tens), Continuous fun g => σs g w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, rfl⟩ := hw
      have : (fun g => σs g (tens x)) = fun g => tens fun i => π i (g i) (x i) :=
        funext fun g => hs g x
      rw [this]
      exact (continuous_tens hi).comp
        (continuous_pi fun i => (hc i (x i)).comp (continuous_apply i))
    | zero => simpa only [map_zero] using continuous_const
    | add w w' _ _ hw hw' =>
      simp only [map_add]
      exact hw.add hw'
    | smul c w _ hw =>
      simp only [map_smul]
      exact hw.const_smul c
  refine ⟨h1, hmul, hnorm, fun u => ?_, fun S hS hSinv => ?_⟩
  · refine continuous_of_uniform_approx_of_continuous fun U hU => ?_
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
    obtain ⟨w, hw, hdw⟩ := Metric.mem_closure_iff.mp (hd u) ε hε
    refine ⟨fun g => σs g w, hcont_span w hw, fun g => hεU ?_⟩
    rw [dist_eq_norm, ← map_sub, hnorm, ← dist_eq_norm]
    exact hdw
  · have : CompleteSpace S := hS.completeSpace_coe
    have horth : ∀ g, ∀ w ∈ Sᗮ, σs g w ∈ Sᗮ := by
      intro g w hw
      rw [Submodule.mem_orthogonal]
      intro s hs'
      have := inner_inv hi hd hs hn g⁻¹ w s
      rw [inv_inv] at this
      rw [this]
      exact Submodule.inner_right_of_mem_orthogonal (hSinv g⁻¹ s hs') hw
    have hP : ∀ g u, σs g (S.starProjection u) = S.starProjection (σs g u) := by
      intro g u
      symm
      refine Submodule.eq_starProjection_of_mem_orthogonal
        (hSinv g _ (S.starProjection_apply_mem u)) ?_
      rw [← map_sub]
      exact horth g _ (Submodule.sub_starProjection_mem_orthogonal u)
    obtain ⟨c, hc⟩ := commutant_scalar hi hd hs hn hirr (S.starProjection) hP
    by_cases hc0 : c = 0
    · left
      rw [Submodule.eq_bot_iff]
      intro s hs'
      rw [← Submodule.starProjection_eq_self_iff.mpr hs', hc, hc0, zero_smul,
        zero_apply]
    · right
      rw [Submodule.eq_top_iff']
      intro u
      have hu : u = c⁻¹ • S.starProjection u := by
        rw [hc, smul_apply, one_apply_eq_self, smul_smul,
          inv_mul_cancel₀ hc0, one_smul]
      rw [hu]
      exact S.smul_mem _ (S.starProjection_apply_mem u)

end Abstract

theorem tensor_rep_rows : ∀ B : RowsAut, (∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) ∧ IsIrredOn (UJset (B.I.ε v)) (B.σ v)) → B.σs 1 = 1 ∧ (∀ g h, B.σs (g * h) = B.σs g * B.σs h) ∧ (∀ g u, ‖B.σs g u‖ = ‖u‖) ∧ (∀ u, Continuous fun g => B.σs g u) ∧ ∀ S : Submodule ℂ B.Hs, IsClosed (S : Set B.Hs) → (∀ g, ∀ u ∈ S, B.σs g u ∈ S) → S = ⊥ ∨ S = ⊤ := by
  intro B hB
  obtain ⟨hi, hs, hd⟩ := B.tens_spec
  have hmem : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), uMat g ∈ UJset (B.I.ε v) := fun v g => g.2
  let π : ∀ v, Formalism.REAL.UJ (B.I.ε v) →* (B.H v →L[ℂ] B.H v) := fun v =>
    { toFun := fun g => B.σ v (uMat g)
      map_one' := (hB v).1.1.1
      map_mul' := fun g h => (hB v).1.1.2 _ (hmem v g) _ (hmem v h) }
  have hn : ∀ v g a, ‖π v g a‖ = ‖a‖ := fun v g a => (hB v).1.2.1 _ (hmem v g) a
  have hc : ∀ v a, Continuous fun g => π v g a := fun v a =>
    ((hB v).1.2.2 a).comp_continuous (Units.continuous_val.comp continuous_subtype_val)
      (hmem v)
  have hirr : ∀ v, ∀ S : Submodule ℂ (B.H v), IsClosed (S : Set (B.H v)) →
      (∀ g, ∀ a ∈ S, π v g a ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro v S hS hSinv
    refine (hB v).2 S hS fun m hm a ha => ?_
    have hm' : Matrix.conjTranspose m * Formalism.REAL.Jm (B.I.ε v) * m = Formalism.REAL.Jm (B.I.ε v) := hm
    have hl : (Formalism.REAL.Jm (B.I.ε v) * Matrix.conjTranspose m * Formalism.REAL.Jm (B.I.ε v)) * m = 1 := by
      rw [mul_assoc, mul_assoc, ← mul_assoc (Matrix.conjTranspose m), hm', Formalism.REAL.Jm_mul_self]
    let u : (Matrix (Fin B.I.n) (Fin B.I.n) ℂ)ˣ :=
      ⟨m, Formalism.REAL.Jm (B.I.ε v) * Matrix.conjTranspose m * Formalism.REAL.Jm (B.I.ε v), mul_eq_one_comm.mp hl, hl⟩
    exact hSinv ⟨u, hm⟩ a ha
  exact tensor_rep (π := π) (σs := B.σs) (tens := B.tens) hi hd hs hn hc hirr

end GlobalTheory.HilbTensorRep
