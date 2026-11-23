import Mathlib
import GroundTheory.AutomorphicForms.Reduction

open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing NNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

section Local

variable {E : Type*} [NormedField E] {n : ℕ}

def locHeight (g : GL (Fin n) E) : ℝ :=
  max 1 ((Finset.univ.sup fun p : Fin n × Fin n =>
    max ‖(g : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊
      ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊ : ℝ≥0) : ℝ)

theorem one_le_locHeight (g : GL (Fin n) E) : 1 ≤ locHeight g := le_max_left _ _

theorem locHeight_pos (g : GL (Fin n) E) : 0 < locHeight g :=
  lt_of_lt_of_le one_pos (one_le_locHeight g)

theorem norm_apply_le_locHeight (g : GL (Fin n) E) (i j : Fin n) :
    ‖(g : Matrix (Fin n) (Fin n) E) i j‖ ≤ locHeight g := by
  refine le_trans ?_ (le_max_right _ _)
  have := Finset.le_sup (f := fun p : Fin n × Fin n =>
    max ‖(g : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊
      ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊) (Finset.mem_univ (i, j))
  exact le_trans (le_max_left _ _) (NNReal.coe_le_coe.2 this)

theorem norm_inv_apply_le_locHeight (g : GL (Fin n) E) (i j : Fin n) :
    ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j‖ ≤ locHeight g := by
  refine le_trans ?_ (le_max_right _ _)
  have := Finset.le_sup (f := fun p : Fin n × Fin n =>
    max ‖(g : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊
      ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊) (Finset.mem_univ (i, j))
  exact le_trans (le_max_right _ _) (NNReal.coe_le_coe.2 this)

theorem locHeight_le {g : GL (Fin n) E} {c : ℝ} (hc : 1 ≤ c)
    (h₁ : ∀ i j, ‖(g : Matrix (Fin n) (Fin n) E) i j‖ ≤ c)
    (h₂ : ∀ i j, ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j‖ ≤ c) :
    locHeight g ≤ c := by
  refine max_le hc ?_
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have : (Finset.univ.sup fun p : Fin n × Fin n =>
      max ‖(g : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊
        ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊) ≤ ⟨c, hc0⟩ :=
    Finset.sup_le fun p _ => max_le (h₁ p.1 p.2) (h₂ p.1 p.2)
  exact this

theorem locHeight_inv (g : GL (Fin n) E) : locHeight g⁻¹ = locHeight g := by
  refine le_antisymm (locHeight_le (one_le_locHeight g) (fun i j => norm_inv_apply_le_locHeight g i j)
    fun i j => ?_) (locHeight_le (one_le_locHeight _) (fun i j => ?_) fun i j => ?_)
  · rw [inv_inv]; exact norm_apply_le_locHeight g i j
  · have := norm_inv_apply_le_locHeight g⁻¹ i j
    rwa [inv_inv] at this
  · exact norm_apply_le_locHeight g⁻¹ i j

theorem locHeight_one : locHeight (1 : GL (Fin n) E) = 1 := by
  refine le_antisymm (locHeight_le le_rfl (fun i j => ?_) fun i j => ?_) (one_le_locHeight _)
  · simp only [Units.val_one, Matrix.one_apply]; split_ifs <;> simp
  · simp only [inv_one, Units.val_one, Matrix.one_apply]; split_ifs <;> simp

theorem norm_mul_apply_le (a b : Matrix (Fin n) (Fin n) E) {A B : ℝ} (hA : ∀ i j, ‖a i j‖ ≤ A)
    (hB : ∀ i j, ‖b i j‖ ≤ B) (hA0 : 0 ≤ A) (i j : Fin n) : ‖(a * b) i j‖ ≤ n * (A * B) := by
  rw [Matrix.mul_apply]
  calc ‖∑ k, a i k * b k j‖ ≤ ∑ k, ‖a i k * b k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, A * B := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]; exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) hA0
    _ = n * (A * B) := by simp

theorem locHeight_mul_le (g h : GL (Fin n) E) :
    locHeight (g * h) ≤ max 1 (n : ℝ) * locHeight g * locHeight h := by
  have hg := one_le_locHeight g
  have hh := one_le_locHeight h
  have hn : (1 : ℝ) ≤ max 1 (n : ℝ) := le_max_left _ _
  have h1 : 1 ≤ max 1 (n : ℝ) * locHeight g * locHeight h := by
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul hn hg zero_le_one (le_trans zero_le_one hn)) hh zero_le_one
          (by positivity)
  have key : ∀ (a b : Matrix (Fin n) (Fin n) E) (A B : ℝ), (∀ i j, ‖a i j‖ ≤ A) →
      (∀ i j, ‖b i j‖ ≤ B) → 1 ≤ A → 1 ≤ B → ∀ i j, ‖(a * b) i j‖ ≤ max 1 (n : ℝ) * A * B := by
    intro a b A B hA hB hA1 hB1 i j
    refine le_trans (norm_mul_apply_le a b hA hB (le_trans zero_le_one hA1) i j) ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  refine locHeight_le h1 (fun i j => ?_) fun i j => ?_
  · rw [Units.val_mul]
    exact key _ _ _ _ (norm_apply_le_locHeight g) (norm_apply_le_locHeight h) hg hh i j
  · rw [mul_inv_rev, Units.val_mul]
    have := key _ _ _ _ (norm_inv_apply_le_locHeight h) (norm_inv_apply_le_locHeight g) hh hg i j
    rwa [mul_right_comm] at this

theorem locHeight_mul_le_of_ultrametric [IsUltrametricDist E] (g h : GL (Fin n) E) :
    locHeight (g * h) ≤ locHeight g * locHeight h := by
  have hg := one_le_locHeight g
  have hh := one_le_locHeight h
  have key : ∀ (a b : Matrix (Fin n) (Fin n) E) (A B : ℝ), (∀ i j, ‖a i j‖ ≤ A) →
      (∀ i j, ‖b i j‖ ≤ B) → 1 ≤ A → 1 ≤ B → ∀ i j, ‖(a * b) i j‖ ≤ A * B := by
    intro a b A B hA hB hA1 hB1 i j
    rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) (le_trans zero_le_one hA1)
  refine locHeight_le (one_le_mul_of_one_le_of_one_le hg hh) (fun i j => ?_) fun i j => ?_
  · rw [Units.val_mul]
    exact key _ _ _ _ (norm_apply_le_locHeight g) (norm_apply_le_locHeight h) hg hh i j
  · rw [mul_inv_rev, Units.val_mul, mul_comm (locHeight g)]
    exact key _ _ _ _ (norm_inv_apply_le_locHeight h) (norm_inv_apply_le_locHeight g) hh hg i j

theorem locHeight_eq_one {g : GL (Fin n) E}
    (h₁ : ∀ i j, ‖(g : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1)
    (h₂ : ∀ i j, ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1) :
    locHeight g = 1 :=
  le_antisymm (locHeight_le le_rfl h₁ h₂) (one_le_locHeight g)

end Local

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open Reduction

theorem locHeight_eq_one_of_mem_integralGL {v : HeightOneSpectrum (𝓞 K)}
    {g : GL (Fin n) (v.adicCompletion K)}
    (hg : g ∈ GLnLocal.integralGL (v.adicCompletion K) n) : locHeight g = 1 := by
  rw [GLnLocal.mem_integralGL_iff] at hg
  simp only [GroundTheory.Global.mem_valuationInteger_iff] at hg
  exact locHeight_eq_one (fun i j => norm_le_one_of_mem v (hg.1 i j))
    fun i j => norm_le_one_of_mem v (hg.2 i j)

theorem finite_mulSupport_locHeight_finAt (g : AdelicGLn.AdelicGL K n) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => locHeight (finAt v g)).Finite := by
  have : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, locHeight (finAt v g) = 1 :=
    (AdelicGLn.eventually_mem_integralGL K n g).mono fun v hv =>
      locHeight_eq_one_of_mem_integralGL (g := finAt v g) hv
  exact Filter.eventually_cofinite.1 this

def height (g : AdelicGLn.AdelicGL K n) : ℝ :=
  (∏ w : InfinitePlace K, locHeight (infAt w g) ^ w.mult) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g)

theorem one_le_finprod_locHeight (g : AdelicGLn.AdelicGL K n) :
    1 ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g) :=
  finprod_induction (fun x : ℝ => 1 ≤ x) le_rfl (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy)
    fun _ => one_le_locHeight _

theorem one_le_prod_locHeight (g : AdelicGLn.AdelicGL K n) :
    1 ≤ ∏ w : InfinitePlace K, locHeight (infAt w g) ^ w.mult :=
  Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy)
    le_rfl fun _ _ => one_le_pow₀ (one_le_locHeight _)

theorem one_le_height (g : AdelicGLn.AdelicGL K n) : 1 ≤ height g :=
  one_le_mul_of_one_le_of_one_le (one_le_prod_locHeight g) (one_le_finprod_locHeight g)

theorem height_pos (g : AdelicGLn.AdelicGL K n) : 0 < height g :=
  lt_of_lt_of_le one_pos (one_le_height g)

theorem height_inv (g : AdelicGLn.AdelicGL K n) : height g⁻¹ = height g := by
  simp only [height, infAt_inv, finAt_inv, locHeight_inv]

theorem height_one : height (1 : AdelicGLn.AdelicGL K n) = 1 := by
  simp [height, locHeight_one]

variable (K n) in

def heightConst : ℝ := ∏ w : InfinitePlace K, (max 1 (n : ℝ)) ^ w.mult

theorem one_le_heightConst : 1 ≤ heightConst K n :=
  Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy)
    le_rfl fun _ _ => one_le_pow₀ (le_max_left _ _)

theorem height_mul_le (g h : AdelicGLn.AdelicGL K n) :
    height (g * h) ≤ heightConst K n * height g * height h := by
  classical
  set s := ((finite_mulSupport_locHeight_finAt g).union
    (finite_mulSupport_locHeight_finAt h)).union (finite_mulSupport_locHeight_finAt (g * h))
  have hfin : ∀ x : AdelicGLn.AdelicGL K n, x = g ∨ x = h ∨ x = g * h →
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v x) =
        ∏ v ∈ s.toFinset, locHeight (finAt v x) := by
    intro x hx
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    intro v hv
    simp only [Set.Finite.coe_toFinset, Set.mem_union]
    rcases hx with rfl | rfl | rfl
    · exact Or.inl (Or.inl hv)
    · exact Or.inl (Or.inr hv)
    · exact Or.inr hv
  have hf : ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v (g * h)) ≤
      (∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g)) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v h) := by
    rw [hfin _ (Or.inr (Or.inr rfl)), hfin _ (Or.inl rfl), hfin _ (Or.inr (Or.inl rfl)),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun v _ => (locHeight_pos _).le) fun v _ => ?_
    rw [finAt_mul]
    exact locHeight_mul_le_of_ultrametric _ _
  have hi : (∏ w : InfinitePlace K, locHeight (infAt w (g * h)) ^ w.mult) ≤
      heightConst K n * (∏ w : InfinitePlace K, locHeight (infAt w g) ^ w.mult) *
        ∏ w : InfinitePlace K, locHeight (infAt w h) ^ w.mult := by
    rw [heightConst, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun w _ => by have := locHeight_pos (infAt w (g * h)); positivity)
      fun w _ => ?_
    rw [← mul_pow, ← mul_pow, infAt_mul]
    exact pow_le_pow_left₀ (locHeight_pos _).le (locHeight_mul_le _ _) _
  unfold height
  calc (∏ w : InfinitePlace K, locHeight (infAt w (g * h)) ^ w.mult) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v (g * h))
      ≤ (heightConst K n * (∏ w : InfinitePlace K, locHeight (infAt w g) ^ w.mult) *
          ∏ w : InfinitePlace K, locHeight (infAt w h) ^ w.mult) *
        ((∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g)) *
          ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v h)) :=
        mul_le_mul hi hf (le_trans zero_le_one (one_le_finprod_locHeight _))
          (mul_nonneg (mul_nonneg (le_trans zero_le_one one_le_heightConst)
            (le_trans zero_le_one (one_le_prod_locHeight g)))
            (le_trans zero_le_one (one_le_prod_locHeight h)))
    _ = _ := by ring

theorem locHeight_infAt_eq_one_of_mem_maxCompact {k : AdelicGLn.AdelicGL K n}
    (hk : k ∈ maxCompact) (w : InfinitePlace K) : locHeight (infAt w k) = 1 := by
  have h1 : infAt w k ∈ archCompact w := hk.1 w
  have h2 : (infAt w k)⁻¹ ∈ archCompact w := inv_mem h1
  exact locHeight_eq_one (fun i j => norm_apply_le_one_of_mem_archCompact h1 i j)
    fun i j => norm_apply_le_one_of_mem_archCompact h2 i j

theorem locHeight_finAt_eq_one_of_mem_maxCompact {k : AdelicGLn.AdelicGL K n}
    (hk : k ∈ maxCompact) (v : HeightOneSpectrum (𝓞 K)) : locHeight (finAt v k) = 1 :=
  locHeight_eq_one_of_mem_integralGL (hk.2 v)

theorem height_eq_one_of_mem_maxCompact {k : AdelicGLn.AdelicGL K n} (hk : k ∈ maxCompact) :
    height k = 1 := by
  unfold height
  rw [Finset.prod_eq_one fun w _ => by
    rw [locHeight_infAt_eq_one_of_mem_maxCompact hk w, one_pow], one_mul]
  exact finprod_eq_one_of_forall_eq_one (locHeight_finAt_eq_one_of_mem_maxCompact hk)

end AutomorphicForm

end

end GroundTheory.Automorphic
