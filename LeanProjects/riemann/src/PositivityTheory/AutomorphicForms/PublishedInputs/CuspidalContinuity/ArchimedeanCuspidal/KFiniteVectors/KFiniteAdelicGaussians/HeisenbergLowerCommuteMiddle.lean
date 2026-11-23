import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace Ad3.K.GA.unipotentTranslateContinuity

variable {K : Type} [Field K] [NumberField K]

local notation "𝔞" => algebraMap K 𝔸[K]

theorem psi_add (a b : 𝔸[K]) :
    (adelicChar K (a + b) : ℂ) = (adelicChar K a : ℂ) * (adelicChar K b : ℂ) := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

theorem psi_rat (q : K) : (adelicChar K (𝔞 q) : ℂ) = 1 := by
  rw [adelicChar_algebraMap, Circle.coe_one]

theorem psi_zero : (adelicChar K 0 : ℂ) = 1 := by
  rw [AddChar.map_zero_eq_one, Circle.coe_one]

theorem norm_psi (a : 𝔸[K]) : ‖(adelicChar K a : ℂ)‖ = 1 := Circle.norm_coe _

theorem exists_psi_ne_one : ∃ b : 𝔸[K], (adelicChar K b : ℂ) ≠ 1 := by
  by_contra h
  push Not at h
  refine adelicChar_ne_one (K := K) (DFunLike.ext _ _ fun b => ?_)
  rw [AddChar.one_apply]
  ext
  simpa using h b

theorem psi_comb {A B C D : 𝔸[K]} (e : A + B = C + D) (w : ℂ) :
    (adelicChar K A : ℂ) * w * (adelicChar K B : ℂ) =
      (adelicChar K C : ℂ) * (w * (adelicChar K D : ℂ)) := by
  calc (adelicChar K A : ℂ) * w * (adelicChar K B : ℂ) = w * (adelicChar K (A + B) : ℂ) := by
        rw [psi_add]; ring
    _ = w * (adelicChar K (C + D) : ℂ) := by rw [e]
    _ = _ := by rw [psi_add]; ring

def splitAt {ι : Type*} [DecidableEq ι] (i : ι) : ι ≃ {j // j ≠ i} ⊕ Unit where
  toFun j := if h : j = i then Sum.inr () else Sum.inl ⟨j, h⟩
  invFun := Sum.elim Subtype.val fun _ => i
  left_inv j := by
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  right_inv p := by
    rcases p with ⟨j, hj⟩ | ⟨⟩
    · simp [hj]
    · simp

theorem setIntegral_eq_zero_of_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : (ι → 𝔸[K]) → ℂ} (hc : Continuous F) (i : ι) {r : K} (hr : r ≠ 0)
    (hF : ∀ y s, F (y + Pi.single i s) = (adelicChar K (𝔞 r * s) : ℂ) * F y) :
    ∫ y in vecDomain K ι, F y ∂vecMeasure K ι = 0 := by
  rw [FourierWhittaker.setIntegral_vecDomain_sum (splitAt i) hc]
  refine integral_eq_zero_of_ae (ae_of_all _ fun x => ?_)
  let G : (Unit → 𝔸[K]) → ℂ := fun y => F fun j => Sum.elim x y (splitAt i j)
  show ∫ y in vecDomain K Unit, G y ∂vecMeasure K Unit = 0
  have hvec : ∀ (y a : Unit → 𝔸[K]), (fun j => Sum.elim x (y + a) (splitAt i j)) =
      (fun j => Sum.elim x y (splitAt i j)) + Pi.single i (a ()) := by
    intro y a
    funext j
    by_cases h : j = i
    · subst h; simp [splitAt]
    · simp [splitAt, h]
  have hG : ∀ y a, G (y + a) = (adelicChar K (𝔞 r * a ()) : ℂ) * G y := by
    intro y a
    simp only [G, hvec, hF]
  have hper : ∀ ξ ∈ FourierWhittaker.vecLattice K Unit, ∀ y, G (ξ + y) = G y := by
    intro ξ hξ y
    obtain ⟨η, rfl⟩ := FourierWhittaker.mem_vecLattice.1 hξ
    rw [add_comm, hG]
    show (adelicChar K (𝔞 r * 𝔞 (η ())) : ℂ) * G y = G y
    rw [← map_mul, psi_rat, one_mul]
  obtain ⟨b, hb⟩ := exists_psi_ne_one (K := K)
  have h1 := FourierWhittaker.setIntegral_comp_add (fun _ => 𝔞 r⁻¹ * b) hper
  have hrb : 𝔞 r * (𝔞 r⁻¹ * b) = b := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hr, map_one, one_mul]
  simp only [hG, hrb] at h1
  rw [integral_const_mul] at h1
  have h2 : ((adelicChar K b : ℂ) - 1) * ∫ y in vecDomain K Unit, G y ∂vecMeasure K Unit = 0 := by
    rw [sub_mul, one_mul, h1, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hb)

theorem setIntegral_eq_of_shift {ι : Type*} [Fintype ι] [DecidableEq ι] {F : (ι → 𝔸[K]) → ℂ}
    (hF : ∀ y i s, F (y + Pi.single i s) = F y) :
    ∫ y in vecDomain K ι, F y ∂vecMeasure K ι = F 0 := by
  have key : ∀ y, F y = F 0 := by
    intro y
    have : ∀ S : Finset ι, F (∑ i ∈ S, Pi.single i (y i)) = F 0 := by
      intro S
      refine Finset.induction_on S (by simp) ?_
      intro a S ha ih
      rw [Finset.sum_insert ha, add_comm, hF, ih]
    rw [← this Finset.univ, Finset.univ_sum_single]
  rw [setIntegral_congr_fun FourierWhittaker.measurableSet_vecDomain (fun y _ => key y),
    setIntegral_const, measureReal_def, FourierWhittaker.vecMeasure_vecDomain, ENNReal.toReal_one,
    one_smul]

theorem setIntegral_tsum_of_le {ι : Type*} [Fintype ι] {α : Type*} [Countable α]
    (F : α → (ι → 𝔸[K]) → ℂ) (hc : ∀ q, Continuous (F q)) (b : α → ℝ) (hb : Summable b)
    (hle : ∀ q, ∀ y ∈ vecDomain K ι, ‖F q y‖ ≤ b q) :
    ∫ y in vecDomain K ι, ∑' q, F q y ∂vecMeasure K ι =
      ∑' q, ∫ y in vecDomain K ι, F q y ∂vecMeasure K ι := by
  have : IsFiniteMeasure ((vecMeasure K ι).restrict (vecDomain K ι)) := ⟨by
    rw [Measure.restrict_apply_univ, FourierWhittaker.vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  have hint : ∀ q, Integrable (F q) ((vecMeasure K ι).restrict (vecDomain K ι)) := fun q =>
    Integrable.mono' (integrable_const (b q)) (hc q).aestronglyMeasurable
      ((ae_restrict_iff' FourierWhittaker.measurableSet_vecDomain).2 (ae_of_all _ (hle q)))
  have hnorm : ∀ q, ∫ y in vecDomain K ι, ‖F q y‖ ∂vecMeasure K ι ≤ b q := by
    intro q
    calc ∫ y in vecDomain K ι, ‖F q y‖ ∂vecMeasure K ι
        ≤ ∫ _ in vecDomain K ι, b q ∂vecMeasure K ι :=
          setIntegral_mono_on (hint q).norm (integrable_const _)
            FourierWhittaker.measurableSet_vecDomain (hle q)
      _ = b q := by
          rw [setIntegral_const, measureReal_def, FourierWhittaker.vecMeasure_vecDomain,
            ENNReal.toReal_one, one_smul]
  exact (integral_tsum_of_summable_integral_norm hint
    (Summable.of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _) hnorm hb)).symm

instance countable_field : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable

instance countable_GL2 : Countable (GL (Fin 2) K) := by
  have : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  exact Function.Injective.countable (f := fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K))
    fun a b h => Units.ext h

instance countable_NQ : Countable (NQ K) := Quotient.countable

theorem continuous_uni {X : Type*} [TopologicalSpace X] {a b c : X → 𝔸[K]} (ha : Continuous a)
    (hb : Continuous b) (hc : Continuous c) : Continuous fun x => (uni (a x) (b x) (c x) : G3K K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x => (!![1, a x, b x; 0, 1, c x; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[K])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x =>
      (!![1, -a x, a x * c x - b x; 0, 1, -c x; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[K])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_lowM {X : Type*} [TopologicalSpace X] {a : X → 𝔸[K]} (ha : Continuous a) :
    Continuous fun x => lowM (a x) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x => (!![1, 0, 0; a x, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[K])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x => (!![1, 0, 0; -a x, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) 𝔸[K])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem val_uni (x y z : 𝔸[K]) :
    ((uni x y z : G3K K) : Matrix (Fin 3) (Fin 3) 𝔸[K]) = !![1, x, y; 0, 1, z; 0, 0, 1] := rfl

theorem val_lowM (c : 𝔸[K]) :
    ((lowM c : G3K K) : Matrix (Fin 3) (Fin 3) 𝔸[K]) = !![1, 0, 0; c, 1, 0; 0, 0, 1] := rfl

theorem diagonal_embed_GL2_matrix (γ : GL (Fin 2) K) :
    ((diaK (e1 K γ) : G3K K) : Matrix (Fin 3) (Fin 3) 𝔸[K]) =
      !![𝔞 (γ.val 0 0), 𝔞 (γ.val 0 1), 0; 𝔞 (γ.val 1 0), 𝔞 (γ.val 1 1), 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e1, b1M]

theorem val_dia_e2sw (γ : GL (Fin 2) K) :
    ((diaK (e2 K γ * sw K) : G3K K) : Matrix (Fin 3) (Fin 3) 𝔸[K]) =
      !![0, 1, 0; 𝔞 (γ.val 0 0), 0, 𝔞 (γ.val 0 1); 𝔞 (γ.val 1 0), 0, 𝔞 (γ.val 1 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e2, b2M, sw, Matrix.mul_apply, Fin.sum_univ_three]

theorem lowM_zero : lowM (0 : 𝔸[K]) = 1 := by
  apply Units.ext
  rw [val_lowM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem uni_zero : (uni 0 0 0 : G3K K) = 1 := by
  apply Units.ext
  rw [val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem inv_rel (γ : GL (Fin 2) K) (i j : Fin 2) :
    𝔞 ((γ⁻¹).val i 0) * 𝔞 (γ.val 0 j) + 𝔞 ((γ⁻¹).val i 1) * 𝔞 (γ.val 1 j) =
      if i = j then 1 else 0 := by
  have := congrArg (fun X : Matrix (Fin 2) (Fin 2) K => 𝔞 (X i j)) (Units.inv_mul γ)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, Matrix.one_apply] at this
  rw [this]
  split_ifs <;> simp

theorem heisenberg_lower_commute_corner (c x t s : 𝔸[K]) :
    lowM c * uni 0 x (t + s) = uni 0 0 s * (lowM c * uni 0 x t) := by
  apply Units.ext
  simp only [Units.val_mul, val_lowM, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem heisenberg_lower_commute_middle (c x t s : 𝔸[K]) :
    lowM c * uni 0 (x + s) t = uni 0 s (c * s) * (lowM c * uni 0 x t) := by
  apply Units.ext
  simp only [Units.val_mul, val_lowM, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem hH_c (c x t s : 𝔸[K]) :
    lowM (c + s) * uni 0 x t = lowM s * (lowM c * uni 0 x t) := by
  apply Units.ext
  simp only [Units.val_mul, val_lowM, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem hY_a (a b s : 𝔸[K]) : uni 0 (a + s) b = uni 0 s 0 * uni 0 a b := by
  apply Units.ext
  simp only [Units.val_mul, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem hY_b (a b s : 𝔸[K]) : uni 0 a (b + s) = uni 0 0 s * uni 0 a b := by
  apply Units.ext
  simp only [Units.val_mul, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem GL2_embed_commute_corner (γ : GL (Fin 2) K) (s : 𝔸[K]) :
    diaK (e1 K γ) * uni 0 0 s = uni 0 (𝔞 (γ.val 0 1) * s) (𝔞 (γ.val 1 1) * s) * diaK (e1 K γ) := by
  apply Units.ext
  simp only [Units.val_mul, diagonal_embed_GL2_matrix, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem GL2_embed_commute_middle (γ : GL (Fin 2) K) (s w : 𝔸[K]) :
    diaK (e1 K γ) * uni 0 s w = uni 0 (𝔞 (γ.val 0 0) * s + 𝔞 (γ.val 0 1) * w)
      (𝔞 (γ.val 1 0) * s + 𝔞 (γ.val 1 1) * w) * diaK (e1 K γ) := by
  apply Units.ext
  simp only [Units.val_mul, diagonal_embed_GL2_matrix, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem det_ne_zero2 (γ : GL (Fin 2) K) : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 ≠ 0 := by
  have h := congrArg Matrix.det (Units.mul_inv γ)
  rw [Matrix.det_mul, Matrix.det_one, Matrix.det_fin_two] at h
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

theorem dU_c (γ : GL (Fin 2) K) (h11 : γ.val 1 1 = 0) (s : 𝔸[K]) :
    diaK (e1 K γ) * lowM s = uni (𝔞 (γ.val 0 1 / γ.val 1 0) * s) 0 0 * diaK (e1 K γ) := by
  have h10 : γ.val 1 0 ≠ 0 := by
    intro h; have := det_ne_zero2 γ; rw [h, h11] at this; simp at this
  have hq : 𝔞 (γ.val 0 1 / γ.val 1 0) * 𝔞 (γ.val 1 0) = 𝔞 (γ.val 0 1) := by
    rw [← map_mul, div_mul_cancel₀ _ h10]
  generalize 𝔞 (γ.val 0 1 / γ.val 1 0) = A at hq ⊢
  apply Units.ext
  simp only [Units.val_mul, diagonal_embed_GL2_matrix, val_uni, val_lowM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h11] <;>
    first | linear_combination s * hq | linear_combination -s * hq | ring1

theorem GL2_swap_embed_commute_corner (γ : GL (Fin 2) K) (s : 𝔸[K]) :
    diaK (e2 K γ * sw K) * uni 0 0 s =
      uni (𝔞 ((γ⁻¹).val 1 0) * s) (𝔞 ((γ⁻¹).val 1 1) * s) 0 * diaK (e2 K γ * sw K) := by
  have r0 := inv_rel γ 1 0
  have r1 := inv_rel γ 1 1
  simp only [Fin.isValue, one_ne_zero, if_false, if_true] at r0 r1
  generalize ((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = N at r0 r1 ⊢
  apply Units.ext
  simp only [Units.val_mul, val_dia_e2sw, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | linear_combination s * r0 | linear_combination -s * r0 |
      linear_combination s * r1 | linear_combination -s * r1 | ring1

theorem dV_c (γ : GL (Fin 2) K) (s : 𝔸[K]) :
    diaK (e2 K γ * sw K) * lowM s =
      uni (𝔞 ((γ⁻¹).val 0 0) * s) (𝔞 ((γ⁻¹).val 0 1) * s) 0 * diaK (e2 K γ * sw K) := by
  have r0 := inv_rel γ 0 0
  have r1 := inv_rel γ 0 1
  simp only [Fin.isValue, zero_ne_one, if_false, if_true] at r0 r1
  generalize ((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = N at r0 r1 ⊢
  apply Units.ext
  simp only [Units.val_mul, val_dia_e2sw, val_uni, val_lowM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | linear_combination s * r0 | linear_combination -s * r0 |
      linear_combination s * r1 | linear_combination -s * r1 | ring1

theorem GL2_swap_embed_commute_middle (γ : GL (Fin 2) K) (h10 : γ.val 1 0 = 0) (s w : 𝔸[K]) :
    diaK (e2 K γ * sw K) * uni 0 s w =
      uni 0 (𝔞 (γ.val 1 1)⁻¹ * w) (𝔞 (γ.val 0 0 / γ.val 1 1) * s) * diaK (e2 K γ * sw K) := by
  have h11 : γ.val 1 1 ≠ 0 := by
    intro h; have := det_ne_zero2 γ; rw [h, h10] at this; simp at this
  have q1 : 𝔞 (γ.val 1 1)⁻¹ * 𝔞 (γ.val 1 1) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ h11, map_one]
  have q2 : 𝔞 (γ.val 0 0 / γ.val 1 1) * 𝔞 (γ.val 1 1) = 𝔞 (γ.val 0 0) := by
    rw [← map_mul, div_mul_cancel₀ _ h11]
  generalize 𝔞 (γ.val 1 1)⁻¹ = A1 at q1 ⊢
  generalize 𝔞 (γ.val 0 0 / γ.val 1 1) = A2 at q2 ⊢
  apply Units.ext
  simp only [Units.val_mul, val_dia_e2sw, val_uni]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h10] <;>
    first | linear_combination w * q1 | linear_combination -w * q1 |
      linear_combination s * q2 | linear_combination -s * q2 | ring1

end Ad3.K.GA.unipotentTranslateContinuity
