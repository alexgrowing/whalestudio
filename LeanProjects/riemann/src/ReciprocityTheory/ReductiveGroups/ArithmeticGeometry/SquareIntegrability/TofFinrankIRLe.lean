import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofSpanCondition

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem tof_shell_term (d k : ℕ) (hd : 2 ≤ d) :
    (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) ≤
      (3 * (d : ℝ)) ^ d * (Real.exp (-1) * Real.exp (1 - Real.pi / 2) ^ k) := by
  have hpi := Real.pi_gt_three
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hE : Real.exp (-1) * Real.exp (1 - Real.pi / 2) ^ k =
      Real.exp (-1 + k * (1 - Real.pi / 2)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
  rw [hE]
  have key : (3 * ((k : ℝ) + 1)) ^ d ≤
      (3 * (d : ℝ)) ^ d * Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · subst hk0
      have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have hdd : (4 : ℝ) ≤ (d : ℝ) ^ d := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ (d : ℝ) ^ 2 := by gcongr
          _ ≤ (d : ℝ) ^ d := pow_le_pow_right₀ (by linarith) hd
      have hQ : Real.pi / 2 * ((0 : ℕ) : ℝ) ^ 2 + (-1 + ((0 : ℕ) : ℝ) * (1 - Real.pi / 2)) = -1 := by
        simp
      rw [hQ, Real.exp_neg]
      have h1 : (1 : ℝ) ≤ (d : ℝ) ^ d * (Real.exp 1)⁻¹ := by
        rw [le_mul_inv_iff₀ (Real.exp_pos 1)]
        linarith
      calc (3 * (((0 : ℕ) : ℝ) + 1)) ^ d = 3 ^ d * 1 := by simp
        _ ≤ 3 ^ d * ((d : ℝ) ^ d * (Real.exp 1)⁻¹) := by gcongr
        _ = (3 * (d : ℝ)) ^ d * (Real.exp 1)⁻¹ := by rw [mul_pow]; ring
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      by_cases hkd : k + 1 ≤ d
      · have hkd' : (k : ℝ) + 1 ≤ d := by exact_mod_cast hkd
        have h1 : (3 * ((k : ℝ) + 1)) ^ d ≤ (3 * (d : ℝ)) ^ d :=
          pow_le_pow_left₀ (by positivity) (by linarith) d
        have h2 : 0 ≤ Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2)) := by
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ Real.pi / 2)
            (by linarith : (0 : ℝ) ≤ k)) (by linarith : (0 : ℝ) ≤ k - 1)]
        calc (3 * ((k : ℝ) + 1)) ^ d ≤ (3 * (d : ℝ)) ^ d := h1
          _ ≤ _ := le_mul_of_one_le_right (by positivity) (Real.one_le_exp h2)
      · have hdk : (d : ℝ) ≤ k := by exact_mod_cast (by omega : d ≤ k)
        have hk2 : (2 : ℝ) ≤ k := le_trans hd' hdk
        have h1 : ((k : ℝ) + 1) ^ d ≤ Real.exp ((k : ℝ) * k) := by
          calc ((k : ℝ) + 1) ^ d ≤ (Real.exp k) ^ d :=
                pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (k : ℝ)]) d
            _ = Real.exp (d * k) := by rw [← Real.exp_nat_mul]
            _ ≤ Real.exp (k * k) := Real.exp_le_exp.mpr (by nlinarith)
        have h2 : (k : ℝ) * k ≤ Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2)) := by
          have hkk : 2 ≤ (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
          have hpp : (1 : ℝ) / 2 ≤ Real.pi / 2 - 1 := by linarith
          nlinarith [mul_le_mul hpp hkk (by norm_num) (by linarith)]
        have h3 : (1 : ℝ) ≤ (d : ℝ) ^ d := one_le_pow₀ (by linarith)
        calc (3 * ((k : ℝ) + 1)) ^ d = 3 ^ d * ((k : ℝ) + 1) ^ d := mul_pow _ _ _
          _ ≤ 3 ^ d * Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) := by
            gcongr
            exact h1.trans (Real.exp_le_exp.mpr h2)
          _ ≤ 3 ^ d * ((d : ℝ) ^ d *
              Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2)))) := by
            gcongr
            exact le_mul_of_one_le_left (Real.exp_pos _).le h3
          _ = _ := by rw [mul_pow]; ring
  have hexp : Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) *
      Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) = Real.exp (-1 + k * (1 - Real.pi / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc _ ≤ (3 * (d : ℝ)) ^ d * Real.exp (Real.pi / 2 * (k : ℝ) ^ 2 + (-1 + k * (1 - Real.pi / 2))) *
        Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, hexp]

theorem tof_shell_sum (d K : ℕ) (hd : 2 ≤ d) :
    ∑ k ∈ Finset.range K, (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) ≤
      2 * (3 * (d : ℝ)) ^ d := by
  set r := Real.exp (1 - Real.pi / 2) with hr
  have hpi := Real.pi_gt_three
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 2 / 3 := by
    have h := Real.add_one_le_exp (Real.pi / 2 - 1)
    have hrr : r * Real.exp (Real.pi / 2 - 1) = 1 := by
      rw [hr, ← Real.exp_add]
      simp
    nlinarith
  have he1 : Real.exp (-1) ≤ 1 / 2 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    have hrr : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]
      simp
    have := Real.exp_pos (-1)
    nlinarith
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range K, r ^ k := Finset.sum_nonneg (fun k _ => pow_nonneg hr0.le k)
  have hS : ∑ k ∈ Finset.range K, r ^ k ≤ 3 := by
    have h := geom_sum_mul r K
    have : 0 ≤ r ^ K := by positivity
    nlinarith
  have hd0 : (0 : ℝ) ≤ (3 * (d : ℝ)) ^ d := by positivity
  calc ∑ k ∈ Finset.range K, (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2)
      ≤ ∑ k ∈ Finset.range K, (3 * (d : ℝ)) ^ d * (Real.exp (-1) * r ^ k) :=
        Finset.sum_le_sum (fun k _ => tof_shell_term d k hd)
    _ = (3 * (d : ℝ)) ^ d * Real.exp (-1) * ∑ k ∈ Finset.range K, r ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring
    _ ≤ (3 * (d : ℝ)) ^ d * (1 / 2) * 3 := by gcongr
    _ ≤ 2 * (3 * (d : ℝ)) ^ d := by nlinarith

theorem tof_uMap_sep [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) {x x' : Vsp X.dim} (hx : x ∈ X.L) (hx' : x' ∈ X.L)
    (hne : uMap I x ≠ uMap I x') : 1 ≤ ‖uMap I x - uMap I x'‖ := by
  have hsub : uMap I x - uMap I x' = uMap I (x - x') := (map_sub (uMap I) x x').symm
  have hne' : uMap I (x - x') ≠ 0 := by
    rw [← hsub]
    exact sub_ne_zero.mpr hne
  have hb := hI.sep (x - x') (X.L.sub_mem hx hx') (uMap I (x - x')) (isU_uMap I (x - x')) hne'
  have h1 : (1 : ℝ) ≤ ‖uMap I (x - x')‖ ^ 2 := le_trans P.C2 hb
  rw [hsub]
  by_contra hlt
  have hlt' : ‖uMap I (x - x')‖ < 1 := lt_of_not_ge hlt
  have h0 := norm_nonneg (uMap I (x - x'))
  nlinarith

theorem tof_finrank_IR_le [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) : Module.finrank ℝ (IR I) ≤ dstar (E := E) P.m := by
  obtain ⟨ρ, hρ, h⟩ := hI.rank
  rw [h]
  unfold dstar
  exact Nat.mul_le_mul_left _ hρ

theorem tof_two_le_dstar {X : PT E} {DF : ℕ} (P : Par X DF) : 2 ≤ dstar (E := E) P.m := by
  have h1 : 1 ≤ PT.f E := le_trans (Nat.one_le_pow _ _ P.hm1) P.hmf
  have h2 := P.hm1
  unfold dstar
  calc 2 = 2 * 1 * 1 := by norm_num
    _ ≤ 2 * PT.f E * P.m := by gcongr

theorem tof_sep_sum [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I)
    (F : Finset (Vsp X.dim)) (hF : ∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) :
    ∑ y ∈ F, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) ≤
      2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m := by
  classical
  set d := dstar (E := E) P.m with hd
  have hd2 : 2 ≤ d := tof_two_le_dstar P
  have hDd : Module.finrank ℝ (IR I) ≤ d := tof_finrank_IR_le P hI
  have hyR : ∀ y ∈ F, y ∈ IR I := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hF y hy
    exact (IR I).starProjection_apply_mem _
  let e := (stdOrthonormalBasis ℝ (IR I)).repr
  let g : Vsp X.dim → EuclideanSpace ℝ (Fin (Module.finrank ℝ (IR I))) := fun y =>
    e ⟨(IR I).starProjection (y - u), (IR I).starProjection_apply_mem _⟩
  have hproj : ∀ y ∈ F, (IR I).starProjection (y - u) = y - u := fun y hy =>
    (Submodule.starProjection_eq_self_iff).mpr ((IR I).sub_mem (hyR y hy) hu)
  have hgn : ∀ y ∈ F, ‖g y‖ = ‖u - y‖ := by
    intro y hy
    simp only [g, LinearIsometryEquiv.norm_map, Submodule.coe_norm, hproj y hy]
    rw [norm_sub_rev]
  have hgd : ∀ y ∈ F, ∀ y' ∈ F, dist (g y) (g y') = ‖y - y'‖ := by
    intro y hy y' hy'
    rw [dist_eq_norm]
    simp only [g, ← map_sub, LinearIsometryEquiv.norm_map]
    simp only [Submodule.coe_norm, Submodule.coe_sub, hproj y hy, hproj y' hy']
    congr 1
    abel
  have hsep : ∀ y ∈ F, ∀ y' ∈ F, y ≠ y' → 1 ≤ ‖y - y'‖ := by
    intro y hy y' hy' hne
    obtain ⟨x, hx, rfl⟩ := hF y hy
    obtain ⟨x', hx', rfl⟩ := hF y' hy'
    exact tof_uMap_sep P hI hx hx' hne
  set K := (F.sup fun y => ⌊‖u - y‖⌋₊) + 1 with hK
  have hmaps : ∀ y ∈ F, ⌊‖u - y‖⌋₊ ∈ Finset.range K := by
    intro y hy
    rw [Finset.mem_range, hK]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun y => ⌊‖u - y‖⌋₊) hy)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (tof_shell_sum d K hd2)
  set Fk := F.filter (fun y => ⌊‖u - y‖⌋₊ = k) with hFk
  have hFkF : ∀ y ∈ Fk, y ∈ F := fun y hy => (Finset.mem_filter.mp hy).1
  have hterm : ∀ y ∈ Fk, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) ≤
      Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
    intro y hy
    have hk : ⌊‖u - y‖⌋₊ = k := (Finset.mem_filter.mp hy).2
    have hle : (k : ℝ) ≤ ‖u - y‖ := by
      rw [← hk]
      exact Nat.floor_le (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have : (k : ℝ) ^ 2 ≤ ‖u - y‖ ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hle 2
    nlinarith [Real.pi_pos]
  have hinj : Set.InjOn g Fk := by
    intro y hy y' hy' hgg
    by_contra hne
    have h1 := hsep y (hFkF y hy) y' (hFkF y' hy') hne
    have h2 := hgd y (hFkF y hy) y' (hFkF y' hy')
    rw [hgg, dist_self] at h2
    linarith
  have hcard : (Fk.card : ℝ) ≤ (3 * ((k : ℝ) + 1)) ^ Module.finrank ℝ (IR I) := by
    rw [← Finset.card_image_of_injOn hinj]
    have hpk := hP (Module.finrank ℝ (IR I)) (Fk.image g) 1 ((k : ℝ) + 1) one_pos
      (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      (by
        intro p hp
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
        rw [hgn y (hFkF y hy)]
        have hk : ⌊‖u - y‖⌋₊ = k := (Finset.mem_filter.mp hy).2
        rw [← hk]
        exact (Nat.lt_floor_add_one _).le)
      (by
        intro p hp p' hp' hne
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hp'
        rw [hgd y (hFkF y hy) y' (hFkF y' hy')]
        exact hsep y (hFkF y hy) y' (hFkF y' hy') (fun h => hne (by rw [h])))
    simpa using hpk
  calc ∑ y ∈ Fk, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2)
      ≤ ∑ y ∈ Fk, Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := Finset.sum_le_sum hterm
    _ = (Fk.card : ℝ) * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * ((k : ℝ) + 1)) ^ Module.finrank ℝ (IR I) * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
        gcongr
    _ ≤ (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) := by
        gcongr
        · have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith

end

end ReciprocityTheory.ChartRestriction.G.I2
