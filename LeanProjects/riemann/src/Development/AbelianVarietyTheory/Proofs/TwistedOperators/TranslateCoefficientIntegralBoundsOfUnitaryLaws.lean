import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.IntBd

variable {m : ℕ} {ε : Fin m → Bool}

theorem isUnit_of_mem {x : Mat m} (hx : x ∈ UJset ε) : IsUnit x := by
  have hx' : xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε := hx
  have h : (Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε) * x = 1 := by
    calc (Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε) * x = Formalism.REAL.Jm ε * (xᴴ * Formalism.REAL.Jm ε * x) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hx', Formalism.REAL.Jm_mul_self]
  exact (Matrix.isUnit_iff_isUnit_det x).2 (Matrix.isUnit_det_of_left_inverse h)

theorem exists_umat {x : Mat m} (hx : x ∈ UJset ε) : ∃ u : Formalism.REAL.UJ ε, umat u = x :=
  ⟨⟨(isUnit_of_mem hx).unit, hx⟩, rfl⟩

theorem mul_mem {x y : Mat m} (hx : x ∈ UJset ε) (hy : y ∈ UJset ε) : x * y ∈ UJset ε := by
  have hx' : xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε := hx
  have hy' : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε := hy
  show (x * y)ᴴ * Formalism.REAL.Jm ε * (x * y) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul]
  calc yᴴ * xᴴ * Formalism.REAL.Jm ε * (x * y) = yᴴ * (xᴴ * Formalism.REAL.Jm ε * x) * y := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hx', hy']

theorem inv_facts {x : Mat m} (hx : x ∈ UJset ε) :
    x⁻¹ ∈ UJset ε ∧ x * x⁻¹ = 1 ∧ x⁻¹ * x = 1 ∧ x⁻¹⁻¹ = x := by
  have hd : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det x).1 (isUnit_of_mem hx)
  refine ⟨?_, Matrix.mul_nonsing_inv _ hd, Matrix.nonsing_inv_mul _ hd, Matrix.nonsing_inv_nonsing_inv _ hd⟩
  obtain ⟨u, rfl⟩ := exists_umat hx
  have hi : (umat u)⁻¹ = umat u⁻¹ := by simp [umat, Matrix.coe_units_inv]
  rw [hi]
  exact (u⁻¹).2

theorem hsn_nonneg (x : Mat m) : 0 ≤ hsn x := Real.sqrt_nonneg _

theorem hsn_pos (hm : 0 < m) {x : Mat m} (hx : x ∈ UJset ε) : 0 < hsn x := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hne : x ≠ 0 := (isUnit_of_mem hx).ne_zero
  obtain ⟨i, j, hij⟩ : ∃ i j, x i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Matrix.ext h)
  have h1 : ‖x i j‖ ^ 2 ≤ ∑ b, ‖x i b‖ ^ 2 :=
    Finset.single_le_sum (f := fun b => ‖x i b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ b, ‖x i b‖ ^ 2 ≤ ∑ a, ∑ b, ‖x a b‖ ^ 2 :=
    Finset.single_le_sum (f := fun a => ∑ b, ‖x a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  have h0 : 0 < ‖x i j‖ ^ 2 := pow_pos (norm_pos_iff.2 hij) 2
  unfold hsn
  exact Real.sqrt_pos.2 (by linarith)

theorem coef_conj {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Mat m → (H →L[ℂ] H)}
    (hπ : IsURepOn (UJset ε) π) {g₀ g : Mat m} (hg₀ : g₀ ∈ UJset ε) (hg : g ∈ UJset ε) (v : H) :
    ⟪π g₀ v, π g (π g₀ v)⟫_ℂ = ⟪v, π (g₀⁻¹ * g * g₀) v⟫_ℂ := by
  obtain ⟨hi, hr, hl, -⟩ := inv_facts hg₀
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hπ
  have hw : ∀ w, π g₀ (π g₀⁻¹ w) = w := fun w => by
    rw [← ContinuousLinearMap.comp_apply, ← hmul _ hg₀ _ hi, hr, h1]; rfl
  let L : H →ₗᵢ[ℂ] H := ⟨(π g₀ : H →ₗ[ℂ] H), fun x => hiso g₀ hg₀ x⟩
  have hL : ∀ x y, ⟪π g₀ x, π g₀ y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y => L.inner_map_map x y
  rw [hmul _ (mul_mem hi hg) _ hg₀, hmul _ hi _ hg]
  conv_lhs => rw [← hw (π g (π g₀ v))]
  rw [hL]; rfl

theorem rpow_neg_anti {x y k : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hk : 0 ≤ k) : y ^ (-k) ≤ x ^ (-k) := by
  rw [Real.rpow_neg (hx.le.trans hxy), Real.rpow_neg hx.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hx k) (Real.rpow_le_rpow hx.le hxy hk)

theorem decay_real {a y G k k2 : ℝ} (ha : 0 < a) (hy : 0 < y) (hG : 0 < G) (hya : y ≤ G ^ 2 * a) (hk : 0 ≤ k)
    (hk2 : k2 = 2 * k) : a ^ (-k) ≤ G ^ k2 * y ^ (-k) := by
  have hyG : y / G ^ 2 ≤ a := by rw [div_le_iff₀ (by positivity)]; linarith [mul_comm (G ^ 2) a]
  calc a ^ (-k) ≤ (y / G ^ 2) ^ (-k) := rpow_neg_anti (by positivity) hyG hk
    _ = (G ^ 2) ^ k * y ^ (-k) := by
      rw [div_eq_mul_inv, Real.mul_rpow hy.le (by positivity), Real.inv_rpow (by positivity),
        Real.rpow_neg (by positivity) (x := G ^ 2), inv_inv, mul_comm]
    _ = G ^ k2 * y ^ (-k) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hG.le, hk2]

theorem real_bound (n : ℕ) {x c s β : ℝ} (hc : 1 ≤ c) (hxc : c ≤ x) (hs : 0 < s) (hβ : 0 < β) (hsx : s ≤ β * x)
    (hβ2 : β ^ 2 ≤ (n : ℝ) + 1 + 2 * c ^ 2) :
    x ^ (-(40 * ((n : ℝ) + 1) ^ 2)) ≤
      (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * c ^ (-(2 * (n : ℝ) + 7)) * s ^ (-(4 * (n : ℝ) ^ 2 + 1)) := by
  set A : ℝ := 4 * (n : ℝ) ^ 2 + 1 with hA
  set R : ℝ := 40 * ((n : ℝ) + 1) ^ 2 - A with hR
  have hc0 : 0 < c := by linarith
  have hx0 : 0 < x := by linarith
  have hA0 : 0 ≤ A := by positivity
  have hR0 : 0 ≤ R := by rw [hR, hA]; nlinarith [sq_nonneg (n : ℝ)]
  have hsplit : x ^ (-(40 * ((n : ℝ) + 1) ^ 2)) = x ^ (-A) * x ^ (-R) := by
    rw [← Real.rpow_add hx0]; congr 1; rw [hR]; ring
  have h1 : x ^ (-A) ≤ s ^ (-A) * β ^ A := by
    have hsb : s / β ≤ x := by rw [div_le_iff₀ hβ]; linarith [mul_comm β x]
    calc x ^ (-A) ≤ (s / β) ^ (-A) := rpow_neg_anti (div_pos hs hβ) hsb hA0
      _ = s ^ (-A) * β ^ A := by
        rw [Real.div_rpow hs.le hβ.le, Real.rpow_neg hβ.le, div_inv_eq_mul]
  have h2 : x ^ (-R) ≤ c ^ (-R) := rpow_neg_anti hc0 hxc hR0
  have h3 : β ^ A ≤ (3 * ((n : ℝ) + 1)) ^ (A / 2) * c ^ A := by
    have e1 : β ^ A = (β ^ 2) ^ (A / 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hβ.le]; congr 1; ring
    have e2 : c ^ A = (c ^ 2) ^ (A / 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hc0.le]; congr 1; ring
    rw [e1, e2, ← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    have : 1 ≤ c ^ 2 := by nlinarith
    nlinarith
  have h4 : c ^ A * c ^ (-R) ≤ c ^ (-(2 * (n : ℝ) + 7)) := by
    rw [← Real.rpow_add hc0]
    apply Real.rpow_le_rpow_of_exponent_le hc
    rw [hR, hA]; nlinarith [sq_nonneg (n : ℝ)]
  have hsA : 0 ≤ s ^ (-A) := by positivity
  calc x ^ (-(40 * ((n : ℝ) + 1) ^ 2)) = x ^ (-A) * x ^ (-R) := hsplit
    _ ≤ (s ^ (-A) * β ^ A) * c ^ (-R) := by gcongr
    _ ≤ (s ^ (-A) * ((3 * ((n : ℝ) + 1)) ^ (A / 2) * c ^ A)) * c ^ (-R) := by gcongr
    _ = (3 * ((n : ℝ) + 1)) ^ (A / 2) * (c ^ A * c ^ (-R)) * s ^ (-A) := by ring
    _ ≤ (3 * ((n : ℝ) + 1)) ^ (A / 2) * c ^ (-(2 * (n : ℝ) + 7)) * s ^ (-A) := by gcongr

theorem const_bound (n : ℕ) {C₀ B G : ℝ} (hC₀ : 0 < C₀) (hB : 1 ≤ B) (hG1 : 1 ≤ G)
    (hG : G ≤ (8 * ((n : ℝ) + 1) * B) ^ (C₀ * ((n : ℝ) + 1))) :
    Real.exp (100 * ((n : ℝ) + 1) ^ 3) * G ^ (80 * ((n : ℝ) + 1) ^ 2) * (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) *
      Real.exp (10 * (n : ℝ) ^ 2) ≤ big (200 + 80 * C₀) n B := by
  unfold big
  set m : ℝ := (n : ℝ) + 1 with hmdef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : 1 ≤ m := by rw [hmdef]; linarith
  set L := Real.log (8 * m * B) with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  have ha0 : 0 ≤ Real.log G := Real.log_nonneg hG1
  have haL : Real.log G ≤ C₀ * m * L := by
    calc Real.log G ≤ Real.log ((8 * m * B) ^ (C₀ * m)) := Real.log_le_log (by linarith) hG
      _ = C₀ * m * L := by rw [Real.log_rpow (by positivity)]
  have h3L : Real.log (3 * m) ≤ L := Real.log_le_log (by positivity) (by nlinarith)
  have h30 : 0 ≤ Real.log (3 * m) := Real.log_nonneg (by linarith)
  rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < G), Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 3 * m),
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hm3 : m ^ 3 ≤ m ^ 4 := pow_le_pow_right₀ hm (by norm_num)
  have hm2 : m ^ 2 ≤ m ^ 4 := pow_le_pow_right₀ hm (by norm_num)
  have hm4L : m ^ 4 ≤ m ^ 4 * L := le_mul_of_one_le_right (by positivity) hL
  have t2 : Real.log G * (80 * m ^ 2) ≤ C₀ * m * L * (80 * m ^ 2) := mul_le_mul_of_nonneg_right haL (by positivity)
  have t2' : C₀ * L * m ^ 3 ≤ C₀ * L * m ^ 4 := mul_le_mul_of_nonneg_left hm3 (by positivity)
  have hA : (4 * (n : ℝ) ^ 2 + 1) / 2 ≤ 2 * m ^ 2 := by rw [hmdef]; nlinarith
  have t3 : Real.log (3 * m) * ((4 * (n : ℝ) ^ 2 + 1) / 2) ≤ L * (2 * m ^ 2) :=
    mul_le_mul h3L hA (by positivity) (by linarith)
  have t3' : L * m ^ 2 ≤ L * m ^ 4 := mul_le_mul_of_nonneg_left hm2 (by linarith)
  have hn2 : (n : ℝ) ^ 2 ≤ m ^ 2 := by rw [hmdef]; nlinarith
  nlinarith

end GlobalTheory.SepReal.IntBd

namespace GlobalTheory.SepReal

open GlobalTheory.SepReal.IntBd in

theorem intBounds_of (hE : EmbLaws) (hBo : Boost) (hP : PowInt) (hD : DecPow) : IntBounds := by
  intro C₀ hC₀
  refine ⟨200 + 80 * C₀, by positivity, ?_⟩
  intro n e ε lam ε' mu B hp H H' _ _ _ _ π σ hπ hσ v₀ hv₀ g₀ hg₀ hg₀n
  obtain ⟨hEmb, hEmul, hEc, hEinv, hcol, -, -, -, hEsq, -, hcolle, hUJ, hsub⟩ := hE n e ε ε' hp.signs
  have hn3 := hp.three_le
  have hB1 : 1 ≤ B := by
    have h01 := hp.wide ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
    have b0 := abs_le.1 (hp.bound.1 ⟨0, by omega⟩)
    have b1 := abs_le.1 (hp.bound.1 ⟨1, by omega⟩)
    linarith
  have hURep := hπ.2.2.1
  have hone : ∀ x ∈ UJset ε, 1 ≤ hsn x := fun x hx => (hUJ x hx).1.trans (hcolle x)
  have hdec : ∀ X ∈ UJset ε, ‖⟪π g₀ v₀, π X (π g₀ v₀)⟫_ℂ‖ ≤
      Real.exp (100 * ((n : ℝ) + 1) ^ 3) * (hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) * hsn X ^ (-(40 * ((n : ℝ) + 1) ^ 2))) := by
    intro X hX
    obtain ⟨hi, hr, hl, -⟩ := inv_facts hg₀
    have hx : g₀⁻¹ * X * g₀ ∈ UJset ε := mul_mem (mul_mem hi hX) hg₀
    rw [coef_conj hURep hg₀ hX]
    have hd := hD (n + 1) ε lam B (by omega) hp.hlam (by have := hp.gap; push_cast; exact this) hp.bound.1 H π hπ v₀ hv₀ _ hx
    push_cast at hd
    refine hd.trans ?_
    gcongr
    have hX' : g₀ * (g₀⁻¹ * X * g₀) * g₀⁻¹ = X := by
      calc g₀ * (g₀⁻¹ * X * g₀) * g₀⁻¹ = (g₀ * g₀⁻¹) * X * (g₀ * g₀⁻¹) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [hr, Matrix.one_mul, Matrix.mul_one]
    have hle : hsn X ≤ hsn g₀ ^ 2 * hsn (g₀⁻¹ * X * g₀) := by
      calc hsn X = hsn (g₀ * (g₀⁻¹ * X * g₀) * g₀⁻¹) := by rw [hX']
        _ ≤ hsn (g₀ * (g₀⁻¹ * X * g₀)) * hsn g₀⁻¹ := hsub _ _
        _ ≤ (hsn g₀ * hsn (g₀⁻¹ * X * g₀)) * hsn g₀ := by
          rw [(hUJ g₀ hg₀).2]; exact mul_le_mul_of_nonneg_right (hsub _ _) (hsn_nonneg _)
        _ = hsn g₀ ^ 2 * hsn (g₀⁻¹ * X * g₀) := by ring
    exact decay_real (by linarith [hone _ hx]) (by linarith [hone _ hX]) (by linarith [hone _ hg₀]) hle (by positivity)
      (by ring)
  refine ⟨fun g hg => ?_, Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2), fun X hX => ?_⟩
  swap
  · refine (hdec X hX).trans ?_
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (hsn_nonneg _) _))
    exact Real.rpow_le_rpow_of_exponent_le (hone X hX) (by nlinarith [sq_nonneg ((n : ℝ) + 1)])
  obtain ⟨hgi, hgr, hgl, hgii⟩ := inv_facts hg
  obtain ⟨h₁, hh₁, b, hb, hgb, hbn⟩ := hBo n e ε ε' hp.signs g⁻¹ hgi
  rw [hgii] at hbn
  obtain ⟨u₁, rfl⟩ := exists_umat hh₁
  obtain ⟨-, -, hl1, -⟩ := inv_facts hh₁
  have hb' : b = embH e (umat u₁)⁻¹ * g⁻¹ := by
    rw [hgb, ← Matrix.mul_assoc, ← hEmul, hl1, embH_one, Matrix.one_mul]
  have hbX : ∀ y : Mat n, b * (g * embH e y) = embH e ((umat u₁)⁻¹ * y) := by
    intro y
    rw [hb', hEmul]
    calc embH e (umat u₁)⁻¹ * g⁻¹ * (g * embH e y) = embH e (umat u₁)⁻¹ * (g⁻¹ * g) * embH e y := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hgl, Matrix.mul_one]
  have humul : ∀ y : Formalism.REAL.UJ ε', umat (u₁⁻¹ * y) = (umat u₁)⁻¹ * umat y := fun y => by
    simp [umat, Matrix.coe_units_inv]
  have hc1 : 1 ≤ colLen e g := (hUJ g hg).1
  have hβ1 : 1 ≤ hsn b := hone b hb
  obtain ⟨hPi, hPb⟩ := hP n ε' (4 * (n : ℝ) ^ 2 + 1) (by omega) le_rfl
  have hpt : ∀ y : Formalism.REAL.UJ ε', ‖⟪π g₀ v₀, π (g * embH e (umat y)) (π g₀ v₀)⟫_ℂ‖ ≤
      (Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
        (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * colLen e g ^ (-(2 * (n : ℝ) + 7))) *
        hsn (umat (u₁⁻¹ * y)) ^ (-(4 * (n : ℝ) ^ 2 + 1)) := by
    intro y
    have hy : umat y ∈ UJset ε' := y.2
    have hX : g * embH e (umat y) ∈ UJset ε := mul_mem hg (hEmb _ hy)
    refine (hdec _ hX).trans ?_
    have hz : umat (u₁⁻¹ * y) ∈ UJset ε' := (u₁⁻¹ * y).2
    have e1 : hsn (embH e (umat (u₁⁻¹ * y))) ≤ hsn b * hsn (g * embH e (umat y)) := by
      rw [humul, ← hbX]; exact hsub _ _
    have e2 : hsn (umat (u₁⁻¹ * y)) ≤ hsn (embH e (umat (u₁⁻¹ * y))) := by
      have := hEsq (umat (u₁⁻¹ * y))
      nlinarith [hsn_nonneg (umat (u₁⁻¹ * y)), hsn_nonneg (embH e (umat (u₁⁻¹ * y)))]
    have hrb := real_bound n hc1 (by rw [← hcol g (umat y)]; exact hcolle _) (hsn_pos (by omega) hz)
      (by linarith : (0 : ℝ) < hsn b) (e2.trans e1) hbn
    calc Real.exp (100 * ((n : ℝ) + 1) ^ 3) * (hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
          hsn (g * embH e (umat y)) ^ (-(40 * ((n : ℝ) + 1) ^ 2)))
        ≤ Real.exp (100 * ((n : ℝ) + 1) ^ 3) * (hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
          ((3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * colLen e g ^ (-(2 * (n : ℝ) + 7)) *
            hsn (umat (u₁⁻¹ * y)) ^ (-(4 * (n : ℝ) ^ 2 + 1)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrb (Real.rpow_nonneg (hsn_nonneg _) _)) (Real.exp_pos _).le
      _ = _ := by ring
  have hcont : Continuous (fun y : Formalism.REAL.UJ ε' => ⟪π g₀ v₀, π (g * embH e (umat y)) (π g₀ v₀)⟫_ℂ) := by
    have hcu : Continuous (fun y : Formalism.REAL.UJ ε' => umat y) := Units.continuous_val.comp continuous_subtype_val
    have hc1' : Continuous (fun y : Formalism.REAL.UJ ε' => g * embH e (umat y)) := continuous_const.mul (hEc.comp hcu)
    have hc2 : Continuous (fun y : Formalism.REAL.UJ ε' => π (g * embH e (umat y)) (π g₀ v₀)) :=
      (hURep.2.2 (π g₀ v₀)).comp_continuous hc1' (fun y => mul_mem hg (hEmb _ y.2))
    exact continuous_const.inner hc2
  have hDint : Integrable (fun y : Formalism.REAL.UJ ε' =>
      (Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
        (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * colLen e g ^ (-(2 * (n : ℝ) + 7))) *
        hsn (umat (u₁⁻¹ * y)) ^ (-(4 * (n : ℝ) ^ 2 + 1))) (muG ε') :=
    (hPi.comp_mul_left u₁⁻¹).const_mul _
  have hfi := Integrable.mono' hDint hcont.aestronglyMeasurable (ae_of_all _ hpt)
  refine ⟨hfi, ?_⟩
  have hcb := const_bound n hC₀ hB1 (hone g₀ hg₀) hg₀n
  have hvol : 0 ≤ (muG ε' (nbh ε' (1 / 4))).toReal := ENNReal.toReal_nonneg
  have hK0 : 0 ≤ Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
        (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * colLen e g ^ (-(2 * (n : ℝ) + 7)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (hsn_nonneg _) _)) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by linarith) _)
  have hcr : 0 ≤ colLen e g ^ (-(2 * (n : ℝ) + 7)) := Real.rpow_nonneg (by linarith) _
  calc ∫ y, ‖⟪π g₀ v₀, π (g * embH e (umat y)) (π g₀ v₀)⟫_ℂ‖ ∂muG ε'
      ≤ ∫ y, (Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
        (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * colLen e g ^ (-(2 * (n : ℝ) + 7))) *
        hsn (umat (u₁⁻¹ * y)) ^ (-(4 * (n : ℝ) ^ 2 + 1)) ∂muG ε' := integral_mono hfi.norm hDint hpt
    _ = (Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
        (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * colLen e g ^ (-(2 * (n : ℝ) + 7))) *
        ∫ y, hsn (umat y) ^ (-(4 * (n : ℝ) ^ 2 + 1)) ∂muG ε' := by
      rw [integral_const_mul, integral_mul_left_eq_self (fun y => hsn (umat y) ^ (-(4 * (n : ℝ) ^ 2 + 1))) u₁⁻¹]
    _ ≤ (Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
        (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * colLen e g ^ (-(2 * (n : ℝ) + 7))) *
        (Real.exp (10 * (n : ℝ) ^ 2) * (muG ε' (nbh ε' (1 / 4))).toReal) :=
      mul_le_mul_of_nonneg_left hPb hK0
    _ = (Real.exp (100 * ((n : ℝ) + 1) ^ 3) * hsn g₀ ^ (80 * ((n : ℝ) + 1) ^ 2) *
        (3 * ((n : ℝ) + 1)) ^ ((4 * (n : ℝ) ^ 2 + 1) / 2) * Real.exp (10 * (n : ℝ) ^ 2)) *
        ((muG ε' (nbh ε' (1 / 4))).toReal * colLen e g ^ (-(2 * (n : ℝ) + 7))) := by ring
    _ ≤ big (200 + 80 * C₀) n B * ((muG ε' (nbh ε' (1 / 4))).toReal * colLen e g ^ (-(2 * (n : ℝ) + 7))) :=
      mul_le_mul_of_nonneg_right hcb (mul_nonneg hvol hcr)
    _ = _ := by ring

theorem intBounds_main : EmbLaws → Boost → PowInt → DecPow → IntBounds := intBounds_of

end GlobalTheory.SepReal
