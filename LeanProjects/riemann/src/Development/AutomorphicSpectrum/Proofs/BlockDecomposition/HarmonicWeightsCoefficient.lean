import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialCoefficientComparisonStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylDenominatorProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VandermondeSquaresStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdPairSumsEqSumPowersetScoreStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScoreTZeroEqLevelCountStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScoreRigidityPermEqOneStatement

noncomputable section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.CoefId
variable {n : ℕ}

theorem coeff_eq {ι κ : Type} (I : Finset ι) (J : Finset κ) (f : ι → ℂ) (g : κ → ℂ) (e : ι → Fin n → ℤ)
    (e' : κ → Fin n → ℤ)
    (h : ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) →
      ∑ i ∈ I, f i * mon (e i) z = ∑ j ∈ J, g j * mon (e' j) z) (m : Fin n → ℤ) :
    ∑ i ∈ I.filter (fun i => e i = m), f i = ∑ j ∈ J.filter (fun j => e' j = m), g j :=
  GlobalTheory.T.monomial_coefficient_comparison I J f g e e' h m

theorem flip_prod (z : Fin n → ℂ) (h0 : ∀ a, z a ≠ 0) :
    (∏ a, ∏ b, (1 + z a / z b)) * (∏ a, z a) ^ (n - 1) = 2 ^ n * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 :=
  GlobalTheory.T.weyl_denominator_product z h0

theorem den_sq (z : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (n - 1 - (j : ℕ))).det =
      (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det * ∏ p ∈ prs n, (z p.1 + z p.2) :=
  GlobalTheory.T.vandermonde_squares z

theorem den_ne_zero (t : Fin n → ℂ) (ht : Function.Injective t) :
    (Matrix.of fun i j : Fin n => t i ^ (n - 1 - (j : ℕ))).det ≠ 0 := by
  have h : (Matrix.of fun i j : Fin n => t i ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde t).submatrix id (Fin.revPerm : Equiv.Perm (Fin n)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  rw [h, Matrix.det_permute']
  exact mul_ne_zero (by simp) (Matrix.det_vandermonde_ne_zero_iff.2 ht)

theorem prod_expand (z : Fin n → ℂ) :
    ∏ p ∈ prs n, (z p.1 + z p.2) = ∑ T ∈ (prs n).powerset, mon (score T) z :=
  GlobalTheory.T.prod_pair_sums_eq_sum_powerset_score z

theorem alt_expand (e : Fin n → ℤ) (z : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => z i ^ e j).det =
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * mon (fun a => e (σ a)) z := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

theorem score_tZero (lev : Fin n → ℕ) (hm : Monotone lev) (a : Fin n) :
    score (tZero lev) a = ((univ.filter fun b => lev a < lev b).card : ℤ) -
      ((univ.filter fun b => lev b < lev a).card : ℤ) + ((a : ℕ) : ℤ) :=
  GlobalTheory.T.score_tZero_eq_level_count lev hm a

theorem step_unique (lev : Fin n → ℕ) (hm : Monotone lev) (L : Fin n → ℤ) (hL : StrictAnti L)
    (hb : ∀ a b, lev a = lev b → L a - L b = ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) (σ : Equiv.Perm (Fin n))
    (T : Finset (Fin n × Fin n)) (hT : T ⊆ prs n)
    (h : ∀ a, score T a = score (tZero lev) a + 2 * (L a - L (σ a))) : σ = 1 ∧ T = tZero lev :=
  GlobalTheory.T.score_rigidity_perm_eq_one lev hm L hL hb (fun a b hab => by
    rw [score_tZero lev hm a, score_tZero lev hm b]
    simp only [hab, add_sub_cancel_right]) σ T hT h

theorem perm_unique (x y : Fin n → ℤ) (hx : StrictAnti x) (hy : StrictAnti y) (σ : Equiv.Perm (Fin n))
    (h : ∀ a, x (σ a) = y a) : σ = 1 := by
  have hs : StrictMono σ := fun a b hab => by
    have h1 := hy hab
    rw [← h a, ← h b] at h1
    rcases lt_trichotomy (σ a) (σ b) with h2 | h2 | h2
    · exact h2
    · rw [h2] at h1
      exact absurd h1 (lt_irrefl _)
    · exact absurd (hx h2) (not_lt.2 h1.le)
  have h3 : hs.orderIsoOfSurjective σ σ.surjective = OrderIso.refl _ := Subsingleton.elim _ _
  exact Equiv.ext fun a => DFunLike.congr_fun h3 a

theorem harmZ_spec (lam : Fin n → ℤ) (hl : Antitone lam) (lev : Fin n → ℕ) (hlev : IsLev lam lev) :
    Antitone (muZ lam lev) := by
  intro a b hab
  have h1 : lev a ≤ lev b := hlev.1 hab
  have h2 := hl hab
  have h3 : (univ.filter fun c => lev b < lev c).card ≤ (univ.filter fun c => lev a < lev c).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  have h4 : (univ.filter fun c => lev c < lev a).card ≤ (univ.filter fun c => lev c < lev b).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  simp only [muZ]
  omega

end GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId
variable {n : ℕ}

theorem mon_shift (x y : Fin n → ℤ) (z : Fin n → ℂ) (h0 : ∀ a, z a ≠ 0) :
    mon (fun a => x a + y a - ((n : ℤ) - 1)) z = mon x z * mon y z * ((∏ a, z a) ^ (n - 1))⁻¹ := by
  have hc : ∏ a, z a ^ (-((n : ℤ) - 1)) = ((∏ a, z a) ^ (n - 1))⁻¹ := by
    cases n with
    | zero => simp
    | succ m =>
      have : (-(((m + 1 : ℕ) : ℤ) - 1)) = -(m : ℤ) := by push_cast; ring
      rw [this]
      simp only [_root_.zpow_neg, zpow_natCast, Nat.add_sub_cancel]
      rw [Finset.prod_inv_distrib, Finset.prod_pow]
  unfold mon
  rw [← hc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  show z a ^ (x a + y a - ((n : ℤ) - 1)) = _
  rw [sub_eq_add_neg (x a + y a), zpow_add₀ (h0 a), zpow_add₀ (h0 a)]

theorem torus_id (lam : Fin n → ℤ) (z : Fin n → ℂ) (h0 : ∀ a, z a ≠ 0)
    (hinj : Function.Injective (fun a => z a ^ 2)) :
    (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2) *
        (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det =
      2 ^ n * ∑ σ : Equiv.Perm (Fin n), ∑ T ∈ (prs n).powerset, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        mon (fun a => 2 * (lam (σ a) + dl n (σ a)) + score T a - ((n : ℤ) - 1)) z := by
  have hD : (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (n - 1 - (j : ℕ))).det ≠ 0 :=
    den_ne_zero (fun a => z a ^ 2) hinj
  have hDe := den_sq z
  rw [hDe] at hD
  set A := (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det with hA
  set P := ∏ p ∈ prs n, (z p.1 + z p.2) with hP
  have hA0 : A ≠ 0 := left_ne_zero_of_mul hD
  have hP0 : P ≠ 0 := right_ne_zero_of_mul hD
  have hZ0 : (∏ a, z a) ^ (n - 1) ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun a _ => h0 a)
  have hN : (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (lam j + (n - 1 - (j : ℕ) : ℕ))).det =
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        mon (fun a => 2 * (lam (σ a) + dl n (σ a))) z := by
    rw [← alt_expand (fun j => 2 * (lam j + dl n j)) z]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, dl]
    rw [← zpow_natCast, ← _root_.zpow_mul]
    norm_num
  have hF := flip_prod z h0
  have hR : ∑ σ : Equiv.Perm (Fin n), ∑ T ∈ (prs n).powerset, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        mon (fun a => 2 * (lam (σ a) + dl n (σ a)) + score T a - ((n : ℤ) - 1)) z =
      (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        mon (fun a => 2 * (lam (σ a) + dl n (σ a))) z) * P * ((∏ a, z a) ^ (n - 1))⁻¹ := by
    rw [hP, prod_expand, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [mon_shift (fun a => 2 * (lam (σ a) + dl n (σ a))) (score T) z h0]
    simp only [mon]
    ring
  rw [hR, ← hN]
  have hW : weylChar lam (fun a => z a ^ 2) =
      (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (lam j + (n - 1 - (j : ℕ) : ℕ))).det / (A * P) := by
    rw [← hDe]; rfl
  rw [hW]
  field_simp
  linear_combination (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (lam j + (n - 1 - (j : ℕ) : ℕ))).det * hF

theorem exp_tZero (lam : Fin n → ℤ) (lev : Fin n → ℕ) (hm : Monotone lev) (a : Fin n) :
    2 * (lam a + dl n a) + score (tZero lev) a - ((n : ℤ) - 1) = muZ lam lev a + dl n a := by
  have h1 : dl n a = (n : ℤ) - 1 - (a : ℕ) := by
    have := a.2
    simp only [dl]
    omega
  rw [score_tZero lev hm, muZ, h1]
  ring

theorem dl_strictAnti : StrictAnti (dl n) := by
  intro a b h
  have h1 := a.2
  have h2 := b.2
  have h3 : (a : ℕ) < b := h
  simp only [dl]
  omega

theorem main_coef {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (F : Finset (Fin n → ℤ)) (hF : ∀ ν ∈ F, Antitone ν)
    (c : (Fin n → ℤ) → ℂ)
    (hc : ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) →
      ∑ ν ∈ F, c ν * weylChar ν z = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2))
    (μ : Fin n → ℤ) (hμ : μ ∈ harmZ lam) : μ ∈ F ∧ c μ = 2 ^ n := by
  classical
  obtain ⟨lv, hlv, rfl⟩ := Finset.mem_image.1 hμ
  set lev : Fin n → ℕ := fun a => (lv a : ℕ) with hlevdef
  have hlev : IsLev lam lev := (Finset.mem_filter.1 hlv).2
  have hm : Monotone lev := hlev.1
  set μ := muZ lam lev with hμdef
  have hμa : Antitone μ := harmZ_spec lam hl lev hlev
  have key := coeff_eq (F ×ˢ (univ : Finset (Equiv.Perm (Fin n))))
    ((univ : Finset (Equiv.Perm (Fin n))) ×ˢ (prs n).powerset)
    (fun x => c x.1 * ((Equiv.Perm.sign x.2 : ℤ) : ℂ)) (fun x => 2 ^ n * ((Equiv.Perm.sign x.1 : ℤ) : ℂ))
    (fun x a => x.1 (x.2 a) + dl n (x.2 a))
    (fun x a => 2 * (lam (x.1 a) + dl n (x.1 a)) + score x.2 a - ((n : ℤ) - 1))
    (by
      intro z hz hinj
      have h0 : ∀ a, z a ≠ 0 := fun a h => by simpa [h] using hz a
      have hzi : Function.Injective z := fun a b h => hinj (by simp only [h])
      have hA := den_ne_zero z hzi
      have ht := torus_id lam z h0 hinj
      have hnum : ∀ ν : Fin n → ℤ, weylChar ν z * (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det =
          ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * mon (fun a => ν (σ a) + dl n (σ a)) z := by
        intro ν
        rw [weylChar, div_mul_cancel₀ _ hA]
        exact alt_expand (fun j => ν j + dl n j) z
      rw [← hc z hz hinj] at ht
      rw [Finset.sum_product, Finset.sum_product]
      have e1 : ∑ x ∈ F, ∑ y : Equiv.Perm (Fin n), c x * ((Equiv.Perm.sign y : ℤ) : ℂ) *
          mon (fun a => x (y a) + dl n (y a)) z =
          (∑ ν ∈ F, c ν * weylChar ν z) * (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [mul_assoc, hnum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by ring
      refine e1.trans (ht.trans ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun T _ => by ring)
    (fun a => μ a + dl n a)
  have hLs : StrictAnti (fun a => lam a + dl n a) := fun a b h =>
    add_lt_add_of_le_of_lt (hl h.le) (dl_strictAnti h)
  have hRf : ((univ : Finset (Equiv.Perm (Fin n))) ×ˢ (prs n).powerset).filter
      (fun x => (fun a => 2 * (lam (x.1 a) + dl n (x.1 a)) + score x.2 a - ((n : ℤ) - 1)) = fun a => μ a + dl n a) =
      {(1, tZero lev)} := by
    ext ⟨σ, T⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_powerset,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨hT, he⟩
      refine step_unique lev hm (fun a => lam a + dl n a) hLs (fun a b hab => ?_) σ T hT fun a => ?_
      · have h1 := a.2
        have h2 := b.2
        simp only [hlev.2 a b hab, dl]
        omega
      · have h1 := congrFun he a
        have h2 := exp_tZero lam lev hm a
        linarith
    · rintro ⟨rfl, rfl⟩
      exact ⟨Finset.filter_subset _ _, funext fun a => by simpa using exp_tZero lam lev hm a⟩
  have hLf : (F ×ˢ (univ : Finset (Equiv.Perm (Fin n)))).filter
      (fun x => (fun a => x.1 (x.2 a) + dl n (x.2 a)) = fun a => μ a + dl n a) =
      if μ ∈ F then {(μ, 1)} else ∅ := by
    ext ⟨ν, σ⟩
    have hu : (ν, σ) ∈ (F ×ˢ (univ : Finset (Equiv.Perm (Fin n)))).filter
        (fun x => (fun a => x.1 (x.2 a) + dl n (x.2 a)) = fun a => μ a + dl n a) ↔ μ ∈ F ∧ ν = μ ∧ σ = 1 := by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      constructor
      · rintro ⟨hν, he⟩
        have hs : σ = 1 := perm_unique (fun a => ν a + dl n a) (fun a => μ a + dl n a)
          (fun a b h => add_lt_add_of_le_of_lt (hF ν hν h.le) (dl_strictAnti h))
          (fun a b h => add_lt_add_of_le_of_lt (hμa h.le) (dl_strictAnti h)) σ (fun a => congrFun he a)
        subst hs
        have hν' : ν = μ := funext fun a => by simpa using congrFun he a
        subst hν'
        exact ⟨hν, rfl, rfl⟩
      · rintro ⟨hμF, rfl, rfl⟩
        exact ⟨hμF, rfl⟩
    rw [hu]
    split_ifs with h <;> simp [h]
  rw [hLf, hRf] at key
  by_cases hmem : μ ∈ F
  · rw [if_pos hmem, Finset.sum_singleton, Finset.sum_singleton] at key
    simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, mul_one] at key
    exact ⟨hmem, key⟩
  · rw [if_neg hmem, Finset.sum_empty, Finset.sum_singleton] at key
    exact absurd key.symm (by simpa using pow_ne_zero n (two_ne_zero (α := ℂ)))

end GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem coef_harm : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ (F : Finset (Fin n → ℤ)), (∀ ν ∈ F, Antitone ν) →
    ∀ c : (Fin n → ℤ) → ℂ, (∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) →
      ∑ ν ∈ F, c ν * weylChar ν z = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2)) →
    ∀ μ ∈ harmZ lam, μ ∈ F ∧ c μ = 2 ^ n :=
  fun lam hl F hF c hc μ hμ => main_coef lam hl F hF c hc μ hμ

end GlobalTheory.CompanionTheory.CoefId
