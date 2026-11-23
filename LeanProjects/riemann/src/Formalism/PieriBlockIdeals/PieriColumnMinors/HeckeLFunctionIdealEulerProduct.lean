import Mathlib
import Formalism.PieriBlockIdeals.LemmaWFromLattice
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeightDescentMinors
import Formalism.PieriBlockIdeals.PieriColumnMinors.RegularCuspidalTrace

noncomputable section

open Finset PowerSeries

namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors

section A

section General

variable {R : Type} [CommRing R]

theorem subst_C_eq_C {a : R⟦X⟧} (r : R) : (C r : R⟦X⟧).subst a = C r := by
  rw [subst_C]; rfl

theorem constantCoeff_subst_of_constantCoeff_zero_alt {a : R⟦X⟧} (ha : constantCoeff a = 0) (f : R⟦X⟧) :
    constantCoeff (f.subst a) = constantCoeff f := by
  have hs : HasSubst a := by
    first
    | exact HasSubst.of_constantCoeff_zero ha
    | exact PowerSeries.HasSubst.of_constantCoeff_zero ha
    | exact HasSubst.of_constantCoeff_zero' ha
  obtain ⟨g, hg⟩ : X ∣ f - C (constantCoeff f) := by
    rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
  have e : f = C (constantCoeff f) + X * g := by
    rw [← hg]; ring
  conv_lhs => rw [e]
  rw [subst_add hs, subst_mul hs, subst_X hs, subst_C_eq_C]
  simp [ha]

theorem constantCoeff_gammaSeries (lam : R) (un : R⟦X⟧) : constantCoeff (gamSer lam un) = 0 := by
  simp [gamSer]

theorem hasSubst_gammaSeries (lam : R) (un : R⟦X⟧) : HasSubst (gamSer lam un) := by
  first
  | exact HasSubst.of_constantCoeff_zero (constantCoeff_gammaSeries lam un)
  | exact PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_gammaSeries lam un)
  | exact HasSubst.of_constantCoeff_zero' (constantCoeff_gammaSeries lam un)

end General

theorem pi0Subst_laws_hold : IncLaws := by
  intro l _ O _ _
  have hP := hasSubst_pi0_alt l O
  have hc := constantCoeff_pi0 l O
  refine ⟨fun f g => subst_add hP f g, fun f g => subst_mul hP f g, fun a => subst_C_eq_C a,
    subst_X hP, inc_X_sub_l_eq_q0 l O, fun f => constantCoeff_subst_of_constantCoeff_zero_alt hc f, ?_, ?_⟩
  · intro f p hp
    have hp' : HasSubst p := HasSubst.of_constantCoeff_zero' hp
    exact subst_comp_subst_apply hp' hP f
  · intro h2 f g hfg
    obtain ⟨g0, -, hu⟩ := r2_basis_holds l O h2 (inc l O f)
    have hpos := prime_sub_one_pos_alt l
    let j0 : Fin (l - 1) := ⟨0, hpos⟩
    have key : ∀ y : O⟦X⟧, inc l O y = inc l O f →
        (fun j : Fin (l - 1) => if j = j0 then y else 0) = g0 := by
      intro y hy
      refine hu _ ?_
      show inc l O f = ∑ j : Fin (l - 1), inc l O (if j = j0 then y else 0) * X ^ (j : ℕ)
      rw [Finset.sum_eq_single j0]
      · simp [j0, hy]
      · intro j _ hj
        simp [hj, inc_zero]
      · intro hj
        exact absurd (Finset.mem_univ _) hj
    have h1 := key f rfl
    have h2' := key g hfg.symm
    have h3 := congrFun (h1.trans h2'.symm) j0
    simpa using h3

section Red

variable (l : ℕ) [Fact l.Prime] (O k : Type) [CommRing O] [CommRing k] [Algebra ℤ_[l] O]
  [Algebra ℤ_[l] k] (red : O →+* k)
  (hred : ∀ z : ℤ_[l], red (algebraMap ℤ_[l] O z) = algebraMap ℤ_[l] k z)

include hred in
theorem map_reduction_binomialSeriesSubOne (c : ℤ_[l]) : PowerSeries.map red (br l O c) = br l k c := by
  rw [← map_binomialSeriesSubOne_algebraMap l O c, ← map_binomialSeriesSubOne_algebraMap l k c]
  ext n
  simp [hred]

include hred in
theorem map_reduction_pi0 : PowerSeries.map red (pi0 l O) = pi0 l k := by
  unfold pi0
  rw [map_prod]
  exact Finset.prod_congr rfl fun d _ => map_reduction_binomialSeriesSubOne l O k red hred d

end Red

theorem pi0Subst_reduction_holds : IncRed := by
  intro l _ O k _ _ _ _ red hred
  refine ⟨map_reduction_pi0 l O k red hred, ?_, ?_, ?_⟩
  · intro g
    unfold inc
    rw [map_subst_powerSeries red (hasSubst_pi0_alt l O), map_reduction_pi0 l O k red hred]
  · intro c f
    unfold act
    rw [map_subst_powerSeries red (hasSubst_binomialSeriesSubOne l O c), map_reduction_binomialSeriesSubOne l O k red hred]
  · intro f
    unfold phi
    rw [map_subst_powerSeries red (hasSubst_one_add_X_pow_sub_one_alt l)]
    simp

theorem gamma_laws_hold : GamLaws := by
  intro R _ lam un
  have hs : HasSubst (gamSer lam un) := hasSubst_gammaSeries lam un
  have hc : constantCoeff (gamSer lam un) = 0 := constantCoeff_gammaSeries lam un
  have hadd : ∀ f g : R⟦X⟧, gam0 lam un (f + g) = gam0 lam un f + gam0 lam un g := by
    intro f g; exact subst_add hs f g
  have hmul : ∀ f g : R⟦X⟧, gam0 lam un (f * g) = gam0 lam un f * gam0 lam un g := by
    intro f g; exact subst_mul hs f g
  have hC : ∀ a : R, gam0 lam un (C a) = C a := fun a => subst_C_eq_C a
  have hX : gam0 lam un X = X * (1 + un * (X - C lam)) := subst_X hs
  have hcc : ∀ y : R⟦X⟧, constantCoeff (gam0 lam un y) = constantCoeff y :=
    fun y => constantCoeff_subst_of_constantCoeff_zero_alt hc y
  refine ⟨hadd, hmul, hC, ?_, hX, ?_, hcc⟩
  · intro y; rw [X_dvd_iff, map_sub, hcc, sub_self]
  · have e : (X : R⟦X⟧) - C lam = X + C (-lam) := by rw [map_neg, sub_eq_add_neg]
    rw [e, hadd, hC, hX, map_neg]; ring

theorem gamma_reduction_holds : GamRed := by
  intro R k _ _ red lam un y
  unfold gam0
  rw [map_subst_powerSeries red (hasSubst_gammaSeries lam un)]
  congr 1
  simp [gamSer]

theorem gamma_on_pi0Subst_holds : GammaOnInc := by
  intro l _ O _ _ u un hun y
  obtain ⟨hadd, hmul, hC, hX, hq, -, hsub, -⟩ := pi0Subst_laws_hold l O
  have hP := hasSubst_pi0_alt l O
  have h1 : act l O u (inc l O y) = y.subst (act l O u (pi0 l O)) :=
    subst_comp_subst_apply hP (hasSubst_binomialSeriesSubOne l O u) y
  have h2 : inc l O (gam0 (l : O) un y) = y.subst (inc l O (gamSer (l : O) un)) :=
    hsub y _ (constantCoeff_gammaSeries _ _)
  have h3 : inc l O (gamSer (l : O) un) = pi0 l O * (1 + inc l O un * q0 l O) := by
    unfold gamSer
    have h1' : inc l O 1 = 1 := by
      have := hC 1
      simpa using this
    rw [hmul, hadd, hmul, hX, hq, h1']
  rw [h1, h2, h3, hun]

theorem unit_series_constant_holds : UnConst := by
  intro l _ O _ _ _ hl u c hu
  obtain ⟨un0, h0, he0, -, -⟩ := r6_holds l O hl u c hu
  obtain ⟨-, -, -, hX, hq, -, -, hinj⟩ := pi0Subst_laws_hold l O
  have hinj := hinj hl
  have hz : inc l O 0 = 0 := inc_zero l O
  have hpi : pi0 l O ≠ 0 := by
    rw [← hX, ← hz]
    exact fun h => X_ne_zero (hinj h)
  have hq0 : q0 l O ≠ 0 := by
    rw [← hq, ← hz]
    intro h
    have h1 := hinj h
    have h2 := congrArg (coeff 1) h1
    rw [map_sub, coeff_one_X, coeff_C, if_neg one_ne_zero, sub_zero, map_zero] at h2
    exact one_ne_zero h2
  have huniq : ∀ a b : O⟦X⟧, IsUn l O u a → IsUn l O u b → a = b := by
    intro a b ha hb
    have h1 : pi0 l O * (1 + inc l O a * q0 l O) = pi0 l O * (1 + inc l O b * q0 l O) :=
      ha.symm.trans hb
    have h2 := mul_left_cancel₀ hpi h1
    have h3 : inc l O a * q0 l O = inc l O b * q0 l O := add_left_cancel h2
    exact hinj (mul_right_cancel₀ hq0 h3)
  refine ⟨⟨un0, h0⟩, fun un hun => ⟨fun un' hun' => huniq un' un hun' hun, ?_⟩⟩
  rw [huniq un un0 hun h0]
  exact he0

theorem frobenius_on_pi0Subst_holds : PhiOnInc := by
  intro l _ O k _ _ _ _ _ red hl hred y
  obtain ⟨-, -, -, -, hcomm, -, -⟩ := action_laws_holds l O
  refine ⟨?_, ?_⟩
  · refine (fixed_relation_holds l O hl (phi l O (inc l O y))).1 ?_
    intro d hd
    rw [← hcomm, (fixed_relation_holds l O hl (inc l O y)).2 ⟨y, rfl⟩ d hd]
  · intro y' hy'
    obtain ⟨-, hinc, -, hphi⟩ := pi0Subst_reduction_holds l O k red hred
    obtain ⟨-, -, -, -, -, -, -, hinj⟩ := pi0Subst_laws_hold l k
    apply hinj hl
    rw [← hinc, ← hy', hphi, hinc, r5_character_holds l k]
    rfl

theorem evaluation_congruence_holds : EvalCong := by
  intro O _ lam a g hg
  obtain ⟨q, hq⟩ := hg
  have hc : constantCoeff g = a + lam * (-constantCoeff q) := by
    have h2 := congrArg constantCoeff hq
    simp only [map_sub, map_mul, constantCoeff_C, constantCoeff_X] at h2
    linear_combination h2
  refine ⟨⟨-constantCoeff q, hc⟩, ?_⟩
  intro k _ red hred
  rw [hc, map_add, map_mul, hred, zero_mul, add_zero]

theorem linear_division_evaluation_holds : LinDivisionEval := by
  intro O _ _ _ _ _ _ _ c a f f₁ hn hf
  have hx : PowerSeries.HasEval c := hn
  have hc : Continuous (RingHom.id O) := continuous_id
  have h2 := congrArg (PowerSeries.eval₂Hom hc hx) hf
  rw [map_add, map_mul, map_sub] at h2
  simp only [PowerSeries.coe_eval₂Hom, eval₂_C, eval₂_X, RingHom.id_apply, sub_self,
    zero_mul, zero_add] at h2
  exact h2

theorem gamma_mod_q_holds : GammaModQ := by
  intro O _ lam n D Th h a b
  obtain ⟨q, hq⟩ := h a b
  refine ⟨X * q + C (Th a b), ?_⟩
  have h1 : (1 : Matrix (Fin n) (Fin n) O⟦X⟧) a b = C ((1 : Matrix (Fin n) (Fin n) O) a b) := by
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h1, map_add, map_mul]
  linear_combination X * hq

theorem derivation_linear_holds : DLinear := by
  intro A N _ _ _ p γA γ d htor hγadd hγsmul hd
  have hadd : ∀ x y, d (x + y) = d x + d y := by
    intro x y
    apply eq_of_sub_eq_zero
    apply htor
    rw [smul_sub, smul_add, hd, hd, hd, hγadd]
    abel
  refine ⟨hadd, ?_⟩
  intro a x ha
  apply eq_of_sub_eq_zero
  apply htor
  rw [smul_sub, hd, hγsmul, ha, smul_comm p a (d x), hd, smul_sub]
  exact sub_self _

theorem dbar_coordinates_hold : DbarCoord := by
  intro k _ n un D y z h a
  obtain ⟨hadd, hmul, hC, -, hX, -, hcc0⟩ := gamma_laws_hold k 0 un
  have h1 : ∀ y : k⟦X⟧, coeff 1 (gam0 0 un y) = coeff 1 y := by
    intro y
    obtain ⟨g, hg⟩ : X ∣ y - C (constantCoeff y) := by
      rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
    have e : y = C (constantCoeff y) + X * g := by rw [← hg]; ring
    rw [e, hadd, hmul, hC, hX]
    rw [map_add, map_add, coeff_C, if_neg one_ne_zero, zero_add, zero_add]
    rw [mul_assoc, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul, hcc0]
    simp
  have e2 : coeff 1 (X * z a) = constantCoeff (z a) := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  rw [← e2, h a]
  have hsm : ∀ v : Fin n → k⟦X⟧, ((X : k⟦X⟧) • D).mulVec v = (X : k⟦X⟧) • D.mulVec v := by
    intro v
    first
    | exact Matrix.smul_mulVec X D v
    | exact Matrix.smul_mulVec_assoc X D v
    | (funext i; simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
        Finset.mul_sum, mul_assoc])
  rw [Matrix.add_mulVec, Matrix.one_mulVec, hsm]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_add]
  rw [h1, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  first
  | (simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hcc0]; ring)
  | (simp only [Matrix.mulVec, Matrix.dotProduct, map_sum, map_mul, Matrix.map_apply, hcc0]; ring)

end A

theorem frobenius_laws_hold : FrobLaws := by
  intro R _ l hl
  have hc : constantCoeff (X ^ l : R⟦X⟧) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hl.ne']
  have hs : HasSubst (X ^ l : R⟦X⟧) := by
    first
    | exact HasSubst.of_constantCoeff_zero hc
    | exact PowerSeries.HasSubst.of_constantCoeff_zero hc
    | exact HasSubst.of_constantCoeff_zero' hc
  refine ⟨fun f g => ?_, fun f g => ?_, fun a => ?_, ?_⟩
  · exact subst_add hs f g
  · exact subst_mul hs f g
  · exact subst_C_eq_C a
  · exact subst_X hs

theorem semilinear_change_holds : SemilinChange := by
  intro R _ n θ M g g' y
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul,
    ← Matrix.mulVec_mulVec]
  congr 1
  funext a
  rw [RingHom.map_mulVec]
  rfl

theorem det_dvd_holds : DetDvd := by
  intro R _ n h x P Q hPQ
  refine ⟨Q.det, ?_⟩
  have h2 := congrArg Matrix.det hPQ
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at h2
  rw [h2, ← pow_mul]

theorem map_smul_one_matrix {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (x : R) :
    ((x • (1 : Matrix (Fin n) (Fin n) R))).map f = f x • (1 : Matrix (Fin n) (Fin n) S) := by
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem blockTriangular_of_mul_eq_pow_smul_one {R : Type} [CommRing R] [IsDomain R] (π : R) (n h : ℕ)
    (Φ Φ' : Matrix (Fin n) (Fin n) R) (b : Fin n → ℕ) (hπ : π ≠ 0) (hΦ : Φ.BlockTriangular b)
    (hm : Φ * Φ' = (π ^ h) • (1 : Matrix (Fin n) (Fin n) R)) : Φ'.BlockTriangular b := by
  intro i j hij
  let φ := algebraMap R (FractionRing R)
  have hinj : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have hm' : Φ.map φ * Φ'.map φ = (φ π ^ h) • (1 : Matrix (Fin n) (Fin n) (FractionRing R)) := by
    rw [← Matrix.map_mul, hm]
    ext a c
    by_cases hac : a = c <;> simp [hac, Matrix.one_apply]
  have hc : (φ π) ^ h ≠ 0 := pow_ne_zero _ ((map_ne_zero_iff φ hinj).2 hπ)
  have hr : Φ.map φ * (((φ π) ^ h)⁻¹ • Φ'.map φ) = 1 := by
    rw [Matrix.mul_smul, hm', smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hinv : (Φ.map φ)⁻¹ = ((φ π) ^ h)⁻¹ • Φ'.map φ := Matrix.inv_eq_right_inv hr
  letI : Invertible (Φ.map φ) := by
    first
    | exact ⟨_, mul_eq_one_comm.mp hr, hr⟩
    | exact Matrix.invertibleOfIsUnitDet _ (Matrix.isUnit_det_of_right_inverse hr)
    | exact Matrix.invertibleOfRightInverse _ _ hr
  have hΦK : (Φ.map φ).BlockTriangular b := fun a c hac => by simp [hΦ hac]
  have h4 := Matrix.blockTriangular_inv_of_blockTriangular hΦK hij
  rw [hinv, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_eq_zero] at h4
  rcases h4 with h5 | h5
  · exact absurd h5 (inv_ne_zero hc)
  · exact hinj (by rw [h5, map_zero])

theorem toSquareBlock_mul_of_blockTriangular_alt {R : Type} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (b : Fin n → ℕ) (hA : A.BlockTriangular b) (hB : B.BlockTriangular b) (r : ℕ) :
    (A * B).toSquareBlock b r = A.toSquareBlock b r * B.toSquareBlock b r := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Matrix.toSquareBlock_def, Matrix.toBlock_apply, Matrix.mul_apply,
    Matrix.of_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => b k = r)]
  have hz : ∑ k : {k // ¬ b k = r}, A i k * B k j = 0 := by
    apply Finset.sum_eq_zero
    rintro ⟨k, hk⟩ -
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA (by rw [hi]; exact h), zero_mul]
    · rw [hB (by rw [hj]; exact h), mul_zero]
  rw [hz, add_zero]

theorem block_height_holds : BlockHeight := by
  intro R _ _ π n h Φ Φ' b hπ hΦ hm
  have hΦ' := blockTriangular_of_mul_eq_pow_smul_one π n h Φ Φ' b hπ hΦ hm
  refine ⟨hΦ', fun r => ?_⟩
  rw [← toSquareBlock_mul_of_blockTriangular_alt Φ Φ' b hΦ hΦ' r, hm]
  ext ⟨i, hi⟩ ⟨j, hj⟩
  by_cases hij : i = j
  · subst hij; simp [Matrix.toSquareBlock_def]
  · simp [Matrix.toSquareBlock_def, Matrix.one_apply, hij]

theorem block_height_on_line_holds : BlockHeightLine := by
  intro R _ _ π n h Φ Φ' b s hπ hΦ hm hs
  have hΦ' := blockTriangular_of_mul_eq_pow_smul_one π n h Φ Φ' b hπ hΦ hm
  have h2 := congrFun (congrFun hm s) s
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h2
  rw [← h2, Finset.sum_eq_single s]
  · intro j _ hj
    rcases lt_trichotomy (b j) (b s) with h3 | h3 | h3
    · rw [hΦ h3, zero_mul]
    · exact absurd (hs j h3) hj
    · rw [hΦ' h3, mul_zero]
  · intro hs'; exact absurd (Finset.mem_univ s) hs'

theorem unit_pow_holds : UnitPow := by
  intro k _ h x x' hxx
  obtain ⟨α, hα, hassoc⟩ := (dvd_prime_pow X_prime h).1 ⟨x', hxx.symm⟩
  obtain ⟨u, hu⟩ := hassoc.symm
  exact ⟨α, u, hα, by rw [← hu, mul_comm]⟩

theorem frobenius_diagonal_holds : PhiDiag := by
  intro k _ l s p v w w' κ κ' hl heq
  obtain ⟨-, hmul, hC, -⟩ := frobenius_laws_hold k l hl
  let φ : k⟦X⟧ →+* LaurentSeries k := HahnSeries.ofPowerSeries ℤ k
  have hφ : Function.Injective φ := HahnSeries.ofPowerSeries_injective
  change φ (frob0 l (w' : k⟦X⟧)) * φ X ^ ((l : ℤ) * κ') * φ ((v : k⟦X⟧) * X ^ s) =
    φ p * φ (w : k⟦X⟧) * φ X ^ κ at heq
  have hx : φ X ≠ 0 := (map_ne_zero_iff φ hφ).2 X_ne_zero
  have hfu : frob0 l (w' : k⟦X⟧) * frob0 l ((w'⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
    rw [← hmul, Units.mul_inv, ← map_one (C : k →+* k⟦X⟧), hC]
  let A : k⟦X⟧ := frob0 l (w' : k⟦X⟧) * (v : k⟦X⟧) * ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)
  have hF : IsUnit (frob0 l (w' : k⟦X⟧)) := ⟨⟨_, _, hfu, by rw [mul_comm]; exact hfu⟩, rfl⟩
  have hA : IsUnit A := (hF.mul v.isUnit).mul (w⁻¹).isUnit
  have hww : φ (w : k⟦X⟧) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  set e : ℤ := (l : ℤ) * κ' + (s : ℤ) - κ with he
  have key : φ p = φ A * φ X ^ e := by
    have h1 : φ p * φ (w : k⟦X⟧) * φ X ^ κ * (φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) * φ X ^ (-κ)) = φ p := by
      rw [show φ p * φ (w : k⟦X⟧) * φ X ^ κ * (φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) * φ X ^ (-κ)) =
        φ p * (φ (w : k⟦X⟧) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)) * (φ X ^ κ * φ X ^ (-κ)) by ring, hww,
        ← zpow_add₀ hx, add_neg_cancel, zpow_zero, mul_one, mul_one]
    rw [← h1, ← heq]
    simp only [A, map_mul, map_pow]
    rw [he, sub_eq_add_neg, zpow_add₀ hx, zpow_add₀ hx, zpow_natCast]
    ring
  by_cases he0 : 0 ≤ e
  · refine ⟨he0, hA.unit, hφ ?_⟩
    rw [IsUnit.unit_spec, map_mul, map_pow, key, ← zpow_natCast, Int.toNat_of_nonneg he0]
  · exfalso
    push_neg at he0
    have hm : φ p * φ X ^ (-e) = φ A := by
      rw [key, mul_assoc, ← zpow_add₀ hx, add_neg_cancel, zpow_zero, mul_one]
    obtain ⟨m, hm'⟩ : ∃ m : ℕ, -e = (m : ℤ) + 1 := ⟨(-e - 1).toNat, by omega⟩
    rw [hm', zpow_add_one₀ hx, zpow_natCast, ← map_pow, ← map_mul, ← map_mul] at hm
    have h5 := congrArg constantCoeff (hφ hm)
    simp only [map_mul, constantCoeff_X, mul_zero] at h5
    exact (hA.map constantCoeff).ne_zero h5.symm

theorem gammaSeries_zero_eq {k : Type} [CommRing k] (un : k⟦X⟧) :
    gamSer 0 un = X * (1 + un * X) := by
  simp [gamSer]

theorem coeff_one_add_X_mul_add_X_sq_mul {k : Type} [CommRing k] (x y z : k⟦X⟧) (hx : coeff 1 x = 0) :
    coeff 1 (x + X * y + X ^ 2 * z) = constantCoeff y := by
  rw [map_add, map_add, hx, zero_add]
  first
  | (rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_X_pow_mul', if_neg (by norm_num),
      add_zero, coeff_zero_eq_constantCoeff_apply])
  | simp [coeff_X_pow_mul']

theorem theta_diagonal_holds : ThetaDiag := by
  intro k _ un g c w κ heq
  obtain ⟨hadd, hmul, hC, -, hX, -, hcc0⟩ := gamma_laws_hold k 0 un
  have e1 : ∀ f : k⟦X⟧, coeff 1 (X * f) = constantCoeff f := by
    intro f
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have h1 : ∀ y : k⟦X⟧, coeff 1 (gam0 0 un y) = coeff 1 y := by
    intro y
    obtain ⟨q, hq⟩ : X ∣ y - C (constantCoeff y) := by
      rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
    have e : y = C (constantCoeff y) + X * q := by rw [← hq]; ring
    rw [e, hadd, hmul, hC, hX]
    rw [map_add, map_add, coeff_C, if_neg one_ne_zero, zero_add, zero_add]
    rw [mul_assoc, e1, e1, map_mul, hcc0]
    simp
  have hc1 : ∀ f q : k⟦X⟧, coeff 1 (f * q) = coeff 1 f * constantCoeff q + constantCoeff f * coeff 1 q := by
    intro f q
    first
    | (rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply]; ring)
    | (rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply])
    | (rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_mul, Finset.Nat.antidiagonal_succ];
        simp [coeff_zero_eq_constantCoeff_apply]; ring)
    | (simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply]; ring)
    | (simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply])
  have hV : IsUnit (1 + un * X : k⟦X⟧) := by
    first
    | (rw [isUnit_iff_constantCoeff]; simp)
    | exact isUnit_iff_constantCoeff.2 (by simp)
  set V := hV.unit with hVdef
  have hV0 : constantCoeff (V : k⟦X⟧) = 1 := by rw [IsUnit.unit_spec]; simp
  have hV1' : coeff 1 (V : k⟦X⟧) = constantCoeff un := by
    rw [IsUnit.unit_spec, map_add, coeff_one, if_neg one_ne_zero, zero_add, mul_comm, e1]
  have hgs : gamSer 0 un = X * (V : k⟦X⟧) := by rw [gammaSeries_zero_eq, IsUnit.unit_spec]
  have hVcc : ∀ m : ℤ, constantCoeff ((V ^ m : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
    intro m
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow, hV0, one_pow]
    · rw [zpow_neg, zpow_natCast, map_units_inv, Units.val_pow_eq_pow_val, map_pow, hV0, one_pow,
        inv_one]
  have hVn : ∀ n : ℕ, coeff 1 ((V : k⟦X⟧) ^ n) = n * constantCoeff un := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, hc1, ih, hV1', map_pow, hV0, one_pow]
      push_cast
      ring
  have hV1 : ∀ m : ℤ, coeff 1 ((V ^ m : (k⟦X⟧)ˣ) : k⟦X⟧) = m * constantCoeff un := by
    intro m
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · rw [zpow_natCast, Units.val_pow_eq_pow_val, hVn, Int.cast_natCast]
    · have hcc_inv : constantCoeff (((V ^ n)⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
        rw [map_units_inv, Units.val_pow_eq_pow_val, map_pow, hV0, one_pow, inv_one]
      have hinv := hc1 ((V ^ n : (k⟦X⟧)ˣ) : k⟦X⟧) (((V ^ n)⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)
      rw [Units.mul_inv, coeff_one, if_neg one_ne_zero, hcc_inv, Units.val_pow_eq_pow_val, hVn,
        map_pow, hV0, one_pow] at hinv
      rw [zpow_neg, zpow_natCast]
      push_cast
      linear_combination -hinv
  let φ : k⟦X⟧ →+* LaurentSeries k := HahnSeries.ofPowerSeries ℤ k
  have hφ : Function.Injective φ := HahnSeries.ofPowerSeries_injective
  have hx : φ X ≠ 0 := (map_ne_zero_iff φ hφ).2 X_ne_zero
  have hVz : ∀ m : ℤ, φ ((V ^ m : (k⟦X⟧)ˣ) : k⟦X⟧) = φ (V : k⟦X⟧) ^ m := by
    intro m
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · rw [zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
    · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, map_units_inv, Units.val_pow_eq_pow_val,
        map_pow]
  have hc : c = gam0 0 un (w : k⟦X⟧) * ((V ^ κ : (k⟦X⟧)ˣ) : k⟦X⟧) * (1 + X * g) *
      ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) := by
    apply hφ
    have hw : φ (w : k⟦X⟧) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hxk : φ X ^ κ ≠ 0 := zpow_ne_zero κ hx
    change φ (gam0 0 un (w : k⟦X⟧)) * φ (gamSer 0 un) ^ κ * φ (1 + X * g) =
      φ c * φ (w : k⟦X⟧) * φ X ^ κ at heq
    rw [hgs, map_mul, mul_zpow] at heq
    apply mul_right_cancel₀ hxk
    simp only [map_mul, hVz]
    calc φ c * φ X ^ κ = φ c * φ X ^ κ * (φ (w : k⟦X⟧) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)) := by
          rw [hw, mul_one]
      _ = (φ c * φ (w : k⟦X⟧) * φ X ^ κ) * φ ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) := by ring
      _ = _ := by rw [← heq]; ring
  have hww0 : constantCoeff (w : k⟦X⟧) * constantCoeff ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hww1 : coeff 1 (w : k⟦X⟧) * constantCoeff ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) +
      constantCoeff (w : k⟦X⟧) * coeff 1 ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧) = 0 := by
    rw [← hc1, Units.mul_inv, coeff_one, if_neg one_ne_zero]
  have hC1 : coeff 1 (1 + X * g) = constantCoeff g := by
    rw [map_add, coeff_one, if_neg one_ne_zero, zero_add, e1]
  have hC0 : constantCoeff (1 + X * g) = 1 := by simp
  rw [hc]
  refine ⟨?_, ?_⟩
  · simp only [map_mul, hcc0, hVcc, hC0, mul_one]
    exact hww0
  · simp only [hc1, map_mul, h1, hcc0, hVcc, hV1, hC0, hC1]
    linear_combination hww1 + ((κ : k) * constantCoeff un + constantCoeff g) * hww0

theorem theta_base_change_holds : ThetaBaseChange := by
  intro k _ n un g D
  obtain ⟨hadd, hmul, hC, -, hX, -, hcc0⟩ := gamma_laws_hold k 0 un
  have e1 : ∀ f : k⟦X⟧, coeff 1 (X * f) = constantCoeff f := by
    intro f
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have h1 : ∀ y : k⟦X⟧, coeff 1 (gam0 0 un y) = coeff 1 y := by
    intro y
    obtain ⟨q, hq⟩ : X ∣ y - C (constantCoeff y) := by
      rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
    have e : y = C (constantCoeff y) + X * q := by rw [← hq]; ring
    rw [e, hadd, hmul, hC, hX]
    rw [map_add, map_add, coeff_C, if_neg one_ne_zero, zero_add, zero_add]
    rw [mul_assoc, e1, e1, map_mul, hcc0]
    simp
  have hc1 : ∀ f q : k⟦X⟧, coeff 1 (f * q) = coeff 1 f * constantCoeff q + constantCoeff f * coeff 1 q := by
    intro f q
    first
    | (rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply]; ring)
    | (rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply])
    | (rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_mul, Finset.Nat.antidiagonal_succ];
        simp [coeff_zero_eq_constantCoeff_apply]; ring)
    | (simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply]; ring)
    | (simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply])
  have hcoef : ∀ M N : Matrix (Fin n) (Fin n) k⟦X⟧, (M * N).map (coeff 1) =
      M.map (coeff 1) * N.map constantCoeff + M.map constantCoeff * N.map (coeff 1) := by
    intro M N
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, hc1,
      Finset.sum_add_distrib]
  set A := ((g⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧) with hA
  set G := (g : Matrix (Fin n) (Fin n) k⟦X⟧) with hG
  have hAG : A * G = 1 := Units.inv_mul g
  have hGA : G * A = 1 := Units.mul_inv g
  have hone0 : (1 : Matrix (Fin n) (Fin n) k⟦X⟧).map constantCoeff = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hAG0 : A.map constantCoeff * G.map constantCoeff = 1 := by
    rw [← Matrix.map_mul, hAG, hone0]
  have hGA0 : G.map constantCoeff * A.map constantCoeff = 1 := by
    rw [← Matrix.map_mul, hGA, hone0]
  have hAG1 : A.map (coeff 1) * G.map constantCoeff + A.map constantCoeff * G.map (coeff 1) = 0 := by
    rw [← hcoef, hAG]
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have hB0 : (1 + (X : k⟦X⟧) • D).map constantCoeff = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have hB1 : (1 + (X : k⟦X⟧) • D).map (coeff 1) = D.map constantCoeff := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, e1]
  have hC0 : (G.map (gam0 0 un)).map constantCoeff = G.map constantCoeff := by
    ext i j
    simp only [Matrix.map_apply, hcc0]
  have hC1 : (G.map (gam0 0 un)).map (coeff 1) = G.map (coeff 1) := by
    ext i j
    simp only [Matrix.map_apply, h1]
  have hθ : thetaOf (chgGam un g D) = A.map constantCoeff * D.map constantCoeff * G.map constantCoeff := by
    show (A * (1 + (X : k⟦X⟧) • D) * G.map (gam0 0 un)).map (coeff 1) = _
    rw [hcoef, hcoef, Matrix.map_mul, hB0, hB1, hC0, hC1, Matrix.mul_one, Matrix.mul_one,
      Matrix.add_mul, add_right_comm, hAG1, zero_add]
  refine ⟨?_, hθ, ?_⟩
  · show (A * (1 + (X : k⟦X⟧) • D) * G.map (gam0 0 un)).map constantCoeff = 1
    rw [Matrix.map_mul, Matrix.map_mul, hB0, Matrix.mul_one, hC0, hAG0]
  · rw [hθ, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hGA0, Matrix.one_mul]

theorem frobenius_base_change_holds : PhiBaseChange := by
  intro k _ n l h g g' P hl
  have hs : HasSubst (X ^ l : k⟦X⟧) := HasSubst.X_pow hl.ne'
  let fr : k⟦X⟧ →+* k⟦X⟧ := (substAlgHom hs).toRingHom
  have hfr : ∀ y, fr y = frob0 l y := fun y => by
    change substAlgHom hs y = _
    rw [coe_substAlgHom hs]; rfl
  let g2 : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ :=
    Units.map (fr.mapMatrix :
      Matrix (Fin n) (Fin n) k⟦X⟧ →+* Matrix (Fin n) (Fin n) k⟦X⟧).toMonoidHom g'
  have hg2 : (g' : Matrix (Fin n) (Fin n) k⟦X⟧).map (frob0 l) = (g2 : Matrix (Fin n) (Fin n) k⟦X⟧) := by
    refine Matrix.ext fun a b => ?_
    change frob0 l _ = fr _
    rw [hfr]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨((g2⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧) * M *
      (g : Matrix (Fin n) (Fin n) k⟦X⟧), ?_⟩
    unfold chgPhi
    rw [hg2]
    calc _ = ((g⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧) * (P *
          ((g2 : Matrix (Fin n) (Fin n) k⟦X⟧) *
            ((g2⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧)) * M) *
          (g : Matrix (Fin n) (Fin n) k⟦X⟧) := by simp only [mul_assoc]
      _ = _ := by
        rw [Units.mul_inv, mul_one, hM, Matrix.mul_smul, Matrix.smul_mul, mul_one, Units.inv_mul]
  · intro x t hx
    exact minors_dvd_mul_holds (k⟦X⟧) n n n n t x _ P _ hx

section Five

variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]

theorem reduction_natCast_prime_eq_zero (l : ℕ) [CharP F l] (red : O →+* F) : red (l : O) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

theorem constantCoeff_map_eq (red : O →+* F) (y : O⟦X⟧) :
    constantCoeff (PowerSeries.map red y) = red (constantCoeff y) := by
  first
  | exact constantCoeff_map red y
  | rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]

theorem map_X_sub_C_prime_pow_eq_X_pow (l : ℕ) [CharP F l] (red : O →+* F) (m : ℕ) :
    PowerSeries.map red ((X - C (l : O)) ^ m) = X ^ m := by
  rw [map_pow, map_sub, map_X, map_C, map_natCast, CharP.cast_eq_zero, map_zero, sub_zero]

theorem reduction_log_unit_pow_eq (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l] (red : O →+* F)
    (u : ℤ_[l]ˣ) (c r : ℤ_[l]) (m : ℤ) (hu : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c)
    (hr : ((u ^ (-m) : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) * r) :
    red (algebraMap ℤ_[l] O r) = -red (algebraMap ℤ_[l] O c) * ((m : ℤ) : F) := by
  have hl0 : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have key : ∀ k : ℕ, ∃ s : ℤ_[l],
      (u : ℤ_[l]) ^ k = 1 + (l : ℤ_[l]) * ((k : ℤ_[l]) * c) + (l : ℤ_[l]) ^ 2 * s := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨s, hs⟩ := ih
      refine ⟨(k : ℤ_[l]) * c ^ 2 + s + s * (l : ℤ_[l]) * c, ?_⟩
      rw [pow_succ, hs, hu]
      push_cast
      ring
  have ht : ∃ t : ℤ_[l], r = -((m : ℤ) : ℤ_[l]) * c + (l : ℤ_[l]) * t := by
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · obtain ⟨s, hs⟩ := key k
      have h1 : ((u ^ (-(k : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) * (u : ℤ_[l]) ^ k = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
        simp
      rw [hr, hs] at h1
      have h2 : (l : ℤ_[l]) * (r + (k : ℤ_[l]) * c +
          (l : ℤ_[l]) * (r * (k : ℤ_[l]) * c + s + r * (l : ℤ_[l]) * s)) = 0 := by
        linear_combination h1
      have h3 := (mul_eq_zero.1 h2).resolve_left hl0
      refine ⟨-(r * (k : ℤ_[l]) * c + s + r * (l : ℤ_[l]) * s), ?_⟩
      push_cast
      linear_combination h3
    · obtain ⟨s, hs⟩ := key k
      have h1 : ((u ^ (-(-(k : ℤ))) : ℤ_[l]ˣ) : ℤ_[l]) = (u : ℤ_[l]) ^ k := by
        rw [neg_neg, zpow_natCast, Units.val_pow_eq_pow_val]
      rw [hr, hs] at h1
      have h2 : (l : ℤ_[l]) * (r - (k : ℤ_[l]) * c - (l : ℤ_[l]) * s) = 0 := by
        linear_combination h1
      have h3 := (mul_eq_zero.1 h2).resolve_left hl0
      refine ⟨s, ?_⟩
      push_cast
      linear_combination h3
  obtain ⟨t, ht⟩ := ht
  rw [ht]
  simp only [map_add, map_mul, map_neg, map_intCast, map_natCast, CharP.cast_eq_zero, zero_mul,
    add_zero]
  ring

theorem rank_one_model_holds : RankOneModel := by
  intro ι l h _ O F _ _ _ _ red N u c wt hu hN i
  obtain ⟨-, -, hdet, hD, hTh⟩ := hN
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv⟩ := hdet i
    refine ⟨v, ?_⟩
    rw [Matrix.det_fin_one, Fin.sum_univ_one] at hv
    exact hv
  · obtain ⟨r, hr, hcp⟩ := hTh i
    have h1 : (N.Th i).charpoly = Polynomial.X - Polynomial.C (N.Th i 0 0) := by
      show (Matrix.charmatrix (N.Th i)).det = _
      rw [Matrix.det_fin_one, Matrix.charmatrix_apply_eq]
    rw [h1, Fin.prod_univ_one] at hcp
    have h2 := congrArg (fun p => Polynomial.coeff p 0) hcp
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub,
      neg_inj] at h2
    have h3 := (evaluation_congruence_holds O (l : O) (N.Th i 0 0) (N.D i 0 0) (hD i 0 0)).2 F red
      (by rw [map_natCast, CharP.cast_eq_zero])
    rw [h3, h2, reduction_log_unit_pow_eq l red u c (r 0) (wt i) hu (hr 0)]

theorem reduction_algebraMap_unit_ne_zero (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] (red : O →+* F) (c : ℤ_[l])
    (hc : IsUnit c) : red (algebraMap ℤ_[l] O c) ≠ 0 := by
  exact ((hc.map (algebraMap ℤ_[l] O)).map red).ne_zero

theorem charpoly_theta_eq_prod (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ)
    (hu : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c) (hN : LatW l W.N h u U') (i : ι) :
    (thetaOf (W.Gam i)).charpoly = ∏ j, (Polynomial.X -
      Polynomial.C (-W.red (algebraMap ℤ_[l] O c) * ((U' i j : ℤ) : F))) := by
  obtain ⟨-, -, -, hD, hTh⟩ := hN
  obtain ⟨r, hr, hcp⟩ := hTh i
  have h3 := (theta_base_change_holds F n W.unbar (W.g i)
    ((W.N.D i).map (PowerSeries.map W.red))).2.2
  have hD' : ((W.N.D i).map (PowerSeries.map W.red)).map constantCoeff = (W.N.Th i).map W.red := by
    ext a b
    simp only [Matrix.map_apply]
    rw [constantCoeff_map_eq]
    exact (evaluation_congruence_holds O (l : O) (W.N.Th i a b) (W.N.D i a b) (hD i a b)).2 F W.red
      (reduction_natCast_prime_eq_zero l W.red)
  show (thetaOf (chgGam W.unbar (W.g i) ((W.N.D i).map (PowerSeries.map W.red)))).charpoly = _
  rw [h3, hD', Matrix.charpoly_map, hcp, Polynomial.map_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    reduction_log_unit_pow_eq l W.red u c (r j) (U' i j) hu (hr j)]

theorem frobenius_mul_eq_X_pow_smul_one (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (u : ℤ_[l]ˣ) (U' : ι → Fin n → ℤ)
    (hN : LatW l W.N h u U') (i : ι) :
    ∃ M, W.Phi l σ i * M = ((X : F⟦X⟧) ^ h) • (1 : Matrix (Fin n) (Fin n) F⟦X⟧) := by
  obtain ⟨hP, -, -, -, -⟩ := hN
  obtain ⟨M, hM⟩ := hP i
  have hmap : (W.N.P i).map (PowerSeries.map W.red) * M.map (PowerSeries.map W.red) =
      ((X : F⟦X⟧) ^ h) • (1 : Matrix (Fin n) (Fin n) F⟦X⟧) := by
    rw [← Matrix.map_mul, hM]
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · simp only [mul_one, map_X_sub_C_prime_pow_eq_X_pow]
    · simp only [mul_zero, map_zero]
  exact (frobenius_base_change_holds F n l h (W.g i) (W.g (σ i)) _ (Fact.out : l.Prime).pos).1 ⟨_, hmap⟩

theorem minorsDvd_frobenius_of_sum_bound (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (u : ℤ_[l]ˣ) (U' : ι → Fin n → ℤ)
    (hN : LatW l W.N h u U') (i : ι) (r S : ℕ)
    (hS : ∀ J : Finset (Fin n), J.card = r → (S : ℤ) ≤ ∑ j ∈ J, U' i j) :
    MinorsDvd ((X : F⟦X⟧) ^ S) r (W.Phi l σ i) := by
  have h2 := (minors_divide_all_holds (O⟦X⟧) n n r _ _).1 (hN.2.1 i r S hS)
  apply (frobenius_base_change_holds F n l h _ _ _ (Fact.out : l.Prime).pos).2
  intro f g _ _
  exact (minor_reduction_holds O F W.red (l : O) n r S (W.N.P i) f g (reduction_natCast_prime_eq_zero l W.red)).2 (h2 f g)

theorem frobenius_diagonal_entry_eq_unit_mul (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ)
    (wt kap : ι → Fin t → ℤ) (hW : WInputs W σ l h u c U' wt kap) (i : ι) (s : Fin t) :
    0 ≤ (l : ℤ) * kap (σ i) s + wt i s - kap i s ∧
      ∃ u0 : (F⟦X⟧)ˣ, W.Phi l σ i (W.pos s) (W.pos s) =
        (u0 : F⟦X⟧) * X ^ ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat := by
  obtain ⟨⟨hu, -, -⟩, -, hwt, -, -, -, hPhiE, -⟩ := hW.1
  obtain ⟨⟨v, hv⟩, -⟩ := rank_one_model_holds ι l h O F W.red (W.Npsi s) u c (fun i => wt i s) hu
    (hW.2.2 s) i
  have hmv : PowerSeries.map W.red ((W.Npsi s).P i 0 0) =
      ((Units.map (PowerSeries.map W.red).toMonoidHom v : (F⟦X⟧)ˣ) : F⟦X⟧) * X ^ (wt i s).toNat := by
    rw [hv, map_mul, map_X_sub_C_prime_pow_eq_X_pow]
    rfl
  have heq := hPhiE i s
  rw [hmv] at heq
  obtain ⟨h1, u0, hu0⟩ := frobenius_diagonal_holds F l (wt i s).toNat _ _ (W.w i s) (W.w (σ i) s) (kap i s)
    (kap (σ i) s) (Fact.out : l.Prime).pos heq
  have hw : (((wt i s).toNat : ℕ) : ℤ) = wt i s := Int.toNat_of_nonneg (hwt i s).1
  rw [hw] at h1 hu0
  exact ⟨h1, u0, hu0⟩

theorem theta_diagonal_entry_eq (l h : ℕ) [Fact l.Prime] [IsDomain O] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ)
    (wt kap : ι → Fin t → ℤ) (hl2 : l ≠ 2) (hW : WInputs W σ l h u c U' wt kap) (i : ι)
    (s : Fin t) :
    thetaOf (W.Gam i) (W.pos s) (W.pos s) =
      -W.red (algebraMap ℤ_[l] O c) * ((wt i s - kap i s : ℤ) : F) := by
  obtain ⟨⟨hu, -, hun⟩, -, -, -, -, -, -, hGamE⟩ := hW.1
  obtain ⟨-, hD⟩ := rank_one_model_holds ι l h O F W.red (W.Npsi s) u c (fun i => wt i s) hu
    (hW.2.2 s) i
  obtain ⟨-, hcc1⟩ := theta_diagonal_holds F W.unbar (PowerSeries.map W.red ((W.Npsi s).D i 0 0))
    (W.Gam i (W.pos s) (W.pos s)) (W.w i s) (kap i s) (hGamE i s)
  obtain ⟨e, he⟩ := ((unit_series_constant_holds l O hl2 (u : ℤ_[l]) c hu).2 W.un hun).2
  show coeff 1 (W.Gam i (W.pos s) (W.pos s)) = _
  rw [hcc1]
  unfold WLat.unbar
  rw [constantCoeff_map_eq, constantCoeff_map_eq, hD, he, map_add, map_mul, map_natCast,
    CharP.cast_eq_zero, zero_mul, add_zero]
  push_cast
  ring

theorem alpha_bounds_hold : AlphaBounds := by
  intro ι _ σ l h t n _ O F _ _ _ _ _ W u c U' wt kap hl2 hW i s
  obtain ⟨h1, u0, hu0⟩ := frobenius_diagonal_entry_eq_unit_mul l h W σ u c U' wt kap hW i s
  refine ⟨h1, ?_⟩
  obtain ⟨M, hM⟩ := frobenius_mul_eq_X_pow_smul_one l h W σ u U' hW.2.1 i
  obtain ⟨-, -, -, ⟨-, hb⟩, hPhiT, -, -, -⟩ := hW.1
  have hline := block_height_on_line_holds (F⟦X⟧) X n h (W.Phi l σ i) M W.b (W.pos s) X_ne_zero
    (hPhiT i) hM (hb s)
  rw [hu0] at hline
  set e := (l : ℤ) * kap (σ i) s + wt i s - kap i s with he
  have hdvd : (X : F⟦X⟧) ^ e.toNat ∣ X ^ h :=
    ⟨u0 * M (W.pos s) (W.pos s), by rw [← hline]; ring⟩
  have hle : e.toNat ≤ h := by
    first
    | exact (pow_dvd_pow_iff X_ne_zero X_prime.not_unit).1 hdvd
    | exact (pow_dvd_pow_iff_le X_ne_zero X_prime.not_unit).1 hdvd
  have h2 : ((e.toNat : ℕ) : ℤ) ≤ (h : ℤ) := by exact_mod_cast hle
  linarith [Int.toNat_of_nonneg h1]

theorem weight_properties_of_inputs : WPropsOfInputs := by
  intro ι _ σ l h t n _ O F _ _ _ _ _ W u c U' bot kap cc hl2 hW hcc
  have hW' := hW
  obtain ⟨⟨⟨hu, hc, hun⟩, hU, hwt, ⟨hinj, hpos⟩, hΦ, hΓ, hcφ, hcγ⟩, hN, hψ⟩ := hW'
  refine ⟨reduction_algebraMap_unit_ne_zero l W.red c hc, hinj, hpos, ?_, ?_, ?_, hΦ, ?_, ?_⟩
  · intro i a b hab
    change coeff 1 (W.Gam i a b) = 0
    rw [hΓ i hab, map_zero]
  · intro i
    exact charpoly_theta_eq_prod l h W u c U' hu hN i
  · intro i s
    exact theta_diagonal_entry_eq l h W σ u c U' _ kap hl2 hW i s
  · intro i s
    exact (frobenius_diagonal_entry_eq_unit_mul l h W σ u c U' _ kap hW i s).2
  · intro i
    exact (minors_divide_all_holds (F⟦X⟧) n n t _ _).1
      (minorsDvd_frobenius_of_sum_bound l h W σ u U' hN i t (cc i) (hcc i)) W.pos W.pos

theorem weight_lemma_from_inputs : LemmaWFromInputs := by
  intro ι _ σ l h t n _ O F _ _ _ _ _ W u c U' bot kap hl2 hW
  classical
  have hα := alpha_bounds_hold ι σ l h t n O F W u c U' _ kap hl2 hW
  have hU := hW.1.2.1
  have hwt := hW.1.2.2.1
  have hmain : ∀ cc : ι → ℕ,
      (∀ i (J : Finset (Fin n)), J.card = t → (cc i : ℤ) ≤ ∑ j ∈ J, U' i j) → _ :=
    fun cc hcc => twisted_block_bounds ι σ l h t n F (W.toWData l c σ) U' bot kap cc Fact.out
      (weight_properties_of_inputs ι σ l h t n O F W u c U' bot kap cc hl2 hW hcc) hwt hα
  have h0 := hmain (fun _ => 0) (fun i J _ => by
    simpa using Finset.sum_nonneg fun j _ => (hU i j).1)
  refine ⟨h0.1, h0.2.1, ?_⟩
  intro i
  by_contra hcon
  push Not at hcon
  have hA0 : 0 ≤ ∑ s : Fin t, (bot i + ((s : ℕ) : ℤ) + (l : ℤ) * kap (σ i) s - kap i s) :=
    Finset.sum_nonneg fun s _ => by have := (hα i s).1; linarith
  generalize hA : ∑ s : Fin t, (bot i + ((s : ℕ) : ℤ) + (l : ℤ) * kap (σ i) s - kap i s) = A at *
  have h1 := (hmain (fun i' => if i' = i then A.toNat + 1 else 0) (by
    intro i' J hJ
    by_cases hi : i' = i
    · subst hi
      have := hcon J hJ
      simp only [if_true]
      push_cast
      rw [Int.toNat_of_nonneg hA0]
      omega
    · simpa [hi] using Finset.sum_nonneg fun j _ => (hU i' j).1)).2.2 i
  rw [hA] at h1
  simp only [if_true] at h1
  push_cast at h1
  rw [Int.toNat_of_nonneg hA0] at h1
  omega

theorem weight_lemma_full : LemmaWFull := by
  intro ι _ σ l h t n _ O F _ _ _ _ _ W u c U' wt kap hl2 hW
  classical
  have hα := alpha_bounds_hold ι σ l h t n O F W u c U' wt kap hl2 hW
  have hW' := hW
  obtain ⟨⟨⟨hu, hc, hun⟩, hU, hwt, ⟨hinj, hpos⟩, hΦ, hΓ, hcφ, hcγ⟩, hN, hψ⟩ := hW'
  have hlp : l.Prime := Fact.out
  refine ⟨?_, ?_, ?_⟩
  · intro i s
    exact shiftBound_holds ι σ l h (fun i => kap i s) (fun i => wt i s) hlp.two_le
      (fun i => hwt i s) (fun i => hα i s) i
  · intro i
    have hΘ : (thetaOf (W.Gam i)).BlockTriangular W.b := by
      intro a b hab
      change coeff 1 (W.Gam i a b) = 0
      rw [hΓ i hab, map_zero]
    have h1 := charpolyDiagBlocks_holds F n (thetaOf (W.Gam i)) W.b (Finset.univ.image W.pos)
      (fun j => -W.red (algebraMap ℤ_[l] O c) * ((U' i j : ℤ) : F)) hΘ
      (by
        intro s hs' j hj
        obtain ⟨s0, _, rfl⟩ := Finset.mem_image.mp hs'
        exact hpos s0 j hj) (charpoly_theta_eq_prod l h W u c U' hu hN i)
    rw [Finset.image_val_of_injOn hinj.injOn, Multiset.map_map] at h1
    apply map_cast_le_of_map_neg_mul_le l hlp F (W.red (algebraMap ℤ_[l] O c)) (reduction_algebraMap_unit_ne_zero l W.red c hc)
    have e : ((fun s => thetaOf (W.Gam i) s s) ∘ W.pos) =
        fun s : Fin t => -W.red (algebraMap ℤ_[l] O c) * ((wt i s - kap i s : ℤ) : F) := by
      funext s
      exact theta_diagonal_entry_eq l h W σ u c U' wt kap hl2 hW i s
    rw [e] at h1
    exact h1
  · intro ν hν i
    have hI : Function.Injective (fun s => W.b (W.pos s)) :=
      fun x y hxy => hinj (hpos y (W.pos x) hxy)
    generalize hch : Finset.univ.image (fun s => W.b (W.pos s)) = ch at *
    generalize hm : ∑ r ∈ Finset.univ.image W.b \ ch, ν r = m at *
    by_contra hcon
    push Not at hcon
    have hA0 : 0 ≤ ∑ s : Fin t, (wt i s + (l : ℤ) * kap (σ i) s - kap i s) + ((m : ℕ) : ℤ) * h := by
      refine add_nonneg (Finset.sum_nonneg fun s _ => ?_) (by positivity)
      have := (hα i s).1; linarith
    generalize hA : ∑ s : Fin t, (wt i s + (l : ℤ) * kap (σ i) s - kap i s) + ((m : ℕ) : ℤ) * h = A
      at *
    have hmin := minorsDvd_frobenius_of_sum_bound l h W σ u U' hN i (t + m) (A.toNat + 1) (fun J hJ => by
      have := hcon J hJ
      push_cast
      rw [Int.toNat_of_nonneg hA0]
      omega)
    let al : ℕ → ℕ := fun r => if hr : ∃ s, W.b (W.pos s) = r then
      ((l : ℤ) * kap (σ i) (Classical.choose hr) + wt i (Classical.choose hr) -
        kap i (Classical.choose hr)).toNat else 0
    have hal : ∀ s, al (W.b (W.pos s)) = ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat := by
      intro s
      have hr : ∃ s', W.b (W.pos s') = W.b (W.pos s) := ⟨s, rfl⟩
      simp only [al, dif_pos hr]
      rw [hI (Classical.choose_spec hr)]
    have hcard : ch.card = t := by
      rw [← hch, Finset.card_image_of_injective _ hI]; simp
    obtain ⟨M, hM⟩ := frobenius_mul_eq_X_pow_smul_one l h W σ u U' hN i
    have hbl := (block_height_holds (F⟦X⟧) X n h (W.Phi l σ i) M W.b X_ne_zero (hΦ i) hM).2
    have h1 := minor_bound_extra_holds (F⟦X⟧) X n h (A.toNat + 1) (W.Phi l σ i) W.b ch al ν X_prime
      (hΦ i)
      (by
        rw [← hch]
        intro r hr
        obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hr
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _))
      (by
        intro r hr
        rw [← hch] at hr
        obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hr
        refine ⟨W.pos s, fun j => ⟨hpos s j, fun h0 => by rw [h0]⟩, ?_⟩
        rw [hal s]
        exact (frobenius_diagonal_entry_eq_unit_mul l h W σ u c U' wt kap hW i s).2)
      (fun r hr => ⟨⟨_, hbl r⟩, hν r hr⟩)
      (by rw [hcard, hm]; exact hmin)
    have hsum : ∑ r ∈ ch, al r = ∑ s : Fin t, ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat := by
      rw [← hch, Finset.sum_image (fun x _ y _ hxy => hI hxy)]
      exact Finset.sum_congr rfl fun s _ => hal s
    rw [hsum, hm] at h1
    have h2 : ((∑ s : Fin t, ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat : ℕ) : ℤ) =
        ∑ s : Fin t, (wt i s + (l : ℤ) * kap (σ i) s - kap i s) := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Int.toNat_of_nonneg (hα i s).1]; ring
    have h3 : ((A.toNat + 1 : ℕ) : ℤ) ≤ ((∑ s : Fin t,
        ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat + m * h : ℕ) : ℤ) := by exact_mod_cast h1
    push_cast at h3 h2
    rw [h2, hA, Int.toNat_of_nonneg hA0] at h3
    omega

theorem sum_tail_le_sum_of_antitone {N : ℕ} (f : Fin N → ℤ) (hf : Antitone f) (m : ℕ) (J : Finset (Fin N))
    (hJ : J.card = (Finset.univ.filter fun a : Fin N => m ≤ (a : ℕ)).card) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin N => m ≤ (a : ℕ)), f a ≤ ∑ a ∈ J, f a := by
  set T := Finset.univ.filter (fun a : Fin N => m ≤ (a : ℕ)) with hT
  rcases Nat.lt_or_ge m N with hmN | hmN
  · set v := f ⟨m, hmN⟩
    have h1 : ∀ x ∈ T \ J, f x ≤ v := by
      intro x hx
      have hx1 : m ≤ (x : ℕ) := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hx).1).2
      exact hf (show (⟨m, hmN⟩ : Fin N) ≤ x from hx1)
    have h2 : ∀ x ∈ J \ T, v ≤ f x := by
      intro x hx
      have hx2 : ¬ m ≤ (x : ℕ) := fun h =>
        (Finset.mem_sdiff.1 hx).2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      exact hf (show x ≤ (⟨m, hmN⟩ : Fin N) from by show (x : ℕ) ≤ m; omega)
    have hc : (T \ J).card = (J \ T).card := by
      have e1 := Finset.card_sdiff_add_card_inter T J
      have e2 := Finset.card_sdiff_add_card_inter J T
      rw [Finset.inter_comm] at e2
      omega
    have s1 := Finset.sum_le_card_nsmul (T \ J) f v h1
    have s2 := Finset.card_nsmul_le_sum (J \ T) f v h2
    rw [hc] at s1
    rw [nsmul_eq_mul] at s1 s2
    have split : ∀ S U : Finset (Fin N), ∑ x ∈ S \ U, f x + ∑ x ∈ S ∩ U, f x = ∑ x ∈ S, f x := by
      intro S U
      first
      | exact Finset.sum_sdiff_add_sum_inter S U f
      | (rw [add_comm]; exact Finset.sum_inter_add_sum_diff S U f)
      | (rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S U), Finset.sdiff_union_inter])
    have e3 := split T J
    have e4 := split J T
    rw [Finset.inter_comm] at e4
    linarith
  · have hT0 : T = ∅ := Finset.filter_eq_empty_iff.2 (fun x _ => by have := x.2; omega)
    have hJ0 : J = ∅ := Finset.card_eq_zero.1 (by rw [hJ, hT0, Finset.card_empty])
    rw [hT0, hJ0]

theorem card_filter_le_val_eq_sub (N m : ℕ) (hm : m ≤ N) :
    (Finset.univ.filter fun a : Fin N => m ≤ (a : ℕ)).card = N - m := by
  have hm2 : (Finset.univ.filter fun a : Fin N => m ≤ (a : ℕ)).map Fin.valEmbedding =
      Finset.Ico m N := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨a, h1, rfl⟩
      exact ⟨h1, a.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hm2, Nat.card_Ico]

theorem weight_exponents_from_inputs : WEFromInputs := by
  intro ι _ σ k j t q l h _ O F _ _ _ _ _ W u c U U' bot cst kap τ hl2 hsmall hW hU hU' hblock hlink
    hU0 hsum hrows
  classical
  have hα := alpha_bounds_hold ι σ l h t _ O F W u c U' _ kap hl2 hW
  have hH1 := hW.1.2.1
  have hwt := hW.1.2.2.1
  have hT0 : 0 ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)),
      U' τ a := Finset.sum_nonneg fun a _ => (hH1 τ a).1
  have hcard := card_filter_le_val_eq_sub (k + j + t + q) (k + j + q) (by omega)
  refine weightExchangeFull_holds ι σ k j t q l h F (W.toWData l c σ) U U' bot cst kap
    (fun i => if i = τ then (∑ a ∈ Finset.univ.filter
      (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' τ a).toNat else 0) τ Fact.out hsmall
    (weight_properties_of_inputs ι σ l h t _ O F W u c U' bot kap _ hl2 hW ?_) hwt hα hU hU' hblock hlink
    hU0 (hH1 τ) hsum hrows ?_
  · intro i J hJ
    by_cases hi : i = τ
    · subst hi
      simp only [if_true]
      rw [Int.toNat_of_nonneg hT0]
      exact sum_tail_le_sum_of_antitone (U' i) (hU' i).antitone _ J (by rw [hJ, hcard]; omega)
    · simpa [hi] using Finset.sum_nonneg fun a _ => (hH1 i a).1
  · simp only [if_true]
    rw [Int.toNat_of_nonneg hT0]

end Five

theorem order_descent_holds : OrderDescent := by
  intro O _ _ I _ x L _ _ em jj hx hem hC hX S
  obtain ⟨w, hw⟩ := hX
  have hj : jj (X - C x) = X * ((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧) := by
    rw [← hw, mul_assoc, Units.mul_inv, mul_one]
  induction S with
  | zero => intro m _; simp
  | succ S ih =>
    intro m hm
    obtain ⟨f₁, a, rfl⟩ := (linear_division_holds O I x hx).1 m
    have h1 : (X : L⟦X⟧) ∣ jj ((X - C x) * f₁ + C a) :=
      dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero S)) hm
    rw [map_add, map_mul, hj, hC] at h1
    have h2 : (X : L⟦X⟧) ∣ C (em a) :=
      (dvd_add_right ((dvd_mul_right _ _).mul_right _)).1 h1
    have h3 : em a = 0 := by
      have := PowerSeries.X_dvd_iff.1 h2
      simpa using this
    have h4 : a = 0 := hem (by simpa using h3)
    subst h4
    rw [map_add, map_mul, hj, map_zero, map_zero, add_zero, pow_succ', mul_assoc] at hm
    have h5 : (X : L⟦X⟧) ^ S ∣ ((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧) * jj f₁ :=
      (mul_dvd_mul_iff_left PowerSeries.X_ne_zero).1 hm
    rw [Units.dvd_mul_left] at h5
    rw [map_zero, add_zero, pow_succ']
    exact mul_dvd_mul_left _ (ih f₁ h5)

def pi0SubstHom (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] :
    O⟦X⟧ →+* O⟦X⟧ :=
  (substAlgHom (hasSubst_pi0_alt l O) : O⟦X⟧ →ₐ[O] O⟦X⟧).toRingHom

theorem pi0SubstHom_apply (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (f : O⟦X⟧) : pi0SubstHom l O f = inc l O f := by
  first
  | rfl
  | exact congrFun (coe_substAlgHom (hasSubst_pi0_alt l O)) f

theorem pi0Subst_C (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (a : O) :
    inc l O (C a) = C a := by
  unfold inc
  rw [subst_C]
  rfl

theorem coe_comp_pi0SubstHom (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] {L : Type}
    [CommRing L] (jj : O⟦X⟧ →+* L⟦X⟧) :
    (⇑(jj.comp (pi0SubstHom l O))) = fun y => jj (inc l O y) := by
  funext y
  rw [RingHom.comp_apply, pi0SubstHom_apply]

theorem pi0Subst_det_map (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] {L : Type}
    [CommRing L] (jj : O⟦X⟧ →+* L⟦X⟧) {t : ℕ} (M : Matrix (Fin t) (Fin t) O⟦X⟧) :
    jj (inc l O M.det) = (M.map (fun y => jj (inc l O y))).det := by
  have h2 := RingHom.map_det (jj.comp (pi0SubstHom l O)) M
  rw [RingHom.mapMatrix_apply, coe_comp_pi0SubstHom] at h2
  exact h2

theorem localization_facts_hold : LocFacts := by
  intro l _ O L _ _ _ _ I ζ em u b jj hl2 hζ hζI hem hb hloc
  obtain ⟨hC, hX, -⟩ := hloc
  obtain ⟨w, hw⟩ := hX
  have hj : jj (X - C (ζ ^ b - 1)) = X * ((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧) := by
    rw [← hw, mul_assoc, Units.mul_inv, mul_one]
  have hbI : ζ ^ b - 1 ∈ I := by
    have h1 : ζ ^ b - 1 = (ζ - 1) * ∑ i ∈ Finset.range b, ζ ^ i := (mul_geom_sum ζ b).symm
    rw [h1]
    exact I.mul_mem_right _ hζI
  have hlI : (l : O) ∈ I := by
    obtain ⟨s, hs⟩ := r3_divisibility_holds l O ζ hl2 hζ b hb
    have h2 := congrArg constantCoeff hs
    rw [map_sub, map_mul, map_sub, constantCoeff_pi0 l O, constantCoeff_C, constantCoeff_C,
      constantCoeff_X] at h2
    have h3 : (l : O) = (ζ ^ b - 1) * constantCoeff s := by linear_combination -h2
    rw [h3]
    exact I.mul_mem_right _ hbI
  have hl0 : (l : O) ≠ 0 := by
    have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    exact (hζ.neZero').out

  have hq0 : ∃ z : L⟦X⟧, IsUnit z ∧ jj (q0 l O) = X * z := by
    obtain ⟨g, hg, -⟩ := r3_unit_holds l O hl2
    have hq := q_roots_holds l O ζ hζ
    have hU : IsUnit (∏ b' ∈ (Finset.Ioo 0 l).erase b, jj (X - C (ζ ^ b' - 1))) := by
      refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one ?_
      intro b' hb'
      rw [Finset.mem_erase] at hb'
      rw [PowerSeries.isUnit_iff_constantCoeff]
      have e : (X - C (ζ ^ b' - 1) : O⟦X⟧) = (X - C (ζ ^ b - 1)) + C (ζ ^ b - ζ ^ b') := by
        rw [map_sub, map_sub, map_sub]; ring
      rw [e, map_add, hj, hC, map_add, map_mul, constantCoeff_X, zero_mul, zero_add,
        constantCoeff_C]
      refine IsUnit.mk0 _ ?_
      intro h0
      have h1 : ζ ^ b - ζ ^ b' = 0 := hem (by rw [h0, map_zero])
      have h2 : b = b' := hζ.pow_inj (Finset.mem_Ioo.1 hb).2 (Finset.mem_Ioo.1 hb'.2).2
        (sub_eq_zero.1 h1)
      exact hb'.1 h2.symm
    refine ⟨((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧) * (jj (g : O⟦X⟧) *
      ∏ b' ∈ (Finset.Ioo 0 l).erase b, jj (X - C (ζ ^ b' - 1))), ?_, ?_⟩
    · exact (Units.isUnit _).mul (((Units.isUnit g).map jj).mul hU)
    · rw [hg, hq, map_mul, map_prod, ← Finset.mul_prod_erase _ _ hb, hj]
      ring
  obtain ⟨z, hz, hzq⟩ := hq0
  refine ⟨hlI, hl0, ?_, ?_⟩
  · rw [hzq]
    exact associated_mul_unit_left _ _ hz
  · intro y a hya
    obtain ⟨s, hs⟩ := hya
    have hy : y = (X - C (l : O)) * s + C a := by linear_combination hs
    rw [hy, ← pi0SubstHom_apply, map_add, map_mul, pi0SubstHom_apply, pi0SubstHom_apply,
      pi0SubstHom_apply, inc_X_sub_l_eq_q0, pi0Subst_C, map_add, map_mul, hzq, hC, map_add, map_mul,
      map_mul, constantCoeff_X, zero_mul, zero_mul, zero_add, constantCoeff_C]

theorem one_add_X_smul_sub_C_dvd {O : Type} [CommRing O] (lam : O) {n : ℕ}
    (D : Matrix (Fin n) (Fin n) O⟦X⟧) (Th : Matrix (Fin n) (Fin n) O)
    (h : ∀ a b, (X - C lam) ∣ D a b - C (Th a b)) (a b : Fin n) :
    (X - C lam) ∣ (1 + (X : O⟦X⟧) • D) a b - C ((1 + lam • Th) a b) := by
  exact gamma_mod_q_holds O lam n D Th h a b

theorem constantCoeff_conj_diagonal_rescale {L : Type} [Field L] {n : ℕ} (Γ G : Matrix (Fin n) (Fin n) L⟦X⟧) (υ : L)
    (a : Fin n → ℕ)
    (h : Γ * (G * Matrix.diagonal (fun j => (X : L⟦X⟧) ^ a j)).map (rescale υ) =
      G * Matrix.diagonal (fun j => (X : L⟦X⟧) ^ a j)) :
    Γ.map constantCoeff * G.map constantCoeff * Matrix.diagonal (fun j => υ ^ a j) =
      G.map constantCoeff := by
  have hr0 : ∀ f : L⟦X⟧, constantCoeff (rescale υ f) = constantCoeff f := fun f => by
    rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale,
      pow_zero, one_mul]
  have hD : (Matrix.diagonal (fun j => (X : L⟦X⟧) ^ a j)).map (rescale υ) =
      Matrix.diagonal (fun j => C (υ ^ a j) * (X : L⟦X⟧) ^ a j) := by
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext j
    simp only [map_pow, rescale_X, mul_pow]
  rw [Matrix.map_mul, hD, ← Matrix.mul_assoc] at h
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal] at hij
  have hX : (X : L⟦X⟧) ^ a j ≠ 0 := pow_ne_zero _ X_ne_zero
  have h2 : (Γ * G.map (rescale υ)) i j * C (υ ^ a j) = G i j := by
    apply mul_right_cancel₀ hX
    rw [mul_assoc, hij]
  have h3 := congrArg constantCoeff h2
  rw [map_mul, constantCoeff_C, Matrix.mul_apply, map_sum] at h3
  rw [Matrix.mul_diagonal, Matrix.map_apply, ← h3, Matrix.mul_apply]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, hr0]

theorem weight_lattice_of_norm : LatWOfN := by
  intro ι l h n _ O L _ _ _ _ I _ ζ em jj N u c U' hl2 hu hζ hζI hem hloc hU hN
  obtain ⟨hP5, hTh, hloc4⟩ := hN
  have hl3 : 1 ∈ Finset.Ioo 0 l := by
    have := (Fact.out : l.Prime).two_le
    rw [Finset.mem_Ioo]; omega
  have hsum : ∀ i (J : Finset (Fin n)),
      ((∑ j ∈ J, (U' i j).toNat : ℕ) : ℤ) = ∑ j ∈ J, U' i j := by
    intro i J
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun j _ => Int.toNat_of_nonneg (hU i j))
  have hW1 : ∀ i, ∃ M : Matrix (Fin n) (Fin n) O⟦X⟧,
      N.P i * M = ((X - C (l : O)) ^ h) • (1 : Matrix (Fin n) (Fin n) O⟦X⟧) := by
    intro i
    obtain ⟨Q, hQ⟩ := hP5 i
    exact height_descent_holds l O hl2 n h (N.P i) Q hQ
  obtain ⟨hlI, hl0, hq0X, hev⟩ :=
    localization_facts_hold l O L I ζ em (u : ℤ_[l]) 1 (jj 1) hl2 hζ hζI hem hl3 (hloc 1 hl3)
  refine ⟨hW1, ?_, ?_, hTh, ?_⟩
  ·
    intro i r S hS f g hf hg
    obtain ⟨m', hm'⟩ := roots_descent_holds l O I ζ hl2 hζ hζI S ((N.P i).submatrix f g).det (by
      intro b hb
      have hbI : ζ ^ b - 1 ∈ I := by
        have h1 : ζ ^ b - 1 = (ζ - 1) * ∑ i ∈ Finset.range b, ζ ^ i := (mul_geom_sum ζ b).symm
        rw [h1]
        exact I.mul_mem_right _ hζI
      obtain ⟨hC, hX, -⟩ := hloc b hb
      refine order_descent_holds O I (ζ ^ b - 1) L em (jj b) hbI hem hC hX S _ ?_
      obtain ⟨G, H, hGH, -⟩ := hloc4 i b hb
      rw [pi0Subst_det_map, ← Matrix.submatrix_map, hGH]
      refine diagonal_minors_holds L⟦X⟧ n r S X (fun a => (U' i a).toNat) G H ?_ f g hf hg
      intro J hJ
      have h1 := hS J hJ
      rw [← hsum i J] at h1
      exact_mod_cast h1)
    exact ⟨m', hm'⟩
  ·
    intro i
    obtain ⟨M, hM⟩ := hW1 i
    have hdet := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← pow_mul]
      at hdet
    have hp : Prime (X - C (l : O) : O⟦X⟧) := linear_prime_holds O I (l : O) hlI
    obtain ⟨e, -, hass⟩ := (dvd_prime_pow hp (h * n)).1 ⟨M.det, hdet.symm⟩
    obtain ⟨G, H, hGH, -⟩ := hloc4 i 1 hl3
    have h1 : Associated ((jj 1).comp (pi0SubstHom l O) (N.P i).det)
        ((jj 1).comp (pi0SubstHom l O) ((X - C (l : O)) ^ e)) := hass.map _
    rw [RingHom.comp_apply, RingHom.comp_apply, pi0SubstHom_apply, pi0SubstHom_apply,
      inc_pow, inc_X_sub_l_eq_q0, map_pow, pi0Subst_det_map, hGH, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum] at h1
    have hG : IsUnit (G : Matrix (Fin n) (Fin n) L⟦X⟧).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 G.isUnit
    have hH : IsUnit (H : Matrix (Fin n) (Fin n) L⟦X⟧).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 H.isUnit
    have h2 : Associated ((X : L⟦X⟧) ^ (∑ j, (U' i j).toNat))
        ((G : Matrix (Fin n) (Fin n) L⟦X⟧).det * X ^ (∑ j, (U' i j).toNat) *
          (H : Matrix (Fin n) (Fin n) L⟦X⟧).det) :=
      ((associated_mul_unit_left _ _ hH).trans (associated_unit_mul_left _ _ hG)).symm
    have h3 : Associated ((X : L⟦X⟧) ^ (∑ j, (U' i j).toNat)) ((X : L⟦X⟧) ^ e) :=
      (h2.trans h1).trans (hq0X.pow_pow)
    have hXu : ¬ IsUnit (X : L⟦X⟧) := PowerSeries.X_prime.not_isUnit
    have h4 : ∑ j, (U' i j).toNat = e :=
      le_antisymm ((pow_dvd_pow_iff X_ne_zero hXu).1 h3.dvd)
        ((pow_dvd_pow_iff X_ne_zero hXu).1 h3.symm.dvd)
    have h5 : (∑ j, U' i j).toNat = e := by
      rw [← hsum i Finset.univ, Int.toNat_natCast, h4]
    rw [h5]
    obtain ⟨v, hv⟩ := hass.symm
    exact ⟨v, by rw [← hv, mul_comm]⟩
  ·
    intro i
    choose e he using fun j => theta_congruence_padic l u c (U' i j) hu
    refine ⟨fun j => -(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j, he, ?_⟩
    obtain ⟨G, H, -, hγ⟩ := hloc4 i 1 hl3
    have hk := constantCoeff_conj_diagonal_rescale _ _ _ _ hγ
    have hA : ((1 + (X : O⟦X⟧) • N.D i).map (fun y => jj 1 (inc l O y))).map constantCoeff =
        (1 + (l : O) • N.Th i).map em := by
      ext1 x y
      rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
      exact hev _ _ (one_add_X_smul_sub_C_dvd (l : O) (N.D i) (N.Th i) (hTh i) x y)
    rw [hA] at hk
    have hunit : ∀ j, (u : ℤ_[l]) ^ (U' i j).toNat *
        (1 + (l : ℤ_[l]) * (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j)) = 1 := by
      intro j
      rw [← he j, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
      have : u ^ (U' i j).toNat * u ^ (-(U' i j)) = 1 := by
        rw [← zpow_natCast, Int.toNat_of_nonneg (hU i j), ← zpow_add, add_neg_cancel, zpow_zero]
      rw [this, Units.val_one]
    let G0 : (Matrix (Fin n) (Fin n) L)ˣ :=
      Units.map (RingHom.mapMatrix (constantCoeff (R := L))).toMonoidHom G
    have hG0 : (G0 : Matrix (Fin n) (Fin n) L) =
        (G : Matrix (Fin n) (Fin n) L⟦X⟧).map constantCoeff := rfl
    refine charpoly_diagonal_holds O L em n (N.Th i) (1 + (l : O) • N.Th i) (l : O)
      (fun j => algebraMap ℤ_[l] O (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j)) G0 hem hl0
      rfl ?_
    rw [hG0]
    have hdd : Matrix.diagonal (fun j => em (algebraMap ℤ_[l] O (u : ℤ_[l])) ^ (U' i j).toNat) *
        Matrix.diagonal (fun j => em (1 + (l : O) *
          algebraMap ℤ_[l] O (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j))) =
        (1 : Matrix (Fin n) (Fin n) L) := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext j
      have := congrArg (fun z => em (algebraMap ℤ_[l] O z)) (hunit j)
      simp only [map_mul, map_pow, map_add, map_one, map_natCast] at this
      simp only [map_mul, map_add, map_one, map_natCast]
      exact this
    calc (1 + (l : O) • N.Th i).map em * (G : Matrix (Fin n) (Fin n) L⟦X⟧).map constantCoeff
        = (1 + (l : O) • N.Th i).map em * (G : Matrix (Fin n) (Fin n) L⟦X⟧).map constantCoeff *
            (Matrix.diagonal (fun j => em (algebraMap ℤ_[l] O (u : ℤ_[l])) ^ (U' i j).toNat) *
            Matrix.diagonal (fun j => em (1 + (l : O) *
              algebraMap ℤ_[l] O (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j)))) := by
          rw [hdd, Matrix.mul_one]
      _ = (G : Matrix (Fin n) (Fin n) L⟦X⟧).map constantCoeff *
            Matrix.diagonal (fun j => em (1 + (l : O) *
              algebraMap ℤ_[l] O (-(((U' i j : ℤ) : ℤ_[l]) * c) + (l : ℤ_[l]) * e j))) := by
          rw [← Matrix.mul_assoc, hk]

theorem weight_inputs_of_norm : WInputsOfN := by
  intro ι σ l h t n _ O F L _ _ _ _ _ I _ W u c U' wt kap ζ em jj hl2 hN
  obtain ⟨hF, ⟨hζ, hζI, hem, hloc⟩, hNN, hNpsi⟩ := hN
  exact ⟨hF, weight_lattice_of_norm ι l h n O L I ζ em jj W.N u c U' hl2 hF.1.1 hζ hζI hem hloc
      (fun i a => (hF.2.1 i a).1) hNN,
    fun s => weight_lattice_of_norm ι l h 1 O L I ζ em jj (W.Npsi s) u c _ hl2 hF.1.1 hζ hζI hem hloc
      (fun i _ => (hF.2.2.1 i s).1) (hNpsi s)⟩

theorem weight_lemma_from_lattice : LemmaWFromLattice := by
  intro ι _ σ l h t n _ O F L _ _ _ _ _ _ I _ W u c U' wt kap ζ em jj hl2 hN
  have hW := weight_inputs_of_norm ι σ l h t n O F L I W u c U' wt kap ζ em jj hl2 hN
  obtain ⟨h1, h2, h3⟩ := weight_lemma_full ι σ l h t n O F W u c U' wt kap hl2 hW
  exact ⟨alpha_bounds_hold ι σ l h t n O F W u c U' wt kap hl2 hW, h1, h2, h3⟩

theorem weight_exponents_from_lattice : WEFromLattice := by
  intro ι _ σ k j t q l h _ O F L _ _ _ _ _ _ I _ W u c U U' bot cst kap τ ζ em jj hl2 hlt hN
  exact weight_exponents_from_inputs ι σ k j t q l h O F W u c U U' bot cst kap τ hl2 hlt
    (weight_inputs_of_norm ι σ l h t (k + j + t + q) O F L I W u c U'
      (fun i s => bot i + ((s : ℕ) : ℤ)) kap ζ em jj hl2 hN)

end Formalism.CohomologicalDescent.FrobeniusPeriodChange
