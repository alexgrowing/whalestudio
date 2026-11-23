import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.CosetOrth.Cong

theorem count_coe_ne_zero_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {J : Ideal (𝓞 E)}
    (hJ : J ≠ ⊥) : FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 ↔ J ≤ w.asIdeal := by
  rw [FractionalIdeal.count_coe E w hJ, Nat.cast_ne_zero, Associates.count_ne_zero_iff_dvd hJ w.irreducible,
    Ideal.dvd_iff_le]

theorem val_le_one_of_mul_eq_one {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) K) (hHG : H * G = 1) (hH : ∀ i j, v ((1 - H) i j) < 1) (i j : Fin n) : v (G i j) ≤ 1 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun k => v (G k j)) ⟨i, Finset.mem_univ _⟩
  refine (hp i (Finset.mem_univ _)).trans ?_
  by_contra hlt
  rw [not_le] at hlt
  have h0 : v (G p j) ≠ 0 := (zero_lt_one.trans hlt).ne'
  have e : G = 1 + (1 - H) * G := by rw [sub_mul, hHG, one_mul]; abel
  have e2 : G p j = (1 : Matrix (Fin n) (Fin n) K) p j + ∑ k, (1 - H) p k * G k j := by
    conv_lhs => rw [e]
    rw [Matrix.add_apply, Matrix.mul_apply]
  have h1 : v ((1 : Matrix (Fin n) (Fin n) K) p j) < v (G p j) := by
    refine lt_of_le_of_lt ?_ hlt
    rw [Matrix.one_apply]; split_ifs <;> simp
  have h2 : v (∑ k, (1 - H) p k * G k j) < v (G p j) := by
    refine v.map_sum_lt h0 fun k _ => ?_
    rw [map_mul]
    calc v ((1 - H) p k) * v (G k j) ≤ v ((1 - H) p k) * v (G p j) := by
          gcongr; exact hp k (Finset.mem_univ _)
      _ < 1 * v (G p j) := mul_lt_mul_of_pos_right (hH p k) (zero_lt_one.trans hlt)
      _ = _ := one_mul _
  have := v.map_add_lt h1 h2
  rw [← e2] at this
  exact lt_irrefl _ this

variable {D : D7}

def evAt (w : HeightOneSpectrum (𝓞 D.host.E)) : FA D →+* w.adicCompletion D.host.E where
  toFun x := x w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem inv_apply {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) (i j : Fin n) :
    (((y⁻¹ : Formalism.MainNotions.StandardLatticesGL3.GA D n) : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j =
      Formalism.MainNotions.StandardLatticesGL3.sgA D (((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) j i) := by
  have hh : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (y.1 : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * y.1 = 1 := by
    have h2 := y.2
    change Formalism.UG.cT _ (y.1 : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * _ * _ = _ at h2
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  rw [Subgroup.coe_inv, Units.inv_eq_of_mul_eq_one_left hh]
  rfl

theorem finMat_inv_mul {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) : finMat y⁻¹ * finMat y = 1 := by
  unfold finMat
  have := (Matrix.map_mul (f := GlobalTheory.BotFormula.toFinE D)
    (L := (((y⁻¹ : Formalism.MainNotions.StandardLatticesGL3.GA D n) : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)))
    (M := ((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)))).symm
  rw [this, Subgroup.coe_inv, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem val_one_le {n : ℕ} (i j : Fin n) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Valued.v ((1 : Matrix (Fin n) (Fin n) (FA D)) i j w) ≤ 1 := by
  change Valued.v (evAt w ((1 : Matrix (Fin n) (Fin n) (FA D)) i j)) ≤ 1
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem val_sub_le {x y : FA D} {w : HeightOneSpectrum (𝓞 D.host.E)} (hx : Valued.v (x w) ≤ 1) (hy : Valued.v (y w) ≤ 1) :
    Valued.v ((x - y) w) ≤ 1 := by
  change Valued.v (evAt w (x - y)) ≤ 1
  rw [map_sub]
  exact (Valued.v.map_sub _ _).trans (max_le hx hy)

theorem integral_of_cong {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) (w : HeightOneSpectrum (𝓞 D.host.E))
    (h : ∀ i j, Valued.v ((1 - finMat y⁻¹) i j w) < 1) (i j : Fin n) :
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
  constructor
  · refine val_le_one_of_mul_eq_one Valued.v ((finMat y).map (evAt w)) ((finMat y⁻¹).map (evAt w)) ?_ (fun a b => ?_) i j
    · rw [← Matrix.map_mul, finMat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · have : (1 - (finMat y⁻¹).map (evAt w)) a b = evAt w ((1 - finMat y⁻¹) a b) := by
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [this]; exact h a b
  · have : finMat y⁻¹ i j = (1 : Matrix (Fin n) (Fin n) (FA D)) i j - (1 - finMat y⁻¹) i j := by
      rw [Matrix.sub_apply, sub_sub_cancel]
    rw [this]
    exact val_sub_le (val_one_le i j w) (h i j).le

theorem inHat_of_inv_cong : ∀ {D : D7}, (∀ w : HeightOneSpectrum (𝓞 D.host.E), ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal = D.host.conj • w.asIdeal ∧
    (∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D, Valued.v (GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D x) w') = Valued.v (GlobalTheory.BotFormula.toFinE D x w)) ∧
    (∀ 𝔞 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → FractionalIdeal.count D.host.E w' ((D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      FractionalIdeal.count D.host.E w (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ∧
    ∀ w'' : HeightOneSpectrum (𝓞 D.host.E), w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ↔ w'' = w ∨ w'' = w') →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)), GoodMod D 𝔪 Sf → ∀ {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n),
  (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sf → ∀ i j,
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1) →
  (∀ w : HeightOneSpectrum (𝓞 D.host.E), D.host.conj • 𝔪 ≤ w.asIdeal → ∀ i j,
    Valued.v ((1 - finMat y⁻¹) i j w) ≤ WithZero.exp (-(FractionalIdeal.count D.host.E w
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)))) →
  ∀ i j, InHat 1 (finMat y i j) ∧ InHat 1 (finMat y⁻¹ i j) ∧
    InHat (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ((finMat y - 1) i j) := by
  intro D hc 𝔪 Sf hG n y hoff hcong
  obtain ⟨h0, hsup, -, hS⟩ := hG
  have h0' : D.host.conj • 𝔪 ≠ ⊥ := fun h => h0 (by
    have := congrArg (fun I => D.host.conj⁻¹ • I) h
    simpa using this)
  have hb : ∀ w : HeightOneSpectrum (𝓞 D.host.E), D.host.conj • 𝔪 ≤ w.asIdeal → ∀ i j,
      Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
    intro w hw
    refine integral_of_cong y w fun i j => (hcong w hw i j).trans_lt ?_
    have h1 := (count_coe_ne_zero_iff w h0').2 hw
    have h2 := FractionalIdeal.count_coe_nonneg D.host.E w (D.host.conj • 𝔪)
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have key : ∀ w : HeightOneSpectrum (𝓞 D.host.E), ∀ i j, Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 ∧
      Valued.v ((finMat y - 1) i j w) ≤ WithZero.exp (-(FractionalIdeal.count D.host.E w
        (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))) := by
    intro w i j
    by_cases hw : 𝔪 ≤ w.asIdeal
    · obtain ⟨w', e', hv, hcnt, -⟩ := hc w
      have hw' : D.host.conj • 𝔪 ≤ w'.asIdeal := by
        rw [e']; exact Ideal.pointwise_smul_le_pointwise_smul_iff.2 hw
      have t : ∀ (z : Formalism.MainNotions.StandardLatticesGL3.GA D n) (a b : Fin n), Valued.v (finMat z a b w) = Valued.v (finMat z⁻¹ b a w') := by
        intro z a b
        unfold finMat
        rw [Matrix.map_apply, Matrix.map_apply, inv_apply, hv]
      refine ⟨(t y i j).trans_le (hb w' hw' j i).2, (t y⁻¹ i j).trans_le (by rw [inv_inv]; exact (hb w' hw' j i).1), ?_⟩
      rw [← hcnt 𝔪 h0]
      refine le_of_eq_of_le ?_ (hcong w' hw' j i)
      have e1 : (finMat y - 1) i j = GlobalTheory.BotFormula.toFinE D
          ((((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) - 1) i j) := by
        unfold finMat
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      have e2 : (1 - finMat y⁻¹) j i = -GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D
          ((((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) - 1) i j)) := by
        unfold finMat
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, map_sub, Matrix.map_apply, inv_apply, neg_sub, Matrix.one_apply,
          Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp
        · rw [if_neg hij, if_neg (Ne.symm hij)]; simp
      rw [e1, e2, ← hv]
      exact (Valuation.map_neg _ _).symm
    · have hint : Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
        by_cases hu : w.under (𝓞 D.host.F) ∈ Sf
        · obtain ⟨w₀, hw₀, e₀⟩ := (hS _).1 hu
          obtain ⟨w', e', -, -, hun⟩ := hc w₀
          rcases (hun w).1 e₀.symm with rfl | rfl
          · exact absurd hw₀ hw
          · exact hb _ (by rw [e']; exact Ideal.pointwise_smul_le_pointwise_smul_iff.2 hw₀) i j
        · exact hoff w hu i j
      refine ⟨hint.1, hint.2, ?_⟩
      have hz : FractionalIdeal.count D.host.E w (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = 0 := by
        by_contra h; exact hw ((count_coe_ne_zero_iff w h0).1 h)
      rw [hz, neg_zero, WithZero.exp_zero, Matrix.sub_apply]
      exact val_sub_le hint.1 (val_one_le i j w)
  exact fun i j => ⟨(inHat_one_iff _).2 fun w => (key w i j).1, (inHat_one_iff _).2 fun w => (key w i j).2.1,
    fun w => (key w i j).2.2⟩

end GlobalTheory.CosetOrth.Cong
