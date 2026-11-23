import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsZEquivGramBoundedMinorsStatement

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GramHeight

theorem max_mul_le {c y : ℝ} (hc : 1 ≤ c) : max 1 (c * y) ≤ c * max 1 y := by
  have hy : 1 ≤ max 1 y := le_max_left _ _
  refine max_le ?_ ?_
  · nlinarith
  · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)

theorem one_le_prod' {ι : Type} (s : Finset ι) (x : ι → ℝ) (h : ∀ i ∈ s, 1 ≤ x i) : 1 ≤ ∏ i ∈ s, x i := by
  exact Finset.prod_induction _ (fun t => 1 ≤ t) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl h

theorem prod_subset_le {ι : Type} {s t : Finset ι} (hst : s ⊆ t) (x : ι → ℝ) (h : ∀ i, 1 ≤ x i) :
    ∏ i ∈ s, x i ≤ ∏ i ∈ t, x i := by
  rw [← Finset.prod_sdiff hst]
  have h1 : 1 ≤ ∏ i ∈ t \ s, x i := one_le_prod' _ _ (fun i _ => h i)
  have h2 : 0 ≤ ∏ i ∈ s, x i := Finset.prod_nonneg (fun i _ => le_trans zero_le_one (h i))
  exact le_mul_of_one_le_left h2 h1

variable (D : D7)

noncomputable def PP (x : D.host.E) : ℝ := ∏ τ, max 1 ‖embS D τ x‖

theorem one_le_PP (x : D.host.E) : 1 ≤ PP D x := by
  exact one_le_prod' _ _ (fun τ _ => le_max_left _ _)

theorem PP_inv_le {x : D.host.E} (hx : IsIntegral ℤ x) : ∏ τ, max 1 ‖embS D τ x‖⁻¹ ≤ PP D x := by
  by_cases h0 : x = 0
  · subst h0
    have : (∏ τ, max (1:ℝ) ‖embS D τ (0 : D.host.E)‖⁻¹) = 1 := by simp
    rw [this]
    exact one_le_PP D 0
  · have hpos : ∀ τ, 0 < ‖embS D τ x‖ := fun τ => norm_pos_iff.mpr ((map_ne_zero _).mpr h0)
    have hint : (1:ℝ) ≤ |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
      let y : 𝓞 D.host.E := ⟨x, hx⟩
      have hy : (y : D.host.E) = x := rfl
      have hy0 : y ≠ 0 := fun h => h0 (by rw [← hy, h]; rfl)
      have hn : ((Algebra.norm ℤ y : ℤ) : ℚ) = Algebra.norm ℚ x := by rw [← hy]; exact Algebra.coe_norm_int y
      have hn0 : Algebra.norm ℤ y ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hy0
      rw [← hn]
      have : (1:ℤ) ≤ |Algebra.norm ℤ y| := Int.one_le_abs hn0
      push_cast
      exact_mod_cast this
    have hN : 1 ≤ ∏ τ, ‖embS D τ x‖ := by
      have hsq := GlobalTheory.RealPlaces.prod_norm D x
      have hp0 : 0 ≤ ∏ τ, ‖embS D τ x‖ := Finset.prod_nonneg (fun τ _ => norm_nonneg _)
      rw [Finset.prod_pow] at hsq
      nlinarith
    calc ∏ τ, max 1 ‖embS D τ x‖⁻¹ ≤ (∏ τ, max 1 ‖embS D τ x‖⁻¹) * ∏ τ, ‖embS D τ x‖ :=
          le_mul_of_one_le_right (Finset.prod_nonneg fun _ _ => le_trans zero_le_one (le_max_left _ _)) hN
      _ = ∏ τ, (max 1 ‖embS D τ x‖⁻¹ * ‖embS D τ x‖) := (Finset.prod_mul_distrib).symm
      _ = ∏ τ, max 1 ‖embS D τ x‖ := Finset.prod_congr rfl (fun τ _ => by
          have := hpos τ
          rw [max_mul_of_nonneg _ _ this.le, one_mul, inv_mul_cancel₀ this.ne', max_comm])
      _ = PP D x := rfl

theorem one_mem_dd (n : ℕ) (a : Fin n) :
    (1 : D.host.E) ∈ (ddS D ^ (-((n : ℤ) - (a : ℕ))) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have hlt : (a : ℕ) < n := a.2
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((n : ℤ) - (a : ℕ)) = (k : ℤ) := ⟨n - a, by omega⟩
  rw [hk, _root_.zpow_neg, zpow_natCast]
  have hI : (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) : Ideal (𝓞 D.host.E)) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact differentIdeal_ne_bot
  have : ddS D ^ k = ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ^ k : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [FractionalIdeal.coeIdeal_pow]; rfl
  rw [this]
  exact FractionalIdeal.one_mem_inv_coe_ideal (pow_ne_zero _ hI)

theorem fvec_mem {T : D.host.E} (Λ : LatV D) (F : LFlag (hS D) D.R.rS T) (hz : IsLift Λ F)
    (hX : XLam Λ F = XS D F.fl) (a : Fin (D.R.rS + 1)) : F.fl.fvec a ∈ Λ := by
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [FlagG.fvec, Fin.snoc_last]
    exact hz.1
  · simp only [FlagG.fvec, Fin.snoc_castSucc]
    have hmem : F.fl.e i ∈ XS D F.fl :=
      Submodule.subset_span ⟨i, 1, one_mem_dd D D.R.rS i, (one_smul _ _).symm⟩
    rw [← hX] at hmem
    exact (Submodule.mem_inf.mp hmem).1

theorem zhat_integral {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) (hΛ : IsRowLat D F0 Λ)
    (F' : LFlag (hS D) D.R.rS T') (hF : IsTermF D Λ (lf D F0) F') (a b : Fin (D.R.rS + 1)) :
    IsIntegral ℤ (ZhatL (lf D F0) F' a b) := by
  have hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ := hΛ.2.1.2.1
  have hx : F'.fl.fvec b ∈ Λ := fvec_mem D Λ F' hF.1.1 hF.2.2 b
  have hy : (lf D F0).fl.fvec a ∈ Λ := fvec_mem D Λ (lf D F0) hΛ.2.1.2.2.1 hΛ.2.2 a
  have hx' : F'.fl.fvec b ∈ Formalism.HermitianLatticesTheory.dual (hS D).hT Λ := by rw [hu]; exact hx
  have hmem : (hS D).hT ((lf D F0).fl.fvec a) (F'.fl.fvec b) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply] at hx'
    exact hx' _ hy
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp hmem
  show IsIntegral ℤ ((hS D).hT ((lf D F0).fl.fvec a) (F'.fl.fvec b))
  rw [← ho]
  exact o.isIntegral_coe

theorem lead_integral {N : ℕ} (Z : Matrix (Fin N) (Fin N) D.host.E) (h : ∀ a b, IsIntegral ℤ (Z a b)) (l : ℕ) :
    IsIntegral ℤ (leadMinorE Z l) := by
  unfold leadMinorE
  split_ifs with hl
  · let S := integralClosure ℤ D.host.E
    let M : Matrix (Fin l) (Fin l) S := fun i j => ⟨Z (Fin.castLE hl i) (Fin.castLE hl j), h _ _⟩
    have hM : (algebraMap S D.host.E).mapMatrix M = Z.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
      ext i j; rfl
    rw [← hM, ← RingHom.map_det]
    exact (M.det).2
  · exact isIntegral_zero

theorem equiv_integral {N : ℕ} {Z Z₂ : Matrix (Fin N) (Fin N) D.host.E} (h : ∀ a b, IsIntegral ℤ (Z a b))
    (he : ZEquiv Z Z₂) (a b : Fin N) : IsIntegral ℤ (Z₂ a b) := by
  obtain ⟨A, B, -, -, -, -, rfl⟩ := he
  have hA : ∀ i j, IsIntegral ℤ ((A i j : 𝓞 D.host.E) : D.host.E) := fun i j => (A i j).isIntegral_coe
  have hB : ∀ i j, IsIntegral ℤ ((B i j : 𝓞 D.host.E) : D.host.E) := fun i j => (B i j).isIntegral_coe
  simp only [Matrix.mul_apply, Matrix.map_apply]
  refine IsIntegral.sum _ (fun j _ => IsIntegral.mul (IsIntegral.sum _ (fun i _ => ?_)) (hB _ _))
  exact IsIntegral.mul (hA _ _) (h _ _)

theorem frameExp_le (r l : ℕ) (hl : l ≤ r + 1) : frameExp r l ≤ (r + 1) ^ 2 := by
  unfold frameExp
  calc ∑ a ∈ Finset.Icc 1 l, (r + 1 - a) ≤ ∑ a ∈ Finset.Icc 1 l, (r + 1) := Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)
    _ = l * (r + 1) := by simp
    _ ≤ (r + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hl

theorem frameExp_succ (r : ℕ) : frameExp r (r + 1) = frameExp r r := by
  unfold frameExp
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp

theorem absDl_eq (Z : GramM D) (l : ℕ) (τ : D.what₂.Tau) :
    absDl D Z l τ = ‖embS D τ (leadMinorE Z l)‖ * (D.host.rdE ^ (2 * frameExp D.R.rS l))⁻¹ := by
  have h1 : 0 ≤ D.host.rdE := le_trans zero_le_one (GlobalTheory.RealPlaces.one_le_rdE D)
  simp only [absDl, absReal]
  rw [Real.rpow_neg h1, show (2 * (frameExp D.R.rS l : ℝ)) = ((2 * frameExp D.R.rS l : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

noncomputable def QQ (Z : GramM D) : ℝ := ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), PP D (leadMinorE Z l)

theorem one_le_QQ (Z : GramM D) : 1 ≤ QQ D Z := by
  exact one_le_prod' _ _ (fun l _ => one_le_PP D _)

theorem QQ_le (Z : GramM D) {b C Y : ℝ} (hH : 1 ≤ b ^ (C * (D.R.m : ℝ) ^ 2))
    (hY : D.host.rdE ^ (2 * (D.R.rS + 1) ^ 2) ≤ Y) :
    QQ D Z ≤ (Y * b ^ (C * (D.R.m : ℝ) ^ 2)) ^ ((D.R.rS + 1) * D.R.f) * sizeZ D b C Z := by
  have hrd : 1 ≤ D.host.rdE := GlobalTheory.RealPlaces.one_le_rdE D
  have hY1 : 1 ≤ Y := le_trans (one_le_pow₀ hrd) hY
  have hH0 : 0 < b ^ (C * (D.R.m : ℝ) ^ 2) := by linarith
  have hc : 1 ≤ Y * b ^ (C * (D.R.m : ℝ) ^ 2) := one_le_mul_of_one_le_of_one_le hY1 hH
  have key : ∀ l ∈ Finset.Icc 1 (D.R.rS + 1), ∀ τ, max 1 ‖embS D τ (leadMinorE Z l)‖ ≤
      (Y * b ^ (C * (D.R.m : ℝ) ^ 2)) * max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) := by
    intro l hl τ
    have hl' : l ≤ D.R.rS + 1 := (Finset.mem_Icc.mp hl).2
    have hp : D.host.rdE ^ (2 * frameExp D.R.rS l) ≤ Y := by
      refine le_trans (pow_le_pow_right₀ hrd ?_) hY
      have := frameExp_le D.R.rS l hl'
      omega
    have hpos : 0 < D.host.rdE ^ (2 * frameExp D.R.rS l) := pow_pos (by linarith) _
    have heq : ‖embS D τ (leadMinorE Z l)‖ = absDl D Z l τ * D.host.rdE ^ (2 * frameExp D.R.rS l) := by
      rw [absDl_eq, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
    have h0 : 0 ≤ absDl D Z l τ := by rw [absDl_eq]; positivity
    refine le_trans (max_le_max le_rfl ?_) (max_mul_le hc)
    rw [heq, show Y * b ^ (C * (D.R.m : ℝ) ^ 2) * (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) = absDl D Z l τ * Y by
      field_simp]
    exact mul_le_mul_of_nonneg_left hp h0
  have hcard : Fintype.card D.what₂.Tau = D.R.f := (GlobalTheory.real_places_facts D).1
  calc QQ D Z = ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), ∏ τ, max 1 ‖embS D τ (leadMinorE Z l)‖ := rfl
    _ ≤ ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), ∏ τ,
          ((Y * b ^ (C * (D.R.m : ℝ) ^ 2)) * max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2))) :=
        Finset.prod_le_prod (fun l _ => Finset.prod_nonneg (fun τ _ => le_trans zero_le_one (le_max_left _ _)))
          (fun l hl => Finset.prod_le_prod (fun τ _ => le_trans zero_le_one (le_max_left _ _)) (fun τ _ => key l hl τ))
    _ = (Y * b ^ (C * (D.R.m : ℝ) ^ 2)) ^ ((D.R.rS + 1) * D.R.f) * sizeZ D b C Z := by
        conv_rhs => rw [sizeZ, Finset.prod_comm]
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, Nat.card_Icc,
          add_tsub_cancel_right]
        ring

theorem G_le (Z : GramM D) {T T' : ℝ} (hT : 0 ≤ T) (hT' : 0 ≤ T') :
    ∏ τ, max 1 (Gz D T T' Z τ) ≤ QQ D Z ^ 2 := by
  have hrd : 1 ≤ D.host.rdE := GlobalTheory.RealPlaces.one_le_rdE D
  have key : ∀ τ, max 1 (Gz D T T' Z τ) ≤ (max 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖) ^ 2 := by
    intro τ
    have hp : 1 ≤ D.host.rdE ^ (2 * frameExp D.R.rS (D.R.rS + 1)) := one_le_pow₀ hrd
    have habs : absDl D Z (D.R.rS + 1) τ ≤ ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖ := by
      rw [absDl_eq]
      exact mul_le_of_le_one_right (norm_nonneg _) (inv_le_one_of_one_le₀ hp)
    have h0 : 0 ≤ absDl D Z (D.R.rS + 1) τ := by rw [absDl_eq]; positivity
    have hG : Gz D T T' Z τ ≤ absDl D Z (D.R.rS + 1) τ ^ 2 := by
      simp only [Gz]; nlinarith [sq_nonneg (absDl D Z D.R.rS τ), mul_nonneg hT hT']
    have hm := le_max_right 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖
    refine max_le (one_le_pow₀ (le_max_left _ _)) ?_
    calc Gz D T T' Z τ ≤ absDl D Z (D.R.rS + 1) τ ^ 2 := hG
      _ ≤ _ := pow_le_pow_left₀ h0 (habs.trans hm) 2
  have h1 : PP D (leadMinorE Z (D.R.rS + 1)) ≤ QQ D Z := by
    have := prod_subset_le (s := {D.R.rS + 1}) (t := Finset.Icc 1 (D.R.rS + 1))
      (Finset.singleton_subset_iff.mpr (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))
      (fun l => PP D (leadMinorE Z l)) (fun l => one_le_PP D _)
    rw [Finset.prod_singleton] at this
    exact this
  calc ∏ τ, max 1 (Gz D T T' Z τ) ≤ ∏ τ, (max 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖) ^ 2 :=
        Finset.prod_le_prod (fun τ _ => le_trans zero_le_one (le_max_left _ _)) (fun τ _ => key τ)
    _ = PP D (leadMinorE Z (D.R.rS + 1)) ^ 2 := by rw [Finset.prod_pow]; rfl
    _ ≤ QQ D Z ^ 2 := pow_le_pow_left₀ (le_trans zero_le_one (one_le_PP D _)) h1 2

theorem G_inv_le (Z : GramM D) (h : ∀ a b, IsIntegral ℤ (Z a b)) (hr : 1 ≤ D.R.rS) {T T' : ℕ} (hT : 1 ≤ T)
    (hT' : 1 ≤ T') {Y : ℝ} (hY : D.host.rdE ^ (2 * (D.R.rS + 1) ^ 2) ≤ Y) :
    ∏ τ, max 1 (Gz D T T' Z τ)⁻¹ ≤ (Y ^ 2 * (2 * T * T')) ^ D.R.f * QQ D Z ^ 2 := by
  have hrd : 1 ≤ D.host.rdE := GlobalTheory.RealPlaces.one_le_rdE D
  have hcard : Fintype.card D.what₂.Tau = D.R.f := (GlobalTheory.real_places_facts D).1
  have hstar : ∀ τ (a : D.host.E), embS D τ (star a) = starRingEnd ℂ (embS D τ a) :=
    (GlobalTheory.real_places_facts D).2.2.2.2.2.1
  have hint : ∀ l, IsIntegral ℤ (leadMinorE Z l) := fun l => lead_integral D Z h l
  have hstarint : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x) :=
    fun x hx => hx.map (starRingEnd D.host.E).toIntAlgHom
  have hnat : ∀ k : ℕ, IsIntegral ℤ (k : D.host.E) :=
    fun k => (integralClosure ℤ D.host.E).natCast_mem k
  have hGint : IsIntegral ℤ (leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)) - ((T : D.host.E) * (T' : D.host.E)) * (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS))) :=
    IsIntegral.sub (IsIntegral.mul (hint _) (hstarint _ (hint _)))
      (IsIntegral.mul (IsIntegral.mul (hnat T) (hnat T')) (IsIntegral.mul (hint _) (hstarint _ (hint _))))
  have hτG : ∀ τ, ‖embS D τ (leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)) - ((T : D.host.E) * (T' : D.host.E)) * (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS)))‖ = |(‖embS D τ (leadMinorE Z (D.R.rS + 1))‖ ^ 2 - (T : ℝ) * (T' : ℝ) * ‖embS D τ (leadMinorE Z D.R.rS)‖ ^ 2)| := by
    intro τ
    have : embS D τ (leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)) - ((T : D.host.E) * (T' : D.host.E)) * (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS))) = (((‖embS D τ (leadMinorE Z (D.R.rS + 1))‖ ^ 2 - (T : ℝ) * (T' : ℝ) * ‖embS D τ (leadMinorE Z D.R.rS)‖ ^ 2) : ℝ) : ℂ) := by
      simp only [map_sub, map_mul, map_natCast, hstar, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      try ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]
  have hρY : D.host.rdE ^ (2 * frameExp D.R.rS D.R.rS) ≤ Y := by
    refine le_trans (pow_le_pow_right₀ hrd ?_) hY
    have := frameExp_le D.R.rS D.R.rS (by omega)
    omega
  have hρ1 : 1 ≤ D.host.rdE ^ (2 * frameExp D.R.rS D.R.rS) := one_le_pow₀ hrd
  have key : ∀ τ, max 1 (Gz D T T' Z τ)⁻¹ ≤ Y ^ 2 * max 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)) - ((T : D.host.E) * (T' : D.host.E)) * (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS)))‖⁻¹ := by
    intro τ
    have hGz : Gz D T T' Z τ = (‖embS D τ (leadMinorE Z (D.R.rS + 1))‖ ^ 2 - (T : ℝ) * (T' : ℝ) * ‖embS D τ (leadMinorE Z D.R.rS)‖ ^ 2) * ((D.host.rdE ^ (2 * frameExp D.R.rS D.R.rS)) ^ 2)⁻¹ := by
      simp only [Gz, absDl_eq, frameExp_succ]
      ring
    rw [hGz, hτG τ]
    have hρ0 : 0 < D.host.rdE ^ (2 * frameExp D.R.rS D.R.rS) := by linarith
    calc max 1 ((‖embS D τ (leadMinorE Z (D.R.rS + 1))‖ ^ 2 - (T : ℝ) * (T' : ℝ) * ‖embS D τ (leadMinorE Z D.R.rS)‖ ^ 2) * ((D.host.rdE ^ (2 * frameExp D.R.rS D.R.rS)) ^ 2)⁻¹)⁻¹ ≤ max 1 ((D.host.rdE ^ (2 * frameExp D.R.rS D.R.rS)) ^ 2 * |(‖embS D τ (leadMinorE Z (D.R.rS + 1))‖ ^ 2 - (T : ℝ) * (T' : ℝ) * ‖embS D τ (leadMinorE Z D.R.rS)‖ ^ 2)|⁻¹) := by
          apply max_le_max le_rfl
          rw [mul_inv, inv_inv, mul_comm]
          exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (abs_inv _).le) (by positivity)
      _ ≤ (D.host.rdE ^ (2 * frameExp D.R.rS D.R.rS)) ^ 2 * max 1 |(‖embS D τ (leadMinorE Z (D.R.rS + 1))‖ ^ 2 - (T : ℝ) * (T' : ℝ) * ‖embS D τ (leadMinorE Z D.R.rS)‖ ^ 2)|⁻¹ := max_mul_le (one_le_pow₀ hρ1)
      _ ≤ Y ^ 2 * max 1 |(‖embS D τ (leadMinorE Z (D.R.rS + 1))‖ ^ 2 - (T : ℝ) * (T' : ℝ) * ‖embS D τ (leadMinorE Z D.R.rS)‖ ^ 2)|⁻¹ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ0.le hρY 2) (le_trans zero_le_one (le_max_left _ _))
  have hsub : PP D (leadMinorE Z (D.R.rS + 1)) * PP D (leadMinorE Z D.R.rS) ≤ QQ D Z := by
    have := prod_subset_le (s := {D.R.rS + 1, D.R.rS}) (t := Finset.Icc 1 (D.R.rS + 1))
      (by intro l hl; simp only [Finset.mem_insert, Finset.mem_singleton] at hl; simp only [Finset.mem_Icc]; omega)
      (fun l => PP D (leadMinorE Z l)) (fun l => one_le_PP D _)
    rw [Finset.prod_pair (by omega)] at this
    exact this
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT1' : (1 : ℝ) ≤ T' := by exact_mod_cast hT'
  have hTT : (1 : ℝ) ≤ (T : ℝ) * T' := one_le_mul_of_one_le_of_one_le hT1 hT1'
  have hPPG : PP D (leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)) - ((T : D.host.E) * (T' : D.host.E)) * (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS))) ≤ (2 * T * T') ^ D.R.f * QQ D Z ^ 2 := by
    have hτ : ∀ τ, max 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)) - ((T : D.host.E) * (T' : D.host.E)) * (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS)))‖ ≤
        (2 * T * T') * ((max 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖) ^ 2 * (max 1 ‖embS D τ (leadMinorE Z D.R.rS)‖) ^ 2) := by
      intro τ
      rw [hτG τ]
      have a1 := le_max_left 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖
      have a2 := le_max_right 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖
      have b1 := le_max_left 1 ‖embS D τ (leadMinorE Z D.R.rS)‖
      have b2 := le_max_right 1 ‖embS D τ (leadMinorE Z D.R.rS)‖
      have n1 := norm_nonneg (embS D τ (leadMinorE Z (D.R.rS + 1)))
      have n0 := norm_nonneg (embS D τ (leadMinorE Z D.R.rS))
      have hx2 : ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖ ^ 2 ≤ (max 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖) ^ 2 := pow_le_pow_left₀ n1 a2 2
      have hy2 : ‖embS D τ (leadMinorE Z D.R.rS)‖ ^ 2 ≤ (max 1 ‖embS D τ (leadMinorE Z D.R.rS)‖) ^ 2 := pow_le_pow_left₀ n0 b2 2
      have hx1 : 1 ≤ (max 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖) ^ 2 := one_le_pow₀ a1
      have hy1 : 1 ≤ (max 1 ‖embS D τ (leadMinorE Z D.R.rS)‖) ^ 2 := one_le_pow₀ b1
      have hP1 : 1 ≤ (max 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖) ^ 2 * (max 1 ‖embS D τ (leadMinorE Z D.R.rS)‖) ^ 2 :=
        one_le_mul_of_one_le_of_one_le hx1 hy1
      have hxP : (max 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖) ^ 2 ≤ (max 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖) ^ 2 * (max 1 ‖embS D τ (leadMinorE Z D.R.rS)‖) ^ 2 :=
        le_mul_of_one_le_right (by positivity) hy1
      have hyP : (max 1 ‖embS D τ (leadMinorE Z D.R.rS)‖) ^ 2 ≤ (max 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖) ^ 2 * (max 1 ‖embS D τ (leadMinorE Z D.R.rS)‖) ^ 2 :=
        le_mul_of_one_le_left (by positivity) hx1
      have hTP := mul_le_mul_of_nonneg_left (hy2.trans hyP) (by positivity : (0:ℝ) ≤ (T : ℝ) * T')
      have hTP' := mul_le_mul_of_nonneg_left hP1 (by positivity : (0:ℝ) ≤ (T : ℝ) * T')
      have hn0' : 0 ≤ (T : ℝ) * T' * ‖embS D τ (leadMinorE Z D.R.rS)‖ ^ 2 := by positivity
      refine max_le (by nlinarith) (abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    calc PP D (leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)) - ((T : D.host.E) * (T' : D.host.E)) * (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS))) = ∏ τ, max 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)) - ((T : D.host.E) * (T' : D.host.E)) * (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS)))‖ := rfl
      _ ≤ ∏ τ, ((2 * T * T') * ((max 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖) ^ 2 * (max 1 ‖embS D τ (leadMinorE Z D.R.rS)‖) ^ 2)) :=
          Finset.prod_le_prod (fun τ _ => le_trans zero_le_one (le_max_left _ _)) (fun τ _ => hτ τ)
      _ = (2 * T * T') ^ D.R.f * ((PP D (leadMinorE Z (D.R.rS + 1)) * PP D (leadMinorE Z D.R.rS)) ^ 2) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, Finset.prod_mul_distrib,
            Finset.prod_pow, Finset.prod_pow]
          simp only [PP]
          ring
      _ ≤ (2 * T * T') ^ D.R.f * QQ D Z ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (mul_nonneg (le_trans zero_le_one (one_le_PP D _)) (le_trans zero_le_one (one_le_PP D _))) hsub 2)
            (by positivity)
  calc ∏ τ, max 1 (Gz D T T' Z τ)⁻¹ ≤ ∏ τ, (Y ^ 2 * max 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)) - ((T : D.host.E) * (T' : D.host.E)) * (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS)))‖⁻¹) :=
        Finset.prod_le_prod (fun τ _ => le_trans zero_le_one (le_max_left _ _)) (fun τ _ => key τ)
    _ = (Y ^ 2) ^ D.R.f * ∏ τ, max 1 ‖embS D τ (leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)) - ((T : D.host.E) * (T' : D.host.E)) * (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS)))‖⁻¹ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
    _ ≤ (Y ^ 2) ^ D.R.f * ((2 * T * T') ^ D.R.f * QQ D Z ^ 2) :=
        mul_le_mul_of_nonneg_left ((PP_inv_le D hGint).trans hPPG) (by positivity)
    _ = (Y ^ 2 * (2 * T * T')) ^ D.R.f * QQ D Z ^ 2 := by rw [mul_pow]; ring

theorem rho_bounds (a : Fin (D.R.rS + 1)) :
    0 < rhoF D a ∧ rhoF D a ≤ 1 ∧ (rhoF D a)⁻¹ ≤ D.host.rdE ^ (D.R.rS + 1) := by
  have h1 : 1 ≤ D.host.rdE := GlobalTheory.RealPlaces.one_le_rdE D
  have ha : (a : ℕ) ≤ D.R.rS := Nat.lt_succ_iff.mp a.2
  have ha' : ((a : ℕ) : ℝ) ≤ D.R.rS := by exact_mod_cast ha
  refine ⟨Real.rpow_pos_of_pos (by linarith) _, Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith), ?_⟩
  rw [rhoF, Real.rpow_neg (by linarith), inv_inv, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le h1
  push_cast
  have : (0 : ℝ) ≤ ((a : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

theorem minors_le (Z Z₂ : GramM D) (h : ∀ a b, IsIntegral ℤ (Z a b)) (he : ZEquiv Z Z₂) {c Y : ℝ} (hc : 1 ≤ c)
    (hY : D.host.rdE ^ (2 * (D.R.rS + 1) ^ 2) ≤ Y) {j : ℕ} (I J : Fin j ↪o Fin (D.R.rS + 1))
    (hb : ∀ τ, ‖embS D τ (Z₂.submatrix I J).det‖ ≤ c * ∏ l ∈ Finset.Icc 1 (D.R.rS + 1),
      (max 1 ‖embS D τ (leadMinorE Z l)‖ * max 1 ‖embS D τ (leadMinorE Z l)‖⁻¹)) :
    ∏ τ, max 1 (UnitaryVolumeMass.absMinor D Z₂ I J τ) ≤ (Y * c) ^ D.R.f * QQ D Z ^ 2 ∧
    ∏ τ, max 1 (UnitaryVolumeMass.absMinor D Z₂ I J τ)⁻¹ ≤ (Y * c) ^ D.R.f * QQ D Z ^ 2 := by
  have hrd : 1 ≤ D.host.rdE := GlobalTheory.RealPlaces.one_le_rdE D
  have hY1 : 1 ≤ Y := le_trans (one_le_pow₀ hrd) hY
  have hcard : Fintype.card D.what₂.Tau = D.R.f := (GlobalTheory.real_places_facts D).1
  have hint : ∀ l, IsIntegral ℤ (leadMinorE Z l) := fun l => lead_integral D Z h l
  have hZ2 : ∀ a b, IsIntegral ℤ (Z₂ a b) := equiv_integral D h he
  have hμ : IsIntegral ℤ (Z₂.submatrix I J).det := by
    let S := integralClosure ℤ D.host.E
    let M : Matrix (Fin j) (Fin j) S := fun a b => ⟨Z₂ (I a) (J b), hZ2 _ _⟩
    have hM : (algebraMap S D.host.E).mapMatrix M = Z₂.submatrix I J := by ext a b; rfl
    rw [← hM, ← RingHom.map_det]
    exact (M.det).2
  have hX1 : ∀ τ, 1 ≤ (∏ l ∈ Finset.Icc 1 (D.R.rS + 1), (max 1 ‖embS D τ (leadMinorE Z l)‖ * max 1 ‖embS D τ (leadMinorE Z l)‖⁻¹)) :=
    fun τ => one_le_prod' _ _ (fun l _ => one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _))
  have hXprod : ∏ τ, (∏ l ∈ Finset.Icc 1 (D.R.rS + 1), (max 1 ‖embS D τ (leadMinorE Z l)‖ * max 1 ‖embS D τ (leadMinorE Z l)‖⁻¹)) ≤ QQ D Z ^ 2 := by
    rw [Finset.prod_comm]
    simp only [Finset.prod_mul_distrib]
    have h2 : ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), ∏ τ, max 1 ‖embS D τ (leadMinorE Z l)‖⁻¹ ≤ QQ D Z :=
      Finset.prod_le_prod (fun l _ => Finset.prod_nonneg (fun τ _ => le_trans zero_le_one (le_max_left _ _)))
        (fun l _ => PP_inv_le D (hint l))
    rw [sq]
    exact mul_le_mul (le_of_eq rfl) h2
      (Finset.prod_nonneg (fun l _ => Finset.prod_nonneg (fun τ _ => le_trans zero_le_one (le_max_left _ _))))
      (le_trans zero_le_one (one_le_QQ D Z))
  have hPPμ : PP D (Z₂.submatrix I J).det ≤ c ^ D.R.f * QQ D Z ^ 2 := by
    calc PP D (Z₂.submatrix I J).det = ∏ τ, max 1 ‖embS D τ (Z₂.submatrix I J).det‖ := rfl
      _ ≤ ∏ τ, (c * (∏ l ∈ Finset.Icc 1 (D.R.rS + 1), (max 1 ‖embS D τ (leadMinorE Z l)‖ * max 1 ‖embS D τ (leadMinorE Z l)‖⁻¹))) :=
          Finset.prod_le_prod (fun τ _ => le_trans zero_le_one (le_max_left _ _))
            (fun τ _ => max_le (one_le_mul_of_one_le_of_one_le hc (hX1 τ)) (hb τ))
      _ = c ^ D.R.f * ∏ τ, (∏ l ∈ Finset.Icc 1 (D.R.rS + 1), (max 1 ‖embS D τ (leadMinorE Z l)‖ * max 1 ‖embS D τ (leadMinorE Z l)‖⁻¹)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
      _ ≤ c ^ D.R.f * QQ D Z ^ 2 := mul_le_mul_of_nonneg_left hXprod (by positivity)
  have hR0 : 0 < (∏ a, (rhoF D (I a) * rhoF D (J a))) := Finset.prod_pos (fun a _ => mul_pos (rho_bounds D _).1 (rho_bounds D _).1)
  have hR1 : (∏ a, (rhoF D (I a) * rhoF D (J a))) ≤ 1 := by
    refine Finset.prod_le_one (fun a _ => mul_nonneg (rho_bounds D _).1.le (rho_bounds D _).1.le) (fun a _ => ?_)
    have h1 := rho_bounds D (I a)
    have h2 := rho_bounds D (J a)
    nlinarith [h1.1, h1.2.1, h2.1, h2.2.1]
  have hj : j ≤ D.R.rS + 1 := by simpa using Fintype.card_le_of_embedding I.toEmbedding
  have hRinv : (∏ a, (rhoF D (I a) * rhoF D (J a)))⁻¹ ≤ Y := by
    rw [← Finset.prod_inv_distrib]
    calc ∏ a, (rhoF D (I a) * rhoF D (J a))⁻¹ ≤ ∏ _a : Fin j, (D.host.rdE ^ (D.R.rS + 1) * D.host.rdE ^ (D.R.rS + 1)) := by
          refine Finset.prod_le_prod (fun a _ => ?_) (fun a _ => ?_)
          · exact inv_nonneg.mpr (mul_nonneg (rho_bounds D _).1.le (rho_bounds D _).1.le)
          · rw [mul_inv]
            exact mul_le_mul (rho_bounds D _).2.2 (rho_bounds D _).2.2 (inv_nonneg.mpr (rho_bounds D _).1.le) (by positivity)
      _ = D.host.rdE ^ (2 * (D.R.rS + 1) * j) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_add, ← pow_mul]; ring_nf
      _ ≤ D.host.rdE ^ (2 * (D.R.rS + 1) ^ 2) := pow_le_pow_right₀ hrd (by nlinarith)
      _ ≤ Y := hY
  constructor
  · calc ∏ τ, max 1 (UnitaryVolumeMass.absMinor D Z₂ I J τ) ≤ ∏ τ, max 1 ‖embS D τ (Z₂.submatrix I J).det‖ := by
          refine Finset.prod_le_prod (fun τ _ => le_trans zero_le_one (le_max_left _ _)) (fun τ _ => max_le_max le_rfl ?_)
          simp only [UnitaryVolumeMass.absMinor]
          exact mul_le_of_le_one_right (norm_nonneg _) hR1
      _ = PP D (Z₂.submatrix I J).det := rfl
      _ ≤ c ^ D.R.f * QQ D Z ^ 2 := hPPμ
      _ ≤ (Y * c) ^ D.R.f * QQ D Z ^ 2 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hY1)) (by positivity)
  · calc ∏ τ, max 1 (UnitaryVolumeMass.absMinor D Z₂ I J τ)⁻¹ ≤ ∏ τ, (Y * max 1 ‖embS D τ (Z₂.submatrix I J).det‖⁻¹) := by
          refine Finset.prod_le_prod (fun τ _ => le_trans zero_le_one (le_max_left _ _)) (fun τ _ => ?_)
          simp only [UnitaryVolumeMass.absMinor]
          rw [mul_inv, mul_comm]
          refine le_trans (max_mul_le ((one_le_inv₀ hR0).mpr hR1)) ?_
          exact mul_le_mul_of_nonneg_right hRinv (le_trans zero_le_one (le_max_left _ _))
      _ = Y ^ D.R.f * ∏ τ, max 1 ‖embS D τ (Z₂.submatrix I J).det‖⁻¹ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
      _ ≤ Y ^ D.R.f * (c ^ D.R.f * QQ D Z ^ 2) :=
          mul_le_mul_of_nonneg_left ((PP_inv_le D hμ).trans hPPμ) (by positivity)
      _ = (Y * c) ^ D.R.f * QQ D Z ^ 2 := by rw [mul_pow]; ring

theorem final_le (Z : GramM D) {b : ℝ} (hb : 1 ≤ b) (n : ℕ)
    (hY : D.host.rdE ^ (2 * (D.R.rS + 1) ^ 2) ≤ b ^ (D.R.m ^ 2)) {W : ℝ} (hW0 : 0 ≤ W)
    (hW : W ≤ (b ^ (D.R.m ^ 2)) ^ (2 * n + 5)) :
    W ^ D.R.f * QQ D Z ^ 2 ≤ HHZ D b ((2 * n + 7 : ℕ) : ℝ) Z := by
  have hm : D.R.m = 2 * D.R.rS + 2 := (GlobalTheory.real_places_facts D).2.2.2.1
  have hb0 : 0 < b := by linarith
  have hm2 : 2 ≤ D.R.m := by omega
  have eC2 : ((2 * n + 7 : ℕ) : ℝ) * (D.R.m : ℝ) ^ 2 = (((2 * n + 7) * D.R.m ^ 2 : ℕ) : ℝ) := by push_cast; ring
  have eC2f : ((2 * n + 7 : ℕ) : ℝ) * (D.R.m : ℝ) ^ 2 * (D.R.f : ℝ) = (((2 * n + 7) * D.R.m ^ 2 * D.R.f : ℕ) : ℝ) := by
    push_cast; ring
  have eCm : ((2 * n + 7 : ℕ) : ℝ) * (D.R.m : ℝ) = (((2 * n + 7) * D.R.m : ℕ) : ℝ) := by push_cast; ring
  have hH : 1 ≤ b ^ (((2 * n + 7 : ℕ) : ℝ) * (D.R.m : ℝ) ^ 2) := Real.one_le_rpow hb (by positivity)
  have hQ := QQ_le D Z hH hY
  rw [eC2, Real.rpow_natCast] at hQ
  have hs1 : 1 ≤ sizeZ D b ((2 * n + 7 : ℕ) : ℝ) Z :=
    one_le_prod' _ _ (fun τ _ => one_le_prod' _ _ (fun l _ => le_max_left _ _))
  have h0 : 0 ≤ QQ D Z := le_trans zero_le_one (one_le_QQ D Z)
  unfold HHZ
  rw [eC2f, Real.rpow_natCast, eCm, Real.rpow_natCast, ← pow_mul]
  have hs0 : 0 ≤ sizeZ D b ((2 * n + 7 : ℕ) : ℝ) Z := le_trans zero_le_one hs1
  calc W ^ D.R.f * QQ D Z ^ 2
      ≤ ((b ^ (D.R.m ^ 2)) ^ (2 * n + 5)) ^ D.R.f *
        ((b ^ (D.R.m ^ 2) * b ^ ((2 * n + 7) * D.R.m ^ 2)) ^ ((D.R.rS + 1) * D.R.f) *
          sizeZ D b ((2 * n + 7 : ℕ) : ℝ) Z) ^ 2 :=
        mul_le_mul (pow_le_pow_left₀ hW0 hW _) (pow_le_pow_left₀ h0 hQ 2) (pow_nonneg h0 2)
          (pow_nonneg (pow_nonneg (pow_nonneg hb0.le _) _) _)
    _ = b ^ (D.R.m ^ 2 * (2 * n + 5) * D.R.f + (D.R.m ^ 2 + (2 * n + 7) * D.R.m ^ 2) * ((D.R.rS + 1) * D.R.f) * 2) *
          sizeZ D b ((2 * n + 7 : ℕ) : ℝ) Z ^ 2 := by ring
    _ ≤ b ^ ((2 * n + 7) * D.R.m ^ 2 * D.R.f * ((2 * n + 7) * D.R.m)) * sizeZ D b ((2 * n + 7 : ℕ) : ℝ) Z ^ 4 := by
        refine mul_le_mul (pow_le_pow_right₀ hb ?_) (pow_le_pow_right₀ hs1 (by norm_num)) (pow_nonneg hs0 2)
          (pow_nonneg hb0.le _)
        have hexp : (2 * n + 5) + (1 + (2 * n + 7)) * D.R.m ≤ (2 * n + 7) * (2 * n + 7) * D.R.m := by
          nlinarith [Nat.mul_le_mul_left n hm2, Nat.zero_le (n * n * D.R.m), Nat.zero_le (n * D.R.m)]
        have := Nat.mul_le_mul_left (D.R.m ^ 2 * D.R.f) hexp
        have e2 : (D.R.rS + 1) * 2 = D.R.m := by omega
        calc D.R.m ^ 2 * (2 * n + 5) * D.R.f + (D.R.m ^ 2 + (2 * n + 7) * D.R.m ^ 2) * ((D.R.rS + 1) * D.R.f) * 2
            = D.R.m ^ 2 * D.R.f * ((2 * n + 5) + (1 + (2 * n + 7)) * D.R.m) := by rw [← e2]; ring
          _ ≤ D.R.m ^ 2 * D.R.f * ((2 * n + 7) * (2 * n + 7) * D.R.m) := this
          _ = (2 * n + 7) * D.R.m ^ 2 * D.R.f * ((2 * n + 7) * D.R.m) := by ring

theorem const_le {b ρ : ℝ} (hb : 2 ≤ b) (r n : ℕ) (h0 : 0 ≤ ρ) (hρ : ρ ≤ b ^ (n + 2)) :
    4 ^ (r + 1) * (((r + 1).factorial : ℕ) : ℝ) ^ 2 * ρ ^ (2 * (r + 1)) ≤ (b ^ ((2 * r + 2) ^ 2)) ^ (n + 4) := by
  have hb1 : (1:ℝ) ≤ b := by linarith
  have h1 : ρ ^ (2 * (r + 1)) ≤ b ^ ((n + 2) * (2 * (r + 1))) := by
    rw [pow_mul b (n + 2)]; exact pow_le_pow_left₀ h0 hρ _
  have h2 : (4:ℝ) ^ (r + 1) ≤ b ^ (2 * (r + 1)) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by nlinarith) _
  have h3 : ((((r + 1).factorial : ℕ) : ℝ)) ^ 2 ≤ b ^ (2 * (r + 1) ^ 2) := by
    have hf : (((r + 1).factorial : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ (r + 1) := by
      exact_mod_cast Nat.factorial_le_pow (r + 1)
    have hs2 : ((r + 1 : ℕ) : ℝ) ≤ b ^ (r + 1) := by
      have : ((r + 1 : ℕ) : ℝ) ≤ (2:ℝ) ^ (r + 1) := by exact_mod_cast (Nat.lt_two_pow_self (n := r + 1)).le
      exact this.trans (pow_le_pow_left₀ (by norm_num) hb _)
    calc (((r + 1).factorial : ℕ) : ℝ) ^ 2 ≤ (((r + 1 : ℕ) : ℝ) ^ (r + 1)) ^ 2 := pow_le_pow_left₀ (by positivity) hf 2
      _ ≤ ((b ^ (r + 1)) ^ (r + 1)) ^ 2 := pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) hs2 _) 2
      _ = b ^ (2 * (r + 1) ^ 2) := by rw [← pow_mul, ← pow_mul]; ring_nf
  calc 4 ^ (r + 1) * (((r + 1).factorial : ℕ) : ℝ) ^ 2 * ρ ^ (2 * (r + 1))
      ≤ b ^ (2 * (r + 1)) * b ^ (2 * (r + 1) ^ 2) * b ^ ((n + 2) * (2 * (r + 1))) :=
        mul_le_mul (mul_le_mul h2 h3 (by positivity) (by positivity)) h1 (by positivity) (by positivity)
    _ = b ^ (2 * (r + 1) + 2 * (r + 1) ^ 2 + (n + 2) * (2 * (r + 1))) := by rw [pow_add, pow_add]
    _ ≤ b ^ ((2 * r + 2) ^ 2 * (n + 4)) := pow_le_pow_right₀ hb1 (by nlinarith [Nat.zero_le (r * n)])
    _ = (b ^ ((2 * r + 2) ^ 2)) ^ (n + 4) := by rw [pow_mul]

theorem height_bounds : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Formalism.MainNotions.S.UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := by
  intro Cg cb Cu cT CT C0 A
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |CT| + |Cg| + 1 ≤ (N : ℝ) := ⟨⌈|CT| + |Cg| + 1⌉₊, Nat.le_ceil _⟩
  have hCT : CT ≤ (N : ℝ) := by linarith [le_abs_self CT, abs_nonneg Cg]
  have hCg : Cg ≤ (N : ℝ) := by linarith [le_abs_self Cg, abs_nonneg CT]
  refine ⟨((2 * N + 7 : ℕ) : ℝ), by push_cast; linarith [(N.cast_nonneg : (0:ℝ) ≤ N)], ?_⟩
  intro D large₂ u u' C' Cl hCl
  unfold Formalism.MainNotions.S.UnitaryVolumeMass.stHH
  intro hyp F0 hF0e hF0z Λ hΛ F' hF' hrel
  have hS0 := hyp.1.1
  obtain ⟨hr1, -, -, hTu3, hTu3', -⟩ := hyp.2.1
  obtain ⟨-, -, hmf, hfk, -, -, -, -, -, -, hlrd, hkb, hg1, -, -, -, -, -, -, -, -, -, hTr, -, -⟩ := hS0
  have hm : D.R.m = 2 * D.R.rS + 2 := (GlobalTheory.real_places_facts D).2.2.2.1
  have hrd1 : 1 ≤ D.host.rdE := GlobalTheory.RealPlaces.one_le_rdE D
  have hL1 : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hb2 : 2 ≤ large₂.sc.b := by
    have := Real.add_one_le_exp large₂.sc.L
    show 2 ≤ Real.exp large₂.sc.L
    linarith
  have hb1 : 1 ≤ large₂.sc.b := by linarith
  have hb0 : 0 < large₂.sc.b := by linarith
  have hrdb : D.host.rdE ≤ large₂.sc.b := by
    have h1 : Real.log D.host.rdE ≤ large₂.sc.L := hlrd.trans (div_le_self (by linarith) hCl)
    exact (Real.log_le_iff_le_exp (by linarith)).mp h1
  have hY : D.host.rdE ^ (2 * (D.R.rS + 1) ^ 2) ≤ (large₂.sc.b ^ (D.R.m ^ 2)) := by
    refine (pow_le_pow_left₀ (by linarith) hrdb _).trans (pow_le_pow_right₀ hb1 ?_)
    rw [hm]; nlinarith
  have hB1 : 1 ≤ (large₂.sc.b ^ (D.R.m ^ 2)) := one_le_pow₀ hb1
  have hB0 : 0 ≤ (large₂.sc.b ^ (D.R.m ^ 2)) := by linarith
  have hZint : ∀ a b, IsIntegral ℤ ((ZhatL (lf D F0) F') a b) := fun a b => zhat_integral D F0 Λ hΛ F' hF' a b
  have hm2 : (2:ℝ) ≤ D.R.m := by rw [hm]; push_cast; linarith [(D.R.rS.cast_nonneg : (0:ℝ) ≤ D.R.rS)]
  have hTB : ∀ w, ((D.mem w).A.T : ℝ) ≤ (large₂.sc.b ^ (D.R.m ^ 2)) ^ N := fun w => by
    have h1 := (hTr w).2
    refine (show ((D.mem w).A.T : ℝ) ≤ _ from h1).trans ?_
    rw [← pow_mul, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hb1
    push_cast
    have e1 : CT * (D.R.m : ℝ) ≤ (N : ℝ) * D.R.m := mul_le_mul_of_nonneg_right hCT (by linarith)
    have e2 : (N : ℝ) * D.R.m ≤ (N : ℝ) * (D.R.m : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (N.cast_nonneg)
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc NT D u = ((D.mem u).A.T : ℝ) ^ D.R.f := rfl
      _ ≤ ((large₂.sc.b ^ (D.R.m ^ 2)) ^ N) ^ D.R.f := pow_le_pow_left₀ (Nat.cast_nonneg _) (hTB u) _
      _ ≤ ((large₂.sc.b ^ (D.R.m ^ 2)) ^ N) ^ D.R.f * QQ D (ZhatL (lf D F0) F') ^ 2 :=
          le_mul_of_one_le_right (pow_nonneg (pow_nonneg hB0 _) _) (one_le_pow₀ (one_le_QQ D _))
      _ ≤ HHZ D large₂.sc.b ((2 * N + 7 : ℕ) : ℝ) (ZhatL (lf D F0) F') :=
          final_le D (ZhatL (lf D F0) F') hb1 N hY (pow_nonneg hB0 _) (pow_le_pow_right₀ hB1 (by omega))
  · have hfin := final_le D (ZhatL (lf D F0) F') hb1 N hY zero_le_one (one_le_pow₀ hB1)
    rw [one_pow, one_mul] at hfin
    exact (G_le D (ZhatL (lf D F0) F') (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hfin
  · have hg := G_inv_le D (ZhatL (lf D F0) F') hZint hr1 (T := Tu D u) (T' := Tu D u') (by omega) (by omega) hY
    refine hg.trans (final_le D (ZhatL (lf D F0) F') hb1 N hY (by positivity) ?_)
    have hm0 : D.R.m ^ 2 ≠ 0 := by rw [hm]; positivity
    have h2B : (2:ℝ) ≤ (large₂.sc.b ^ (D.R.m ^ 2)) := hb2.trans (le_self_pow₀ hb1 hm0)
    have hT1 : ((Tu D u : ℕ) : ℝ) ≤ (large₂.sc.b ^ (D.R.m ^ 2)) ^ N := hTB u
    have hT2 : ((Tu D u' : ℕ) : ℝ) ≤ (large₂.sc.b ^ (D.R.m ^ 2)) ^ N := hTB u'
    have hTT : 2 * ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) ≤ (large₂.sc.b ^ (D.R.m ^ 2)) * (large₂.sc.b ^ (D.R.m ^ 2)) ^ N * (large₂.sc.b ^ (D.R.m ^ 2)) ^ N :=
      mul_le_mul (mul_le_mul h2B hT1 (Nat.cast_nonneg _) hB0) hT2 (Nat.cast_nonneg _)
        (mul_nonneg hB0 (pow_nonneg hB0 _))
    calc (large₂.sc.b ^ (D.R.m ^ 2)) ^ 2 * (2 * ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ≤ (large₂.sc.b ^ (D.R.m ^ 2)) ^ 2 * ((large₂.sc.b ^ (D.R.m ^ 2)) * (large₂.sc.b ^ (D.R.m ^ 2)) ^ N * (large₂.sc.b ^ (D.R.m ^ 2)) ^ N) :=
          mul_le_mul_of_nonneg_left hTT (pow_nonneg hB0 _)
      _ = (large₂.sc.b ^ (D.R.m ^ 2)) ^ (2 * N + 3) := by ring
      _ ≤ (large₂.sc.b ^ (D.R.m ^ 2)) ^ (2 * N + 5) := pow_le_pow_right₀ hB1 (by omega)
  · have hcx : ∀ w : InfinitePlace D.host.E, w.IsComplex := by
      intro w
      obtain ⟨τ, hτ, -⟩ := GlobalTheory.RealPlaces.existsUnique_place D w
      rw [← hτ, InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_iff]
      exact fun h => GlobalTheory.RealPlaces.ne_conj D τ τ h.symm
    obtain ⟨p, hp⟩ := hrel
    obtain ⟨Z₂, hZ2, hbd⟩ := GlobalTheory.T.exists_zEquiv_gram_bounded_minors D.host.E hcx D.R.rS (ZhatL (lf D F0) F') p hp
    refine ⟨Z₂, hZ2, fun j I J _ => ?_⟩
    have hfr : finrank ℚ D.host.E = 2 * D.R.f := GlobalTheory.RealPlaces.finrank_E D
    have hf1 : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
    have hrdE : |(discr D.host.E : ℝ)| ^ (1 / (finrank ℚ D.host.E : ℝ)) = D.host.rdE := rfl
    have hρ0 : 0 ≤ (Real.sqrt (finrank ℚ D.host.E) * |(discr D.host.E : ℝ)| ^ (1 / (finrank ℚ D.host.E : ℝ))) := by positivity
    have hρ1 : 1 ≤ (Real.sqrt (finrank ℚ D.host.E) * |(discr D.host.E : ℝ)| ^ (1 / (finrank ℚ D.host.E : ℝ))) := by
      rw [hrdE]
      refine one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr ?_) hrd1
      rw [hfr]; push_cast
      have : (1:ℝ) ≤ D.R.f := by exact_mod_cast hf1
      linarith
    have hfb : (D.R.f : ℝ) ≤ large₂.sc.b ^ N := by
      have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (hf1.trans hfk)
      have hfk' : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
      have h1 : (D.R.f : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
      have h2 : (D.R.k : ℝ) * large₂.sc.b ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 :=
        le_self_pow₀ (one_le_mul_of_one_le_of_one_le hk1 hb1) (by norm_num)
      have h3 : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ large₂.sc.b ^ Cg := hkb.trans hg1
      have h4 : large₂.sc.b ^ Cg ≤ large₂.sc.b ^ N := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hb1 hCg
      linarith
    have hsq : Real.sqrt (finrank ℚ D.host.E) ≤ large₂.sc.b ^ (N + 1) := by
      have h1 : ((finrank ℚ D.host.E : ℕ) : ℝ) ≤ (large₂.sc.b ^ (N + 1)) ^ 2 := by
        rw [hfr]; push_cast
        calc 2 * (D.R.f : ℝ) ≤ 2 * large₂.sc.b ^ N := by linarith
          _ ≤ large₂.sc.b * large₂.sc.b ^ N := by nlinarith [pow_nonneg hb0.le N]
          _ = large₂.sc.b ^ (N + 1) := by ring
          _ ≤ (large₂.sc.b ^ (N + 1)) ^ 2 := le_self_pow₀ (one_le_pow₀ hb1) (by norm_num)
      calc Real.sqrt (finrank ℚ D.host.E) ≤ Real.sqrt ((large₂.sc.b ^ (N + 1)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = large₂.sc.b ^ (N + 1) := Real.sqrt_sq (pow_nonneg hb0.le _)
    have hρb : (Real.sqrt (finrank ℚ D.host.E) * |(discr D.host.E : ℝ)| ^ (1 / (finrank ℚ D.host.E : ℝ))) ≤ large₂.sc.b ^ (N + 2) := by
      rw [hrdE]
      calc Real.sqrt (finrank ℚ D.host.E) * D.host.rdE ≤ large₂.sc.b ^ (N + 1) * large₂.sc.b :=
            mul_le_mul hsq hrdb (by linarith) (pow_nonneg hb0.le _)
        _ = large₂.sc.b ^ (N + 2) := by ring
    have hc1 : 1 ≤ (4 ^ (D.R.rS + 1) * (((D.R.rS + 1).factorial : ℕ) : ℝ) ^ 2 * (Real.sqrt (finrank ℚ D.host.E) * |(discr D.host.E : ℝ)| ^ (1 / (finrank ℚ D.host.E : ℝ))) ^ (2 * (D.R.rS + 1))) :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
          (one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))))
        (one_le_pow₀ hρ1)
    have hcB := const_le hb2 D.R.rS N hρ0 hρb
    obtain ⟨hmA, hmB⟩ := minors_le D (ZhatL (lf D F0) F') Z₂ hZint hZ2 hc1 hY I J (fun τ => hbd (embS D τ) j I J)
    have hW : (large₂.sc.b ^ (D.R.m ^ 2)) * (4 ^ (D.R.rS + 1) * (((D.R.rS + 1).factorial : ℕ) : ℝ) ^ 2 * (Real.sqrt (finrank ℚ D.host.E) * |(discr D.host.E : ℝ)| ^ (1 / (finrank ℚ D.host.E : ℝ))) ^ (2 * (D.R.rS + 1))) ≤ (large₂.sc.b ^ (D.R.m ^ 2)) ^ (2 * N + 5) := by
      have e : (2 * D.R.rS + 2) ^ 2 = D.R.m ^ 2 := by rw [hm]
      calc (large₂.sc.b ^ (D.R.m ^ 2)) * (4 ^ (D.R.rS + 1) * (((D.R.rS + 1).factorial : ℕ) : ℝ) ^ 2 * (Real.sqrt (finrank ℚ D.host.E) * |(discr D.host.E : ℝ)| ^ (1 / (finrank ℚ D.host.E : ℝ))) ^ (2 * (D.R.rS + 1))) ≤ (large₂.sc.b ^ (D.R.m ^ 2)) * (large₂.sc.b ^ ((2 * D.R.rS + 2) ^ 2)) ^ (N + 4) :=
            mul_le_mul_of_nonneg_left hcB hB0
        _ = (large₂.sc.b ^ (D.R.m ^ 2)) ^ (N + 5) := by rw [e]; ring
        _ ≤ _ := pow_le_pow_right₀ hB1 (by omega)
    have hfW := final_le D (ZhatL (lf D F0) F') hb1 N hY (mul_nonneg hB0 (by linarith)) hW
    exact ⟨hmA.trans hfW, hmB.trans hfW⟩

end GlobalTheory.GramHeight
