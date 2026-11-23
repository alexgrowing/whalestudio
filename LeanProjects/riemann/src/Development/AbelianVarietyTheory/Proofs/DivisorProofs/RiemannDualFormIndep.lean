import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnProdOfForall
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoOfSameFactor
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomLift

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

noncomputable section

namespace GlobalTheory.RiemIndep

section Frames

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L N : LB A.left} {L' : LB A'.left} {g : ℕ}

theorem ex_add_mem (u : HolUnif A L g) (l : u.Λ) (z : Fin g → ℂ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

open PullHermitian in

theorem herm_eq_zero (hN : N.IsLB) (h0 : cls N hN = 0) (u : HolUnif A N g) (B : Matrix (Fin g) (Fin g) ℂ)
    (c : u.Λ → ℂ) (hB : B.IsHermitian) (hc : ∀ l, ‖c l‖ = 1)
    (hf : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ N.U i → u.fr i z =
      c l * Complex.exp (Real.pi * hermForm B z l + Real.pi / 2 * hermForm B l l) * u.fr i (z + l)) : B = 0 := by
  obtain ⟨t, ht⟩ := (CechPic.cls_eq_zero_iff hN).1 h0
  obtain ⟨r, hr, hrφ⟩ := exists_glue (fun i : N.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ N.U i})
    (fun i => (u.hol _ 0).1) (fun z => exists_chart (u.ex z).left hN)
    (fun i z => valAt' (u.ex z).left _ (t.s i).val / u.fr i z)
    (fun i => by
      simp only [div_eq_mul_inv]
      exact (u.hol _ (t.s i).val).2.mul ((u.fr_hol i).inv fun z hz => u.fr_ne i z hz))
    (fun i j z hi hj => by
      have hij := inf_of _ hi hj
      have e := congrArg (unitVal _ hij) (ht i j)
      have e' : unitVal _ hi (t.s i) = unitVal _ hij (N.g i j) * unitVal _ hj (t.s j) :=
        (unitVal_res _ inf_le_left hij hi _).symm.trans (e.trans ((map_mul _ _ _).trans
          (congrArg (_ * ·) (unitVal_res _ inf_le_right hij hj _))))
      rw [div_eq_div_iff (u.fr_ne _ _ hi) (u.fr_ne _ _ hj), u.fr_compat i j z hij, valAt'_eq_unitVal _ hi,
        valAt'_eq_unitVal _ hj, valAt'_eq_unitVal _ hij, e', Units.val_mul]
      ring)
  haveI := u.discrete
  refine (appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full B c r hB hc hr (fun z => ?_) fun l z => ?_).1
  · obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hN
    rw [hrφ i z hi, valAt'_eq_unitVal _ hi]
    exact div_ne_zero (Units.ne_zero _) (u.fr_ne _ _ hi)
  · obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hN
    have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ N.U i := by rwa [ex_add_mem]
    have h1 := u.fr_ne _ _ hi
    have h2 := u.fr_ne _ _ hi'
    rw [hrφ i z hi, hrφ i (z + l) hi', ex_add_mem, div_eq_iff h2, mul_right_comm, ← hf l i z hi]
    field_simp

variable (u : HolUnif A L g) (u' : HolUnif A' L' g) (ψ : A ⟶ A') (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))

theorem covers (hT : ∀ z, u'.ex (T z) = u.ex z ≫ ψ) (k : Fin 3) (z : Fin g → ℂ) :
    u'.ex (![T + T, T, 0] k z) = u.ex z ≫ ![ψ * ψ, ψ, 1] k := by
  fin_cases k
  · change u'.ex (T z + T z) = u.ex z ≫ (ψ * ψ)
    rw [u'.ex_add, hT, MonObj.comp_mul]
  · exact hT z
  · change u'.ex 0 = u.ex z ≫ 1
    rw [MonObj.comp_one]
    exact (u'.ker 0).2 (zero_mem _)

abbrev diagLB (L' : LB A'.left) (ψ : A ⟶ A') : LB A.left :=
  LB.LinComb L' (fun k => (![ψ * ψ, ψ, 1] k).left) ![1, -2, 1]

theorem cls_diagLB (hL' : L'.IsLB) (h : (diagLB L' ψ).IsLB) : cls _ h = lam (cls L' hL') ψ ψ := by
  refine (CechPic.cls_linComb hL' _ _ h).trans ?_
  rw [Fin.sum_univ_three, lam]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  module

theorem factor_diag (hT : ∀ z, u'.ex (T z) = u.ex z ≫ ψ) {H : Matrix (Fin g) (Fin g) ℂ} {χ : u'.Λ → ℂ}
    (hA : u'.IsAH H χ) (l : u.Λ) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (diagLB L' ψ).U i →
      (linCombUnif u u' _ _ ![1, -2, 1] (covers u u' ψ T hT)).fr i z =
        c * Complex.exp (Real.pi * (2 * hermForm H (T z) (T l)) + Real.pi / 2 * (2 * hermForm H (T l) (T l))) *
          (linCombUnif u u' _ _ ![1, -2, 1] (covers u u' ψ T hT)).fr i (z + l) := by
  have hl : T l ∈ u'.Λ := by
    rw [← u'.ker, hT, (u.ker l).2 l.2, ← (u.ker 0).2 u.Λ.zero_mem, ← hT, map_zero]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hχ := hA.2.2.1
  refine ⟨χ ⟨T l + T l, add_mem hl hl⟩ / χ ⟨T l, hl⟩ ^ 2, by simp [hχ], fun i z hz => ?_⟩
  have hc : ∀ k, ⊤ ≤ (u'.ex (![T + T, T, 0] k z)).left ⁻¹ᵁ L'.U (i k) := fun k => by
    rw [covers u u' ψ T hT]
    exact (CubeValues.le_preimage_wchart (u.ex z).left L' _ i).1 hz k
  have h0 := hA.2.2.2 ⟨T l + T l, add_mem hl hl⟩ (i 0) (T z + T z) (hc 0)
  have h1 := hA.2.2.2 ⟨T l, hl⟩ (i 1) (T z) (hc 1)
  have h4 : χ ⟨T l, hl⟩ ≠ 0 := norm_ne_zero_iff.1 (by rw [hχ]; exact one_ne_zero)
  change ∏ k, u'.fr (i k) (![T + T, T, 0] k z) ^ (![1, -2, 1] k : ℤ) =
    _ * ∏ k, u'.fr (i k) (![T + T, T, 0] k (z + l)) ^ (![1, -2, 1] k : ℤ)
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, LinearMap.add_apply,
    LinearMap.zero_apply, map_add, zpow_one, zpow_neg, zpow_ofNat]
  rw [h0, h1, add_zero]
  simp only [hermForm, star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  generalize (T z ⬝ᵥ H.mulVec (star (T l))) = a
  generalize (T l ⬝ᵥ H.mulVec (star (T l))) = b
  have e : Complex.exp (Real.pi * (a + a + (a + a)) + Real.pi / 2 * (b + b + (b + b))) =
      Complex.exp (Real.pi * (2 * a) + Real.pi / 2 * (2 * b)) * Complex.exp (Real.pi * a + Real.pi / 2 * b) ^ 2 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h6 := Complex.exp_ne_zero (Real.pi * a + Real.pi / 2 * b)
  rw [e]
  generalize Complex.exp (Real.pi * a + Real.pi / 2 * b) = s at h6
  simp only [mul_pow, mul_inv]
  field_simp

open PullHermitian in

theorem hermForm_eq_of_lam (hL : L.IsLB) (hL' : L'.IsLB) (hT : ∀ z, u'.ex (T z) = u.ex z ≫ ψ)
    {H H' : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} {χ' : u'.Λ → ℂ} (hA : u.IsAH H χ) (hA' : u'.IsAH H' χ')
    (h : lam (cls L' hL') ψ ψ = lam (cls L hL) (𝟙 A) (𝟙 A)) (z w : Fin g → ℂ) :
    hermForm H' (T z) (T w) = hermForm H z w := by
  have hI : ∀ z, u.ex (LinearMap.id (R := ℂ) z) = u.ex z ≫ 𝟙 A := fun z => (Category.comp_id _).symm
  choose c hc hf using factor_diag u u (𝟙 A) LinearMap.id hI hA
  choose c' hc' hf' using factor_diag u u' ψ T hT hA'
  have d : (diagLB L (𝟙 A)).IsLB := LB.isLB_linComb hL _ _
  have d' : (diagLB L' ψ).IsLB := LB.isLB_linComb hL' _ _
  set H₂ := (LinearMap.toMatrix' T).transpose * H' * (LinearMap.toMatrix' T).transpose.conjTranspose with hH₂
  have hH₂h : H₂.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hA'.1
  have hs : ∀ z w, hermForm ((2 : ℂ) • H₂ - (2 : ℂ) • H) z w = 2 * hermForm H' (T z) (T w) - 2 * hermForm H z w :=
    fun z w => by rw [hermForm_sub_smul, hH₂, hermForm_pull]
  have key := herm_eq_zero (LB.isLB_div d' d)
    (by rw [CechPic.cls_div d' d, cls_diagLB ψ hL', cls_diagLB _ hL, h, sub_self])
    (SameFactor.divUnif (linCombUnif u u _ _ ![1, -2, 1] (covers u u _ _ hI))
      (linCombUnif u u' _ _ ![1, -2, 1] (covers u u' ψ T hT)) rfl)
    ((2 : ℂ) • H₂ - (2 : ℂ) • H) (fun l => c' l / c l)
    ((hH₂h.smul (by simp [IsSelfAdjoint])).sub (hA.1.smul (by simp [IsSelfAdjoint])))
    (fun l => (norm_div _ _).trans ((congrArg₂ (· / ·) (hc' l) (hc l)).trans (div_one _))) fun l i z hz => by
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
      have e1 := hf' l i.1 z h1
      have e2 := hf l i.2 z h2
      refine (congrArg₂ (fun a b => a * b⁻¹) e1 e2).trans ?_
      rw [hs, hs]
      change _ = _ * (_ * _⁻¹)
      rw [mul_sub, mul_sub, sub_add_sub_comm, Complex.exp_sub]
      simp only [LinearMap.id_apply, mul_inv, div_eq_mul_inv]
      ring
  have := hs z w
  rw [key] at this
  simp only [hermForm, Matrix.zero_mulVec, dotProduct_zero] at this ⊢
  linear_combination (-1 / 2 : ℂ) * this

end Frames

theorem exists_lin (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d d' : P.RiemannData y) :
    ∃ T : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), (∀ z, (d'.u.ex (T z)).left ≫ d'.φ = (d.u.ex z).left ≫ d.φ) ∧
      ∀ z w, hermForm d'.H (T z) (T w) = hermForm d.H z w := by
  obtain ⟨ψ, e⟩ := SharpPull.exists_lift d.isPull d'.isPull (𝟙 P.A)
  have hψ := SharpPull.isMonHom_lift d.isPull d'.isPull e
  have hψφ : ψ.left ≫ d'.φ = d.φ := e.trans (Category.comp_id _)
  have hA := PolPull.isAbelianScheme_of_isGrpPullback P.isAb d.isPull
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback P.isAb d'.isPull
  obtain ⟨t₁, t₂⟩ := TorusTransfer.tangent_bijective d'.u
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback d'.isPull.1 P.smoothDim)
  obtain ⟨T, hT, -⟩ := HomLinear.exists_linear_of_isMonHom d.B d'.B hA hA' d.L d'.L P.g P.g d.u d'.u t₁ t₂ ψ hψ
  refine ⟨T, fun z => ?_, hermForm_eq_of_lam d.u d'.u ψ T d.isLB d'.isLB hT d.isAH d'.isAH ?_⟩
  · rw [hT, Over.comp_left, Category.assoc, hψφ]
  have k (b : P.RiemannData y) (x : d.B ⟶ b.B) : lam (cls b.L b.isLB) x x =
      CechPic.pull ((lift x x).left ≫ sqMap b.isPull.1.w) P.c := by
    rw [CechPic.pull_comp, b.pol, CechPic.pull_lam, lift_fst, lift_snd]
  have k₁ (b : P.RiemannData y) (x : d.B ⟶ b.B) :
      ((lift x x).left ≫ sqMap b.isPull.1.w) ≫ pullback.fst _ _ = x.left ≫ b.φ := by
    refine (Category.assoc _ _ _).trans ((congrArg _ (pullback.lift_fst _ _ _)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans (congrArg (·.left ≫ b.φ) (lift_fst x x))
  have k₂ (b : P.RiemannData y) (x : d.B ⟶ b.B) :
      ((lift x x).left ≫ sqMap b.isPull.1.w) ≫ pullback.snd _ _ = x.left ≫ b.φ := by
    refine (Category.assoc _ _ _).trans ((congrArg _ (pullback.lift_snd _ _ _)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans (congrArg (·.left ≫ b.φ) (lift_snd x x))
  have k₃ : ψ.left ≫ d'.φ = (𝟙 d.B : d.B ⟶ d.B).left ≫ d.φ := hψφ.trans (Category.id_comp _).symm
  rw [k, k]
  congr 2
  exact pullback.hom_ext ((k₁ _ _).trans (k₃.trans (k₁ _ _).symm)) ((k₂ _ _).trans (k₃.trans (k₂ _ _).symm))

open Matrix HermFrame in

theorem riemann_dual_form_indep : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d d' : P.RiemannData y)
    (W : P.A.left.Opens) (f f' : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W →
    HermFrame.form (HermFrame.dualGram d.H) (d.cov W f) (d.cov W f') =
      HermFrame.form (HermFrame.dualGram d'.H) (d'.cov W f) (d'.cov W f') := by
  intro S P y d d' W f f' hW
  obtain ⟨T, hT, hH⟩ := RiemIndep.exists_lin S P y d d'
  set M := LinearMap.toMatrix' T with hM
  have hMv : ∀ z, M *ᵥ z = T z := fun z => LinearMap.toMatrix'_mulVec T z
  have hchg : d.H = chg M d'.H := by
    ext a b
    rw [← form_single (chg M d'.H), form_chg, hMv, hMv]
    exact (form_single d.H a b).symm.trans (hH _ _).symm
  have hinj : Function.Injective M.mulVec := by
    refine (injective_iff_map_eq_zero M.mulVecLin).2 fun v hv => ?_
    by_contra hne
    have h1 := (posDef_iff.1 d.posDef).2 v hne
    rw [hchg, form_chg] at h1
    have h0 : M *ᵥ v = 0 := hv
    rw [h0] at h1
    simp [form] at h1
  have hU : IsUnit M := mulVec_injective_iff_isUnit.1 hinj
  have hMN : M * M⁻¹ = 1 := mul_nonsing_inv M ((isUnit_iff_isUnit_det M).1 hU)
  have hfn : ∀ g : Γ(P.A.left, W), d.fn W g = d'.fn W g ∘ T := fun g => by
    funext z
    simp only [PPAS.RiemannData.fn, Function.comp_apply, hT]
  have hTd : ∀ v, fderiv ℂ (⇑T) 0 v = T v := fun v => by
    have := (LinearMap.toContinuousLinearMap T).fderiv (x := 0)
    exact congrArg (fun L => L v) this
  have hcov : ∀ g : Γ(P.A.left, W), d.cov W g = Mᵀ *ᵥ d'.cov W g := fun g => by
    funext a
    have hd := d'.differentiableAt_fn g hW
    have hd' : DifferentiableAt ℂ (d'.fn W g) (T 0) := by rw [map_zero]; exact hd
    have hTdiff : DifferentiableAt ℂ (⇑T) 0 := (LinearMap.toContinuousLinearMap T).differentiableAt
    simp only [PPAS.RiemannData.cov]
    rw [hfn, fderiv_comp 0 hd' hTdiff, ContinuousLinearMap.comp_apply, hTd, map_zero, ← hMv,
      mulVec_single_one]
    change _ = ∑ b, M.col a b * fderiv ℂ (d'.fn W g) 0 (Pi.single b 1)
    generalize fderiv ℂ (d'.fn W g) 0 = L
    conv_lhs => rw [pi_eq_sum_univ (M.col a)]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [hchg, dualGram_chg hMN, form_chg, hcov, hcov, mulVec_mulVec, mulVec_mulVec, ← transpose_mul, hMN,
    transpose_one, one_mulVec, one_mulVec]

end GlobalTheory.RiemIndep
