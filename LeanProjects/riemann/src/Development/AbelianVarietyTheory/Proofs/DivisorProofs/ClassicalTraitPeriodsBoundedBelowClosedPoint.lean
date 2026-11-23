import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupRegularOverModuliPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRegularThetaSetupCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicTraitLiftFiniteThroughPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSingletonOfIsFiniteOfIsClosedImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassicalTraitPeriodsBoundedBelowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowNormValLeUnitaryThetaFiniteModelsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupFinrankLeMinSignatureUnitaryTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.PerBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

theorem sc_pos (t : UCTrait X₁ p z₁) : 0 < t.sc := by
  have hϖ0 : algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 t.T.irr.ne_zero
  have h0 : t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (t.int _).1 hinv
    apply t.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective t.T.V (FractionRing t.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold UCTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem be_pos (T : UTrait Xo c) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem eq_zero_of_sum_eq_zero (hpq : ¬ 1 ≤ Dw.p + Dw.q) (T : UTrait Xo c) (x : T.P.D.toPre.X) : x = 0 := by
  have hr := UTrait.finrank_le_min E H Dw l Xo c T
  have h0 : Module.finrank (𝓞 E) T.P.D.toPre.X = 0 := by omega
  have : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨a, ha, hax⟩ := Module.finrank_eq_zero_iff.1 h0 x
  obtain ⟨n, hn, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) a).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero ha)
  have h : n • x = 0 := by
    rw [← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul, hax, smul_zero]
  exact (smul_eq_zero.1 h).resolve_left hn

end GlobalTheory.UPoinc.PerBound

open GlobalTheory.UPoinc.PerBound in

theorem GlobalTheory.UPoinc.lam_of_closed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ K : ℝ, ∀ (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X), x ≠ 0 → ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  intro E _ _ _ H Dw l Xo c C X₁ p _ z₁ hz
  by_cases hpq : 1 ≤ Dw.p + Dw.q
  swap
  · exact ⟨0, fun t x hx => absurd (eq_zero_of_sum_eq_zero hpq t.T x) hx⟩
  obtain ⟨m, X', U, hU, hcov⟩ := GlobalTheory.T.exists_finite_regular_thetaSetup_cover E H Dw l Xo c C (GlobalTheory.T.exists_thetaSetup_regular_over_moduliPoint E H Dw hpq l Xo c C)
  choose K hK using fun k => GlobalTheory.T.unitary_classical_trait_periods_bounded_below E H Dw l Xo c C (X' k) p
  choose e he1 he using fun k => GlobalTheory.T.exists_pow_norm_val_le_unitaryTheta_finite_models E H Dw l Xo c C X₁ (X' k) z₁
  refine ⟨∑ k, (e k : ℝ) * |K k|, fun t x hx => ?_⟩
  have hzc : IsClosed ({X₁.π z₁} : Set C.Z) := by
    haveI := X₁.fin
    have := X₁.π.isClosedMap _ hz
    rwa [Set.image_singleton] at this
  obtain ⟨k, w, hwU, hw⟩ := hcov ((spMap t.ι ≫ t.T.y) (IsLocalRing.closedPoint (PadicAlgCl p)))
  have hgen : (X' k).π w = (gPt p ≫ (t.y ≫ X₁.π)) (IsLocalRing.closedPoint (PadicAlgCl p)) := by
    rw [hw, t.comm]
    rfl
  obtain ⟨y', hy'π, hy'w⟩ := GlobalTheory.T.exists_padicTrait_lift_finite_through_point _ _ (X' k).π (X' k).fin p (t.y ≫ X₁.π) w hgen
  have hz'π : (X' k).π (y' (cPt p)) = X₁.π z₁ := by
    have := congrArg (fun f => f (cPt p)) hy'π
    simp only [Scheme.Hom.comp_apply] at this
    rw [this, t.cen]
  have hz'c := GlobalTheory.T.isClosed_singleton_of_isFinite_of_isClosed_image _ _ _ (X' k).fin (y' (cPt p)) (hz'π ▸ hzc)
  let t' : UCTrait (X' k) p (y' (cPt p)) :=
    { y := y', cen := rfl, T := t.T, ι := t.ι, int := t.int, comm := by rw [hy'π]; exact t.comm }
  have hreg : (X' k).S.R ≤ (X' k).M.O ((gPt p ≫ t'.y) (IsLocalRing.closedPoint (PadicAlgCl p))) := by
    show (X' k).S.R ≤ (X' k).M.O ((gPt p ≫ y') (IsLocalRing.closedPoint (PadicAlgCl p)))
    rw [hy'w]
    exact (hU k).trans (RatModel.ringOn_le_O hwU)
  obtain ⟨h', hh'm, hh'⟩ := hK k (y' (cPt p)) hz'c t' hreg x hx
  obtain ⟨h, hhm, hh⟩ := he k p t (y' (cPt p)) t' hy'π.symm h' hh'm
  refine ⟨h, hhm, le_trans ?_ hh⟩
  have hs : 0 ≤ t.sc * t.T.be x x := mul_nonneg (sc_pos t).le (by exact_mod_cast (be_pos _ x hx).le)
  have hsum : (e k : ℝ) * |K k| ≤ ∑ k, (e k : ℝ) * |K k| :=
    Finset.single_le_sum (f := fun k => (e k : ℝ) * |K k|) (fun k _ => by positivity) (Finset.mem_univ k)
  have hKk : (e k : ℝ) * K k ≤ (e k : ℝ) * |K k| := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  calc Real.exp (-((∑ k, (e k : ℝ) * |K k|) * (t.sc * t.T.be x x)))
      ≤ Real.exp (-(K k * (t.sc * t.T.be x x))) ^ e k := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.2
        nlinarith
    _ ≤ ‖t'.val h'‖ ^ e k := pow_le_pow_left₀ (Real.exp_pos _).le hh' _
