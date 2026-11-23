import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open NumberField CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.Mean4O

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SecLower
open GlobalTheory.CxPts

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem ev_secToPow_one {B : LB X} (s : B.Sec) {σ : k →+* ℂ} (J : PUnit → B.ι) (y : CxPts p σ)
    (hy : y ∈ ptsIn p σ (B.U (J PUnit.unit))) :
    ev p σ ((lbPow B 1).U J) ((secToPow s 1).f J) y = ev p σ (B.U (J PUnit.unit)) (s.f (J PUnit.unit)) y := by
  have hJ : y ∈ ptsIn p σ ((lbPow B 1).U J) := mem_pow_iff.2 hy
  change ev p σ _ (resG X _ (s.f (J PUnit.unit) ^ 1)) y = _
  exact (ev_res _ hJ _).trans (congrArg (ev p σ _ · y) (pow_one _))

theorem nsq_pow_one_secToPow {B : LB X} {σ : k →+* ℂ} (φ : Weight p σ B) (s : B.Sec) (y : CxPts p σ) :
    (φ.pow 1).nsq (secVal p σ (secToPow s 1)) y = φ.nsq (secVal p σ s) y := by
  have hi := mem_pick φ.isLB y
  rw [(φ.pow 1).nsq_eq (secVal_mem _) (i := fun _ => pick φ.isLB y) (mem_pow_iff.2 hi), φ.nsq_eq (secVal_mem _) hi,
    Weight.zpow_φ]
  refine congrArg₂ (fun a b => ‖a‖ ^ 2 * Real.exp b) (ev_secToPow_one s _ y hi) ?_
  simp

theorem exists_lower_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (N : HermLB p) (s : N.B.Sec), ∃ c : ℝ, ∀ x : X, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s → IsAlgPt x →
      ∀ b : ℝ, IsPtHt N x b → -c ≤ b := by
  intro k _ X _ p D hX N s
  have := hX.finite_emb
  have hc : ∀ σ, ∃ M : ℝ, ∀ y : CxPts p σ, (N.φ σ).nsq (secVal p σ s) y ≤ M := fun σ => by
    have := hX.compactSpace σ
    obtain ⟨M, hM⟩ := (isCompact_range ((N.cInf σ).continuous_nsq s)).bddAbove
    exact ⟨M, fun y => hM ⟨y, rfl⟩⟩
  choose M hM using hc
  obtain ⟨B, hB⟩ := Finite.exists_le M
  refine ⟨Real.log (max B 1) / 2, fun x hx hxa b hb => ?_⟩
  refine GlobalTheory.SmallSecHeight.le_ptHt k X p D hX N 1 (-(Real.log (max B 1) / 2)) b x (secToPow s 1) le_rfl
    (fun σ y => ?_) ((nonzeroLocus_secToPow s le_rfl).symm ▸ hx) hxa hb
  refine (nsq_pow_one_secToPow ((N.shift _ _).φ σ) s y).trans_le ((N.nsq_shift _ _ (secVal p σ s) y).trans_le ?_)
  have hpos : (0 : ℝ) < max B 1 := lt_max_of_lt_right one_pos
  have e : Real.exp (-(2 * -(-(Real.log (max B 1) / 2)))) = (max B 1)⁻¹ := by
    rw [show -(2 * -(-(Real.log (max B 1) / 2))) = -Real.log (max B 1) by ring, Real.exp_neg, Real.exp_log hpos]
  rw [e, ← div_eq_mul_inv, div_le_one hpos]
  exact ((hM σ y).trans (hB σ)).trans (le_max_left _ _)

end GlobalTheory.SecLower
