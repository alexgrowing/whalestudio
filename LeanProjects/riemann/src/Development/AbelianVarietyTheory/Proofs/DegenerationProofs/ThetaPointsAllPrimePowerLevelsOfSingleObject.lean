import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullAll
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteAlgClosedFieldPowerSeriesExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QvalAddTowerStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxNestStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValuesStatement
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.AllLevels

theorem ser_nested {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    {a : ArcIn D l β O' b} {K : Type} [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K]
    [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K] (S : Ser a K (algebraMap _ K))
    (r m : ℕ) (hr : Odd r) (hm : Odd m) : ∃ c : Kˣ, ∀ x, S.v (r * m) (r • x) = c * S.v m x := by
  obtain ⟨C, _, _, _, _, _, gam, u, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.exists_complete_algClosed_field_powerSeries_extension O' K
  obtain ⟨A, ρ, -, -, hρ, hv⟩ := S.val C gam u h₁ h₂ h₃ h₄
  have hR : Roots u ρ := ⟨Units.ext ((hρ 1).trans ((congrArg gam S.r_one).trans h₃.symm)), fun n k hn hk => Units.ext (by
    rw [Units.val_pow_eq_pow_val, hρ, hρ, ← map_pow, ← Units.val_pow_eq_pow_val, S.roots.2 n k hn hk])⟩
  obtain ⟨b₁, -, b₃, -, b₅⟩ := GlobalTheory.T.torus_torsion_points_correspond_values O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨q₁, q₂⟩ := GlobalTheory.T.qval_add_of_tower E H D O' a.D₀ a.oa a.even a.bimult C A.I A.N A.ν A.q b₁ b₃
    (fun k => ⟨(b₅ k).1, (b₅ k).2.2⟩) A.hq
  have hrm : Odd (r * m) := hr.mul hm
  choose p hp _ using fun x => existsUnique_twRel A.be u (ρ (m ^ 2)) (hR.pow (pow_pos hm.pos 2)) (A.q _ x)
  choose p' hp' _ using fun x => existsUnique_twRel A.be u (ρ ((r * m) ^ 2)) (hR.pow (pow_pos hrm.pos 2)) (A.q _ x)
  obtain ⟨s, hs⟩ := (hv m hm p hp).1
  obtain ⟨s', hs'⟩ := (hv _ hrm p' hp').1
  have key : ∀ x, gam (S.v (r * m) (r • x)) = (s' * s⁻¹ : Cˣ) * gam (S.v m x) := fun x => by
    rw [hs, hs', GlobalTheory.T.twist_tx_nsmul_eq_of_odd C A.N D.La A.q q₁ q₂ _ A.be u ρ hR r m hr hm x _ _ (hp' _) (hp x), Units.val_mul,
      _root_.mul_assoc, Units.inv_mul_cancel_left]
  by_cases h : ∃ x, S.v m x ≠ 0
  · obtain ⟨x₀, h₀⟩ := h
    have e : gam (S.v (r * m) (r • x₀) / S.v m x₀) = (s' * s⁻¹ : Cˣ) := by
      rw [map_div₀, key, mul_div_cancel_right₀ _ ((map_ne_zero gam).2 h₀)]
    refine ⟨Units.mk0 (S.v (r * m) (r • x₀) / S.v m x₀) fun h => (s' * s⁻¹).ne_zero (by rw [← e, h, map_zero]),
      fun x => gam.injective ?_⟩
    rw [map_mul, Units.val_mk0, e, key]
  · simp only [not_exists, not_not] at h
    exact ⟨1, fun x => gam.injective (by rw [key, h, mul_zero, map_zero, mul_zero])⟩

theorem one_object : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n : ℕ), n.Prime → Odd n → (∀ j, 2 ≤ j → ∃ o : Full D K, o.ρ = S.A.ρ ∧ o.I.ζ ((n ^ j) ^ 2) = S.A.I.ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (S.v (n ^ j))) → ∃ o : Full D K, o.ρ = S.A.ρ ∧ ∀ j, o.I.ζ (n ^ j) = S.A.I.ζ (n ^ j) ∧ o.Theta (n ^ j) (S.v (n ^ j)) := by
  intro hV _ _ _ h₁ h₂ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a _ K _ _ _ _ _ _ _ S n hn ho h
  exact exists_full_all hV.1.1 h₁ h₂ S.A.ρ S.A.I.ζ S.A.I.ζ_pow S.v (ser_nested S) hn ho h

end GlobalTheory.Ex.AllLevels
