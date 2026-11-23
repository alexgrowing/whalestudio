import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]

theorem pullSecs_fe' (hGF : GlobalFnsSt) {O : Type} [CommRing O] [StarRing O]
    [Module O D.toPre.X] (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O) (hΨ : Geo.Tor.TraceFormTwistIso D.toPre oa w0)
    (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
    (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ)
    (s : Fam D.toPre F k) :
    DegPre.FamFE D.toPre F (k * N) (pullSecs D F hL oa w0 uΨ huΨ a N hN hN1 k s) := by
  have hinj : ∀ χ₁ χ₂ : D.toPre.X, star a • χ₁ = star a • χ₂ → χ₁ = χ₂ := by
    intro χ₁ χ₂ h
    have h2 : (N : O) • χ₁ = (N : O) • χ₂ := by rw [← hN, mul_smul, mul_smul, h]
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul] at h2
    have h3 : (N : ℤ) • χ₁ = (N : ℤ) • χ₂ := by rw [natCast_zsmul, natCast_zsmul]; exact h2
    exact smul_right_injective D.toPre.X (Int.natCast_ne_zero.2 (by omega)) h3
  refine famFE_of_pullAl (D := D) (F := F) hGF oa w0 hΨ a N hN hN1 k s _ (fun χ => ?_) (fun β hβ j => ?_)
  · obtain ⟨hgen, hcorr⟩ := uPull_spec (D := D) (F := F) hL oa w0 uΨ huΨ a N hN hN1 k χ
    refine ⟨uPull (D := D) (F := F) hL oa w0 uΨ huΨ a N hN hN1 k χ, hgen, hcorr, ?_⟩
    have hex : ∃ χ', star a • χ' = star a • χ := ⟨χ, rfl⟩
    unfold pullSecs
    rw [dif_pos hex]
    exact secRel_pullSecs (D := D) (F := F) hL oa w0 uΨ huΨ a N hN hN1 k s χ hex.choose hex.choose_spec
      (hinj _ _ hex.choose_spec)
  · unfold pullSecs
    rw [dif_neg (by rintro ⟨χ, hχ⟩; exact hβ χ hχ.symm)]
    rfl

end ReciprocityTheory.ChartRestriction.G.DVR
