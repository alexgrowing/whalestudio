import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesOfIsoOfIsGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmpleStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsVeryAmpleH1Zero

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Algebraise

theorem exists_veryAmple_h1Zero_pull : ∀ (A : Type) [CommRing A] (X : Over (Spec (CommRingCat.of A))) (L : LB X.left), L.IsLB → RelAmple X L → ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (g₀ : A →+* K) (X₀ : Scheme.{0}) (π : X₀ ⟶ X.left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ X.hom (Spec.map (CommRingCat.ofHom g₀)) → ∃ d : ℕ, 1 ≤ d ∧ FirstCohomologyVanishes ((AbLaw.pw L d).pull π) ∧ ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (AbLaw.pw L d)), VeryAmpleBy X.hom (AbLaw.pw L d) s := by
  intro A _ X L hL h K _ _ g₀ X₀ π f₀ hπ
  obtain ⟨d₀, hd₀, n₀, s₀, hs₀⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy A X L hL).1 h
  have hH := isLB_pw hL (d₀ : ℤ)
  have hH₀ := LB.isLB_pull hH π
  obtain ⟨s', w₀, hw₀, c⟩ := GlobalTheory.MorAlg.exists_isPull π hH s₀
  have hci : IsClosedImmersion (pullback.lift π f₀ hπ.w) := by
    have e : pullback.lift π f₀ hπ.w = hπ.isoPullback.hom := by
      apply pullback.hom_ext
      · exact (pullback.lift_fst _ _ _).trans hπ.isoPullback_hom_fst.symm
      · exact (pullback.lift_snd _ _ _).trans hπ.isoPullback_hom_snd.symm
    rw [e]
    infer_instance
  have hva := GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull A X.left X.hom _ n₀ s₀ hH hs₀ K g₀ X₀ f₀ π hπ.w hci
    _ w₀ s' hH₀ hw₀ c
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.serre_vanishing_very_ample.1 K X₀ f₀ _ n₀ s' hH₀ hva _ hH₀
  have h1 := ht₀ (t₀.toNat : ℤ) (Int.self_le_toNat t₀)
  obtain ⟨w, hw⟩ := lbIso_tw hH₀ (t₀.toNat : ℤ)
  have h2 := H1Iso.firstCohomologyVanishes_of_iso_of_isGen (isLB_tw hH₀ hH₀ _).cover (isLB_pw hH₀ _) w hw h1
  have h3 := veryAmpleBy_pw A X.left X.hom _ n₀ s₀ hH hs₀ (t₀.toNat + 1) (Nat.le_add_left _ _)
  have e : AbLaw.pw (AbLaw.pw L (d₀ : ℤ)) ((t₀.toNat + 1 : ℕ) : ℤ) =
      AbLaw.pw L ((d₀ * (t₀.toNat + 1) : ℕ) : ℤ) := by
    rw [pw_pw, Nat.cast_mul]
  refine ⟨d₀ * (t₀.toNat + 1), Nat.mul_pos hd₀ (Nat.succ_pos _), ?_, ?_⟩
  · rw [← e, pw_pull, Nat.cast_add, Nat.cast_one]
    exact h2
  · rw [← e]
    exact h3

end GlobalTheory.Algebraise
