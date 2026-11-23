import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EndoEqOfSections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationNonnegIffSpanMultiplicationTranslates

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
noncomputable section

namespace GlobalTheory.Poinc.Origin
open GlobalTheory.UT.CoefBasic

theorem exists_sec_value_ne_zero : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ k : ℕ, 4 ≤ k → ∃ (t : SecA A F k) (c : F), c ≠ 0 ∧ ∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val := by
  intro hL R _ _ A F _ _ ρ hρ k hk
  obtain ⟨M, s, hcov⟩ := (hL.1.ample _ A k hk).1 ⊤ (isAffineOpen_top _)
  obtain ⟨i', hi⟩ : ∃ i' : A.A.left ⟶ (A.A.hom ⁻¹ᵁ ⊤).toScheme, i' ≫ (A.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.A.left.topIso.inv, A.A.left.topIso.inv_hom_id⟩
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  let χ : (TFK (R := R) F).left ⟶ (A.A.hom ⁻¹ᵁ ⊤).toScheme :=
    (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left ≫ i'
  have hmem : χ z ∈ (⨆ j, nonzeroLocus (s j)) := by rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  obtain ⟨t, ht⟩ := exists_sec A.isLB (φ := fun _ : Fin k => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => 1)
      (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε' := fun _ => (k : ℤ))
      (fun U _ f => by
        simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, zpow_natCast])
      (VVRank.pullTo (L := A.L) (φ := fun _ : Fin k => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
        ((snd (TFK (R := R) F) A.A).left ≫ i') (fun _ => by rw [Category.assoc, hi, Category.comp_id]))
  obtain ⟨c, hc⟩ := ThetaSpan.exists_value A hρ (F := F) (k := k) t
  refine ⟨t, c, ?_, hc⟩
  rintro rfl
  obtain ⟨J, hJ⟩ := exists_good' A.isLB (Z := (TFK (R := R) F).left) z
  have h1 := hc z J hJ
  have h0 : @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z 0) = 0 := by
    show cst (R := R) F z 0 = 0
    rw [cst_eq, map_zero]
  rw [h0, zero_mul] at h1
  have h2 : sA t (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left z J = sval (s j) χ z J :=
    (ht _ _ z J hJ).trans ((VVRank.sval_pullTo _ _ _ _ z hJ).trans (by simp only [χ, Category.assoc]))
  have hu : IsUnit (sval (s j) χ z J) :=
    (AmpleSpan.mem_nonzeroLocus_iff_gs (s j) χ z (hJ.mem (fun _ : Fin k => (A.A.hom ⁻¹ᵁ ⊤).ι) χ)).1 hj
  rw [← h2, h1] at hu
  exact not_isUnit_zero hu

end GlobalTheory.Poinc.Origin

end
