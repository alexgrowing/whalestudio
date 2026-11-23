import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionNe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

set_option maxHeartbeats 400000 in

theorem GlobalTheory.Poinc.Sep.CoefInt.isUnit_of_theta_sq : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁)
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)),
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ N₁ = 1 →
      ∃ c, p = toUnit _ ≫ b c) →
    ∃ c₁ : C, ∀ (G : V₁) (U : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Sp V₁) (z : Z) (_ : (Z ⟶ D.P.A.left) → D.P.L.ι),
        (Z.presheaf.stalk z)ˣ),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom G) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c₁).left) z J ^ 2 *
            (U Z r z J).val) → IsUnit G := by
  intro N₁ hN V₁ _ _ _ hV hunit D θ hθ C b hcov
  let K := AlgebraicClosure (ResidueField V₁)
  let ev : V₁ →+* K := (algebraMap (ResidueField V₁) K).comp (residue V₁)
  have hθ' : ∃ j, (ThetaOne.pullTo D ev θ).f j ≠ 0 :=
    ThetaOne.exists_ne_zero D ev _ (hθ K ev _ (ThetaOne.isPullSecLC_pullTo D ev θ))
  have hNK : (N₁ : K) ≠ 0 := by
    have := (hunit N₁ (by omega)).map ev
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨p, hp, hne⟩ := GlobalTheory.Poinc.Sep.Coef.exists_torsion_ne D ev θ hθ' N₁ hN hNK
  obtain ⟨c₁, hc⟩ := hcov K (spMap ev) p hp
  refine ⟨c₁, fun G U hG => ?_⟩
  by_contra hGu
  have hG0 : ev G = 0 := by
    show algebraMap (ResidueField V₁) K (residue V₁ G) = 0
    rw [(residue_eq_zero_iff G).2 ((mem_maximalIdeal G).2 hGu), map_zero]
  let z : Sp K := IsLocalRing.closedPoint K
  have hch : ∀ ψ : Sp K ⟶ D.P.A.left, ∃ i, ψ z ∈ D.P.L.U i := fun ψ =>
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart D.P.isLB (ψ z)
  choose J hJ using hch
  have hgood : Good D.P.L z J := hJ
  have e := hG (Sp K) (spMap ev) z J hgood
  have e2 : gs (spMap ev) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom G) = toStk z (ev G) := by
    have := GlobalTheory.Poinc.Sep.Coef.gs_ev ev ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom G) z
    simpa using this
  have hpl : p.left = spMap ev ≫ (b c₁).left := by rw [hc]; rfl
  have h1 := hne z J hgood
  rw [hpl] at h1
  obtain ⟨y, hy⟩ := GlobalTheory.Poinc.Sep.Coef.toStk_surj z (sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (spMap ev ≫ (b c₁).left) z J)
  rw [e2, hG0, map_zero, ← hy, ← map_pow] at e
  have h3 : toStk z (y ^ 2) = 0 := (Units.mul_left_eq_zero _).1 e.symm
  have h4 : y ^ 2 = 0 := (toStk z).injective (h3.trans (map_zero _).symm)
  exact h1 (by rw [← hy, pow_eq_zero_iff two_ne_zero |>.1 h4, map_zero])
