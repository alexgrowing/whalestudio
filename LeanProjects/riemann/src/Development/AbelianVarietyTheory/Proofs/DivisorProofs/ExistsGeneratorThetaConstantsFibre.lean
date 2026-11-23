import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaPointNormalisedThetaConstant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FibThetaMove

open GlobalTheory.Ex.OneGen GlobalTheory.ThetaPtMove GlobalTheory.ThetaPtUp GlobalTheory.UMin.ThMove

theorem exists_gen_thG_fibre : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K)
  (o : Type) [CommRing o] (g m : ℕ) (J : Type) (b : TBase o (m ^ 2)) (s : Sp K ⟶ Sp o) (t : TObj g (m ^ 2) J b s)
  (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ →
  LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) →
  ∀ v : Ix g (m ^ 2) → K, t.HasTh (𝟙 _) v →
  ∃ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))) (κ : K), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th ∧ κ ≠ 0 ∧
    ∀ a, ∃ y : Over.mk (spMap ev) ⟶ D.P.A, GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L D.rig m th y (GlobalTheory.Ex.fnOf (κ * v a)) := by
  intro V₁ _ _ D K _ _ ev o _ g m J b s t ψ hψ hLB v H
  obtain ⟨w, hw⟩ := hLB
  have := t.ab.comm
  have := D.P.isAb.comm
  let F := (Over.pullback (spMap ev)).obj D.P.A
  have : IsCommMonObj F := Functor.isCommMonObj_obj
  let φF := pullback.fst D.P.A.hom (spMap ev)
  have hpD : IsGrpPullback F D.P.A (spMap ev) φF := isGrpPullback_pullback D.P.A (spMap ev)
  have hLD : D.P.L.IsLB := D.P.isLB
  have hLF : (D.P.L.pull φF).IsLB := pull_isLB hLD φF
  have hLt : t.L.IsLB := t.isLB
  have hw₁ : (idIso (D.P.L.pull φF)).IsGen := idIso_isGen hLF
  obtain ⟨ρF, hρF, hrF⟩ := exists_rigidificationPullbackCompatibleIso (w := idIso (D.P.L.pull φF)) (ρ₀ := D.rig) hpD hw₁ hLD hLF D.rig_gen

  have hE : eSec F ≫ ψ = 𝟙 _ ≫ eSec t.A := by
    have := over_one hψ (T := baseOver _) (T₀ := baseOver _) (𝟙 _) ((Category.comp_id _).trans (Category.id_comp _).symm)
    exact ((Category.id_comp _).symm.trans (Category.assoc _ _ _).symm).trans
      (this.symm.trans (congrArg (𝟙 _ ≫ ·) (Category.id_comp _)))
  obtain ⟨ρt, hρt, hrt'⟩ := exists_gen_up_iso (K := PUnit) (φ' := fun _ => eSec F) (φ := fun _ => eSec t.A)
    (ε := fun _ => 1) (h := 𝟙 _) (χ := 𝟙 _) hw hLt hLF (Category.id_comp _) (Category.id_comp _) (fun _ => hE) ρF hρF
  have hrt : IsRigidificationPullbackCompatibleIso w (𝟙 _) ρF ρt := fun Z r z J J' hJ hJ' =>
    (hrt' Z r z J J' hJ hJ').trans (by rw [Fintype.prod_unique, zpow_one])

  let x : Ix g (m ^ 2) → (baseOver (Sp K) ⟶ t.pol.A) := fun a =>
    (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ baseOver (Sp K)) ≫ t.lab a
  have hx : ∀ a, x a ^ (m ^ 2) = 1 := fun a => by
    show ((Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ baseOver (Sp K)) ≫ t.lab a) ^ (m ^ 2) = 1
    rw [← MonObj.comp_pow, lab_pow, MonObj.comp_one]
  obtain ⟨tht, hgt, hTt⟩ := exists_gen_thG_of_isThetaPt K t.pol ρt hρt m (Ix g (m ^ 2)) x v hx H

  have hτ₁ : 𝟙 (Sp K) ≫ (baseOver (Sp K)).hom = (baseOver (Sp K)).hom ≫ 𝟙 (Sp K) := by simp
  choose xF hxF hnF using fun a => torsion_down hψ (T := baseOver (Sp K)) (T₀ := baseOver (Sp K)) (𝟙 _) hτ₁ (x a) (hx a)
  obtain ⟨thF, hsF⟩ := exists_secRel hψ (T := baseOver (Sp K)) (T₀ := baseOver (Sp K)) (𝟙 _) hτ₁ hw hLt hLF tht
  have hgF := isGenSec_down hψ (𝟙 _) hτ₁ hw hLt hLF hsF hgt
  have hTF := fun a =>
    ThG.move hψ (𝟙 _) hτ₁ hw hLt hLF hrt (hxF a) (hnF a) hsF (hTt a)

  have hτ₂ : 𝟙 (Sp K) ≫ (Over.mk (spMap ev)).hom = (baseOver (Sp K)).hom ≫ spMap ev := by simp
  choose x₀ hx₀ hn₀ using fun a => torsion_up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ (xF a) (hnF a)
  obtain ⟨th₀, hs₀⟩ := exists_secRel_up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ hw₁ hLD hLF thF
  have hg₀ : IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th₀ := isGenSec_up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ hw₁ hLD hLF hs₀ hgF
  refine ⟨th₀, 1, hg₀, one_ne_zero, fun a => ⟨x₀ a, ?_⟩⟩
  have q := ThG.up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ hw₁ hLD hLF hrF (hx₀ a) (hn₀ a) hs₀ (hTF a)
  simpa using q

end GlobalTheory.FibThetaMove
end
