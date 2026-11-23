import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCommutesTranslation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHorizOfComm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtsHoriz

theorem transl_horizontal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (y : P.D.toPre.X) (x : Sp (DualNumber k) ⟶ B'.left), x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left → x ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab
  letI := H.starRing
  intro Y n' v' dd hdd D q hq h hbas hdef hΘ ρ hρ B' _ π₁ π₂ h₁ h₂ hcl y x hx hx₁
  obtain ⟨_, hA₀, -, -⟩ := GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback _ _
    ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) P.D.toPre.P.A _ _ _
    (IsPullback.of_hasPullback P.D.toPre.P.A.hom (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)))
  obtain ⟨dl, hdl, hcomm⟩ := GlobalTheory.HeatTranslW.lift_commutes_translation E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hbas hdef hΘ ρ hρ _ _ _ hA₀
  have hw : (pullback.fst P.D.toPre.P.A.hom (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) ≫
      (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left) ≫ P.D.toPre.P.A.hom =
      pullback.snd _ _ ≫ spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := by
    rw [Category.assoc, Over.w, pullback.condition]
  let T₀ := pullback.lift _ _ hw
  exact GlobalTheory.TranslHoriz.isHoriz_of_comm k _ P.D.toPre.P.A P.D.toPre.P.isAb ρ B' _ π₁ π₂ h₁ h₂ hcl _ _ _ hA₀ dl hdl (P.D.toPre.c y) T₀
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (hcomm y T₀ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)) x hx hx₁

end GlobalTheory.PtsHoriz
