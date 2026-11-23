import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TauPullOn

open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull GlobalTheory.FactorPull
open GlobalTheory.PsiEvenPull (proj)

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {θ : R →+* V} {D₀ : DegPre R}
  {D₁ : DegPre V} (hD : IsPullDeg θ D₀ D₁) {z : (TK V).left} {J : ((TK V).left ⟶ D₀.P.A.left) → D₀.P.L.ι}
  {J₁ : ((TK V).left ⟶ D₁.P.A.left) → D₁.P.L.ι} (hJ : Good D₀.P.L z J) (hJ₁ : Good D₁.P.L z J₁)
include hJ hJ₁

theorem psiW_val (x : D₁.X) : val (hD.psiW.psi (hD.xe x)) hD.g z J =
    (om hD.w z J J₁ (D₁.xK x))⁻¹ * val (D₁.psi x) (𝟙 _) z J₁ := by
  have e := PsiEvenPull.psi_pull hD x (𝟙 _) z hJ hJ₁
  simp only [Category.id_comp] at e
  exact e

theorem rigW_val : val (D₀.rigW hD.W) hD.g z J =
    om hD.w z J J₁ (1 : TK V ⟶ D₁.P.A).left * val D₁.rigK (𝟙 _) z J₁ := by
  have pm := (maps_iff hD.w _ (fun _ => eSec D₀.P.A) _ D₁.rig D₀.rig (specOf θ) _
    (rigPull_le (proj hD) (specOf θ) hD.he D₀.P.L) (fun _ => rfl)).1 hD.w_rig
  have e := pmaps_om (fun _ => hD.he) pm (jK V) z hJ hJ₁
  rw [Fintype.prod_unique, zpow_one] at e
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ₁ _ _ _).symm))
  rw [Category.id_comp]
  exact (congrArg (fun q => val D₀.rig q z J) hD.g_comm).trans e

omit hJ hJ₁ in

theorem tau_pull : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (D₀ : DegPre R) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁), ∃ (β₂ : (G2 D₁.P.A).left ⟶ (G2 D₀.P.A).left) (w₀ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ D₀.P.A D₀.P.L).pull β₂)), IsSquare (GlobalTheory.PsiEvenPull.proj hD) β₂ ∧ w₀.IsGen ∧ ∀ a b z J J₁, Good D₀.P.L z J → Good D₁.P.L z J₁ → val (D₁.tau a b) (𝟙 _) z J₁ = lamVal w₀ (lift (toUnit (TK V) ≫ D₁.c a) (toUnit (TK V) ≫ D₁.c b)).left z J J₁ * val (hD.psiW.tau (hD.xe a) (hD.xe b)) hD.g z J := by
  intro R V _ _ _ _ θ D₀ D₁ hD
  refine ⟨sqOf (pull_grp hD), lamIso (pull_grp hD) hD.w, isSquare_sqOf _, isGen_lamIso _ _ hD.w_gen,
    fun a b z J J₁ hJ hJ₁ => ?_⟩
  have g := gw_lam (pull_grp hD) hD.w (lift (toUnit (TK V) ≫ D₁.c a) (toUnit (TK V) ≫ D₁.c b)).left z hJ hJ₁
  have p := prod_lam (DVR.cP D₁ (TK V) a) (DVR.cP D₁ (TK V) b) (om hD.w z J J₁)
  rw [← DVR.cPoint_add] at p
  have l : lamVal (lamIso (pull_grp hD) hD.w) (lift (toUnit (TK V) ≫ D₁.c a) (toUnit (TK V) ≫ D₁.c b)).left z J J₁ =
      om hD.w z J J₁ (D₁.xK (a + b)) * (om hD.w z J J₁ (D₁.xK a))⁻¹ * (om hD.w z J J₁ (D₁.xK b))⁻¹ *
        om hD.w z J J₁ (1 : TK V ⟶ D₁.P.A).left := by
    refine Eq.trans ?_ (g.trans p)
    simp only [Category.assoc]
    rfl
  rw [l, TauPull.val_tauW _ _ hJ, TauPull.val_tau _ hJ₁, ← map_add, psiW_val hD hJ hJ₁, psiW_val hD hJ hJ₁,
    psiW_val hD hJ hJ₁, rigW_val hD hJ hJ₁]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TauPullOn

end
