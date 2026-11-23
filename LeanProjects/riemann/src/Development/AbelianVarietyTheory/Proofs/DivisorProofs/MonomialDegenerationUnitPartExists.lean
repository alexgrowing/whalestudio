import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SubsingletonSpDualNumber
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitPart

theorem exists_gen_of_top {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (j₀ : K → M.ι) (all : ∀ w : Y, w ∈ LB.wchart M φ j₀) (v : Γ(Y, ⊤)ˣ) :
    ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → M.ι),
      r z ∈ LB.wchart M φ j → gm r z (LB.wchart M φ j) (t.s j) = trF φ ε r z j j₀ * gm r z ⊤ v := by
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ j₀ := fun j w hw => ⟨hw, all w⟩
  let t : LB.Gen (LB.LinComb M φ ε) :=
    ⟨fun j => res (le j) ((LB.LinComb M φ ε).g j j₀) * res (le_top : LB.wchart M φ j ≤ ⊤) v⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → M.ι),
      r z ∈ LB.wchart M φ j → gm r z (LB.wchart M φ j) (t.s j) = trF φ ε r z j j₀ * gm r z ⊤ v :=
    fun Z r z j h => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z (le j) h _).trans (gm_linComb M φ ε r z j j₀ h (all _))) (gm_res r z le_top h _))
  refine ⟨t, fun j j' => Geo.Tor.unit_ext fun w hw => ?_, key⟩
  have hm : (𝟙 Y : Y ⟶ Y) w ∈ LB.wchart M φ j ⊓ LB.wchart M φ j' := hw
  refine ((gm_res _ w _ hm _).trans (key _ _ w j hm.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb M φ ε (𝟙 Y) w j j' hm.1 hm.2)
      ((gm_res _ w _ hm _).trans (key _ _ w j' hm.2)))).symm)
  rw [← trF_trans hM φ ε (𝟙 Y) w hm.1 hm.2 (all _), _root_.mul_assoc]
  rfl

theorem jK_app_toOpen {R : Type} [CommRing R] [IsDomain R] (r : R) :
    ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r) := by
  have e : DegPre.toOpen (R := R) ⊤ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    ext r
    simp [DegPre.toOpen]
  rw [e]
  exact (congrArg (fun q => q.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm

theorem exists_isUnitPart : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → ∀ y, ∃ n ψ₀, IsUnitPart Q t gam y n ψ₀ := by
  intro R _ _ Q m t gam h y
  obtain ⟨u, n, hn, hc⟩ := h y
  have h0 : ∏ i, t i ^ n i ≠ 0 := right_ne_zero_of_mul (PsiCoordLocal.ne_zero_of_coord hc)
  have h1 : algebraMap R (FractionRing R) (∏ i, t i ^ n i) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 h0
  obtain ⟨j₀, hj, hle, e⟩ := hc
  have all : ∀ w, w ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c y).left) j₀ := fun w =>
    Set.mem_iInter.2 fun _ => hj trivial
  obtain ⟨ψ₀, hg, hv⟩ := exists_gen_of_top Q.P.isLB (K := PUnit) (fun _ => (Q.c y).left) (fun _ => -1) j₀ all (unitOn u)
  refine ⟨n, ψ₀, hg, hn, Units.mk0 _ h1, rfl, fun z J hJ => ?_⟩
  have m₀ : (𝟙 (TK R).left : _ ⟶ _) z ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK y) j₀ := hle trivial
  have a := gen_trans (Q.psi_gen y) (𝟙 (TK R).left) z (hJ.mem (fun _ : PUnit => Q.xK y) (𝟙 _)) m₀
  have b := hv _ (toUnit (TK R)).left z _ (hJ.mem (fun _ : PUnit => (Q.c y).left) (toUnit (TK R)).left)
  have c : gm (𝟙 (TK R).left) z (LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK y) j₀) ((Q.psi y).s j₀) =
      gm (𝟙 (TK R).left) z ⊤ (unitOn (Units.mk0 _ h1)) * gm (toUnit (TK R)).left z ⊤ (unitOn u) := by
    have d : res hle ((Q.psi y).s j₀) =
        unitOn (Units.mk0 _ h1) * (show Γ(Sp (FractionRing R), ⊤)ˣ from pullU (jK R) ⊤ (unitOn u)) := by
      refine Units.ext (e.symm.trans ?_)
      rw [jK_app_toOpen, map_mul, _root_.mul_comm, map_mul]
      refine congrArg₂ (· * ·) rfl ?_
      rw [← jK_app_toOpen]
      exact congrArg _ (by simp [DegPre.toOpen, unitOn])
    refine (gm_res _ z hle trivial _).symm.trans ((congrArg _ d).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ?_)))
    exact gm_pull (𝟙 _) (jK R) z ⊤ trivial _
  refine a.trans (Eq.trans ?_ (congrArg _ b).symm)
  rw [c, mul_left_comm]
  rfl

end GlobalTheory.UnitPart
