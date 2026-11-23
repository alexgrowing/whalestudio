import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PsiRing GlobalTheory.StrictPull GlobalTheory.ModelData GlobalTheory.DegPull

namespace GlobalTheory.BaseChangeDeg

theorem exists_baseChange : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsNoetherianRing R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → ∃ (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X), IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β ∧ v.IsGen ∧ (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) ∧ GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v ∧ GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) := by
  intro R₁ _ _ R₂ _ _ _ σ D₁ gam hgam
  let P' := polPull D₁.P (spMap σ)
  let F := pullback.fst D₁.P.A.hom (spMap σ)
  have gp : IsGrpPullback P'.A D₁.P.A (spMap σ) F := isGrpPullback_pullback D₁.P.A (spMap σ)
  obtain ⟨w, hw, -⟩ := exists_strict D₁.P.isLB F
  have hF := gp.1
  have hw' := (isGen_iff w).1 hw
  have hE : eSec P'.A ≫ F = spMap σ ≫ eSec D₁.P.A := (cubeMapOf gp).e_comm
  obtain ⟨rig, hrig, Hrig⟩ := exists_pmaps hw' D₁.P.isLB P'.isLB (K := PUnit) (φ' := fun _ => eSec P'.A)
    (φ := fun _ => eSec D₁.P.A) (ε := fun _ => 1) (spMap σ) (fun _ => hE) D₁.rig D₁.rig_gen
  obtain ⟨cub⟩ := nonempty_cubical_pull gp D₁.cub ⟨P'.L, rig, P'.isLB, hrig⟩ hw'
  obtain ⟨sym, hsym, hsr⟩ := exists_sym_pull gp D₁.P.isLB P'.isLB hw' D₁.sym D₁.sym_gen D₁.sym_rig
  obtain ⟨c, hc⟩ : ∃ c : D₁.X → (𝟙_ (Over (Spec (CommRingCat.of R₂))) ⟶ P'.A), ∀ x,
      (c x).left ≫ F = spMap σ ≫ (D₁.c x).left :=
    ⟨fun x => Over.homMk (hF.lift (spMap σ ≫ (D₁.c x).left) (𝟙 _) (by
      rw [Category.assoc, Over.w, Category.id_comp]; exact Category.comp_id _)) (hF.lift_snd _ _ _),
      fun x => hF.lift_fst _ _ _⟩
  have cadd : ∀ a b, c (a + b) = padd P'.A (c a) (c b) := fun a b => by
    refine Over.OverMorphism.ext (hF.hom_ext ?_ (by rw [Over.w, Over.w]))
    have u : (toUnit (Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R₂)))).hom ≫ spMap σ))).left = spMap σ :=
      Category.id_comp _
    have m := gp.2 _ (c a) (c b) (toUnit _ ≫ D₁.c a) (toUnit _ ≫ D₁.c b)
      (by rw [hc, Over.comp_left, u]) (by rw [hc, Over.comp_left, u])
    rw [← MonObj.comp_mul, Over.comp_left, u] at m
    rw [hc, D₁.c_add]
    exact m
  have hK : jK R₂ ≫ spMap σ = spMap gam ≫ jK R₁ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact (hgam r).symm
  have hx : ∀ x, ptK (c x) ≫ F = spMap gam ≫ D₁.xK x := fun x => by
    show (jK R₂ ≫ (c x).left) ≫ F = spMap gam ≫ jK R₁ ≫ (D₁.c x).left
    refine (Category.assoc _ _ _).trans ((congrArg (jK R₂ ≫ ·) (hc x)).trans ?_)
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (D₁.c x).left) hK)).trans (Category.assoc _ _ _)
  choose psi hpsi vpsi using fun x => exists_pmaps hw' D₁.P.isLB P'.isLB (K := PUnit)
    (φ' := fun _ => ptK (c x)) (φ := fun _ => D₁.xK x) (ε := fun _ => -1) (spMap gam) (fun _ => hx x)
    (D₁.psi x) (D₁.psi_gen x)
  let D' : DegPre R₂ :=
    { P := P', rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D₁.X,
      c := c, c_add := cadd, psi := psi, psi_gen := hpsi }
  exact ⟨D', F, w, AddEquiv.refl _, gp, hw, hc, Hrig, vpsi⟩

end GlobalTheory.BaseChangeDeg
