import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.EndCompat

def preH {S : Scheme.{0}} {T T' G : Over S} [GrpObj G] (w : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) :=
  MonoidHom.mk' (w ≫ ·) fun a b => MonObj.comp_mul w a b

def postH {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) (hf : IsMonHom f) :
    (T ⟶ G) →* (T ⟶ H) :=
  haveI := hf
  MonoidHom.mk' (· ≫ f) fun a b => MonObj.mul_comp a b f

def pullH {S S' : Scheme.{0}} (f : S' ⟶ S) (T G : Over S) [GrpObj G] :
    (T ⟶ G) →* ((Over.pullback f).obj T ⟶ (Over.pullback f).obj G) where
  toFun := (Over.pullback f).map
  map_one' := by simp
  map_mul' a b := Functor.map_mul _ a b

theorem map_ofFn_prod {M N : Type} [Group M] [Group N] (f : M →* N) (x : Fin 8 → M) (k : Fin 8 → ℤ) :
    f (List.ofFn fun v => x v ^ k v).prod = (List.ofFn fun v => f (x v) ^ k v).prod := by
  rw [map_list_prod, List.map_ofFn]
  simp [Function.comp_def, map_zpow]

theorem aG_comp_eq_prod : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (E : EndU U.toUnifPre), (∀ u, E.aA ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod := by
  intro g n o _ ζ F V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ y α hG₀ hα P c φc hφc pr hpr G _ _ hG D U q hq hqc a E hE u
  haveI : IsNoetherianRing V₁ := hCN.1
  haveI : IsIntegrallyClosed V₁ := hCN.2.1
  haveI := E.homG
  haveI := hq u
  haveI := U₀.gen_hom
  have hR : IsMonHom (List.ofFn fun v => q v ^ a u v).prod := by
    refine isMonHom_of_mul _ fun T x z => ?_
    have key : ∀ w : T ⟶ G, w ≫ (List.ofFn fun v => q v ^ a u v).prod = ∏ v, (w ≫ q v) ^ a u v := fun w => by
      rw [← List.prod_ofFn]
      exact map_ofFn_prod (preH w) q (a u)
    rw [key, key, key, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    haveI := hq v
    rw [MonObj.mul_comp, mul_zpow]
  obtain ⟨F0, -, huniq⟩ := GlobalTheory.semiAbelianHomExtension_holds.fractionField V₁ (FractionRing V₁) G G₀ hG hG₀
    ((Over.pullback (jK V₁)).map (E.aG ≫ q u))
  refine (huniq _ ⟨inferInstance, rfl⟩).trans (huniq _ ⟨hR, ?_⟩).symm
  rw [← cancel_mono U₀.gen.hom]
  apply Over.OverMorphism.ext
  refine hα.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)
  have hv : ∀ v, pushHom hα ((Over.pullback (jK V₁)).obj G) ((Over.pullback (jK V₁)).map (q v) ≫ U₀.gen.hom) =
      pushHom hφc ((Over.pullback (jK V₁)).obj G) (U.gen.hom ≫ pr v) :=
    fun v => Over.OverMorphism.ext (hqc v)
  have e₁ : ((Over.pullback (jK V₁)).map (List.ofFn fun v => q v ^ a u v).prod ≫ U₀.gen.hom).left ≫ α =
      (List.ofFn fun v => pushHom hφc ((Over.pullback (jK V₁)).obj G) (U.gen.hom ≫ pr v) ^ a u v).prod.left := by
    have := map_ofFn_prod ((pushHom hα ((Over.pullback (jK V₁)).obj G)).comp
      ((postH U₀.gen.hom U₀.gen_hom).comp (pullH (jK V₁) G G₀))) q (a u)
    refine (congrArg (fun z => z.left) this).trans ?_
    refine congrArg (fun z => Over.Hom.left (List.ofFn z).prod) (funext fun v => ?_)
    rw [← hv v]
    rfl
  have e₂ : ((Over.pullback (jK V₁)).map (E.aG ≫ q u) ≫ U₀.gen.hom).left ≫ α =
      (List.ofFn fun v => pushHom hφc ((Over.pullback (jK V₁)).obj G) (U.gen.hom ≫ pr v) ^ a u v).prod.left := by
    have h1 : ((Over.pullback (jK V₁)).map (E.aG ≫ q u) ≫ U₀.gen.hom).left ≫ α =
        (U.gen.hom ≫ (List.ofFn fun v => pr v ^ a u v).prod).left ≫ φc := by
      rw [Functor.map_comp, Category.assoc, Over.comp_left, Category.assoc, hqc u, ← Category.assoc,
        ← Over.comp_left, ← Category.assoc, E.ext, Category.assoc, hE u]
    have h2 := map_ofFn_prod ((pushHom hφc ((Over.pullback (jK V₁)).obj G)).comp (preH U.gen.hom)) pr (a u)
    exact h1.trans (congrArg (fun z => z.left) h2)
  exact e₁.trans e₂.symm

end GlobalTheory.Poinc.Sep.EndCompat
