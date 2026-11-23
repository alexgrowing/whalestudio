import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsPelRepIsPEL
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeomRegFibAdicCompletionOfEssFiniteTypeInt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (powObj powPr powIsLimit)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LowChart

section Pull

variable {S S' : Scheme.{0}} {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B}

def siegPull (c : SiegPre h M ζ s) (f : S' ⟶ S) (s' : S' ⟶ Sp B) (hs : f ≫ s = s') : SiegPre h M ζ s' where
  A := (Over.pullback f).obj c.A
  ab :=
    { comm := by have := c.ab.comm; infer_instance
      smooth := by have := c.ab.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := c.ab.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := c.ab.geomConnected
        show GeometricallyConnected (pullback.snd _ _); infer_instance }
  P := c.P.pull (Pdiv.PullbackComparison.pφ₂ f c.A)
  isLB := pull_isLB c.isLB (Pdiv.PullbackComparison.pφ₂ f c.A)
  rig₁ := by
    obtain ⟨t₁, ht₁⟩ := c.rig₁
    exact gen_chartPull (chartPullLinComb c.P _ _ _ _ (Pdiv.PullbackComparison.pφ f c.A)
      (fun _ => Pdiv.PullbackComparison.lift_one_id f c.A)) t₁ ht₁
  rig₂ := by
    obtain ⟨t₂, ht₂⟩ := c.rig₂
    exact gen_chartPull (chartPullLinComb c.P _ _ _ _ (Pdiv.PullbackComparison.pφ f c.A)
      (fun _ => Pdiv.PullbackComparison.lift_id_one f c.A)) t₂ ht₂
  symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl)
      (chartPullLinComb c.P _ _ _ _ (Pdiv.PullbackComparison.pφ₂ f c.A) (fun _ => Pdiv.PullbackComparison.lift_swap f c.A)) c.symm
  lev := fun a => GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback f c.A) (c.lev a)
  lev_add := fun a b => GlobalTheory.SiegelPull.push_injective (Pdiv.PullbackComparison.isGrpPullback f c.A) _ (by
    rw [map_mul, GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull', c.lev_add, MonObj.comp_mul])
  lev_tors := fun a => GlobalTheory.SiegelPull.push_injective (Pdiv.PullbackComparison.isGrpPullback f c.A) _ (by
    rw [map_pow, map_one, GlobalTheory.SiegelPull.push_secPull', ← MonObj.comp_pow, c.lev_tors, MonObj.comp_one])
  geom := fun k _ _ x β z hx hz => by
    have pb := Pdiv.PullbackComparison.isGrpPullback f c.A
    obtain ⟨g₁, g₂, g₃⟩ := c.geom k (x ≫ f) β z (by rw [Category.assoc, hs, hx]) hz
    refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
    · rw [← (GlobalTheory.SiegelPull.push_injective pb (Over.mk x)).eq_iff, GlobalTheory.SiegelPull.push_secPull, map_one]
      rfl
    · obtain ⟨a, ha⟩ := g₂ (pushHom pb (Over.mk x) g) (by
        have := congrArg (pushHom pb (Over.mk x)) hg
        rw [map_pow, map_one] at this
        exact this)
      exact ⟨a, GlobalTheory.SiegelPull.push_injective pb _ ((GlobalTheory.SiegelPull.push_secPull pb _ _).trans ha)⟩
    · exact (weilIs_grpPullback_of_comm S S' c.A _ f (Pdiv.PullbackComparison.pφ f c.A) _ _ (pull_isLB c.isLB _)
        (pull_isLB (pull_isLB c.isLB (Pdiv.PullbackComparison.pφ₂ f c.A)) _) pb
        (GlobalTheory.SiegelPull.diag_iso (Pdiv.PullbackComparison.isSquare f c.A) (Pdiv.PullbackComparison.gen_refl _ (pull_isLB c.isLB (Pdiv.PullbackComparison.pφ₂ f c.A))))
        (Over.mk x) M _ _ _ _ _
        (congrArg (fun q => q.left) (GlobalTheory.SiegelPull.push_secPull pb (c.lev a) (Over.mk x)).symm)
        (congrArg (fun q => q.left) (GlobalTheory.SiegelPull.push_secPull pb (c.lev b) (Over.mk x)).symm)).2 (g₃ a b)

theorem siegPB_siegPull (c : SiegPre h M ζ s) (f : S' ⟶ S) (s' : S' ⟶ Sp B) (hs : f ≫ s = s') :
    SiegPB (siegPull c f s' hs) c f :=
  ⟨Pdiv.PullbackComparison.pφ f c.A, Pdiv.PullbackComparison.pφ₂ f c.A, Pdiv.PullbackComparison.isGrpPullback f c.A, Pdiv.PullbackComparison.isSquare f c.A,
    Pdiv.PullbackComparison.gen_refl _ (pull_isLB c.isLB _), fun a => GlobalTheory.SiegelPull.secPull_left (Pdiv.PullbackComparison.isGrpPullback f c.A) _⟩

theorem principal_siegPull (c : SiegPre h M ζ s) (f : S' ⟶ S) (s' : S' ⟶ Sp B) (hs : f ≫ s = s')
    (hc : c.Principal) : (siegPull c f s' hs).Principal :=
  (GlobalTheory.siegPre_pullback h M B ζ S S' s s' f c hs).2 _ (siegPB_siegPull c f s' hs) hc

end Pull

end GlobalTheory.LowChart

namespace GlobalTheory.LowChart

section Pow

variable {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F : ZM.SFam h n ζ)

abbrev powA (r : ℕ) : Over F.X := powObj F.univ.A r

def toO (r : ℕ) : (powA F r).left ⟶ Sp o := (powA F r).hom ≫ F.s

abbrev coord {r : ℕ} (i : Fin r) : powA F r ⟶ F.univ.A := powPr F.univ.A i

variable {F}

def lift {T : Scheme.{0}} (u : T ⟶ F.X) {r : ℕ} (p : Fin r → (T ⟶ F.univ.A.left))
    (hp : ∀ i, p i ≫ F.univ.A.hom = u) : T ⟶ (powA F r).left :=
  ((powIsLimit F.univ.A r).lift (Fan.mk (Over.mk u) fun i => Over.homMk (p i) (hp i))).left

@[reassoc]
theorem lift_hom {T : Scheme.{0}} (u : T ⟶ F.X) {r : ℕ} (p : Fin r → (T ⟶ F.univ.A.left))
    (hp : ∀ i, p i ≫ F.univ.A.hom = u) : lift u p hp ≫ (powA F r).hom = u :=
  Over.w ((powIsLimit F.univ.A r).lift (Fan.mk (Over.mk u) fun i => Over.homMk (p i) (hp i)))

@[reassoc]
theorem lift_coord {T : Scheme.{0}} (u : T ⟶ F.X) {r : ℕ} (p : Fin r → (T ⟶ F.univ.A.left))
    (hp : ∀ i, p i ≫ F.univ.A.hom = u) (i : Fin r) : lift u p hp ≫ (coord F i).left = p i :=
  congrArg (fun q => q.left) ((powIsLimit F.univ.A r).fac (Fan.mk (Over.mk u) fun i => Over.homMk (p i) (hp i)) ⟨i⟩)

theorem hom_ext {T : Scheme.{0}} {r : ℕ} (f g : T ⟶ (powA F r).left) (h₀ : f ≫ (powA F r).hom = g ≫ (powA F r).hom)
    (h : ∀ i, f ≫ (coord F i).left = g ≫ (coord F i).left) : f = g := by
  let f' : Over.mk (f ≫ (powA F r).hom) ⟶ powA F r := Over.homMk f rfl
  let g' : Over.mk (f ≫ (powA F r).hom) ⟶ powA F r := Over.homMk g h₀.symm
  have : f' = g' := (powIsLimit F.univ.A r).hom_ext fun ⟨i⟩ => Over.OverMorphism.ext (h i)
  exact congrArg (fun q => q.left) this

variable (F)

abbrev siegAt {T : Scheme.{0}} {r : ℕ} (f : T ⟶ (powA F r).left) (s' : T ⟶ Sp o) (hs : f ≫ toO F r = s') :
    SiegPre h n ζ s' :=
  siegPull F.univ (f ≫ (powA F r).hom) s' (by rw [Category.assoc]; exact hs)

def ptAt {T : Scheme.{0}} {r : ℕ} (f : T ⟶ (powA F r).left) (s' : T ⟶ Sp o) (hs : f ≫ toO F r = s') (i : Fin r) :
    𝟙_ (Over T) ⟶ (siegAt F f s' hs).A :=
  Over.homMk (pullback.lift (f ≫ (coord F i).left) (𝟙 T) (by
      rw [Category.assoc, Over.w (coord F i)]; exact (Category.id_comp _).symm)) (pullback.lift_snd _ _ _)

theorem ptAt_left {T : Scheme.{0}} {r : ℕ} (f : T ⟶ (powA F r).left) (s' : T ⟶ Sp o) (hs : f ≫ toO F r = s')
    (i : Fin r) : (ptAt F f s' hs i).left ≫ Pdiv.PullbackComparison.pφ (f ≫ (powA F r).hom) F.univ.A = f ≫ (coord F i).left :=
  pullback.lift_fst _ _ _

def cAt {T : Scheme.{0}} {r : ℕ} (f : T ⟶ (powA F r).left) (s' : T ⟶ Sp o) (hs : f ≫ toO F r = s')
    (a : Fin r → ℤ) : 𝟙_ (Over T) ⟶ (siegAt F f s' hs).A :=
  ∏ i, ptAt F f s' hs i ^ a i

theorem cAt_add {T : Scheme.{0}} {r : ℕ} (f : T ⟶ (powA F r).left) (s' : T ⟶ Sp o) (hs : f ≫ toO F r = s')
    (a b : Fin r → ℤ) : cAt F f s' hs (a + b) = cAt F f s' hs a * cAt F f s' hs b := by
  simp only [cAt, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem cAt_single {T : Scheme.{0}} {r : ℕ} (f : T ⟶ (powA F r).left) (s' : T ⟶ Sp o) (hs : f ≫ toO F r = s')
    (i : Fin r) : cAt F f s' hs (Pi.single i 1) = ptAt F f s' hs i := by
  classical
  show ∏ j, ptAt F f s' hs j ^ (Pi.single i 1 : Fin r → ℤ) j = _
  rw [Finset.prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zpow_zero]) (by simp),
    Pi.single_eq_same, zpow_one]

end Pow

end GlobalTheory.LowChart

namespace GlobalTheory.LowChart

section Base

variable {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F : ZM.SFam h n ζ) {r : ℕ} (y : (powA F r).left)

instance smooth_toO : Smooth (toO F r) := by
  have := F.smooth
  have : Smooth F.s := SmoothOfRelativeDimension.smooth (h * (h + 1) / 2) F.s
  have := F.univ.ab.smooth
  have := GlobalTheory.smooth_powObj_hom F.univ.A r
  unfold toO
  infer_instance

instance isLocallyNoetherian_powA [IsNoetherianRing o] : IsLocallyNoetherian (powA F r).left :=
  LocallyOfFiniteType.isLocallyNoetherian (toO F r)

variable [IsNoetherianRing o]

abbrev W : Type :=
  AdicCompletion (maximalIdeal ((powA F r).left.presheaf.stalk y)) ((powA F r).left.presheaf.stalk y)

def toPow : Sp (W F y) ⟶ (powA F r).left := GlobalTheory.fromSpecCompletedStalk _ y

def base : o →+* W F y := (Spec.preimage (toPow F y ≫ toO F r)).hom

theorem spMap_base : spMap (base F y) = toPow F y ≫ toO F r := by
  show Spec.map (CommRingCat.ofHom (Spec.preimage (toPow F y ≫ toO F r)).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

abbrev sieg : SiegPre h n ζ (spMap (base F y)) := siegAt F (toPow F y) _ (spMap_base F y).symm

abbrev pt (i : Fin r) : 𝟙_ (Over (Sp (W F y))) ⟶ (sieg F y).A := ptAt F (toPow F y) _ (spMap_base F y).symm i

abbrev c₀ (a : Fin r → ℤ) : 𝟙_ (Over (Sp (W F y))) ⟶ (sieg F y).A := cAt F (toPow F y) _ (spMap_base F y).symm a

theorem principal_sieg : (sieg F y).Principal :=
  principal_siegPull _ _ _ _ F.princ

abbrev cLev (a : Fin r → ℤ) : 𝟙_ (Over (Sp (W F y))) ⟶ (sieg F y).A := c₀ F y ((n : ℤ) • a)

theorem c₀_add (a b : Fin r → ℤ) : c₀ F y (a + b) = c₀ F y a * c₀ F y b := cAt_add _ _ _ _ a b

theorem c₀_single (i : Fin r) : c₀ F y (Pi.single i 1) = pt F y i := cAt_single _ _ _ _ i

theorem pt_left (i : Fin r) :
    (pt F y i).left ≫ Pdiv.PullbackComparison.pφ (toPow F y ≫ (powA F r).hom) F.univ.A = toPow F y ≫ (coord F i).left :=
  ptAt_left _ _ _ _ i

theorem toPow_closedPoint : toPow F y (closedPoint (W F y)) = y := by
  rw [toPow, GlobalTheory.fromSpecCompletedStalk]
  erw [Scheme.Hom.comp_apply]
  have hc : spMap (algebraMap ((powA F r).left.presheaf.stalk y) (W F y)) (closedPoint (W F y)) = closedPoint _ :=
    @IsLocalRing.comap_closedPoint _ _ _ _ _ _ _ (by
      show IsLocalHom (algebraMap ((powA F r).left.presheaf.stalk y) (W F y))
      infer_instance)
  erw [hc]
  exact Scheme.fromSpecStalk_closedPoint

end Base

end GlobalTheory.LowChart

namespace GlobalTheory.LowChart

section Props

variable {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F : ZM.SFam h n ζ) {r : ℕ} (y : (powA F r).left)

theorem isAdicComplete_completedStalkSiegelFibrePower [IsNoetherianRing o] : IsAdicComplete (maximalIdeal (W F y)) (W F y) := inferInstance

theorem isNoetherianRing_completedStalkSiegelFibrePower [IsNoetherianRing o] : IsNoetherianRing (W F y) :=
  GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _

theorem isRegularLocalRing_stalk [IsRegularRing o] : IsRegularLocalRing ((powA F r).left.presheaf.stalk y) := by
  have : IsRegularRing ((powA F r).left.presheaf.stalk y) :=
    GlobalTheory.ExtendRig.isRegularRing_stalk GlobalTheory.isRegularRing_of_smooth o (toO F r) y
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing _

theorem isRegularLocalRing_W_of_isRegularRing [IsRegularRing o] : IsRegularLocalRing (W F y) := by
  have := isRegularLocalRing_stalk F y
  exact GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion _

theorem isDomain_W_of_isRegularRing [IsRegularRing o] : IsDomain (W F y) := by
  have := isRegularLocalRing_W_of_isRegularRing F y
  exact (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing _).1

theorem existsUnique_factor [IsNoetherianRing o] (V : Type) [CommRing V] [IsLocalRing V]
    [IsAdicComplete (maximalIdeal V) V] (f : Sp V ⟶ (powA F r).left) (hf : f (closedPoint V) = y) :
    ∃! g : Sp V ⟶ Sp (W F y), g ≫ toPow F y = f := by
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.existsUnique_factor_stalk f hf
  have hl := GlobalTheory.isLocalHom_of_factor_stalk hf hφ
  refine GlobalTheory.existsUnique_factor_completedStalk' (maximalIdeal V) hφ
    (maximalIdeal _).fg_of_isNoetherianRing ⟨1, ?_⟩
  rw [pow_one, Ideal.map_le_iff_le_comap]
  intro x hx
  exact (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hx (isUnit_of_map_unit φ.hom x hu)

theorem exists_local_hom [IsNoetherianRing o] (V : Type) [CommRing V] [IsLocalRing V]
    [IsAdicComplete (maximalIdeal V) V] (f : Sp V ⟶ (powA F r).left) (hf : f (closedPoint V) = y) :
    ∃ ψ : W F y →+* V, IsLocalHom ψ ∧ spMap ψ ≫ toPow F y = f := by
  obtain ⟨g, hg, -⟩ := existsUnique_factor F y V f hf
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  exact ⟨ψ.hom, GlobalTheory.isLocalHom_of_factor_completedStalk hf (maximalIdeal _).fg_of_isNoetherianRing hg, hg⟩

end Props

end GlobalTheory.LowChart

namespace GlobalTheory.LowChart

section Zero

open SiegelTor

variable (n : ℕ) (hn : 3 ≤ n)

theorem isUnit_zetaAway (n : ℕ) (hn : 3 ≤ n) : IsUnit (zetaAway n) := by
  rw [← cycBase_ζ (show n ≠ 0 by omega)]
  exact (cycBase (show n ≠ 0 by omega)).ζ.isUnit

def zeroFam : ZM.SFam 0 n (zetaAway n) :=
  ZM.SFamModel.zeroFamLevel (isUnit_zetaAway n hn) (isUnit_natCast (show n ≠ 0 by omega)) (by omega)

instance : IsRegularRing (cycAway n) := by
  have := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  infer_instance

def primeUnder {r : ℕ} (y : (powA (zeroFam n hn) r).left) : PrimeSpectrum (cycAway n) := toO (zeroFam n hn) r y

example (r : ℕ) (y : (powA (zeroFam n hn) r).left) : IsDomain (W (zeroFam n hn) y) := isDomain_W_of_isRegularRing _ y
example (r : ℕ) (y : (powA (zeroFam n hn) r).left) : IsRegularLocalRing (W (zeroFam n hn) y) := isRegularLocalRing_W_of_isRegularRing _ y
example (r : ℕ) (y : (powA (zeroFam n hn) r).left) : (sieg (zeroFam n hn) y).Principal := principal_sieg _ y

end Zero

end GlobalTheory.LowChart

namespace GlobalTheory.LowChart

section Flat

variable {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F : ZM.SFam h n ζ) {r : ℕ} (y : (powA F r).left)
  [IsNoetherianRing o]

theorem flat_spMap_base : Flat (spMap (base F y)) := by
  rw [spMap_base, toPow, GlobalTheory.fromSpecCompletedStalk]
  have h₁ : Flat (Spec.map (CommRingCat.ofHom (algebraMap ((powA F r).left.presheaf.stalk y) (W F y)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk (powA F r).left y
  infer_instance

theorem flat_base : (base F y).Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 (flat_spMap_base F y)

theorem injective_base [IsDomain o] : Function.Injective (base F y) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h0
  algebraize [base F y]
  have : Module.Flat o (W F y) := flat_base F y
  have hreg := IsSMulRegular.of_ne_zero (M := W F y) h0
  have e : a • (1 : W F y) = a • 0 := by
    rw [Algebra.smul_def, _root_.mul_one, smul_zero]
    exact ha
  exact one_ne_zero (hreg e)

theorem charZero_W_of_charZero [IsDomain o] [CharZero o] : CharZero (W F y) :=
  charZero_of_injective_ringHom (injective_base F y)

example (n : ℕ) (hn : 3 ≤ n) (r : ℕ) (y : (powA (zeroFam n hn) r).left) : CharZero (W (zeroFam n hn) y) :=
  charZero_W_of_charZero _ y

end Flat

end GlobalTheory.LowChart
