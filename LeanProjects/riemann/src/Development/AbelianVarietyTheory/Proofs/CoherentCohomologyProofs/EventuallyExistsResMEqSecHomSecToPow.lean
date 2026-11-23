import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AwayEquivAwayFracEqIff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Filter DirectSum
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)

namespace GlobalTheory

namespace Twist

open MvPolynomial

variable {X : Scheme.{0}} {L : LB X} {ι : Type} {m n : ℤ}

theorem eval₂Hom_unit_mul {R B : Type*} [CommRing R] [CommRing B] (c : R →+* B) (u : Bˣ) (b : ι → B)
    {p : MvPolynomial ι R} {d : ℤ} (hp : p ∈ polyGrading ι R d) :
    eval₂Hom c (fun j => u * b j) p = ((u ^ d : Bˣ) : B) * eval₂Hom c b p := by
  rw [coe_eval₂Hom, coe_eval₂Hom, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← mem_polyGrading_iff.1 hp a (mem_support_iff.1 ha), zpow_natCast, Units.val_pow_eq_pow_val]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [Finsupp.degree_apply, mul_left_comm]

variable (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] (x : ι → LB.Sec L)

def chartEval (i : L.ι) {V : X.Opens} (h : V ≤ L.U i) : MvPolynomial ι R →+* Γ(X, V) :=
  eval₂Hom ((resG X le_top).comp (algebraMap R Γ(X, ⊤))) fun j => resG X h ((x j).f i)

@[simp] theorem chartEval_C (i : L.ι) {V : X.Opens} (h : V ≤ L.U i) (r : R) :
    chartEval R x i h (C r) = resG X le_top (algebraMap R Γ(X, ⊤) r) := eval₂Hom_C _ _ r

@[simp] theorem chartEval_X (i : L.ι) {V : X.Opens} (h : V ≤ L.U i) (j : ι) :
    chartEval R x i h (MvPolynomial.X j) = resG X h ((x j).f i) := eval₂Hom_X' _ _ j

@[simp] theorem resG_chartEval (i : L.ι) {V W : X.Opens} (h : V ≤ L.U i) (h' : W ≤ V)
    (p : MvPolynomial ι R) : resG X h' (chartEval R x i h p) = chartEval R x i (h'.trans h) p := by
  induction p using MvPolynomial.induction_on with
  | C r => rw [chartEval_C, chartEval_C, resG_resG]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, hp, chartEval_X, resG_resG]

variable {R} in

def formSec {p : MvPolynomial ι R} {d : ℤ} (hp : p ∈ polyGrading ι R d) : LB.Sec (lbZPow L d) :=
  zmkGlobal (fun i => chartEval R x i le_rfl p) fun i j => by
    rw [resG_chartEval, resG_chartEval, chartEval, chartEval, ← eval₂Hom_unit_mul _ _ _ hp]
    exact congrArg (fun b => eval₂Hom _ b p) (funext fun l => (x l).compat i j)

variable {R} in

@[simp] theorem zfun_formSec {p : MvPolynomial ι R} {d : ℤ} (hp : p ∈ polyGrading ι R d)
    (i : L.ι) : zfun (formSec x hp) i = chartEval R x i le_rfl p := zfun_zmkGlobal _ _ i

def prodSec (I : Finset ι) : LB.Sec (lbZPow L I.card) :=
  formSec (R := Γ(X, ⊤)) x (xProd_mem _ I)

theorem chartEval_xProd (i : L.ι) {V : X.Opens} (h : V ≤ L.U i) (I : Finset ι) :
    chartEval R x i h (xProd R I) = ∏ j ∈ I, resG X h ((x j).f i) := by
  simp only [map_prod, chartEval_X]

@[simp] theorem zfun_prodSec (I : Finset ι) (i : L.ι) :
    zfun (prodSec x I) i = ∏ j ∈ I, (x j).f i := by
  simp only [prodSec, zfun_formSec, chartEval_xProd, resG_self]

theorem nonzeroLocus_prodSec (hL : L.IsLB) (I : Finset ι) :
    Out.nonzeroLocus (prodSec x I) = ⨅ j ∈ I, Out.nonzeroLocus (x j) := by
  classical
  refine nonzeroLocus_eq_of_zfun hL _ fun i => ?_
  rw [zfun_prodSec]
  induction I using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul, ih, Finset.iInf_insert,
      ← nonzeroLocus_inf_chart, inf_comm (Out.nonzeroLocus _), ← inf_inf_distrib_left]

variable (F : X.Modules) {G : X.Modules} {U V W : X.Opens}

variable (V) in

def gammaOp (j : ι) (n : ℤ) :
    sectionsOn (twistZ F L n) V →ₗ[R] sectionsOn (twistZ F L (n + 1)) V :=
  sectionsOn.map R (mulSec F (zofSec (x j)) n) V

variable (V) in

theorem gammaOp_commute : OperatorsCommute (gammaOp R x F V) := fun i j n a =>
  congr(sectionsOn.map R $(mulSecOfEq_comm (F := F) (zofSec (x j)) (zofSec (x i)) (n := n)
    rfl rfl rfl rfl) V a)

variable (V) in

abbrev GammaStar : Type := GrSum (gammaOp_commute R x F V)

variable (V) in

abbrev gammaGrading : ℤ → Submodule R (GammaStar R x F V) :=
  GrSum.grading (gammaOp_commute R x F V)

variable (V) in

abbrev gammaOf (n : ℤ) : sectionsOn (twistZ F L n) V →ₗ[R] GammaStar R x F V :=
  GrSum.of (gammaOp_commute R x F V) n

def gammaRes (h : W ≤ V) : GammaStar R x F V →ₗ[MvPolynomial ι R] GammaStar R x F W :=
  GrSum.map _ _ (fun n => sectionsOn.res R (twistZ F L n) h) fun _ _ a =>
    sectionsOn.res_map R _ h a

@[simp] theorem gammaRes_gammaOf (h : W ≤ V) (a : sectionsOn (twistZ F L n) V) :
    gammaRes R x F h (gammaOf R x F V n a) = gammaOf R x F W n (sectionsOn.res R _ h a) :=
  GrSum.map_of (gammaOp_commute R x F V) (gammaOp_commute R x F W)
    (fun n => sectionsOn.res R (twistZ F L n) h) _ n a

theorem isGradedMap_gammaRes (h : W ≤ V) :
    IsGradedMap (gammaGrading R x F V) (gammaGrading R x F W) (gammaRes R x F h) :=
  GrSum.isGradedMap_map _ _ _ _

theorem gammaRes_gammaRes (h : V ≤ U) (h' : W ≤ V) (y : GammaStar R x F U) :
    gammaRes R x F h' (gammaRes R x F h y) = gammaRes R x F (h'.trans h) y := by
  have e : ((gammaRes R x F h' ∘ₗ gammaRes R x F h).restrictScalars R) =
      (gammaRes R x F (h'.trans h)).restrictScalars R :=
    GrSum.lhom_ext _ fun n a => by
      simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, gammaRes_gammaOf,
        sectionsOn.res_res]
  exact congr($e y)

variable {F} in

def gammaMap (φ : F ⟶ G) (V : X.Opens) :
    GammaStar R x F V →ₗ[MvPolynomial ι R] GammaStar R x G V :=
  GrSum.map _ _ (fun n => sectionsOn.map R (map (lbZPow L n) φ) V) fun j n a =>
    congr(sectionsOn.map R $((mulSecOfEq_naturality (zofSec (x j)) (n := n) rfl φ).symm) V a)

variable {F} in

@[simp] theorem gammaMap_gammaOf (φ : F ⟶ G) (a : sectionsOn (twistZ F L n) V) :
    gammaMap R x φ V (gammaOf R x F V n a) =
      gammaOf R x G V n (sectionsOn.map R (map (lbZPow L n) φ) V a) := by
  rw [gammaMap, GrSum.map_of]

variable (V) in

def gammaCoord (i : L.ι) : GammaStar R x F V →ₗ[R] sectionsOn F (V ⊓ L.U i) :=
  GrSum.desc _ fun _ =>
    { toFun := fun a => (sectionsOn.toΓ F _).symm (zcoord (sectionsOn.toΓ _ V a) i)
      map_add' := fun a b => zcoord_add (F := F) a b i
      map_smul' := fun _ a => (zcoord_smul (F := F) _ a i).trans
        (congrArg (· • zcoord (F := F) a i) (resG_resG le_top inf_le_left _)) }

theorem gammaCoord_gammaOf (i : L.ι) (a : sectionsOn (twistZ F L n) V) :
    sectionsOn.toΓ F _ (gammaCoord R x F V i (gammaOf R x F V n a)) =
      zcoord (sectionsOn.toΓ _ V a) i :=
  by rw [gammaCoord, GrSum.desc_of]; rfl

theorem gammaCoord_smul (i : L.ι) (p : MvPolynomial ι R) (y : GammaStar R x F V) :
    sectionsOn.toΓ F _ (gammaCoord R x F V i (p • y)) =
      chartEval R x i (inf_le_right : V ⊓ L.U i ≤ L.U i) p • sectionsOn.toΓ F _ (gammaCoord R x F V i y) := by
  induction p using MvPolynomial.induction_on generalizing y with
  | C r =>
    rw [chartEval_C, ← algebraMap_eq, algebraMap_smul, map_smul]
    rfl
  | add p q hp hq => simp only [add_smul, map_add, hp, hq]
  | mul_X p j hp =>
    rw [mul_smul, hp, map_mul, mul_smul, chartEval_X]
    congr 1
    induction y using Decomposition.inductionOn (gammaGrading R x F V) with
    | zero => simp only [smul_zero, map_zero]
    | add a b ha hb => simp only [smul_add, map_add, ha, hb]
    | homogeneous a =>
      obtain ⟨_, a, rfl⟩ := a
      rw [GrSum.X_smul_of, gammaCoord_gammaOf, gammaCoord_gammaOf, gammaOp, sectionsOn.toΓ_map,
        zcoord_mulSecOfEq_app, zfun_zofSec]

variable {R x} in

theorem smul_gammaOf {p : MvPolynomial ι R} {e e' d : ℤ} (hp : p ∈ polyGrading ι R e)
    (σ : LB.Sec (lbZPow L e')) (hσ : ∀ i, zfun σ i = chartEval R x i le_rfl p) (he : e = e')
    (h : n + e' = d) (a : sectionsOn (twistZ F L n) V) :
    p • gammaOf R x F V n a = gammaOf R x F V d (sectionsOn.map R (mulSecOfEq F σ h) V a) := by
  subst he h
  obtain ⟨b, hb⟩ := grSMul_mem (gammaGrading R x F V) hp (GrSum.of_mem_grading _ n a)
  rw [← hb]
  refine congrArg _ ((sectionsOn.toΓ _ V).injective (zsec_ext fun i => ?_))
  rw [← gammaCoord_gammaOf R x, hb, gammaCoord_smul, gammaCoord_gammaOf, sectionsOn.toΓ_map,
    zcoord_mulSecOfEq_app, hσ, resG_chartEval]

theorem xProd_pow_smul_gammaOf (I : Finset ι) (k : ℕ) {d : ℤ} (h : n + k * I.card = d)
    (a : sectionsOn (twistZ F L n) V) :
    xProd R I ^ k • gammaOf R x F V n a =
      gammaOf R x F V d (sectionsOn.map R (mulSecOfEq F (zpowSec (prodSec x I) k) h) V a) :=
  smul_gammaOf F (xProd_pow_mem R I k) _ (fun i => by
    simp only [zfun_zpowSec, zfun_prodSec, map_pow, chartEval_xProd, resG_self]) rfl h a

theorem gammaOp_bijective (hL : L.IsLB) {j : ι} (hV : V ≤ Out.nonzeroLocus (x j)) (n : ℤ) :
    Function.Bijective (gammaOp R x F V j n) :=
  bijective_mulSecOfEq_app hL (zofSec (x j)) rfl (hV.trans (nonzeroLocus_zofSec hL _).ge)

theorem xProd_smul_gammaStar_bijective (hL : L.IsLB) {I : Finset ι}
    (hV : V ≤ ⨅ j ∈ I, Out.nonzeroLocus (x j)) :
    Function.Bijective fun y : GammaStar R x F V => xProd R I • y :=
  xProd_smul_bijective_of I fun _ hj => GrSum.X_smul_bijective _
    (gammaOp_bijective R x F hL (hV.trans (biInf_le (fun j => Out.nonzeroLocus (x j)) hj)))

section Loc

variable [F.IsQuasicoherent] (hL : L.IsLB) (hW : IsCompact (W : Set X))
  (hW' : IsQuasiSeparated (W : Set X))

include hL hW in

theorem eventually_xProd_pow_smul_eq_zero {I : Finset ι} (h : V ≤ W)
    (hV : W ⊓ ⨅ j ∈ I, Out.nonzeroLocus (x j) ≤ V) (y : GammaStar R x F W)
    (hy : gammaRes R x F h y = 0) : ∀ᶠ k : ℕ in atTop, xProd R I ^ k • y = 0 := by
  obtain ⟨T, hT⟩ := exists_sum_grProj (gammaGrading R x F W) y
  have key : ∀ n, ∀ᶠ k : ℕ in atTop,
      xProd R I ^ k • GradedHilbert.proj (gammaGrading R x F W) n y = 0 := fun n => by
    have h0 := (isGradedMap_gammaRes R x F h).proj_apply n y
    rw [hy, map_zero, GrSum.proj_grading, gammaRes_gammaOf] at h0
    have h1 := GrSum.of_injective _ n (h0.symm.trans (map_zero _).symm)
    refine (eventually_mulSecOfEq_zpowSec_eq_zero hL (prodSec x I) hW h
      (by rwa [nonzeroLocus_prodSec x hL]) _ h1).mono fun k hk => ?_
    rw [GrSum.proj_grading, xProd_pow_smul_gammaOf R x F I k rfl]
    exact (congrArg _ (hk _ rfl)).trans (map_zero _)
  refine ((eventually_all_finset T).2 fun n _ => key n).mono fun k hk => ?_
  rw [← hT, Finset.smul_sum]
  exact Finset.sum_eq_zero hk

include hL hW hW' in

theorem eventually_exists_gammaRes_eq {I : Finset ι} (h : V ≤ W)
    (hV : V = W ⊓ ⨅ j ∈ I, Out.nonzeroLocus (x j)) (z : GammaStar R x F V) :
    ∀ᶠ k : ℕ in atTop, ∃ y, gammaRes R x F h y = xProd R I ^ k • z := by
  induction z using Decomposition.inductionOn (gammaGrading R x F V) with
  | zero => exact .of_forall fun k => ⟨0, by rw [smul_zero, map_zero]⟩
  | add y z hy hz =>
    exact (hy.and hz).mono fun k ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => ⟨a + b, by rw [smul_add, map_add, ha, hb]⟩
  | homogeneous b =>
    obtain ⟨_, b, rfl⟩ := b
    refine (eventually_exists_resM_eq_mulSecOfEq_zpowSec hL (prodSec x I) hW hW' h
      (by rwa [nonzeroLocus_prodSec x hL]) b).mono fun k hk => ?_
    obtain ⟨a, ha⟩ := hk _ rfl
    exact ⟨gammaOf R x F W _ a, (gammaRes_gammaOf R x F h a).trans
      ((congrArg _ ha).trans (xProd_pow_smul_gammaOf R x F I k rfl b).symm)⟩

def gammaLocEquiv {I : Finset ι} (h : V ≤ W) (hV : V = W ⊓ ⨅ j ∈ I, Out.nonzeroLocus (x j))
    (n : ℤ) : homLoc (gammaGrading R x F W) I n ≃ₗ[R] sectionsOn (twistZ F L n) V :=
  (LinearEquiv.ofBijective (homLocMap (isGradedMap_gammaRes R x F h) I n)
    ⟨homLocMap_injective_of _ (fun y hy =>
        (eventually_xProd_pow_smul_eq_zero R x F hL hW h hV.ge y hy).exists) n,
      homLocMap_surjective_of _ (fun z =>
        (eventually_exists_gammaRes_eq R x F hL hW hW' h hV z).exists) n⟩).trans
    ((LinearEquiv.ofBijective _ (toHomLoc_bijective _
      (xProd_smul_gammaStar_bijective R x F hL (hV.le.trans inf_le_right)) n)).symm.trans
        (GrSum.pieceEquiv _ n).symm)

theorem xProd_pow_smul_gammaLocEquiv {I : Finset ι} (h : V ≤ W)
    (hV : V = W ⊓ ⨅ j ∈ I, Out.nonzeroLocus (x j)) (z : homLoc (gammaGrading R x F W) I n) (k : ℕ)
    (y : GammaStar R x F W) (e : awayFrac _ (xProd R I) k y = z) :
    xProd R I ^ k • gammaOf R x F V n (gammaLocEquiv R x F hL hW hW' h hV n z) =
      gammaRes R x F h y := by
  have hb := xProd_smul_gammaStar_bijective R x F hL (hV.le.trans inf_le_right)
  let e' := LinearEquiv.ofBijective _ (toHomLoc_bijective (gammaGrading R x F V) hb n)
  have h₁ : gammaOf R x F V n (gammaLocEquiv R x F hL hW hW' h hV n z) =
      (e'.symm (homLocMap (isGradedMap_gammaRes R x F h) I n z) : GammaStar R x F V) :=
    congrArg Subtype.val ((GrSum.pieceEquiv _ n).apply_symm_apply _)
  have h₂ : awayFrac _ (xProd R I) 0
      (e'.symm (homLocMap (isGradedMap_gammaRes R x F h) I n z) : GammaStar R x F V) =
        awayMap _ (gammaRes R x F h) z :=
    congrArg Subtype.val (e'.apply_symm_apply _)
  apply awayFrac_injective hb.1 0
  rw [map_smul, h₁, h₂, ← e, awayMap_awayFrac, pow_smul_awayFrac]

theorem gammaLocEquiv_eq_iff {I : Finset ι} (h : V ≤ W)
    (hV : V = W ⊓ ⨅ j ∈ I, Out.nonzeroLocus (x j)) (z : homLoc (gammaGrading R x F W) I n) (k : ℕ)
    (y : GammaStar R x F W) (e : awayFrac _ (xProd R I) k y = z) (b : sectionsOn (twistZ F L n) V) :
    gammaLocEquiv R x F hL hW hW' h hV n z = b ↔
      xProd R I ^ k • gammaOf R x F V n b = gammaRes R x F h y := by
  rw [← xProd_pow_smul_gammaLocEquiv R x F hL hW hW' h hV z k y e,
    (IsSMulRegular.pow k
      (xProd_smul_gammaStar_bijective R x F hL (hV.le.trans inf_le_right)).1).eq_iff,
    (GrSum.of_injective _ n).eq_iff, eq_comm]

theorem gammaLocEquiv_homLocRes {I J : Finset ι} (hIJ : I ⊆ J) (h : V ≤ W)
    (hV : V = W ⊓ ⨅ j ∈ I, Out.nonzeroLocus (x j)) (h' : U ≤ V)
    (hU : U = W ⊓ ⨅ j ∈ J, Out.nonzeroLocus (x j)) (z : homLoc (gammaGrading R x F W) I n) :
    gammaLocEquiv R x F hL hW hW' (h'.trans h) hU n (homLocRes _ hIJ n z) =
      sectionsOn.res R _ h' (gammaLocEquiv R x F hL hW hW' h hV n z) := by
  obtain ⟨k, y, e⟩ := exists_awayFrac z.1
  obtain ⟨c, hc⟩ : ∃ c, xProd R J = c * xProd R I :=
    exists_eq_mul_left_of_dvd (Finset.prod_dvd_prod_of_subset I J MvPolynomial.X hIJ)
  refine (gammaLocEquiv_eq_iff R x F hL hW hW' _ hU _ k (c ^ k • y) ?_ _).2 ?_
  · rw [coe_homLocRes, ← e, locRes_awayFrac MvPolynomial.X hIJ hc]
  · rw [map_smul, ← gammaRes_gammaRes R x F h h',
      ← xProd_pow_smul_gammaLocEquiv R x F hL hW hW' h hV z k y e, map_smul, gammaRes_gammaOf, hc,
      mul_pow, mul_smul]

def gammaCubeIso (n : ℤ) : grCube ι (gammaGrading R x F W) n ≅
    cechCube R (twistZ F L n) W fun j => Out.nonzeroLocus (x j) :=
  Cube.isoMk (A := grCube ι (gammaGrading R x F W) n)
    (fun I => gammaLocEquiv R x F hL hW hW' (cechOpen_le W _ I) rfl n)
    fun hIJ z => gammaLocEquiv_homLocRes R x F hL hW hW' hIJ _ rfl (cechOpen_anti W _ hIJ) rfl z

def gammaCechIso [LinearOrder ι] (n : ℤ) : grCech ι (gammaGrading R x F W) n ≅
    cech R (twistZ F L n) W fun j => Out.nonzeroLocus (x j) :=
  (cechFunctor ι R).mapIso (gammaCubeIso R x F hL hW hW' n)

end Loc

example (hL : L.IsLB) [Nontrivial Γ(F, V)] : Nontrivial (GammaStar R x F V) :=
  ((GrSum.of_injective (gammaOp_commute R x F V) 0).comp
    (ConcreteCategory.bijective_of_isIso ((twistZZeroIso F hL).hom.app V)).1).nontrivial

end Twist

end GlobalTheory
