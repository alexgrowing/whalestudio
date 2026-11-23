import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCycPerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasChainW

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat
open GlobalTheory.DeRham (spOver spOver_comp)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus

section Bplus

abbrev BplusIn (A K : Type) [CommRing A] [Field K] [Algebra A K] : Type := integralClosure A K

abbrev Bplus (A : Type) [CommRing A] [IsDomain A] : Type := BplusIn A (AlgebraicClosure (FractionRing A))

theorem faithfulSMul_algClosure (A F : Type) [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F] :
    FaithfulSMul A (AlgebraicClosure F) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 <| by
    rw [IsScalarTower.algebraMap_eq A F (AlgebraicClosure F)]
    exact (algebraMap F (AlgebraicClosure F)).injective.comp (IsFractionRing.injective _ _)

theorem isAlgebraic_algClosure (A F : Type) [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F] :
    Algebra.IsAlgebraic A (AlgebraicClosure F) :=
  (IsFractionRing.comap_isAlgebraic_iff (K := F)).2 inferInstance

instance (A : Type) [CommRing A] [IsDomain A] : FaithfulSMul A (AlgebraicClosure (FractionRing A)) :=
  faithfulSMul_algClosure A _

instance (A : Type) [CommRing A] [IsDomain A] : Algebra.IsAlgebraic A (AlgebraicClosure (FractionRing A)) :=
  isAlgebraic_algClosure A _

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

instance isFractionRing [IsDomain A] [FaithfulSMul A K] [Algebra.IsAlgebraic A K] : IsFractionRing (BplusIn A K) K :=
  integralClosure.isFractionRing_of_algebraic fun _ hx => FaithfulSMul.algebraMap_injective A K (hx.trans (map_zero _).symm)

instance isIntegrallyClosed [IsDomain A] [FaithfulSMul A K] [Algebra.IsAlgebraic A K] : IsIntegrallyClosed (BplusIn A K) :=
  (isIntegrallyClosed_iff_isIntegrallyClosedIn K).2 inferInstance

variable {A K}

theorem mem_of_pow_mem {x : K} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ integralClosure A K) : x ∈ integralClosure A K :=
  IsIntegral.of_pow hn h

theorem exists_pow_eq [IsAlgClosed K] (x : BplusIn A K) {n : ℕ} (hn : 0 < n) : ∃ y : BplusIn A K, y ^ n = x := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : K) hn
  exact ⟨⟨y, mem_of_pow_mem hn (hy ▸ x.2)⟩, Subtype.ext hy⟩

theorem not_isUnit_algebraMap [FaithfulSMul A K] {a : A} (h : ¬ IsUnit a) : ¬ IsUnit (algebraMap A (BplusIn A K) a) := by
  haveI : FaithfulSMul A (BplusIn A K) := (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y e =>
    FaithfulSMul.algebraMap_injective A K (congrArg Subtype.val e)
  exact fun h' => h (isUnit_of_map_unit (algebraMap A (BplusIn A K)) a h')

theorem not_isUnit_natCast [FaithfulSMul A K] {p : ℕ} (h : ¬ IsUnit (p : A)) : ¬ IsUnit (p : BplusIn A K) :=
  map_natCast (algebraMap A (BplusIn A K)) p ▸ not_isUnit_algebraMap h

variable (A K) in

theorem exists_zeta [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] : ∃ ζ : ℕ → BplusIn A K,
    (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) ∧ ∀ n, ζ (n + 1) ^ p = ζ n := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p : K) := ⟨Nat.cast_ne_zero.2 hp.ne_zero⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  have hz' : IsPrimitiveRoot (⟨z, mem_of_pow_mem hp.pos (hz.pow_eq_one ▸ one_mem _)⟩ : BplusIn A K) p :=
    IsPrimitiveRoot.of_map_of_injective (f := (integralClosure A K).val) hz Subtype.val_injective
  generalize (⟨z, _⟩ : BplusIn A K) = z₁ at hz'
  choose r hr using fun x : BplusIn A K => exists_pow_eq x hp.pos
  have key : ∀ n, (r^[n] z₁) ^ p ^ n = z₁ := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', pow_succ', pow_mul, hr, ih]
  refine ⟨fun n => Nat.casesOn n 1 fun m => r^[m] z₁, fun n => ?_, fun n => ?_⟩
  · cases n with
    | zero => exact IsPrimitiveRoot.one
    | succ m =>
      refine (IsPrimitiveRoot.iff_orderOf).2 (orderOf_eq_prime_pow ?_ ?_)
      · exact (key m).symm ▸ hz'.ne_one hp.one_lt
      · change (r^[m] z₁) ^ p ^ (m + 1) = 1
        rw [pow_succ, pow_mul, key, hz'.pow_eq_one]
  · cases n with
    | zero => exact hz'.pow_eq_one
    | succ m => exact (congrArg (· ^ p) (Function.iterate_succ_apply' r m z₁)).trans (hr _)

def incl {A' : Type} [CommRing A'] [Algebra A' K] (φ : A →+* A') (h : ∀ a, algebraMap A' K (φ a) = algebraMap A K a) :
    BplusIn A K →+* BplusIn A' K :=
  (integralClosure A K).val.toRingHom.codRestrict (integralClosure A' K) fun x =>
    IsIntegral.map_of_comp_eq φ (RingHom.id K) (RingHom.ext h) x.2

@[simp] theorem coe_incl {A' : Type} [CommRing A'] [Algebra A' K] (φ : A →+* A')
    (h : ∀ a, algebraMap A' K (φ a) = algebraMap A K a) (x : BplusIn A K) : (incl φ h x : K) = x := rfl

example (A : Type) [CommRing A] [IsDomain A] : IsDomain (Bplus A) ∧ IsIntegrallyClosed (Bplus A) ∧
    IsFractionRing (Bplus A) (AlgebraicClosure (FractionRing A)) := ⟨inferInstance, inferInstance, inferInstance⟩

example : (∃ y : Bplus ℤ, y ^ 2 = 2) ∧ ¬ IsUnit ((2 : ℕ) : Bplus ℤ) :=
  ⟨exists_pow_eq 2 two_pos, not_isUnit_natCast (by decide)⟩

end Bplus

section Opens

variable (X : Scheme.{0}) [IsIntegral X]

abbrev Kbar : Type := AlgebraicClosure X.functionField

def AffOp : Type := {U : X.Opens // IsAffineOpen U ∧ Nonempty U}

variable {X}

instance (U : AffOp X) : Nonempty U.1 := U.2.2

instance (U : AffOp X) : IsFractionRing Γ(X, U.1) X.functionField :=
  functionField_isFractionRing_of_isAffineOpen X U.1 U.2.1

instance (U : AffOp X) : FaithfulSMul Γ(X, U.1) (Kbar X) := faithfulSMul_algClosure _ _

instance (U : AffOp X) : Algebra.IsAlgebraic Γ(X, U.1) (Kbar X) := isAlgebraic_algClosure _ _

abbrev AffOp.Bp (U : AffOp X) : Type := BplusIn Γ(X, U.1) (Kbar X)

def AffOp.toX (U : AffOp X) : Sp U.Bp ⟶ X := spMap (algebraMap Γ(X, U.1) U.Bp) ≫ U.2.1.fromSpec

def AffOp.res {U U' : AffOp X} (h : U'.1 ≤ U.1) : U.Bp →+* U'.Bp :=
  incl (resG X h) fun a => congrArg (algebraMap X.functionField (Kbar X))
    (X.presheaf.germ_res_apply (homOfLE h) _ _ a)

theorem AffOp.res_toX {U U' : AffOp X} (h : U'.1 ≤ U.1) : spMap (AffOp.res h) ≫ U.toX = U'.toX := by
  rw [AffOp.toX, AffOp.toX, ← U.2.1.map_fromSpec U'.2.1 (homOfLE h).op, ← Category.assoc, ← Category.assoc,
    ← Cris.spMap_comp]
  have e : (AffOp.res h).comp (algebraMap Γ(X, U.1) U.Bp) = (algebraMap Γ(X, U'.1) U'.Bp).comp (resG X h) :=
    RingHom.ext fun a => Subtype.ext
      (congrArg (algebraMap X.functionField (Kbar X)) (X.presheaf.germ_res_apply (homOfLE h) _ _ a).symm)
  rw [e, Cris.spMap_comp]
  rfl

variable (X) in

def genPt : Sp (Kbar X) ⟶ X := spMap (algebraMap X.functionField (Kbar X)) ≫ X.fromSpecStalk (genericPoint X)

theorem AffOp.val_toX (U : AffOp X) : spMap (algebraMap U.Bp (Kbar X)) ≫ U.toX = genPt X := by
  have hx : genericPoint X ∈ U.1 := ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).2 (by simpa using U.2.2)
  rw [AffOp.toX, genPt, ← U.2.1.fromSpecStalk_eq_fromSpecStalk hx, IsAffineOpen.fromSpecStalk, ← Category.assoc,
    ← Cris.spMap_comp]
  exact (congrArg (· ≫ U.2.1.fromSpec) (Cris.spMap_comp (X.presheaf.germ U.1 _ hx).hom
    (algebraMap X.functionField (Kbar X)))).trans (Category.assoc ..)

example (U : AffOp X) : IsIntegrallyClosed U.Bp ∧ IsFractionRing U.Bp (Kbar X) := ⟨inferInstance, inferInstance⟩

end Opens

section TorsionMap

variable {p : ℕ} {O : Type} [CommRing O]

abbrev Tors (A : Over (Sp O)) [GrpObj A] (N : ℕ) (B : Type) [CommRing B] [Algebra O B] : Type :=
  {z : SpAlg O B ⟶ A // z ^ N = 1}

structure TorsionMap (A : Over (Sp O)) [GrpObj A] (G : PDivGroup p O) : Type 1 where

  pt : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B], Tors A (p ^ n) B → (G.A n →ₐ[O] B)

  nat : ∀ (n : ℕ) (B C : Type) [CommRing B] [Algebra O B] [CommRing C] [Algebra O C] (φ : B →ₐ[O] C)
    (z : Tors A (p ^ n) B) (z' : Tors A (p ^ n) C), z'.1 = spOver φ ≫ z.1 → pt n C z' = φ.comp (pt n B z)

  mul : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (x y z : Tors A (p ^ n) B), z.1 = x.1 * y.1 →
    toConv (pt n B z) = toConv (pt n B x) * toConv (pt n B y)

  res : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (z : Tors A (p ^ n) B) (z' : Tors A (p ^ (n + 1)) B), z'.1 = z.1 →
    pt (n + 1) B z' = (pt n B z).comp (G.res n : G.A (n + 1) →ₐ[O] G.A n)

variable {A : Over (Sp O)} [GrpObj A] {G : PDivGroup p O}

theorem isTangent_iff_lieG (v : epsR O ⟶ A) : IsTangent v ↔
    Pdiv.ptMap (TrivSqZeroExt.fstHom O O O) ≫ (v : Pdiv.specO O (DualNumber O) ⟶ A) = toUnit (Pdiv.specO O O) ≫ η[A] := by
  have h' : (toUnit (Pdiv.specO O O)).left = 𝟙 (Sp O) := by
    rw [Over.toUnit_left]
    exact Spec.map_id _
  rw [Over.OverMorphism.ext_iff, Over.comp_left, Over.comp_left, h']
  exact ⟨fun h => h.trans (Category.id_comp _).symm, fun h => h.trans (Category.id_comp _)⟩

theorem isTangent_lieG (x : Pdiv.LieG A) : IsTangent (G := A) x.1 := (isTangent_iff_lieG _).2 x.2

def tanTors (p n : ℕ) (x : Pdiv.LieG A) : Tors A (p ^ n) (DualNumber (ModPow p O n)) :=
  ⟨epsRedPow p n x.1, epsRedPow_pow (isTangent_lieG x) n⟩

namespace TorsionMap

variable (θ : TorsionMap A G)

theorem pt_one (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (hp : p ≠ 0) : toConv (θ.pt n B ⟨1, one_pow _⟩) = 1 := by
  have h := θ.mul n B ⟨1, one_pow _⟩ ⟨1, one_pow _⟩ ⟨1, one_pow _⟩ (_root_.mul_one _).symm
  exact ((IsUnit.of_pow_eq_one (G.pts_pow_self n _) (pow_ne_zero n hp)).mul_eq_left).1 h.symm

def IsOpenNearZero : Prop :=
  ∀ n, ∃ (U : A.left.Opens) (V : (Sp (G.A n)).Opens), Set.range η[A].left ⊆ U ∧
    ∀ (B : Type) [CommRing B] [Algebra O B], Set.BijOn (θ.pt n B) {z | Set.range z.1.left ⊆ U}
      {φ | Set.range (spMap (φ : G.A n →+* B)) ⊆ V}

def IsIsoOver (W : Set (Sp O)) : Prop :=
  ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B], Set.range (spMap (algebraMap O B)) ⊆ W → Function.Bijective (θ.pt n B)

def IsOmegaAt (n : ℕ) (c : Pdiv.omega A →ₗ[O] Cot O (G.A n)) : Prop :=
  Function.Surjective c ∧ (∀ w, c w = 0 ↔ ∃ w', w = (p : O) ^ n • w') ∧
    ∀ (x : Pdiv.LieG A) (w : Pdiv.omega A) (a : G.A n), dUnit O a = c w →
      (θ.pt n _ (tanTors p n x) a).snd = Ideal.Quotient.mk _ (w.1 x)

def IsOmega (c : Pdiv.omega A →ₗ[O] G.omega) : Prop :=
  ∀ n, θ.IsOmegaAt n ((LinearMap.proj n ∘ₗ G.omegaSub.subtype) ∘ₗ c)

def Intertwines (f : A ⟶ A) (g : G ⟶ G) : Prop :=
  ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (z z' : Tors A (p ^ n) B), z'.1 = z.1 ≫ f →
    θ.pt n B z' = (θ.pt n B z).comp (g.app n : G.A n →ₐ[O] G.A n)

def ofTower (t : G.TorsionTower A) : TorsionMap A G where
  pt n B _ _ z := t.lift n z.1 z.2
  nat n B C _ _ _ _ φ z z' h := t.inj n C _ _ (by rw [t.lift_y, ← spOver_comp, Category.assoc, t.lift_y, h])
  mul n B _ _ x y z h := t.pts_injective n B (by rw [map_mul]; simp only [TorsionTower.pts_apply, t.lift_y, h])
  res n B _ _ z z' h := t.inj (n + 1) B _ _ (by rw [t.lift_y, ← spOver_comp, Category.assoc, t.res, t.lift_y, h])

theorem ofTower_bijective (t : G.TorsionTower A) (n : ℕ) (B : Type) [CommRing B] [Algebra O B] :
    Function.Bijective ((ofTower t).pt n B) :=
  ⟨fun z z' h => Subtype.ext ((t.lift_y n z.1 z.2).symm.trans ((congrArg (spOver · ≫ t.y n) h).trans (t.lift_y n z'.1 z'.2))),
    fun φ => ⟨⟨_, (t.exists_iff n _).1 ⟨φ, rfl⟩⟩, t.inj n B _ _ (t.lift_y n _ ((t.exists_iff n _).1 ⟨φ, rfl⟩))⟩⟩

theorem ofTower_isIsoOver (t : G.TorsionTower A) (W : Set (Sp O)) : (ofTower t).IsIsoOver W :=
  fun n B _ _ _ => ofTower_bijective t n B

theorem ofTower_isOpenNearZero (t : G.TorsionTower A) : (ofTower t).IsOpenNearZero := fun n =>
  ⟨⊤, ⊤, Set.subset_univ _, fun B _ _ => by
    simpa using ofTower_bijective t n B⟩

theorem ofTower_intertwines (t : G.TorsionTower A) (f : A ⟶ A) [IsMonHom f] : (ofTower t).Intertwines f (t.map t f) :=
  fun n B _ _ z z' h => t.inj n B _ _ (by
    change spOver (t.lift n z'.1 z'.2) ≫ _ = spOver ((t.lift n z.1 z.2).comp _) ≫ _
    rw [t.lift_y, ← spOver_comp, Category.assoc, t.map_y, ← Category.assoc, t.lift_y, h])

theorem ofTower_tanTors (t : G.TorsionTower A) (n : ℕ) (x : Pdiv.LieG A) :
    (ofTower t).pt n _ (tanTors p n x) = t.tanPt (isTangent_lieG x) n := rfl

end TorsionMap

section Mult

variable (p O) [Fact p.Prime]

def gmVec (c : O) : Pdiv.LieG (Gm (Sp O)) :=
  ⟨Diag.lieVec ((zmultiplesHom O c).comp (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).toAddMonoidHom),
    (isTangent_iff_lieG _).1 (Diag.isTangent_lieVec _)⟩

omit [Fact p.Prime] in

theorem gmCoord_gmVec (c : O) : gmCoord (B := DualNumber O) (gmVec O c).1 = 1 + TrivSqZeroExt.inr c :=
  (Diag.charVal_lieVec _ _).trans (congrArg (1 + TrivSqZeroExt.inr ·) (one_zsmul c))

omit [Fact p.Prime] in

theorem fst_gmCoord (x : Pdiv.LieG (Gm (Sp O))) : (gmCoord (B := DualNumber O) x.1).fst = 1 :=
  (gmCoord_comp (TrivSqZeroExt.fstHom O O O) x.1).symm.trans ((congrArg gmCoord x.2).trans (map_one gmCoordHom))

def gmForm : Pdiv.omega (Gm (Sp O)) :=
  ⟨fun x => (gmCoord (B := DualNumber O) x.1).snd, fun x y _ => by
      have h : gmCoord (B := DualNumber O) (x.1 * y.1) = gmCoord (B := DualNumber O) x.1 * gmCoord (B := DualNumber O) y.1 :=
        map_mul gmCoordHom _ _
      change (gmCoord (B := DualNumber O) (x.1 * y.1)).snd = _
      rw [h, DualNumber.snd_mul, fst_gmCoord, fst_gmCoord, _root_.one_mul, _root_.mul_one, add_comm],
    fun a x _ => (congrArg TrivSqZeroExt.snd (gmCoord_comp (Pdiv.dualScale a) x.1)).trans (by simp [Pdiv.dualScale])⟩

omit [Fact p.Prime] in

theorem omega_gm_eq (w : Pdiv.omega (Gm (Sp O))) : w = w.1 (gmVec O 1) • gmForm O :=
  Subtype.ext (funext fun x => by
    have h0 : gmCoord (B := DualNumber O) x.1 =
        Pdiv.dualScale (gmCoord (B := DualNumber O) x.1).snd (gmCoord (B := DualNumber O) (gmVec O 1).1) := by
      rw [gmCoord_gmVec]
      ext
      · simp [fst_gmCoord, Pdiv.dualScale]
      · simp [Pdiv.dualScale]
    have h1 : x.1 = spOver (Pdiv.dualScale (gmCoord (B := DualNumber O) x.1).snd) ≫ (gmVec O 1).1 :=
      gmCoord_ext (B := DualNumber O) (h0.trans (gmCoord_comp _ _).symm)
    have h : x = Pdiv.AvDefs.lieScale _ (gmCoord (B := DualNumber O) x.1).snd (gmVec O 1) := Subtype.ext h1
    exact (congrArg w.1 h).trans ((HTLat.omega_lieScale w _ _).trans (mul_comm _ _)))

theorem isOmega_muTower : (TorsionMap.ofTower (muTower p O)).IsOmega
    (LinearMap.toSpanSingleton O _ (dlogT p O) ∘ₗ LinearMap.proj (gmVec O 1) ∘ₗ (Pdiv.omega _).subtype) := fun n => by
  have h1 : (gmForm O).1 (gmVec O 1) = 1 := (congrArg TrivSqZeroExt.snd (gmCoord_gmVec O 1)).trans (by simp)
  refine ⟨fun v => ?_, fun w => (smul_dUnit_muT_eq_zero_iff p O n _).trans ⟨?_, ?_⟩, fun x w a ha => ?_⟩
  · obtain ⟨c, rfl⟩ := mu_cot_span p O n v
    exact ⟨c • gmForm O, congrArg (· • dUnit O (muT O (p ^ n))) ((congrArg (c * ·) h1).trans (_root_.mul_one c))⟩
  · rintro ⟨d, hd⟩
    exact ⟨d • gmForm O, (omega_gm_eq O w).trans ((congrArg (· • gmForm O) hd).trans (mul_smul _ _ _))⟩
  · rintro ⟨w', rfl⟩
    exact ⟨w'.1 (gmVec O 1), rfl⟩
  · rw [TorsionMap.ofTower_tanTors, ← TorsionTower.tanDer_d, ha]
    refine (map_smul ((muTower p O).tanDer _ n) (w.1 (gmVec O 1)) (dUnit O (muT O (p ^ n)))).trans ?_
    rw [TorsionTower.tanDer_d, ← gmCoord_muTower, TorsionTower.tanPt_y, gmCoord_comp, snd_epsTo, Algebra.smul_def, ← map_mul]
    exact congrArg _ (congrArg (fun w : Pdiv.omega (Gm (Sp O)) => w.1 x) (omega_gm_eq O w)).symm

example : ∃ θ : TorsionMap (Gm (Sp O)) (PDivGroup.mu p O), θ.IsOpenNearZero ∧ θ.IsIsoOver Set.univ ∧ ∃ c, θ.IsOmega c :=
  ⟨.ofTower (muTower p O), TorsionMap.ofTower_isOpenNearZero _, TorsionMap.ofTower_isIsoOver _ _, _, isOmega_muTower p O⟩

end Mult

end TorsionMap

section PropG

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {p : ℕ} [Fact p.Prime]
  {R : Type} [CommRing R]

abbrev tatePt {G : PDivGroup p R} (s : G.Tate) (n : ℕ) (B : Type) [CommRing B] [Algebra R B] : G.A n →ₐ[R] B :=
  (Algebra.ofId R B).comp (s.pt n)

structure IsPropG (t : SAB H (Sp R)) (GG : PDivGroup p R) (act : Action (𝓞 E) GG) (pol : GG ≅ GG.dual)
    (θ : TorsionMap t.G GG) (ε : (PDivGroup.mu p R).Tate) (τ : Dw.La →+ GG.Tate) : Prop where

  height : GG.height = 2 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))

  equivariant : ∀ a, θ.Intertwines (t.act.act a) (act a)

  interior : θ.IsIsoOver (abLocus t.G)

  nearZero : θ.IsOpenNearZero

  omega : ∃ c : Pdiv.omega t.G →ₗ[R] GG.omega, θ.IsOmega c ∧ ∀ (a : 𝓞 E) (w w' : Pdiv.omega t.G),
    (∀ x x' : Pdiv.LieG t.G, x'.1 = x.1 ≫ t.act.act a → w'.1 x = w.1 x') → c w' = omegaMap GG GG (act a) (c w)

  adj : ∀ a, (act a : GG ⟶ GG) ≫ pol.hom = pol.hom ≫ dualHom GG GG (act (H.bar a))

  skew : GG.bidual.hom ≫ dualHom GG GG.dual pol.hom = -pol.hom

  prim : ∀ n, IsPrimitiveRoot (muRoot ε n) (p ^ n)

  lin : ∀ (a : 𝓞 E) (x : Dw.La), τ (a • x) = tateMap GG GG R (act a) (τ x)

  pair : ∀ x y, pairing GG R (τ x) (tateMap GG GG.dual R pol.hom (τ y)) = ((Dw.EF x y : ℤ) : ℤ_[p]) • ε

  onto : ∀ (n : ℕ) (k : Type) [Field k] [Algebra R k], (p : k) ≠ 0 → ∀ φ : GG.A n →ₐ[R] k, ∃ x, tatePt (τ x) n k = φ

  weil : ∀ (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [Algebra R k], (p : k) ≠ 0 →
    Set.range (spMap (algebraMap R k)) ⊆ abLocus t.G → ∀ (x x' : Tors t.G (p ^ n) k) (y : Dw.La) (u : kˣ),
      θ.pt n k x' = tatePt (τ y) n k → (u : k) = θ.pt n k x (charElem (tateMap GG GG.dual R pol.hom (τ y)) n) →
        Out.WeilIs t.G t.PP.L ((p ^ n : ℕ) : ℤ) x.1 x'.1 (unitOn u)

variable {Dw}

def dualVec {J : Type} (b : Module.Basis J ℤ Dw.La) (j : J) : Dw.La := -(Dw.unimod.2 (b.coord j)).choose

theorem EF_dualVec {J : Type} (b : Module.Basis J ℤ Dw.La) (x : Dw.La) (j : J) : Dw.EF x (dualVec b j) = b.repr x j := by
  rw [dualVec, map_neg, LinearMap.IsAlt.neg Dw.alt, (Dw.unimod.2 (b.coord j)).choose_spec, Module.Basis.coord_apply]

namespace IsPropG

variable {t : SAB H (Sp R)} {GG : PDivGroup p R} {act : Action (𝓞 E) GG} {pol : GG ≅ GG.dual} {θ : TorsionMap t.G GG}
  {ε : (PDivGroup.mu p R).Tate} {τ : Dw.La →+ GG.Tate} (h : IsPropG Dw t GG act pol θ ε τ)

include h in

theorem nonempty_basis : Nonempty (Module.Basis (Fin GG.height) ℤ Dw.La) :=
  have k := Coisotropic.lattice_rank E H Dw
  haveI := k.1
  haveI := k.2.1
  ⟨Module.finBasisOfFinrankEq ℤ _ (k.2.2.trans h.height.symm)⟩

def constTate (b : Module.Basis (Fin GG.height) ℤ Dw.La) : ConstTate ε GG where
  t i := τ (b i)
  t' j := tateMap GG GG.dual R pol.hom (τ (dualVec b j))
  pair i j := by
    rw [h.pair, EF_dualVec, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem toTate_repr (b : Module.Basis (Fin GG.height) ℤ Dw.La) (x : Dw.La) :
    (h.constTate b).toTate (fun i => (b.repr x i : ℤ_[p])) = τ x := by
  conv_rhs => rw [← b.sum_repr x, map_sum]
  simp only [ConstTate.toTate, Fintype.linearCombination_apply, map_zsmul, Int.cast_smul_eq_zsmul]
  rfl

theorem stable (b : Module.Basis (Fin GG.height) ℤ Dw.La) (a : 𝓞 E) :
    (h.constTate b).Stable (act a) (Matrix.of fun k i => (b.repr (a • b i) k : ℤ_[p])) := fun i =>
  (h.lin a (b i)).symm.trans ((h.toTate_repr b _).symm.trans (Fintype.linearCombination_apply ..))

include h in

theorem exists_constTate : ∃ c : ConstTate ε GG, ∀ a, ∃ ρ, c.Stable (act a) ρ :=
  h.nonempty_basis.elim fun b => ⟨h.constTate b, fun a => ⟨_, h.stable b a⟩⟩

include h in

theorem weil_lattice (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [Algebra R k] (hp : (p : k) ≠ 0)
    (hk : Set.range (spMap (algebraMap R k)) ⊆ abLocus t.G) (z z' : Tors t.G (p ^ n) k) (x y : Dw.La) (u : kˣ)
    (hz : θ.pt n k z = tatePt (τ x) n k) (hz' : θ.pt n k z' = tatePt (τ y) n k)
    (hu : (u : k) = algebraMap R k (muRoot (((Dw.EF x y : ℤ) : ℤ_[p]) • ε) n)) :
    Out.WeilIs t.G t.PP.L ((p ^ n : ℕ) : ℤ) z.1 z'.1 (unitOn u) :=
  h.weil n k hp hk z z' y u hz' (by rw [hu, ← h.pair, muRoot_pairing, hz]; rfl)

include h in

theorem exists_completion (K : Type) [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]
    [IsFractionRing R K] (hp : ¬ IsUnit (p : R)) :
    ∃ (S : GlobalTheory.Published.CycPerfd p) (e : AdicCompletion (Ideal.span {(p : R)}) R ≃+* S.R),
      letI := (e.toRingHom.comp (algebraMap R _)).toAlgebra
      (∀ n, muRoot (eps S) n = algebraMap R S.R (muRoot ε n)) ∧ Nonempty (ConstTate (eps S) (GG.baseChange S.R)) := by
  obtain ⟨S, e, he⟩ := GlobalTheory.PerfdCompletion.exists_cycPerfd p R K hp _ h.prim (muRoot_succ_pow ε)
  letI := (e.toRingHom.comp (algebraMap R _)).toAlgebra
  have k : ∀ n, muRoot (eps S) n = algebraMap R S.R (muRoot ε n) := fun n => (muRoot_eps S n).trans (he n)
  exact ⟨S, e, k, h.exists_constTate.elim fun c _ => ⟨c.baseChange S.R k⟩⟩

end IsPropG

def IsRestr {R' : Type} [CommRing R'] [Algebra R R'] {T : Scheme.{0}}
    {t : SAB H (Sp R)} (φ : t.G.left ⟶ T) {GG : PDivGroup p R} (act : Action (𝓞 E) GG) (pol : GG ≅ GG.dual)
    (θ : TorsionMap t.G GG) (ε : (PDivGroup.mu p R).Tate) (τ : Dw.La →+ GG.Tate)
    {t' : SAB H (Sp R')} (φ' : t'.G.left ⟶ T) {GG' : PDivGroup p R'} (act' : Action (𝓞 E) GG') (pol' : GG' ≅ GG'.dual)
    (θ' : TorsionMap t'.G GG') (ε' : (PDivGroup.mu p R').Tate) (τ' : Dw.La →+ GG'.Tate) : Prop :=
  (∀ n, muRoot ε' n = algebraMap R R' (muRoot ε n)) ∧ ∃ e : GG' ≅ GG.baseChange R',
    (∀ a, (act' a : GG' ⟶ GG') ≫ e.hom = e.hom ≫ PDivGroup.baseChangeMap R' (act a : GG ⟶ GG)) ∧
    pol'.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange R' GG).hom = e.hom ≫ PDivGroup.baseChangeMap R' pol.hom ∧
    (∀ x, tateMap _ _ R' e.hom (τ' x) = bcTate R' (τ x)) ∧
    ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] [Algebra R' B] [IsScalarTower R R' B]
      (z : Tors t.G (p ^ n) B) (z' : Tors t'.G (p ^ n) B), z.1.left ≫ φ = z'.1.left ≫ φ' →
        ∀ a, θ.pt n B z a = θ'.pt n B z' (e.hom.app n (1 ⊗ₜ a))

variable (Dw p) in

def PropGOn {X Z : Scheme.{0}} [IsIntegral X] (g : X ⟶ Z) (tZ : SAB H Z) : Prop :=
  ∀ (t : ∀ U : AffOp X, SAB H (Sp U.Bp)) (m : ∀ U, SABMap (t U) tZ (U.toX ≫ g)),
    ∃ (GG : ∀ U : AffOp X, PDivGroup p U.Bp) (act : ∀ U, Action (𝓞 E) (GG U)) (pol : ∀ U, GG U ≅ (GG U).dual)
      (θ : ∀ U, TorsionMap (t U).G (GG U)) (ε : ∀ U : AffOp X, (PDivGroup.mu p U.Bp).Tate) (τ : ∀ U, Dw.La →+ (GG U).Tate),
      (∀ U, IsPropG Dw (t U) (GG U) (act U) (pol U) (θ U) (ε U) (τ U)) ∧
      ∀ (U U' : AffOp X) (h : U'.1 ≤ U.1), letI := (AffOp.res h).toAlgebra
        IsRestr (m U).φ (act U) (pol U) (θ U) (ε U) (τ U) (m U').φ (act U') (pol U') (θ U') (ε U') (τ U')

theorem exists_pullbacks {X Z : Scheme.{0}} [IsIntegral X] (g : X ⟶ Z) (tZ : SAB H Z) :
    ∃ t : ∀ U : AffOp X, SAB H (Sp U.Bp), Nonempty (∀ U, SABMap (t U) tZ (U.toX ≫ g)) :=
  ⟨fun U => (exists_sab (U.toX ≫ g) tZ).choose, ⟨fun U => (exists_sab (U.toX ≫ g) tZ).choose_spec.some⟩⟩

variable (Dw) in

def IsOfType {k : Type} [Field k] (t : SAB H (Sp k)) : Prop :=
  IsProper t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧
    Nonempty (TateIso Dw k (Over.mk (𝟙 (Sp k)) ⟶ t.G) (fun a g => g ≫ t.act.act a)
      fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))

theorem isOfType_obj {l : Level H} {B k : Type} [CommRing B] [Field k] [IsAlgClosed k] {b : Base l B} (β : B →+* k)
    (o : Obj Dw l b (spMap β)) : IsOfType Dw o.t :=
  ⟨o.proper, o.ample, o.ktriv, (o.geom k (𝟙 _) β (Category.id_comp _)).2.elim fun I _ => ⟨I⟩⟩

theorem IsOfType.charZero {k : Type} [Field k] {t : SAB H (Sp k)} (h : IsOfType Dw t) : CharZero k :=
  h.2.2.2.elim fun I => charZero_of_inj_zero fun n hn => by
    by_contra h0
    haveI : NeZero n := ⟨h0⟩
    exact ((IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim n (Nat.pos_of_ne_zero h0))).neZero'.out hn)

variable (Dw) in

def GenericType {X Z : Scheme.{0}} [IsIntegral X] (g : X ⟶ Z) (tZ : SAB H Z) : Prop :=
  ∃ t₀ : SAB H (Sp (Kbar X)), Nonempty (SABMap t₀ tZ (genPt X ≫ g)) ∧ IsOfType Dw t₀

theorem genericType_of_obj {X Z : Scheme.{0}} [IsIntegral X] {g : X ⟶ Z} {tZ : SAB H Z} {l : Level H} {B : Type} [CommRing B]
    {b : Base l B} (β : B →+* Kbar X) (o : Obj Dw l b (spMap β)) (m : SABMap o.t tZ (genPt X ≫ g)) : GenericType Dw g tZ :=
  ⟨o.t, ⟨m⟩, isOfType_obj β o⟩

end PropG

section Levels

open GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ}

def IsLevelTower (Y : LocalSystem Xo p W) (i₀ : Idx H p) {S : Scheme.{0}} (y₀ : S ⟶ (Y i₀).X) (i : ℕ → Idx H p)
    (y : ∀ n, S ⟶ (Y (i n)).X) : Prop :=
  (∀ n, IsLvl i₀ (i n) (some n)) ∧
  (∃ τ mu, IsTrans (Y := Y) i₀ (i 0) τ mu ∧ y 0 ≫ τ = y₀) ∧
  (∀ n, ∃ τ mu, IsTrans (Y := Y) (i n) (i (n + 1)) τ mu ∧ y (n + 1) ≫ τ = y n) ∧
  ∀ (n : ℕ) (x : S), (∀ x' : S, x' ⤳ x → x' = x) → y n x ∈ Set.range (Y (i n)).j

def HasLevelTowers (Y : LocalSystem Xo p W) (i₀ : Idx H p) {R : Type} [CommRing R] (y₀ : Sp R ⟶ (Y i₀).X) : Prop :=
  ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧ ∀ r ∈ s, ∃ i y,
    IsLevelTower Y i₀ (spMap (algebraMap R (Localization.Away r)) ≫ y₀) i y

theorem IsLevelTower.zero_eq {Y : LocalSystem Xo p W} {i₀ : Idx H p} {S : Scheme.{0}} {y₀ : S ⟶ (Y i₀).X} {i : ℕ → Idx H p}
    {y : ∀ n, S ⟶ (Y (i n)).X} (h : IsLevelTower Y i₀ y₀ i y) : (i 0).l.A = i₀.l.A ∧ (i 0).l.M' = i₀.l.M' ∧ (i 0).c.F = i₀.c.F := by
  obtain ⟨h1, -, h2, h3⟩ := h.1 0
  rw [pow_zero, _root_.mul_one] at h2
  have h4 : (i 0).l.M' = i₀.l.M' := by rw [Level.M', Level.M', h1, h2]
  refine ⟨h2, h4, h3.trans (sup_eq_left.2 ?_)⟩
  rw [h4, IntermediateField.adjoin_simple_le_iff]
  exact i₀.c.zeta_mem

end Levels

section Statements

open GlobalTheory.MixedLocalChains GlobalTheory.ShFam.Pad

def GroupSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime]
    (X Z : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (g : X ⟶ Z) (tZ : SAB H Z),
    GlobalTheory.IsNormalScheme X → GenericType Dw g tZ → PropGOn Dw p g tZ

def GroupAt {D : Formalism.BasicNotions.D7} {A : GlobalTheory.ShFam.Amb D} {N j : ℕ} {S : GlobalTheory.ShFam.Sig A N j} {κ : GlobalTheory.ShFam.Lv A} {p : ℕ}
    [Fact p.Prime] {hp : p.Prime} {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  ∀ (c : (nmodel z.Z).Comp) (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c)),
    GlobalTheory.IsNormalScheme B.X → f.relDim = 0 → PropGOn S.Dw p (f.f ≫ (nmodel z.Z).compι c) z.Z.t

def GenericAt {D : Formalism.BasicNotions.D7} {A : GlobalTheory.ShFam.Amb D} {N j : ℕ} {S : GlobalTheory.ShFam.Sig A N j} {κ : GlobalTheory.ShFam.Lv A} {p : ℕ}
    {hp : p.Prime} {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  ∀ (c : (nmodel z.Z).Comp) (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c)),
    GenericType S.Dw (f.f ≫ (nmodel z.Z).compι c) z.Z.t

def GroupAllSt : Prop := GlobalTheory.BundleChernComparison.AtAll fun _ _ _ _ _ _ _ z => GroupAt z

def GroupGoodSt : Prop := AtGood fun _ _ _ _ _ _ _ z => GroupAt z

def GenericSt : Prop := GlobalTheory.BundleChernComparison.AtAll fun _ _ _ _ _ _ _ z => GenericAt z

theorem GroupSt.all (h : GroupSt) (hg : GenericSt) : GroupAllSt := fun D O hO p _ W hW jc hj z c B f hB _ =>
  haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
  h _ _ _ p _ _ _ _ hB (hg D O hO p W hW jc hj z c B f)

theorem GroupAllSt.good (h : GroupAllSt) : GroupGoodSt := fun D O hO p _ _ _ _ W hW jc hj z => h D O hO p W hW jc hj z

def LevelSt : Prop := AtGood fun _ O p _ W hW _ z =>
  haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
  ∀ (c : (nmodel z.Z).Comp) (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c)),
    GlobalTheory.IsNormalScheme B.X → f.relDim = 0 → ∀ U : AffOp B.X,
      HasLevelTowers (O.S.sys.Y p W Fact.out hW) z.Z.i (U.toX ≫ f.f ≫ (nmodel z.Z).compι c ≫ z.Z.π)

end Statements

end GlobalTheory.GroupBplus

end
