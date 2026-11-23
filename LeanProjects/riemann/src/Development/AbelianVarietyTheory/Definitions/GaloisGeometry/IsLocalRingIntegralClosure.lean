import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsContinuousForgetForget
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullPreservesFiniteLimits
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PullHXApply

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite IsLocalRing

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section Ring

theorem isLocalRing_integralClosure (O Ω : Type) [CommRing O] [HenselianLocalRing O] [Field Ω] [Algebra O Ω] :
    IsLocalRing (integralClosure O Ω) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  let S := Algebra.adjoin O {(x : Ω)}
  haveI : Module.Finite O S := Module.Finite.iff_fg.2 (IsIntegral.fg_adjoin_singleton x.2)
  haveI : IsLocalRing S := by
    obtain ⟨q, hq⟩ := Ideal.exists_maximal S
    have e : S ≃+* Localization.AtPrime q := RingEquiv.ofBijective (algebraMap _ _)
      ⟨IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors,
        GlobalTheory.surjective_algebraMap_localization_of_henselian O q⟩
    exact e.symm.isLocalRing
  have hle : S ≤ (integralClosure O Ω) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 x.2)
  let f : S →+* integralClosure O Ω := (Subalgebra.inclusion hle).toRingHom
  have hx : f ⟨x, Algebra.self_mem_adjoin_singleton O _⟩ = x := rfl
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨x, Algebra.self_mem_adjoin_singleton O _⟩ : S) with h | h
  · left; simpa [hx] using h.map f
  · right; simpa [hx] using h.map f

variable (O : Type) [CommRing O] [HenselianLocalRing O] (K : Type) [Field K] [Algebra O K]
  (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]

instance : IsLocalRing (integralClosure O Ω) := isLocalRing_integralClosure O Ω

variable {Ω}

def galInt (σ : Ω ≃ₐ[K] Ω) : integralClosure O Ω ≃+* integralClosure O Ω where
  toFun x := ⟨σ x, x.2.map ((σ.restrictScalars O : Ω ≃ₐ[O] Ω) : Ω →ₐ[O] Ω)⟩
  invFun x := ⟨σ.symm x, x.2.map ((σ.symm.restrictScalars O : Ω ≃ₐ[O] Ω) : Ω →ₐ[O] Ω)⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x.1)
  right_inv x := Subtype.ext (σ.apply_symm_apply x.1)
  map_mul' x y := Subtype.ext (map_mul σ x.1 y.1)
  map_add' x y := Subtype.ext (map_add σ x.1 y.1)

variable {O K}

@[simp] theorem galInt_apply (σ : Ω ≃ₐ[K] Ω) (x : integralClosure O Ω) : ((galInt O K σ x : integralClosure O Ω) : Ω) = σ x := rfl

theorem galInt_algebraMap (σ : Ω ≃ₐ[K] Ω) (r : O) :
    galInt O K σ (algebraMap O (integralClosure O Ω) r) = algebraMap O (integralClosure O Ω) r := by
  apply Subtype.ext
  change σ (algebraMap O Ω r) = algebraMap O Ω r
  rw [IsScalarTower.algebraMap_apply O K Ω, σ.commutes]

theorem galInt_mul (σ τ : Ω ≃ₐ[K] Ω) (x : integralClosure O Ω) : galInt O K (σ * τ) x = galInt O K σ (galInt O K τ x) := rfl

theorem galInt_one (x : integralClosure O Ω) : galInt O K (1 : Ω ≃ₐ[K] Ω) x = x := rfl

def galRes (σ : Ω ≃ₐ[K] Ω) : ResidueField (integralClosure O Ω) ≃+* ResidueField (integralClosure O Ω) :=
  ResidueField.mapEquiv (galInt O K σ)

theorem galRes_residue (σ : Ω ≃ₐ[K] Ω) (x : integralClosure O Ω) :
    galRes σ (residue _ x) = residue _ (galInt O K σ x) := rfl

variable (O K Ω)

def inertia : Subgroup (Ω ≃ₐ[K] Ω) where
  carrier := {σ | ∀ x : integralClosure O Ω, residue _ (galInt O K σ x) = residue _ x}
  mul_mem' {σ τ} hσ hτ x := (hσ _).trans (hτ x)
  one_mem' x := rfl
  inv_mem' {σ} hσ x := by
    have h := hσ (galInt O K σ⁻¹ x)
    rw [← galInt_mul, mul_inv_cancel, galInt_one] at h
    exact h.symm

end Ring
end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section Schemes

variable {O : Type} [CommRing O] [HenselianLocalRing O] (K : Type) [Field K] [Algebra O K]
  (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]
  {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O))

abbrev intFib : Scheme.{0} := GlobalTheory.Et.fibre p (algebraMap O (integralClosure O Ω))

abbrev intStr : intFib Ω p ⟶ Spec (CommRingCat.of (integralClosure O Ω)) := pullback.snd _ _

abbrev spFib : Scheme.{0} :=
  pullback (intStr Ω p) (Spec.map (CommRingCat.ofHom (residue (integralClosure O Ω))))

abbrev iSp : spFib Ω p ⟶ intFib Ω p := pullback.fst _ _

abbrev genStr : GlobalTheory.Et.fibre p (algebraMap O K) ⟶ Spec (CommRingCat.of K) := pullback.snd _ _

abbrev genFib : Scheme.{0} := GlobalTheory.Et.geom Ω (genStr K p)

theorem ringHom_tower :
    CommRingCat.ofHom (algebraMap O K) ≫ CommRingCat.ofHom (algebraMap K Ω) =
      CommRingCat.ofHom (algebraMap O (integralClosure O Ω)) ≫ CommRingCat.ofHom (integralClosure O Ω).val.toRingHom := by
  ext r
  change algebraMap K Ω (algebraMap O K r) = algebraMap O Ω r
  rw [← IsScalarTower.algebraMap_apply]

def jGen : genFib K Ω p ⟶ intFib Ω p :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (integralClosure O Ω).val.toRingHom)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ringHom_tower])

@[reassoc] theorem jGen_fst : jGen K Ω p ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc] theorem jGen_snd : jGen K Ω p ≫ intStr Ω p =
    pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (integralClosure O Ω).val.toRingHom) := pullback.lift_snd _ _ _

variable {K Ω}

def galIntMap (σ : Ω ≃ₐ[K] Ω) : intFib Ω p ⟶ intFib Ω p :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (galInt O K σ).toRingHom)) (by
    rw [pullback.condition, Category.assoc, ← Spec.map_comp]
    congr 3
    ext r
    exact congrArg Subtype.val (galInt_algebraMap σ r).symm)

@[reassoc] theorem galIntMap_fst (σ : Ω ≃ₐ[K] Ω) : galIntMap p σ ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc] theorem galIntMap_snd (σ : Ω ≃ₐ[K] Ω) :
    galIntMap p σ ≫ intStr Ω p = intStr Ω p ≫ Spec.map (CommRingCat.ofHom (galInt O K σ).toRingHom) :=
  pullback.lift_snd _ _ _

def galSpMap (σ : Ω ≃ₐ[K] Ω) : spFib Ω p ⟶ spFib Ω p :=
  pullback.lift (iSp Ω p ≫ galIntMap p σ) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (galRes σ).toRingHom)) (by
    have e : CommRingCat.ofHom (galInt O K σ).toRingHom ≫ CommRingCat.ofHom (residue (integralClosure O Ω)) =
        CommRingCat.ofHom (residue (integralClosure O Ω)) ≫ CommRingCat.ofHom (galRes σ).toRingHom := by
      ext x; rfl
    rw [Category.assoc, galIntMap_snd, pullback.condition_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, e])

@[reassoc] theorem galSpMap_i (σ : Ω ≃ₐ[K] Ω) : galSpMap p σ ≫ iSp Ω p = iSp Ω p ≫ galIntMap p σ :=
  pullback.lift_fst _ _ _

theorem galGen_j (σ : Ω ≃ₐ[K] Ω) : GlobalTheory.Et.galMap Ω (genStr K p) σ ≫ jGen K Ω p = jGen K Ω p ≫ galIntMap p σ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, galIntMap_fst, jGen_fst, GlobalTheory.Et.galMap_fst_assoc]
  · have e : CommRingCat.ofHom (integralClosure O Ω).val.toRingHom ≫ CommRingCat.ofHom (σ : Ω →+* Ω) =
        CommRingCat.ofHom (galInt O K σ).toRingHom ≫ CommRingCat.ofHom (integralClosure O Ω).val.toRingHom := by
      ext x; rfl
    rw [Category.assoc, Category.assoc, galIntMap_snd, jGen_snd, jGen_snd_assoc, GlobalTheory.Et.galMap_snd_assoc,
      ← Spec.map_comp, ← Spec.map_comp, e]

theorem iSp_galIntMap {σ : Ω ≃ₐ[K] Ω} (hσ : σ ∈ inertia O K Ω) : iSp Ω p ≫ galIntMap p σ = iSp Ω p := by
  apply pullback.hom_ext
  · rw [Category.assoc, galIntMap_fst]
  · rw [Category.assoc, galIntMap_snd, pullback.condition_assoc, pullback.condition, ← Spec.map_comp]
    congr 3
    ext x
    exact hσ x

end Schemes
end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section Nearby

variable (R : Type) [CommRing R]
variable {O : Type} [CommRing O] [HenselianLocalRing O] (K : Type) [Field K] [Algebra O K]
  (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]
  {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O))

def RPsiC (F : Shv R) : CochainComplex (ShvS R (spFib Ω p)) ℤ := nbC R (iSp Ω p) (jGen K Ω p) F

def RPsi (F : Shv R) : DerivedCategory (ShvS R (spFib Ω p)) := DerivedCategory.Q.obj (RPsiC R K Ω p F)

def RPsiStd (F : Shv R) : DerivedCategory (ShvS R (spFib Ω p)) :=
  (Rel.pull R (iSp Ω p)).mapDerivedCategory.obj (DerivedCategory.Plus.ι.obj
    ((Rpush R (jGen K Ω p)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj ((Rel.res R _).obj F))))

def RqPsi (q : ℤ) (F : Shv R) : ShvS R (spFib Ω p) := (RPsiC R K Ω p F).homology q

def stalkPsi (q : ℤ) (F : Shv R) {Ω' : Type} [Field Ω'] [IsSepClosed Ω'] (s : Spec (CommRingCat.of Ω') ⟶ spFib Ω p) :
    ModuleCat.{1} (ULift.{1} R) :=
  (Scheme.pointSmallEtale s).sheafFiber.obj (RqPsi R K Ω p q F)

abbrev HPsi (F : Shv R) (n : ℤ) : Type _ := HXC R (spFib Ω p) (RPsiC R K Ω p F) n

variable {K Ω}

def galC (F : Shv R) (σ : Ω ≃ₐ[K] Ω) : (pullC R (galSpMap p σ)).obj (RPsiC R K Ω p F) ⟶ RPsiC R K Ω p F :=
  transC R (bcSq (galSpMap_i p σ)).hom (galGen_j p σ) F

def galPushC (F : Shv R) (σ : Ω ≃ₐ[K] Ω) :
    RPsiC R K Ω p F ⟶ (((bc (galSpMap p σ)).sheafPushforwardContinuous _ _ _).mapHomologicalComplex _).obj
      (RPsiC R K Ω p F) :=
  (NatTrans.mapHomologicalComplex (trans R (bcSq (galSpMap_i p σ)).hom (galGen_j p σ)) _).app (GlobalTheory.EtC.res R F)

def ineNat {σ : Ω ≃ₐ[K] Ω} (hσ : σ ∈ inertia O K Ω) :
    nb R (iSp Ω p) (jGen K Ω p) ⟶ nb R (iSp Ω p) (jGen K Ω p) :=
  trans R (A := 𝟭 _) (bcComp (iSp_galIntMap p hσ)).inv (galGen_j p σ) ≫
    Functor.whiskerLeft _ (Functor.sheafPushforwardContinuousId _ _).hom

def ineC (F : Shv R) {σ : Ω ≃ₐ[K] Ω} (hσ : σ ∈ inertia O K Ω) : RPsiC R K Ω p F ⟶ RPsiC R K Ω p F :=
  (NatTrans.mapHomologicalComplex (ineNat R p hσ) _).app (GlobalTheory.EtC.res R F)

def ineRq (q : ℤ) (F : Shv R) {σ : Ω ≃ₐ[K] Ω} (hσ : σ ∈ inertia O K Ω) : RqPsi R K Ω p q F ⟶ RqPsi R K Ω p q F :=
  HomologicalComplex.homologyMap (ineC R p F hσ) q

def ineStalk (q : ℤ) (F : Shv R) {σ : Ω ≃ₐ[K] Ω} (hσ : σ ∈ inertia O K Ω) {Ω' : Type} [Field Ω'] [IsSepClosed Ω']
    (s : Spec (CommRingCat.of Ω') ⟶ spFib Ω p) : stalkPsi R K Ω p q F s ⟶ stalkPsi R K Ω p q F s :=
  (Scheme.pointSmallEtale s).sheafFiber.map (ineRq R p q F hσ)

def galH (F : Shv R) (n : ℤ) (σ : Ω ≃ₐ[K] Ω) : HPsi R K Ω p F n →+ HPsi R K Ω p F n :=
  (postHX R (DerivedCategory.Q.map (galC R p F σ)) n).comp (pullHXC R (galSpMap p σ) (RPsiC R K Ω p F) n)

def ineH (F : Shv R) (n : ℤ) {σ : Ω ≃ₐ[K] Ω} (hσ : σ ∈ inertia O K Ω) : HPsi R K Ω p F n →+ HPsi R K Ω p F n :=
  postHX R (DerivedCategory.Q.map (ineC R p F hσ)) n

end Nearby
end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section Adic

variable (l : ℕ) [Fact l.Prime]

abbrev liftMod (k : ℕ) : Module (ULift.{1} ℤ_[l]) (ULift.{1} (ZMod (l ^ k))) :=
  Module.compHom _ ((ULift.ringEquiv.symm : ZMod (l ^ k) ≃+* ULift.{1} (ZMod (l ^ k))).toRingHom.comp
    ((PadicInt.toZModPow k).comp (ULift.ringEquiv : ULift.{1} ℤ_[l] ≃+* ℤ_[l]).toRingHom))

def lamObj (k : ℕ) : ModuleCat.{1} (ULift.{1} ℤ_[l]) := @ModuleCat.of _ _ (ULift.{1} (ZMod (l ^ k))) _ (liftMod l k)

def lam (k : ℕ) : Shv ℤ_[l] := ofRings ℤ_[l] ((Functor.const _).obj (lamObj l k))

def lamRedLin (k : ℕ) : lamObj l (k + 1) ⟶ lamObj l k :=
  letI := liftMod l (k + 1); letI := liftMod l k
  ModuleCat.ofHom
    { toFun := fun x => (⟨ZMod.castHom (pow_dvd_pow l (Nat.le_succ k)) (ZMod (l ^ k)) x.down⟩ : ULift.{1} (ZMod (l ^ k)))
      map_add' := fun x y => congrArg ULift.up (map_add _ x.down y.down)
      map_smul' := fun r x => by
        apply congrArg ULift.up
        change ZMod.castHom _ (ZMod (l ^ k)) (PadicInt.toZModPow (k + 1) r.down * x.down) =
          PadicInt.toZModPow k r.down * ZMod.castHom _ (ZMod (l ^ k)) x.down
        rw [map_mul]
        congr 1
        exact PadicInt.cast_toZModPow k (k + 1) (Nat.le_succ k) r.down }

def lamRed (k : ℕ) : lam l (k + 1) ⟶ lam l k :=
  (presheafToSheaf _ _).map (Functor.whiskerLeft Scheme.Γ ((Functor.const _).map (lamRedLin l k)))

instance (X : Scheme.{0}) (L : DerivedCategory (ShvS ℤ_[l] X)) (n : ℤ) : Module ℤ_[l] (HX ℤ_[l] X L n) :=
  Module.compHom _ (ULift.ringEquiv.symm : ℤ_[l] ≃+* ULift.{1} ℤ_[l]).toRingHom

variable {O : Type} [CommRing O] [HenselianLocalRing O] (K : Type) [Field K] [Algebra O K]
  (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]
  {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O))

def redPsi (n : ℤ) (k : ℕ) : HPsi ℤ_[l] K Ω p (lam l (k + 1)) n →ₗ[ℤ_[l]] HPsi ℤ_[l] K Ω p (lam l k) n where
  toFun x := x ≫ (DerivedCategory.Q.map (nbCMap ℤ_[l] (iSp Ω p) (jGen K Ω p) (lamRed l k)))⟦n⟧'
  map_add' x y := Preadditive.add_comp _ _ _ _ _ _
  map_smul' r x := Linear.smul_comp (R := ULift.{1} ℤ_[l]) _ _ _ (ULift.up r) x _

def HPsiLSub (n : ℤ) : Submodule ℤ_[l] (∀ k, HPsi ℤ_[l] K Ω p (lam l k) n) where
  carrier := {x | ∀ k, redPsi l K Ω p n k (x (k + 1)) = x k}
  zero_mem' k := map_zero _
  add_mem' {a b} ha hb k := (map_add (redPsi l K Ω p n k) _ _).trans (congrArg₂ (· + ·) (ha k) (hb k))
  smul_mem' r x hx k := (map_smul (redPsi l K Ω p n k) r _).trans (congrArg _ (hx k))

abbrev HPsiL (n : ℤ) : Type _ := HPsiLSub l K Ω p n

abbrev HPsiQ (n : ℤ) : Type _ := TensorProduct ℤ_[l] ℚ_[l] (HPsiL l K Ω p n)

end Adic
end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section AdicGal

variable (R : Type) [CommRing R]
variable {O : Type} [CommRing O] [HenselianLocalRing O] {K : Type} [Field K] [Algebra O K]
  {Ω : Type} [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]
  {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O))

theorem galC_natural {F G : Shv R} (φ : F ⟶ G) (σ : Ω ≃ₐ[K] Ω) :
    (pullC R (galSpMap p σ)).map (nbCMap R (iSp Ω p) (jGen K Ω p) φ) ≫ galC R p G σ =
      galC R p F σ ≫ nbCMap R (iSp Ω p) (jGen K Ω p) φ :=
  (NatTrans.mapHomologicalComplex (transFlat R (bcSq (galSpMap_i p σ)).hom (galGen_j p σ)) _).naturality
    (resMap R φ)

def galHFam (l : ℕ) [Fact l.Prime] (n : ℤ) (σ : Ω ≃ₐ[K] Ω) :
    HPsiL l K Ω p n →+ (∀ k, HPsi ℤ_[l] K Ω p (lam l k) n) where
  toFun x k := galH ℤ_[l] p (lam l k) n σ (x.1 k)
  map_zero' := funext fun k => map_zero (galH ℤ_[l] p (lam l k) n σ)
  map_add' x y := funext fun k => map_add (galH ℤ_[l] p (lam l k) n σ) (x.1 k) (y.1 k)

end AdicGal
end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section Examples

variable (R : Type) [CommRing R] (O : Type) [CommRing O] [HenselianLocalRing O] (K : Type) [Field K] [Algebra O K]
  (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]

example : DerivedCategory (ShvS R (spFib Ω (𝟙 (Spec (CommRingCat.of O))))) :=
  RPsi R K Ω (𝟙 (Spec (CommRingCat.of O))) (coef R)

example (n : ℤ) : AddCommGroup (HPsi R K Ω (𝟙 (Spec (CommRingCat.of O))) (coef R) n) := inferInstance

example {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) (F : Shv R) :
    RPsiC R K Ω p F ⟶ RPsiC R K Ω p F :=
  ineC R p F (one_mem (inertia O K Ω))

example (σ : Ω ≃ₐ[K] Ω) (r : O) :
    galInt O K σ (algebraMap O (integralClosure O Ω) r) = algebraMap O (integralClosure O Ω) r :=
  galInt_algebraMap σ r

example (x : integralClosure O Ω) : galInt O K (1 : Ω ≃ₐ[K] Ω) x = x := rfl

example : Field (ResidueField (integralClosure O Ω)) := inferInstance

example (n : ℤ) : Module ℚ_[3] (HPsiQ 3 K Ω (𝟙 (Spec (CommRingCat.of O))) n) := inferInstance

example : (lamRedLin 3 1).hom (⟨1⟩ : ULift.{1} (ZMod (3 ^ 2))) = (⟨1⟩ : ULift.{1} (ZMod (3 ^ 1))) := by
  apply congrArg ULift.up
  exact map_one _

end Examples

example : Subgroup (AlgebraicClosure ℚ_[3] ≃ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3]) × Type 2 :=
  haveI : HenselianLocalRing ℤ_[3] := GlobalTheory.henselianLocalRing_of_henselianRing ℤ_[3]
  (inertia ℤ_[3] ℚ_[3] (AlgebraicClosure ℚ_[3]),
    HPsi ℤ_[3] ℚ_[3] (AlgebraicClosure ℚ_[3]) (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (lam 3 1) 0)

end GlobalTheory.EtC.Psi
