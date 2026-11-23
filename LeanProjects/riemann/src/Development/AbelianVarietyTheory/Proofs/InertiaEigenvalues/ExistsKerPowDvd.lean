import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstantCoeffMapEqZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueIsEval
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.BKReal GlobalTheory.Prism IsLocalRing Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.DiscEval
open GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per TensorProduct

namespace GlobalTheory.AcrisK

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

variable (l) in

abbrev aC : Ainf l →+* Per.Acris l := algebraMap (Per.Ainf l) (Per.Acris l)

scoped instance algWC : Algebra (W0 K) (Per.Acris l) := ((aC l).comp (wA l (fK K)).toRingHom).toAlgebra

def CK : Type := Per.Acris l ⊗[W0 K] ↥(OL K)

instance : CommRing (CK K) := inferInstanceAs (CommRing (Per.Acris l ⊗[W0 K] ↥(OL K)))

instance : Algebra (Per.Acris l) (CK K) :=
  inferInstanceAs (Algebra (Per.Acris l) (Per.Acris l ⊗[W0 K] ↥(OL K)))

instance : Algebra ↥(OL K) (CK K) :=
  (Algebra.TensorProduct.includeRight : ↥(OL K) →ₐ[W0 K] Per.Acris l ⊗[W0 K] ↥(OL K)).toRingHom.toAlgebra

instance : Module.Free (Per.Acris l) (CK K) :=
  inferInstanceAs (Module.Free (Per.Acris l) (Per.Acris l ⊗[W0 K] ↥(OL K)))

instance : Module.Finite (Per.Acris l) (CK K) :=
  inferInstanceAs (Module.Finite (Per.Acris l) (Per.Acris l ⊗[W0 K] ↥(OL K)))

abbrev inC : Per.Acris l →+* CK K := algebraMap (Per.Acris l) (CK K)

abbrev inI : ↥(OL K) →+* CK K := algebraMap ↥(OL K) (CK K)

theorem tmul_eq (a : Per.Acris l) (c : ↥(OL K)) : (show CK K from a ⊗ₜ[W0 K] c) = inC K a * inI K c := by
  change a ⊗ₜ[W0 K] c = (a ⊗ₜ[W0 K] (1 : ↥(OL K))) * ((1 : Per.Acris l) ⊗ₜ[W0 K] c)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem inC_wA (w : W0 K) : inC K (aC l (wA l (fK K) w)) = inI K (thetaW (fK K) K w) :=
  ((Algebra.TensorProduct.includeRight : ↥(OL K) →ₐ[W0 K] Per.Acris l ⊗[W0 K] ↥(OL K)).commutes w).symm

variable {K} in

@[elab_as_elim] theorem induction_on {p : CK K → Prop} (x : CK K) (mul : ∀ a c, p (inC K a * inI K c))
    (add : ∀ x y, p x → p y → p (x + y)) : p x :=
  TensorProduct.induction_on (motive := p) x (by
    have := mul 0 0; rwa [map_zero, zero_mul] at this) (fun a c => by
    have := mul a c; rwa [← tmul_eq] at this) add

variable {K} in

theorem ringHom_ext {S : Type*} [CommRing S] {u v : CK K →+* S} (hA : ∀ a, u (inC K a) = v (inC K a))
    (hO : ∀ c, u (inI K c) = v (inI K c)) : u = v :=
  RingHom.ext fun x => induction_on x (fun a c => by rw [map_mul, map_mul, hA, hO])
    fun x y hx hy => by rw [map_add, map_add, hx, hy]

section Lift

variable {K} {S : Type*} [CommRing S] (u : Per.Acris l →+* S) (v : ↥(OL K) →+* S)
  (h : ∀ w : W0 K, u (aC l (wA l (fK K) w)) = v (thetaW (fK K) K w))

def lift : CK K →+* S :=
  letI : Algebra (W0 K) S := (u.comp ((aC l).comp (wA l (fK K)).toRingHom)).toAlgebra
  (Algebra.TensorProduct.productMap (R := W0 K) { toRingHom := u, commutes' := fun _ => rfl }
    { toRingHom := v, commutes' := fun w => (h w).symm }).toRingHom

@[simp] theorem lift_inC (a : Per.Acris l) : lift u v h (inC K a) = u a := by
  change u a * v 1 = u a
  rw [map_one, mul_one]

@[simp] theorem lift_inI (c : ↥(OL K)) : lift u v h (inI K c) = v c := by
  change u 1 * v c = v c
  rw [map_one, one_mul]

end Lift

def ofA : AK K →+* CK K := AinfK.lift ((inC K).comp (aC l)) (inI K) (inC_wA K)

theorem ofA_inA (a : Ainf l) : ofA K (inA K a) = inC K (aC l a) := lift_inA _ _ _ a

theorem ofA_inO (c : ↥(OL K)) : ofA K (inO K c) = inI K c := lift_inO _ _ _ c

instance complete_l : IsAdicComplete (Ideal.span {(l : CK K)}) (CK K) := by
  have h := GlobalTheory.HWL.TensorWitt.complete_tensor (Module.Free.chooseBasis (W0 K) ↥(OL K)) (l : Per.Acris l)
    (h := (acris_basic l).1)
  let e : ↥(OL K) ⊗[W0 K] Per.Acris l ≃+* CK K :=
    (Algebra.TensorProduct.comm (W0 K) ↥(OL K) (Per.Acris l)).toRingEquiv
  rw [← IsAdicComplete.congr_ringEquiv _ e, Ideal.map_span, Set.image_singleton] at h
  have e1 : e ((1 : ↥(OL K)) ⊗ₜ[W0 K] (l : Per.Acris l)) = (l : CK K) := map_natCast (inC K) l
  rwa [e1] at h

variable {K} in

theorem eq_zero_of_l_mul {x : CK K} (h : (l : CK K) * x = 0) : x = 0 := by
  rw [← map_natCast (inC K), ← Algebra.smul_def] at h
  refine (Module.Free.chooseBasis (Per.Acris l) (CK K)).repr.injective (Finsupp.ext fun i => ?_)
  have h1 := congrArg (fun y => (Module.Free.chooseBasis (Per.Acris l) (CK K)).repr y i) h
  simp only [map_smul, map_zero, Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply] at h1 ⊢
  exact (acris_basic l).2.1 _ h1

theorem phiA_pow_aC (n : ℕ) (a : Ainf l) : (phiA l ^ n) (aC l a) = aC l ((Per.φA l ^ n) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', RingHom.coe_mul, RingHom.coe_mul, Function.comp_apply, Function.comp_apply, ih]
    exact (GlobalTheory.CrisMaps.phiA_extends l).alg _

def frobC : CK K →+* CK K :=
  lift ((inC K).comp (phiA l ^ fK K)) (inI K) fun w => by
    rw [RingHom.comp_apply, phiA_pow_aC, iter_wA, inC_wA]

theorem frobC_inC (a : Per.Acris l) : frobC K (inC K a) = inC K ((⇑(phiA l))^[fK K] a) := by
  rw [frobC, lift_inC, RingHom.comp_apply, RingHom.coe_pow]

theorem frobC_inI (c : ↥(OL K)) : frobC K (inI K c) = inI K c := lift_inI _ _ _ c

theorem frobC_ofA (x : AK K) : frobC K (ofA K x) = ofA K (frobq K x) :=
  AinfK.induction_on x (fun a c => by
    simp only [map_mul, ofA_inA, ofA_inO, frobC_inC, frobC_inI, frobq_inA, frobq_inO]
    rw [← RingHom.coe_pow, ← RingHom.coe_pow, phiA_pow_aC])
    fun x y hx hy => by simp only [map_add, hx, hy]

variable {K}

theorem sigA_aC (g : GQ l) (a : Ainf l) : sigA g (aC l a) = aC l (Per.σA g a) := (GlobalTheory.CrisMaps.sigA_extends g).alg a

def galC (g : ↥(GK K)) : CK K →+* CK K :=
  lift ((inC K).comp (sigA (g : GQ l))) (inI K) fun w => by
    rw [RingHom.comp_apply, sigA_aC, σA_wA, inC_wA]

theorem galC_inC (g : ↥(GK K)) (a : Per.Acris l) : galC g (inC K a) = inC K (sigA (g : GQ l) a) :=
  lift_inC _ _ _ a

theorem galC_inI (g : ↥(GK K)) (c : ↥(OL K)) : galC g (inI K c) = inI K c := lift_inI _ _ _ c

theorem galC_ofA (g : ↥(GK K)) (x : AK K) : galC g (ofA K x) = ofA K (gal K g x) :=
  AinfK.induction_on x (fun a c => by
    simp only [map_mul, ofA_inA, ofA_inO, galC_inC, galC_inI, gal_inA, gal_inO, sigA_aC])
    fun x y hx hy => by simp only [map_add, hx, hy]

theorem l_dvd_pow {x : Ainf l} (hx : Per.θ l x = 0) : (l : Per.Acris l) ∣ aC l x ^ l := by
  obtain ⟨g, hg, e⟩ := exists_dividedPower_mem_Acris0 l x hx l
  have e' : ((l.factorial : ℕ) : Per.Acris0 l) * ⟨g, hg⟩ = algebraMap (Per.Ainf l) (Per.Acris0 l) x ^ l :=
    Subtype.ext (by simpa using e)
  have e2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) e'
  rw [map_mul, map_natCast, map_pow] at e2
  rw [← GlobalTheory.RingIface.tower l x] at e2
  change _ = aC l x ^ l at e2
  rw [← e2]
  exact (Nat.cast_dvd_cast (Nat.dvd_factorial hl.out.pos le_rfl)).mul_right _

variable (K) in

theorem exists_ker_pow_dvd : ∃ M : ℕ, 0 < M ∧ ∀ (k : ℕ), ∀ z ∈ RingHom.ker (thetaK K) ^ k,
    (l : CK K) ^ (k / M) ∣ ofA K z := by
  obtain ⟨π, hπ⟩ := exists_unif (K := K)
  obtain ⟨p, hp⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l (intToOC K π)
  obtain ⟨N, hN⟩ := exists_ker_pow_le K
  have h1 : Ideal.span {(l : AK K)} ⊔ (RingHom.ker (Per.θ l)).map (inA K) ≤
      (Ideal.span {(l : CK K)}).radical.comap (ofA K) := by
    refine sup_le ?_ (Ideal.map_le_iff_le_comap.2 fun x hx => ⟨l, ?_⟩)
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
      exact Ideal.le_radical (Ideal.mem_span_singleton_self _)
    · rw [ofA_inA, ← map_pow, Ideal.mem_span_singleton, ← map_natCast (inC K)]
      exact map_dvd _ (l_dvd_pow hx)
  obtain ⟨m, hm⟩ := h1 (hN (Ideal.pow_mem_pow (thetaK_eta hp) N))
  rw [map_pow, ← pow_mul, Ideal.mem_span_singleton] at hm
  obtain ⟨M, hM, h2⟩ := exists_pos_pow ⟨_, hm⟩
  refine ⟨M, hM, fun k z hz => ?_⟩
  rw [ker_thetaK hπ hp, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz
  refine (pow_div_dvd h2 k).trans ?_
  rw [← map_pow]
  exact map_dvd _ hz

theorem exists_l_dvd_pow {x : AK K} (hx : thetaK K x = 0) : ∃ M : ℕ, (l : CK K) ∣ ofA K x ^ M := by
  obtain ⟨M, hM, h⟩ := exists_ker_pow_dvd K
  refine ⟨M, ?_⟩
  have := h M _ (Ideal.pow_mem_pow hx M)
  rwa [Nat.div_self hM, pow_one, map_pow] at this

variable (K)

def BK : Type := Localization.Away (l : CK K)

instance : CommRing (BK K) := inferInstanceAs (CommRing (Localization.Away (l : CK K)))

instance : Algebra (CK K) (BK K) := inferInstanceAs (Algebra (CK K) (Localization.Away (l : CK K)))

instance : IsLocalization.Away (l : CK K) (BK K) :=
  inferInstanceAs (IsLocalization.Away _ (Localization.Away (l : CK K)))

abbrev toB : CK K →+* BK K := algebraMap (CK K) (BK K)

theorem isUnit_l : IsUnit (l : BK K) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := BK K) (l : CK K)
  rwa [map_natCast] at h

theorem toB_injective : Function.Injective (toB K) :=
  IsLocalization.injective (M := Submonoid.powers (l : CK K)) (BK K) (Submonoid.powers_le.2
    (mem_nonZeroDivisors_iff_left.2 fun _ h => eq_zero_of_l_mul h))

variable {K} in

theorem exists_pow_mul (b : BK K) : ∃ (D : ℕ) (z : CK K), (l : BK K) ^ D * b = toB K z := by
  obtain ⟨D, z, h⟩ := IsLocalization.Away.surj (l : CK K) b
  exact ⟨D, z, by rw [← h, map_natCast, mul_comm]⟩

variable {K} in

theorem isUnit_map {S : Type*} [CommRing S] (hS : IsUnit (l : S)) (v : ↥(OL K) →+* S)
    (c : nonZeroDivisors ↥(OL K)) : IsUnit (v c) := by
  obtain ⟨π, hπ⟩ := exists_unif (K := K)
  obtain ⟨n, h⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.coe_ne_zero c) hπ
  have h1 := map_dvd v (h.dvd.trans (pow_dvd_pow_of_dvd (dvd_of_not_isUnit hπ (l_mem_max K)) n))
  rw [map_pow, map_natCast] at h1
  exact isUnit_of_dvd_unit h1 (hS.pow n)

abbrev oK : ↥(OL K) →+* ↥K.1 := algebraMap ↥(OL K) ↥K.1

def inK : ↥K.1 →+* BK K :=
  IsLocalization.lift (M := nonZeroDivisors ↥(OL K)) (g := (toB K).comp (inI K)) (isUnit_map (isUnit_l K) _)

theorem inK_oK (c : ↥(OL K)) : inK K (oK K c) = toB K (inI K c) := IsLocalization.lift_eq _ c

def inP : BcrisP l →+* BK K := plusLift ((toB K).comp (inC K)) (isUnit_l K)

theorem inP_algebraMap (a : Per.Acris l) : inP K (algebraMap _ _ a) = toB K (inC K a) := plusLift_alg _ _ a

variable {K}

theorem ringHom_extB {S : Type*} [CommRing S] {u v : BK K →+* S} (h : ∀ z, u (toB K z) = v (toB K z)) : u = v :=
  IsLocalization.ringHom_ext (Submonoid.powers (l : CK K)) (RingHom.ext h)

theorem ringHom_extK {S : Type*} [CommRing S] {u v : ↥K.1 →+* S} (h : ∀ c, u (oK K c) = v (oK K c)) : u = v :=
  IsLocalization.ringHom_ext (nonZeroDivisors ↥(OL K)) (RingHom.ext h)

def awayLift {S : Type*} [CommRing S] (f : CK K →+* S) (h : IsUnit (l : S)) : BK K →+* S :=
  IsLocalization.Away.lift (l : CK K) (g := f) (by rwa [map_natCast])

theorem awayLift_toB {S : Type*} [CommRing S] (f : CK K →+* S) (h : IsUnit (l : S)) (z : CK K) :
    awayLift f h (toB K z) = f z := IsLocalization.Away.lift_eq _ _ z

section LiftB

variable {S : Type*} [CommRing S] (u : Per.Acris l →+* S) (v : ↥K.1 →+* S)
  (h : ∀ w : W0 K, u (aC l (wA l (fK K) w)) = v (oK K (thetaW (fK K) K w)))

include v in
theorem isUnit_l_of : IsUnit (l : S) := by
  have : IsUnit (l : ↥K.1) := (Nat.cast_ne_zero.2 hl.out.ne_zero : (l : ↥K.1) ≠ 0).isUnit
  simpa using this.map v

def liftB : BK K →+* S := awayLift (lift u (v.comp (oK K)) h) (isUnit_l_of v)

theorem liftB_toB (z : CK K) : liftB u v h (toB K z) = lift u (v.comp (oK K)) h z := awayLift_toB _ _ z

theorem liftB_inC (a : Per.Acris l) : liftB u v h (toB K (inC K a)) = u a := by rw [liftB_toB, lift_inC]

theorem liftB_inK (c : ↥K.1) : liftB u v h (inK K c) = v c :=
  RingHom.congr_fun (ringHom_extK (u := (liftB u v h).comp (inK K)) (v := v) fun c => by
    rw [RingHom.comp_apply, inK_oK, liftB_toB, lift_inI, RingHom.comp_apply]) c

end LiftB

theorem awayLift_inK (s : CK K →+* CK K) (hs : ∀ c, s (inI K c) = inI K c) (c : ↥K.1) :
    awayLift ((toB K).comp s) (isUnit_l K) (inK K c) = inK K c :=
  RingHom.congr_fun (ringHom_extK (u := (awayLift ((toB K).comp s) (isUnit_l K)).comp (inK K)) (v := inK K)
    fun c => by rw [RingHom.comp_apply, inK_oK, awayLift_toB, RingHom.comp_apply, hs]) c

variable (K) in

def frobB : BK K →+* BK K := awayLift ((toB K).comp (frobC K)) (isUnit_l K)

theorem frobB_toB (z : CK K) : frobB K (toB K z) = toB K (frobC K z) := awayLift_toB _ _ z

theorem frobB_inK (c : ↥K.1) : frobB K (inK K c) = inK K c := awayLift_inK _ (frobC_inI K) c

def galB (g : ↥(GK K)) : BK K →+* BK K := awayLift ((toB K).comp (galC g)) (isUnit_l K)

theorem galB_toB (g : ↥(GK K)) (z : CK K) : galB g (toB K z) = toB K (galC g z) := awayLift_toB _ _ z

theorem galB_inK (g : ↥(GK K)) (c : ↥K.1) : galB g (inK K c) = inK K c := awayLift_inK _ (galC_inI g) c

variable (K)

scoped instance algWP : Algebra (W0 K) (BcrisP l) :=
  ((algebraMap (Per.Acris l) (BcrisP l)).comp ((aC l).comp (wA l (fK K)).toRingHom)).toAlgebra

scoped instance algWK : Algebra (W0 K) ↥K.1 := ((oK K).comp (thetaW (fK K) K).toRingHom).toAlgebra

abbrev PK : Type := BcrisP l ⊗[W0 K] ↥K.1

def toPK : BK K →+* PK K :=
  liftB ((Algebra.TensorProduct.includeLeftRingHom : BcrisP l →+* PK K).comp (algebraMap (Per.Acris l) (BcrisP l)))
    (Algebra.TensorProduct.includeRight : ↥K.1 →ₐ[W0 K] PK K).toRingHom fun w =>
      ((Algebra.TensorProduct.includeRight : ↥K.1 →ₐ[W0 K] PK K).commutes w).symm

theorem toPK_inP (b : BcrisP l) : toPK K (inP K b) = b ⊗ₜ[W0 K] (1 : ↥K.1) :=
  RingHom.congr_fun (plus_ext (f := (toPK K).comp (inP K))
    (f' := (Algebra.TensorProduct.includeLeftRingHom : BcrisP l →+* PK K)) fun a => by
      rw [RingHom.comp_apply, inP_algebraMap, toPK, liftB_inC, RingHom.comp_apply]) b

theorem toPK_inK (c : ↥K.1) : toPK K (inK K c) = (1 : BcrisP l) ⊗ₜ[W0 K] c := liftB_inK _ _ _ c

def ofPK : PK K →+* BK K :=
  letI : Algebra (W0 K) (BK K) := ((inP K).comp (algebraMap (W0 K) (BcrisP l))).toAlgebra
  (Algebra.TensorProduct.productMap (R := W0 K) { toRingHom := inP K, commutes' := fun _ => rfl }
    { toRingHom := inK K
      commutes' := fun w => ((inK_oK K _).trans (congrArg (toB K) (inC_wA K w).symm)).trans (inP_algebraMap K _).symm
    }).toRingHom

theorem ofPK_tmul (b : BcrisP l) (c : ↥K.1) : ofPK K (b ⊗ₜ[W0 K] c) = inP K b * inK K c := rfl

def equivPK : BK K ≃+* PK K :=
  RingEquiv.ofRingHom (toPK K) (ofPK K)
    (RingHom.ext fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b c =>
        rw [RingHom.comp_apply, ofPK_tmul, map_mul, toPK_inP, toPK_inK, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul, RingHom.id_apply]
      | add x y hx hy => simp only [map_add, hx, hy])
    (ringHom_extB fun z => induction_on z (fun a c => by
      rw [map_mul, ← inP_algebraMap, ← inK_oK, RingHom.comp_apply, map_mul, toPK_inP, toPK_inK, map_mul, ofPK_tmul,
        ofPK_tmul, map_one, map_one, mul_one, one_mul, RingHom.id_apply])
      fun x y hx hy => by simp only [map_add, hx, hy])

variable {K}

def Ev (L : PowerSeries ↥K.1) (x : AK K) (y : BK K) : Prop := IsEval l (toB K) (inK K) L (toB K (ofA K x)) y

theorem Ev.unique {L : PowerSeries ↥K.1} {x : AK K} {y y' : BK K} (h : Ev L x y) (h' : Ev L x y') : y = y' :=
  Tends.unique (toB_injective K) h h'

theorem existsUnique_ev {L : PowerSeries ↥K.1} (hL : OnDisc l (oK K) L) {x : AK K} (hx : thetaK K x = 0) :
    ∃! y, Ev L x y :=
  existsUnique_isEval (toB_injective K) (isUnit_l K) (fun c => (inK_oK K c).symm) hL (exists_l_dvd_pow hx)

theorem Ev.frob {L : PowerSeries ↥K.1} {x : AK K} {y : BK K} (h : Ev L x y) : Ev L (frobq K x) (frobB K y) := by
  have := IsEval.map (i' := toB K) (κ' := inK K) (frobB K) (RingHom.id _) (fun z => ⟨_, frobB_toB z⟩) frobB_inK h
  rwa [PowerSeries.map_id, frobB_toB, frobC_ofA] at this

theorem Ev.gal (g : ↥(GK K)) {L : PowerSeries ↥K.1} {x : AK K} {y : BK K} (h : Ev L x y) :
    Ev L (gal K g x) (galB g y) := by
  have := IsEval.map (i' := toB K) (κ' := inK K) (galB g) (RingHom.id _) (fun z => ⟨_, galB_toB g z⟩) (galB_inK g) h
  rwa [PowerSeries.map_id, galB_toB, galC_ofA] at this

theorem Ev.C_mul (c : ↥K.1) {L : PowerSeries ↥K.1} {x : AK K} {y : BK K} (h : Ev L x y) :
    Ev (PowerSeries.C c * L) x (inK K c * y) :=
  IsEval.C_mul (isUnit_l K) (exists_pow_mul _) h

theorem Ev.subst {L : PowerSeries ↥K.1} (hL : OnDisc l (oK K) L) {u : PowerSeries ↥(OL K)}
    (hu : PowerSeries.constantCoeff u = 0) {x y : AK K} (hx : thetaK K x = 0)
    (hy : ∀ n, y - ∑ j ∈ Finset.range n, inO K (PowerSeries.coeff j u) * x ^ j ∈ RingHom.ker (thetaK K) ^ n)
    {w : BK K} (hw : Ev L y w) : Ev (L.subst (PowerSeries.map (oK K) u)) x w := by
  obtain ⟨M, hM, h⟩ := exists_ker_pow_dvd K
  refine IsEval.subst (o := inI K) (isUnit_l K) (fun c => (inK_oK K c).symm) hL hu hM ?_ (fun n => ?_) hw
  · have := h M _ (Ideal.pow_mem_pow hx M)
    rwa [Nat.div_self hM, pow_one, map_pow] at this
  · simpa only [map_sub, map_sum, map_mul, map_pow, ofA_inO] using h n _ (hy n)

theorem Ev.tendsto (ψ : BK K →+* ℂ_[l]) (hψ : ∀ z, ‖ψ (toB K z)‖ ≤ 1) {L : PowerSeries ↥K.1} {x : AK K} {y : BK K}
    (h : Ev L x y) : Filter.Tendsto
      (fun n => ∑ k ∈ Finset.range n, ψ (inK K (PowerSeries.coeff k L)) * ψ (toB K (ofA K x)) ^ k)
      Filter.atTop (nhds (ψ y)) := by
  simpa only [psum, map_sum, map_mul, map_pow] using Tends.tendsto ψ hψ GlobalTheory.RingBasics.norm_p_lt h

section Log

variable {π : ↥(OL K)} (hπ : Irreducible π) {f : PowerSeries ↥(OL K)} (hf : IsLubinTateSeries π f)

theorem onDisc_log : OnDisc l (oK K) (LTLog.log ↥K.1 hπ hf) :=
  have := OL_resFinite K
  onDisc_of_log (dvd_of_not_isUnit hπ (l_mem_max K)) Finite.one_lt_card (LTLog.pow_log_mul_coeff_mem ↥K.1 hπ hf)

def ltLog (x : AK K) (hx : thetaK K x = 0) : BK K := (existsUnique_ev (onDisc_log hπ hf) hx).exists.choose

theorem ev_ltLog (x : AK K) (hx : thetaK K x = 0) : Ev (LTLog.log ↥K.1 hπ hf) x (ltLog hπ hf x hx) :=
  (existsUnique_ev (onDisc_log hπ hf) hx).exists.choose_spec

theorem ev_log_hom (a : ↥(OL K)) {x y : AK K} (hx : thetaK K x = 0)
    (hy : haveI := OL_resFinite K
      ∀ n, y - ∑ j ∈ Finset.range n, inO K (PowerSeries.coeff j (lubinTateHom hπ hf hf a).toPowerSeries) * x ^ j ∈
        RingHom.ker (thetaK K) ^ n)
    {w : BK K} (hw : Ev (LTLog.log ↥K.1 hπ hf) y w) : w = inK K (oK K a) * ltLog hπ hf x hx := by
  have := OL_resFinite K
  have h := Ev.subst (onDisc_log hπ hf) (isLubinTateLift_lubinTateHom hπ hf hf a).1 hx hy hw
  rw [LTLog.log_subst_lubinTateHom ↥K.1 hπ hf hf a] at h
  exact h.unique (Ev.C_mul _ (ev_ltLog hπ hf x hx))

theorem ev_log_self {x y : AK K} (hx : thetaK K x = 0)
    (hy : ∀ n, y - ∑ j ∈ Finset.range n, inO K (PowerSeries.coeff j f) * x ^ j ∈ RingHom.ker (thetaK K) ^ n)
    {w : BK K} (hw : Ev (LTLog.log ↥K.1 hπ hf) y w) : w = inK K (oK K π) * ltLog hπ hf x hx := by
  have h := Ev.subst (onDisc_log hπ hf) hf.constantCoeff_eq_zero hx hy hw
  rw [LTLog.log_subst_self ↥K.1 hπ hf] at h
  exact h.unique (Ev.C_mul _ (ev_ltLog hπ hf x hx))

end Log

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
    IsAdicComplete (Ideal.span {(l : CK K)}) (CK K) ∧ Function.Injective (toB K) ∧
    (∀ b, equivPK K (inP K b) = b ⊗ₜ[W0 K] (1 : ↥K.1)) ∧ (∀ c, equivPK K (inK K c) = (1 : BcrisP l) ⊗ₜ[W0 K] c) ∧
    ∀ (π : ↥(OL K)) (hπ : Irreducible π) (f : PowerSeries ↥(OL K)) (hf : IsLubinTateSeries π f) (x : AK K),
      thetaK K x = 0 →
      (∃ D N : ℕ, 0 < N ∧ ∀ k : ℕ, ∃ z : CK K,
        (l : BK K) ^ D * (inK K (PowerSeries.coeff k (LTLog.log ↥K.1 hπ hf)) * toB K (ofA K x) ^ k) =
          toB K ((l : CK K) ^ (k / N) * z)) ∧
      ∃! y : BK K, ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ z : CK K,
        ∑ k ∈ Finset.range n, inK K (PowerSeries.coeff k (LTLog.log ↥K.1 hπ hf)) * toB K (ofA K x) ^ k - y =
          toB K ((l : CK K) ^ r * z) := by
  intro l _ K
  refine ⟨complete_l K, toB_injective K, toPK_inP K, toPK_inK K, fun π hπ f hf x hx =>
    ⟨?_, existsUnique_ev (onDisc_log hπ hf) hx⟩⟩
  obtain ⟨-, -, D, N, hN, h, -⟩ := exists_isEval_rate (isUnit_l K) (fun c => (inK_oK K c).symm)
    (onDisc_log hπ hf) (exists_l_dvd_pow hx)
  exact ⟨D, N, hN, h⟩

end GlobalTheory.AcrisK
