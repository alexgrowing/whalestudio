import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CyclotomicFrobeniusPowerSeriesXEqMulQuotient
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory.Cyc

variable (l : ℕ) [Fact l.Prime]

section Rings₀

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]

def cyc (c : ℤ_[l]) : PowerSeries O :=
  PowerSeries.map (algebraMap ℤ_[l] O) (PowerSeries.binomialSeries ℤ_[l] c) - 1

theorem cyc_const (c : ℤ_[l]) : PowerSeries.constantCoeff (cyc l O c) = 0 := by
  rw [cyc, map_sub, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.binomialSeries_coeff]
  simp

def act (c : ℤ_[l]) : PowerSeries O →ₐ[O] PowerSeries O :=
  PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' (cyc_const l O c))

def phi : PowerSeries O →ₐ[O] PowerSeries O := act l O (l : ℤ_[l])

def XX (s : ℕ) : PowerSeries O := (1 + PowerSeries.X) ^ l ^ (s - 1) - 1

def QQ (s : ℕ) : PowerSeries O := ∑ k ∈ Finset.range l, (1 + XX l O s) ^ k

namespace Series

theorem cyc_eq (c : ℤ_[l]) : cyc l O c = PowerSeries.binomialSeries O c - 1 := by
  rw [cyc, Fon.map_binomialSeries _ (fun _ => rfl)]

theorem act_X (c : ℤ_[l]) : act l O c PowerSeries.X = cyc l O c := PowerSeries.substAlgHom_X _

theorem act_eq (c : ℤ_[l]) : act l O c = Fon.gam O c :=
  Fon.algHom_ext_X (by rw [act_X, cyc_eq, Fon.gam_X]) (by rw [act_X, cyc_const])

theorem phi_eq : phi l O = Fon.phi0 l O := by rw [phi, act_eq, Fon.gam_l]

theorem cyc_natCast (k : ℕ) : cyc l O (k : ℤ_[l]) = (1 + PowerSeries.X) ^ k - 1 := by
  rw [cyc_eq, PowerSeries.binomialSeries_nat]

theorem act_act (c c' : ℤ_[l]) (a : PowerSeries O) : act l O c (act l O c' a) = act l O (c * c') a := by
  simp only [act_eq, Fon.gam_mul]

theorem act_one (a : PowerSeries O) : act l O 1 a = a := by rw [act_eq, Fon.gam_one]

theorem phi_act (c : ℤ_[l]) (a : PowerSeries O) : phi l O (act l O c a) = act l O c (phi l O a) := by
  rw [phi, act_act, act_act, mul_comm]

theorem phi_X : phi l O PowerSeries.X = (1 + PowerSeries.X) ^ l - 1 := by rw [phi_eq, Fon.cyclotomicFrobeniusPowerSeries_X]

theorem phi_pow_X (s : ℕ) : (phi l O ^ (s - 1)) PowerSeries.X = XX l O s := by
  rw [phi_eq, Fon.cyclotomicFrobeniusPowerSeries_pow_apply_X, XX]

theorem phi_XX (s : ℕ) : phi l O (XX l O s) = XX l O s * QQ l O s := by
  rw [phi_eq]; exact Fon.cyclotomicFrobenius_iteratedVariable_eq_mul l O s

theorem act_X_unit (c : ℤ_[l]ˣ) : ∃ v, IsUnit v ∧ act l O c PowerSeries.X = PowerSeries.X * v :=
  ⟨_, Fon.isUnit_vser O c, by rw [act_eq, Fon.gam_X_eq]⟩

theorem phi_X_mod : ∃ r, phi l O PowerSeries.X = PowerSeries.X ^ l + (l : PowerSeries O) * r := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (1 : PowerSeries O) PowerSeries.X
  exact ⟨PowerSeries.X * r, by rw [phi_X, hr]; ring⟩

end Series

def EE (n : ℕ) : Type :=
  AdicCompletion (Ideal.span {((l : ℕ) : Localization.Away (letπ : LetA O n))})
    (Localization.Away (letπ : LetA O n))

instance (n : ℕ) : CommRing (EE l O n) :=
  inferInstanceAs (CommRing (AdicCompletion (Ideal.span {((l : ℕ) : Localization.Away (letπ : LetA O n))})
    (Localization.Away (letπ : LetA O n))))

instance (n : ℕ) : Algebra (Localization.Away (letπ : LetA O n)) (EE l O n) :=
  inferInstanceAs (Algebra (Localization.Away (letπ : LetA O n))
    (AdicCompletion (Ideal.span {((l : ℕ) : Localization.Away (letπ : LetA O n))})
      (Localization.Away (letπ : LetA O n))))

def toEE (n : ℕ) : LetA O n →+* EE l O n :=
  (algebraMap (Localization.Away (letπ : LetA O n)) (EE l O n)).comp (algebraMap (LetA O n) _)

instance (n : ℕ) : Algebra (LetA O n) (EE l O n) := (toEE l O n).toAlgebra

instance (n : ℕ) : Algebra O (EE l O n) := ((toEE l O n).comp (algebraMap O (LetA O n))).toAlgebra

instance (n : ℕ) : IsScalarTower O (LetA O n) (EE l O n) := IsScalarTower.of_algebraMap_eq fun _ => rfl

namespace Completion

open Series

variable (n : ℕ)

private theorem dvd_iff_eval (S : Type) [CommRing S] (k : ℕ) (x : AdicCompletion (Ideal.span {(l : S)}) S) : (l : AdicCompletion (Ideal.span {(l : S)}) S) ^ k ∣ x ↔
    AdicCompletion.eval (Ideal.span {(l : S)}) S k x = 0 := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _),
    Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, trivial, by rw [Algebra.smul_def, map_pow, map_natCast]⟩
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, by rw [Algebra.smul_def, map_pow, map_natCast]⟩

omit [Algebra ℤ_[l] O] in

theorem isUnit_toEE_π : IsUnit (toEE l O n letπ) :=
  (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (letπ : LetA O n)) letπ).map
    (algebraMap _ (EE l O n))

instance lComplete_EE : Fon.LComplete l (EE l O n) := by
  have h := (IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {(l : Localization.Away (letπ : LetA O n))}) (Localization.Away (letπ : LetA O n)))
    (Ideal.span {(l : Localization.Away (letπ : LetA O n))})
    (AdicCompletion (Ideal.span {(l : Localization.Away (letπ : LetA O n))}) (Localization.Away (letπ : LetA O n)))).2
    (AdicCompletion.isAdicComplete (Submodule.fg_span_singleton _))
  rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h

variable {l O n}

omit [Algebra ℤ_[l] O] in

theorem EE_dense (x : EE l O n) (k : ℕ) :
    ∃ (a : LetA O n) (m : ℕ), (l : EE l O n) ^ k ∣ x * toEE l O n (letπ ^ m) - toEE l O n a := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    (AdicCompletion.eval (Ideal.span {(l : Localization.Away (letπ : LetA O n))}) _ k x)
  have h1 : (l : EE l O n) ^ k ∣ x - algebraMap _ (EE l O n) y := by
    refine (dvd_iff_eval l _ k _).2 ?_
    erw [map_sub, ← hy]
    exact sub_self _
  obtain ⟨⟨a, _, m, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers (letπ : LetA O n)) y
  refine ⟨a, m, ?_⟩
  simp only [toEE, RingHom.comp_apply]
  rw [← h, map_mul, ← sub_mul]
  exact h1.mul_right _

omit [Algebra ℤ_[l] O] in

theorem EE_hom_ext {B : Type} [CommRing B] [IsHausdorff (Ideal.span {(l : B)}) B]
    {f g : EE l O n →+* B} (h : ∀ a, f (toEE l O n a) = g (toEE l O n a)) : f = g := by
  ext x
  rw [← sub_eq_zero]
  refine Fon.eq_zero_of_l_pow_dvd (l := l) _ fun k => ?_
  obtain ⟨a, m, z, hz⟩ := EE_dense x k
  have hu : IsUnit (f (toEE l O n (letπ ^ m))) := by
    rw [map_pow]; exact ((isUnit_toEE_π l O n).pow m).map f
  have h1 := congrArg f hz
  have h2 := congrArg g hz
  simp only [map_sub, map_mul f, map_mul g, map_pow f, map_pow g, map_natCast, ← h] at h1 h2
  rw [← hu.dvd_mul_right]
  exact ⟨f z - g z, by linear_combination h1 - h2⟩

def liftEE {B : Type} [CommRing B] [Fon.LComplete l B] (f : LetA O n →+* B) (hf : IsUnit (f letπ)) :
    EE l O n →+* B :=
  ((AdicCompletion.ofAlgEquiv (Ideal.span {(l : B)})).symm : _ →+* B).comp
    (GlobalTheory.AdicMaps.padicMap l (IsLocalization.Away.lift (S := Localization.Away (letπ : LetA O n)) letπ hf))

omit [Algebra ℤ_[l] O] in

@[simp] theorem liftEE_toEE {B : Type} [CommRing B] [Fon.LComplete l B] (f : LetA O n →+* B)
    (hf : IsUnit (f letπ)) (a : LetA O n) : liftEE (l := l) f hf (toEE l O n a) = f a := by
  have h := GlobalTheory.AdicMaps.padicMap_alg l
    (IsLocalization.Away.lift (S := Localization.Away (letπ : LetA O n)) letπ hf) (algebraMap _ _ a)
  rw [IsLocalization.Away.lift_eq] at h
  exact (congrArg (AdicCompletion.ofAlgEquiv (Ideal.span {(l : B)})).symm h).trans
    ((AdicCompletion.ofAlgEquiv (Ideal.span {(l : B)})).symm.commutes _)

def extEE (f : LetA O n →ₐ[O] LetA O n) (hf : IsUnit (toEE l O n (f letπ))) : EE l O n →ₐ[O] EE l O n where
  toRingHom := liftEE ((toEE l O n).comp (f : LetA O n →+* LetA O n)) hf
  commutes' r := (liftEE_toEE _ hf (algebraMap O (LetA O n) r)).trans
    (congrArg (toEE l O n) (f.commutes r))

omit [Algebra ℤ_[l] O] in

@[simp] theorem extEE_toEE (f : LetA O n →ₐ[O] LetA O n) (hf : IsUnit (toEE l O n (f letπ))) (a : LetA O n) :
    extEE f hf (toEE l O n a) = toEE l O n (f a) := liftEE_toEE _ hf a

variable (l O n)

def phiEE : EE l O n →ₐ[O] EE l O n :=
  extEE (letφ (phi l O)) (by
    obtain ⟨r, hr⟩ := phi_X_mod l O
    have h : letφ (phi l O) (letπ : LetA O n) = letπ ^ l + (l : LetA O n) * fun _ => r := funext fun _ => hr
    refine Fon.isUnit_of_l_dvd (l := l) ((isUnit_toEE_π l O n).pow l) ⟨toEE l O n fun _ => r, ?_⟩
    rw [h]; simp)

theorem phiEE_toEE (a : LetA O n) : phiEE l O n (toEE l O n a) = toEE l O n (letφ (phi l O) a) :=
  extEE_toEE _ _ _

private def actEE1 (c : ℤ_[l]ˣ) : EE l O n →ₐ[O] EE l O n :=
  extEE (letγ (act l O c)) (by
    obtain ⟨v, hv, h⟩ := act_X_unit l O c
    have h' : letγ (act l O c) (letπ : LetA O n) = letπ * fun _ => v := funext fun _ => h
    rw [h', map_mul]
    exact (isUnit_toEE_π l O n).mul ((Pi.isUnit_iff.2 fun _ => hv).map _))

private theorem actEE1_toEE (c : ℤ_[l]ˣ) (a : LetA O n) :
    actEE1 l O n c (toEE l O n a) = toEE l O n (letγ (act l O c) a) := extEE_toEE _ _ _

def actEE : ℤ_[l]ˣ →* (EE l O n →ₐ[O] EE l O n) where
  toFun := actEE1 l O n
  map_one' := AlgHom.coe_ringHom_injective (EE_hom_ext fun a => (actEE1_toEE l O n 1 a).trans
    (congrArg (toEE l O n) (funext fun i => act_one l O (a i))))
  map_mul' c c' := AlgHom.coe_ringHom_injective (EE_hom_ext fun a => by
    change actEE1 l O n (c * c') _ = actEE1 l O n c (actEE1 l O n c' _)
    rw [actEE1_toEE, actEE1_toEE, actEE1_toEE]
    exact congrArg (toEE l O n) (funext fun i => (act_act l O c c' (a i)).symm))

theorem actEE_toEE (c : ℤ_[l]ˣ) (a : LetA O n) :
    actEE l O n c (toEE l O n a) = toEE l O n (letγ (act l O c) a) := actEE1_toEE l O n c a

def toPiEE : EE l O n →+* Fon.EE l O n :=
  liftEE (algebraMap (LetA O n) (Fon.EE l O n)) (Fon.EE_isUnit_π l O n)

omit [Algebra ℤ_[l] O] in

theorem toPiEE_bijective [NeZero n] : Function.Bijective (toPiEE l O n) := by
  have e : ∀ a, toPiEE l O n (toEE l O n a) = algebraMap (LetA O n) (Fon.EE l O n) a := liftEE_toEE _ _
  have hu : ∀ m : ℕ, IsUnit (toEE l O n (letπ ^ m)) := fun m => by
    rw [map_pow]; exact (isUnit_toEE_π l O n).pow m
  have hI : (Ideal.span {(l : EE l O n)}).map (toPiEE l O n) = Ideal.span {(l : Fon.EE l O n)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    refine Fon.eq_zero_of_l_pow_dvd (l := l) _ fun k => ?_
    obtain ⟨a, m, z, hz⟩ := EE_dense x k
    have h1 := congrArg (toPiEE l O n) hz
    rw [map_sub, map_mul, hx, zero_mul, e, map_mul, map_pow, map_natCast] at h1
    obtain ⟨b, rfl⟩ := Fon.EE_sat l O n a k
      (Ideal.mem_span_singleton.2 ⟨-toPiEE l O n z, by linear_combination -h1⟩)
    rw [← (hu m).dvd_mul_right]
    rw [map_mul, map_pow (toEE l O n) (l : LetA O n), map_natCast] at hz
    exact ⟨z + toEE l O n b, by linear_combination hz⟩
  · haveI : IsHausdorff ((Ideal.span {(l : EE l O n)}).map (toPiEE l O n)) (Fon.EE l O n) := by
      rw [hI]; infer_instance
    refine surjective_of_mk_map_comp_surjective (I := Ideal.span {(l : EE l O n)}) _ fun y => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, m, h⟩ := Fon.EE_dense l O n y 1
    obtain ⟨w, hw⟩ := (hu m).exists_right_inv
    have hw' := congrArg (toPiEE l O n) hw
    rw [map_mul, e, map_one] at hw'
    refine ⟨toEE l O n a * w, ?_⟩
    rw [RingHom.comp_apply, eq_comm, Ideal.Quotient.eq, hI, map_mul, e]
    rw [pow_one] at h
    convert Ideal.mul_mem_right (toPiEE l O n w) _ h using 1
    linear_combination (-y) * hw'

end Completion

end Rings₀

open Series Completion

def clW (S : Set (WCb l)) : Set (WCb l) :=
  {x | ∀ k : ℕ, ∃ y ∈ S, x - y ∈ Ideal.span {((l : ℕ) : WCb l) ^ k}}

variable {l}

theorem mem_clW {S : Set (WCb l)} {x : WCb l} :
    x ∈ clW l S ↔ ∀ k : ℕ, ∃ y ∈ S, (l : WCb l) ^ k ∣ x - y := by
  simp only [clW, Set.mem_setOf_eq, Ideal.mem_span_singleton]

def clAlg (S : Subalgebra ℤ_[l] (WCb l)) : Subalgebra ℤ_[l] (WCb l) where
  carrier := clW l S
  add_mem' {a b} ha hb := mem_clW.2 fun k => by
    obtain ⟨x, hx, h⟩ := mem_clW.1 ha k
    obtain ⟨y, hy, h'⟩ := mem_clW.1 hb k
    exact ⟨x + y, S.add_mem hx hy, by convert h.add h' using 1; ring⟩
  mul_mem' {a b} ha hb := mem_clW.2 fun k => by
    obtain ⟨x, hx, h⟩ := mem_clW.1 ha k
    obtain ⟨y, hy, h'⟩ := mem_clW.1 hb k
    exact ⟨x * y, S.mul_mem hx hy, by convert (h.mul_right b).add (h'.mul_left x) using 1; ring⟩
  algebraMap_mem' z := mem_clW.2 fun _ => ⟨_, S.algebraMap_mem z, by simp⟩

theorem mem_clAlg {S : Subalgebra ℤ_[l] (WCb l)} {x : WCb l} :
    x ∈ clAlg S ↔ ∀ k : ℕ, ∃ y ∈ S, (l : WCb l) ^ k ∣ x - y := mem_clW

theorem le_clAlg (S : Subalgebra ℤ_[l] (WCb l)) : S ≤ clAlg S :=
  fun x hx => mem_clAlg.2 fun _ => ⟨x, hx, by simp⟩

theorem clAlg_clAlg (S : Subalgebra ℤ_[l] (WCb l)) : clAlg (clAlg S) = clAlg S :=
  le_antisymm (fun x hx => mem_clAlg.2 fun k => by
    obtain ⟨y, hy, h⟩ := mem_clAlg.1 hx k
    obtain ⟨z, hz, h'⟩ := mem_clAlg.1 hy k
    exact ⟨z, hz, by convert h.add h' using 1; ring⟩) (le_clAlg _)

theorem map_mem_clAlg {S S' : Subalgebra ℤ_[l] (WCb l)} (σ : WCb l →+* WCb l)
    (h : ∀ x ∈ S, σ x ∈ clAlg S') {x : WCb l} (hx : x ∈ clAlg S) : σ x ∈ clAlg S' := by
  rw [← clAlg_clAlg]
  refine mem_clAlg.2 fun k => ?_
  obtain ⟨y, hy, h'⟩ := mem_clAlg.1 hx k
  refine ⟨σ y, h y hy, ?_⟩
  simpa using map_dvd σ h'

theorem inv_mem_clAlg {S : Subalgebra ℤ_[l] (WCb l)} {r w : WCb l} (hr : r ∈ S)
    (hw : (1 - l * r) * w = 1) : w ∈ clAlg S :=
  mem_clAlg.2 fun k => ⟨∑ i ∈ Finset.range k, (l * r) ^ i,
    S.sum_mem fun i _ => S.pow_mem (S.mul_mem (natCast_mem S l) hr) i, r ^ k * w, by
      have := mul_neg_geom_sum ((l : WCb l) * r) k
      rw [mul_pow] at this
      linear_combination (-w) * this + (∑ i ∈ Finset.range k, ((l : WCb l) * r) ^ i) * hw⟩

def IsIo (e : OCb l) (io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l) : Prop :=
  io PowerSeries.X = WittVector.teichmuller l e - 1

theorem IsIo.isUnit_X {e : OCb l} {io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l} (h : IsIo e io) (he : e ≠ 1) :
    IsUnit (inclW l (io PowerSeries.X)) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  have h0 : (io PowerSeries.X).coeff 0 = e - 1 := by
    rw [h]
    change WittVector.constantCoeff (WittVector.teichmuller l e - 1) = _
    rw [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  rw [inclW, WittVector.map_coeff, h0, map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))]
  exact sub_ne_zero.2 he

theorem εroot_pow {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : AI.εroot s ^ l ^ s = AI.ε := by
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ s ih =>
    rw [← ih, pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p,
      LocAinf.εroot]

theorem εroot_ne_one {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : AI.εroot s ≠ 1 := fun h =>
  AI.ε_ne_one (by rw [← εroot_pow AI s, h, one_pow])

theorem εroot_sub_one_not_unit {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : ¬ IsUnit (AI.εroot s - 1) := by
  intro h
  have h1 := (h.pow (l ^ s)).map (PreTilt.coeff 0)
  rw [sub_pow_char_pow, εroot_pow, one_pow, map_sub, AI.ε_coeff, AI.ζ_zero, map_one, map_one, sub_self] at h1
  haveI : Nontrivial (ModP (OC l) l) := CharP.nontrivial_of_char_ne_one (Fact.out : l.Prime).ne_one
  exact not_isUnit_zero h1

private theorem coeff_mem {A : Type} [CommRing A] [Algebra ℤ_[l] A] (S : Subalgebra ℤ_[l] A) {a : A}
    (ha : a ∈ S) (m k i : ℕ) :
    (Polynomial.X ^ m - Polynomial.C a * Polynomial.X ^ k : Polynomial A).coeff i ∈ S := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow]
  refine S.sub_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _ | exact ha

section Rings

variable (io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l)

def E0loc : Subalgebra ℤ_[l] (WCb l) where
  carrier := {x | ∃ (a : PowerSeries ℤ_[l]) (m : ℕ), x * inclW l (io PowerSeries.X) ^ m = inclW l (io a)}
  add_mem' := by
    rintro x y ⟨a, m, h⟩ ⟨b, n, h'⟩
    refine ⟨a * PowerSeries.X ^ n + b * PowerSeries.X ^ m, m + n, ?_⟩
    simp only [map_add, map_mul, map_pow, ← h, ← h']
    ring
  mul_mem' := by
    rintro x y ⟨a, m, h⟩ ⟨b, n, h'⟩
    refine ⟨a * b, m + n, ?_⟩
    simp only [map_mul, ← h, ← h']
    ring
  algebraMap_mem' z := ⟨algebraMap _ _ z, 0, by
    rw [pow_zero, mul_one, io.commutes]; exact ((inclWA l).commutes z).symm⟩

def E0 : Subalgebra ℤ_[l] (WCb l) := clAlg (E0loc io)

def simpleRoots : Set (WCb l) :=
  {y | ∃ f : Polynomial (WCb l), f.Monic ∧ (∀ i, f.coeff i ∈ E0 io) ∧ f.eval y = 0 ∧
    IsUnit (f.derivative.eval y)}

def EurAlg : Subalgebra ℤ_[l] (WCb l) := Algebra.adjoin ℤ_[l] (simpleRoots io)

def Eur : Subalgebra ℤ_[l] (WCb l) := clAlg (EurAlg io)

theorem io_mem_E0 (a : PowerSeries ℤ_[l]) : inclW l (io a) ∈ E0 io :=
  le_clAlg _ ⟨a, 0, by rw [pow_zero, mul_one]⟩

theorem inv_X_mem_E0 {w : WCb l} (hw : inclW l (io PowerSeries.X) * w = 1) : w ∈ E0 io :=
  le_clAlg _ ⟨1, 1, by rw [pow_one, mul_comm, hw, map_one, map_one]⟩

theorem clAlg_E0 : clAlg (E0 io) = E0 io := clAlg_clAlg _

theorem clAlg_Eur : clAlg (Eur io) = Eur io := clAlg_clAlg _

theorem simpleRoots_subset_Eur : simpleRoots io ⊆ Eur io :=
  fun _ hy => le_clAlg _ (Algebra.subset_adjoin hy)

theorem E0_le_Eur : E0 io ≤ Eur io := fun a ha =>
  simpleRoots_subset_Eur io ⟨Polynomial.X - Polynomial.C a, Polynomial.monic_X_sub_C a, fun i => by
    have h := coeff_mem (E0 io) ha 1 0 i
    rwa [pow_one, pow_zero, mul_one] at h,
    by rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self],
    by rw [Polynomial.derivative_X_sub_C, Polynomial.eval_one]; exact isUnit_one⟩

variable {io}

theorem map_mem_E0 (σ : WCb l →+* WCb l) (f : PowerSeries ℤ_[l] → PowerSeries ℤ_[l])
    (hσ : ∀ a, σ (inclW l (io a)) = inclW l (io (f a)))
    (hw : ∃ w ∈ E0 io, inclW l (io (f PowerSeries.X)) * w = 1) {x : WCb l} (hx : x ∈ E0 io) :
    σ x ∈ E0 io := by
  obtain ⟨w, hw, hw1⟩ := hw
  refine map_mem_clAlg σ ?_ hx
  rintro x ⟨a, m, h⟩
  have h1 := congrArg σ h
  rw [map_mul, map_pow, hσ, hσ] at h1
  have h2 : σ x = inclW l (io (f a)) * w ^ m := by rw [← h1, mul_assoc, ← mul_pow, hw1, one_pow, mul_one]
  rw [h2]
  exact (E0 io).mul_mem (io_mem_E0 io _) ((E0 io).pow_mem hw m)

theorem map_mem_E0_act (hX : IsUnit (inclW l (io PowerSeries.X))) (σ : WCb l →+* WCb l) (c : ℤ_[l]ˣ)
    (hσ : ∀ a, σ (inclW l (io a)) = inclW l (io (act l ℤ_[l] c a))) {x : WCb l} (hx : x ∈ E0 io) :
    σ x ∈ E0 io := by
  obtain ⟨v, hv, h⟩ := act_X_unit l ℤ_[l] c
  obtain ⟨v', hv'⟩ := hv.exists_right_inv
  obtain ⟨w, hw⟩ := hX.exists_right_inv
  refine map_mem_E0 σ _ hσ ⟨w * inclW l (io v'),
    (E0 io).mul_mem (inv_X_mem_E0 io hw) (io_mem_E0 io _), ?_⟩ hx
  rw [h, map_mul, map_mul, mul_mul_mul_comm, hw, ← map_mul, ← map_mul, hv', map_one, map_one, mul_one]

theorem map_mem_E0_phi (hX : IsUnit (inclW l (io PowerSeries.X))) (σ : WCb l →+* WCb l)
    (hσ : ∀ a, σ (inclW l (io a)) = inclW l (io (phi l ℤ_[l] a))) {x : WCb l} (hx : x ∈ E0 io) :
    σ x ∈ E0 io := by
  obtain ⟨r, h⟩ := phi_X_mod l ℤ_[l]
  obtain ⟨w, hw⟩ := hX.exists_right_inv
  obtain ⟨u, hu⟩ : ∃ u, inclW l (io (phi l ℤ_[l] PowerSeries.X)) * u = 1 := by
    rw [← hσ]; exact (hX.map σ).exists_right_inv
  refine map_mem_E0 σ _ hσ ⟨u, ?_, hu⟩ hx
  have hwl : inclW l (io PowerSeries.X) ^ l * w ^ l = 1 := by rw [← mul_pow, hw, one_pow]
  simp only [h, map_add, map_mul, map_pow, map_natCast] at hu
  have h1 : inclW l (io PowerSeries.X) ^ l * u ∈ clAlg (E0 io) :=
    inv_mem_clAlg (r := -(inclW l (io r) * w ^ l))
      ((E0 io).neg_mem ((E0 io).mul_mem (io_mem_E0 io _) ((E0 io).pow_mem (inv_X_mem_E0 io hw) l)))
      (by linear_combination hu + (l : WCb l) * inclW l (io r) * u * hwl)
  rw [clAlg_E0] at h1
  have h2 : u = inclW l (io PowerSeries.X) ^ l * u * w ^ l := by linear_combination (-u) * hwl
  rw [h2]
  exact (E0 io).mul_mem h1 ((E0 io).pow_mem (inv_X_mem_E0 io hw) l)

theorem map_mem_Eur (σ : WCb l →ₐ[ℤ_[l]] WCb l) (hσ : ∀ x ∈ E0 io, σ x ∈ E0 io) {x : WCb l}
    (hx : x ∈ Eur io) : σ x ∈ Eur io := by
  refine map_mem_clAlg (σ : WCb l →+* WCb l) (fun y hy => ?_) hx
  refine (Algebra.adjoin_le (S := (Eur io).comap σ) ?_) hy
  rintro y ⟨f, hf, hc, h0, hu⟩
  refine simpleRoots_subset_Eur io ⟨f.map (σ : WCb l →+* WCb l), hf.map _, fun i => ?_, ?_, ?_⟩
  · rw [Polynomial.coeff_map]; exact hσ _ (hc i)
  · have := Polynomial.eval_map_apply (f := (σ : WCb l →+* WCb l)) (p := f) y
    rw [h0, map_zero] at this
    exact this
  · have := Polynomial.eval_map_apply (f := (σ : WCb l →+* WCb l)) (p := f.derivative) y
    rw [Polynomial.derivative_map]
    exact this ▸ hu.map _

variable (io)

theorem teichmuller_mem_Eur {a : Cb l} {d : ℕ} (hd : 0 < d) (ha : a ^ l ^ d = a) :
    WittVector.teichmuller l a ∈ Eur io := by
  have h1 : 1 < l ^ d := Nat.one_lt_pow hd.ne' (Fact.out : l.Prime).one_lt
  refine simpleRoots_subset_Eur io ⟨Polynomial.X ^ l ^ d - Polynomial.X,
    Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast h1), fun i => ?_, ?_, ?_⟩
  · have h := coeff_mem (E0 io) (E0 io).one_mem (l ^ d) 1 i
    rwa [pow_one, map_one, one_mul] at h
  · rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, ← map_pow, ha, sub_self]
  · apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [← WittVector.constantCoeff_apply, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_X, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_one, map_sub, map_mul, map_natCast, map_one, Nat.cast_pow, CharP.cast_eq_zero,
      zero_pow hd.ne', zero_mul, zero_sub]
    exact neg_ne_zero.2 one_ne_zero

theorem mem_Eur_of_teichmuller_series (a : ℕ → Cb l) (ha : ∀ n, ∃ d, 0 < d ∧ a n ^ l ^ d = a n) (x : WCb l)
    (hx : ∀ k, (l : WCb l) ^ k ∣ x - ∑ n ∈ Finset.range k, (l : WCb l) ^ n * WittVector.teichmuller l (a n)) :
    x ∈ Eur io := by
  rw [← clAlg_Eur]
  refine mem_clAlg.2 fun k => ⟨_, (Eur io).sum_mem fun n _ => ?_, hx k⟩
  obtain ⟨d, hd, h⟩ := ha n
  exact (Eur io).mul_mem ((Eur io).pow_mem (natCast_mem _ l) n) (teichmuller_mem_Eur io hd h)

end Rings

section Module

private theorem map_smul_gen {O R M : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M]
    [Module O M] (f : R →ₐ[O] R) (g : M →ₗ[O] M) (r : R) (y : R ⊗[O] M) :
    TensorProduct.map f.toLinearMap g (r • y) = f r • TensorProduct.map f.toLinearMap g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem smul_mem_gen {Z O W M : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] [AddCommGroup M] [Module O M] (S : Subalgebra Z W) (o : O) {w : W} (hw : w ∈ S)
    {z : (O ⊗[Z] W) ⊗[O] M}
    (hz : z ∈ Submodule.span O {z | ∃ w ∈ S, ∃ t : M, z = ((1 : O) ⊗ₜ[Z] w) ⊗ₜ[O] t}) :
    (o ⊗ₜ[Z] w : O ⊗[Z] W) • z ∈ Submodule.span O {z | ∃ w ∈ S, ∃ t : M, z = ((1 : O) ⊗ₜ[Z] w) ⊗ₜ[O] t} := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w', hw', t, rfl⟩ := hz
    have h : (o ⊗ₜ[Z] w : O ⊗[Z] W) • (((1 : O) ⊗ₜ[Z] w') ⊗ₜ[O] t) = o • (((1 : O) ⊗ₜ[Z] (w * w')) ⊗ₜ[O] t) := by
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul,
        smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
    rw [h]
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨_, S.mul_mem hw hw', t, rfl⟩)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

private theorem map_map_gen {Z O W M : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] [AddCommGroup M] [Module O M] {a b c d : W →ₐ[Z] W} {f g h k : M →ₗ[O] M}
    (h1 : ∀ w, a (b w) = c (d w)) (h2 : ∀ t, f (g t) = h (k t)) (y : (O ⊗[Z] W) ⊗[O] M) :
    TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id O O) a).toLinearMap f
      (TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id O O) b).toLinearMap g y) =
    TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id O O) c).toLinearMap h
      (TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id O O) d).toLinearMap k y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r t =>
    simp only [TensorProduct.map_tmul, h2]
    congr 1
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul o w => simp [h1]

private theorem map_comm_gen {O R M M' : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M]
    [Module O M] [AddCommGroup M'] [Module O M'] (a : R →ₐ[O] R) (f : M →ₗ[O] M') (g : M →ₗ[O] M)
    (g' : M' →ₗ[O] M') (h : ∀ t, f (g t) = g' (f t)) (y : R ⊗[O] M) :
    TensorProduct.map a.toLinearMap g' (TensorProduct.map LinearMap.id f y) =
      TensorProduct.map LinearMap.id f (TensorProduct.map a.toLinearMap g y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r t => simp [h]

@[reducible] def leftModuleGen (O R M : Type) [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M]
    [Module O M] : Module R (R ⊗[O] M) := inferInstance

@[reducible] def leftSMulGen (O R M : Type) [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M]
    [Module O M] : SMul R (R ⊗[O] M) := inferInstance

variable {G : Type} [Group G] [TopologicalSpace G]

scoped instance smulTW (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) : SMul (RW LL) (TW (RW LL) T) :=
  leftSMulGen _ _ _

scoped instance moduleTW (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    Module (RW LL) (TW (RW LL) T) :=
  leftModuleGen _ _ _

def EurT (LL : FinExt l) (io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    Submodule ↥(OL LL) (TW (RW LL) T) :=
  Submodule.span ↥(OL LL) {z | ∃ w ∈ Eur io, ∃ t : ↥T.L.T,
    z = ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w) ⊗ₜ[↥(OL LL)] t}

variable {LL : FinExt l} {io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l} {T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)}

theorem tmul_mem_EurT {w : WCb l} (hw : w ∈ Eur io) (t : ↥T.L.T) :
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w) ⊗ₜ[↥(OL LL)] t ∈ EurT LL io T :=
  Submodule.subset_span ⟨w, hw, t, rfl⟩

theorem map_mem_EurT {T' : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} (σ : WCb l →ₐ[ℤ_[l]] WCb l)
    (hσ : ∀ x ∈ Eur io, σ x ∈ Eur io) (f : ↥T.L.T →ₗ[↥(OL LL)] ↥T'.L.T) {z : TW (RW LL) T}
    (hz : z ∈ EurT LL io T) :
    TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id ↥(OL LL) ↥(OL LL)) σ).toLinearMap f z ∈
      EurT LL io T' := by
  refine (Submodule.span_le (p := (EurT LL io T').comap (TensorProduct.map
    (Algebra.TensorProduct.map (AlgHom.id ↥(OL LL) ↥(OL LL)) σ).toLinearMap f))).2 ?_ hz
  rintro _ ⟨w, hw, t, rfl⟩
  exact tmul_mem_EurT (hσ w hw) (f t)

theorem smul_mem_EurT (o : ↥(OL LL)) {w : WCb l} (hw : w ∈ Eur io) {z : TW (RW LL) T}
    (hz : z ∈ EurT LL io T) : (o ⊗ₜ[ℤ_[l]] w : RW LL) • z ∈ EurT LL io T :=
  smul_mem_gen (Eur io) o hw hz

end Module

def FonD {P : LocPrime l} (AI : LocAinf l P) (K LL : FinExt l)
    (io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) :
    Submodule ↥(OL LL) (TW (RW LL) T) :=
  EurT LL io T ⊓ ⨅ g : {g : ↥(GK K) // P.χQ (g : GQ l) = 1},
    LinearMap.eqLocus (TWact (AI.gRW LL (g.1 : GQ l)) T g.1)
      (LinearMap.id : TW (RW LL) T →ₗ[↥(OL LL)] TW (RW LL) T)

section Fon

variable {P : LocPrime l} {AI : LocAinf l P} {K LL : FinExt l}
  {io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l} {T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)}

theorem mem_FonD {z : TW (RW LL) T} : z ∈ FonD AI K LL io T ↔ z ∈ EurT LL io T ∧
    ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → TWact (AI.gRW LL (g : GQ l)) T g z = z := by
  simp only [FonD, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply,
    Subtype.forall]

set_option synthInstance.maxHeartbeats 200000 in

theorem tmul_mem_FonD {w : WCb l} (hw : w ∈ Eur io)
    (hwH : ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → AI.actWCbHom (g : GQ l) w = w) {t : ↥T.L.T}
    (ht : ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → T.actT g t = t) :
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w) ⊗ₜ[↥(OL LL)] t ∈ FonD AI K LL io T :=
  mem_FonD.2 ⟨tmul_mem_EurT hw t, fun g hg => by
    have h1 : AI.gRW LL (g : GQ l) ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w :=
      (Algebra.TensorProduct.map_tmul _ _ 1 w).trans (congrArg ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] ·) (hwH g hg))
    exact (TensorProduct.map_tmul _ _ _ t).trans (congrArg₂ (· ⊗ₜ[↥(OL LL)] ·) h1 (ht g hg))⟩

theorem smul_mem_FonD (o : ↥(OL LL)) {w : WCb l} (hw : w ∈ Eur io)
    (hwH : ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → AI.actWCbHom (g : GQ l) w = w) {z : TW (RW LL) T}
    (hz : z ∈ FonD AI K LL io T) : (o ⊗ₜ[ℤ_[l]] w : RW LL) • z ∈ FonD AI K LL io T := by
  refine mem_FonD.2 ⟨smul_mem_EurT o hw (mem_FonD.1 hz).1, fun g hg => ?_⟩
  refine (map_smul_gen (AI.gRW LL (g : GQ l)) (T.actT g) _ z).trans ?_
  have h1 : AI.gRW LL (g : GQ l) (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] w :=
    (Algebra.TensorProduct.map_tmul _ _ o w).trans (congrArg (o ⊗ₜ[ℤ_[l]] ·) (hwH g hg))
  exact congrArg₂ (fun (r : RW LL) (y : TW (RW LL) T) => r • y) h1 ((mem_FonD.1 hz).2 g hg)

theorem phi_mem_FonD (hφ : ∀ x ∈ E0 io, frobW l x ∈ E0 io) {z : TW (RW LL) T}
    (hz : z ∈ FonD AI K LL io T) : TWmap (φRW LL) T z ∈ FonD AI K LL io T := by
  refine mem_FonD.2 ⟨map_mem_EurT (frobW l) (fun _ => map_mem_Eur _ hφ) _ (mem_FonD.1 hz).1, fun g hg => ?_⟩
  refine (map_map_gen (a := (AI.actWCbHom (g : GQ l)).toAlgHom) (b := frobW l) (c := frobW l)
    (d := (AI.actWCbHom (g : GQ l)).toAlgHom) (f := T.actT g) (g := LinearMap.id) (h := LinearMap.id)
    (k := T.actT g) (fun w => ?_) (fun _ => rfl) z).trans
    (congrArg (TWmap (φRW LL) T) ((mem_FonD.1 hz).2 g hg))
  ext n
  exact map_pow (autCb l (AI.actT g)) (w.coeff n) l

theorem act_mem_EurT (g : ↥(GK K)) (hg : ∀ x ∈ E0 io, AI.actWCbHom (g : GQ l) x ∈ E0 io) {z : TW (RW LL) T}
    (hz : z ∈ EurT LL io T) : TWact (AI.gRW LL (g : GQ l)) T g z ∈ EurT LL io T :=
  map_mem_EurT (T' := T) (AI.actWCbHom (g : GQ l)).toAlgHom
    (fun _ hx => map_mem_Eur (AI.actWCbHom (g : GQ l)).toAlgHom hg hx) (T.actT g) hz

private theorem act_act_TW {g h h' : ↥(GK K)} (e : h * g = g * h') (z : TW (RW LL) T) :
    TWact (AI.gRW LL (h : GQ l)) T h (TWact (AI.gRW LL (g : GQ l)) T g z) =
      TWact (AI.gRW LL (g : GQ l)) T g (TWact (AI.gRW LL (h' : GQ l)) T h' z) := by
  have h1 : ∀ w, (AI.actWCbHom (h : GQ l)).toAlgHom ((AI.actWCbHom (g : GQ l)).toAlgHom w) =
      (AI.actWCbHom (g : GQ l)).toAlgHom ((AI.actWCbHom (h' : GQ l)).toAlgHom w) := fun w => by
    have e' : (h : GQ l) * g = (g : GQ l) * h' := congrArg Subtype.val e
    have := congrArg AI.actWCbHom e'
    rw [map_mul, map_mul] at this
    exact congrArg (fun u : WCb l ≃ₐ[ℤ_[l]] WCb l => u w) this
  have h2 : ∀ t, T.actT h (T.actT g t) = T.actT g (T.actT h' t) := fun t => by
    have := congrArg T.ρ e
    rw [map_mul, map_mul] at this
    exact Subtype.ext (congrArg (fun u : Module.End ↥LL.1 T.V => u t) this)
  exact map_map_gen h1 h2 z

theorem act_mem_FonD (g : ↥(GK K)) (hg : ∀ x ∈ E0 io, AI.actWCbHom (g : GQ l) x ∈ E0 io) {z : TW (RW LL) T}
    (hz : z ∈ FonD AI K LL io T) : TWact (AI.gRW LL (g : GQ l)) T g z ∈ FonD AI K LL io T := by
  refine mem_FonD.2 ⟨act_mem_EurT g hg (mem_FonD.1 hz).1, fun h hh => ?_⟩
  have e : h * g = g * (g⁻¹ * h * g) := by group
  have hχ : P.χQ ((g⁻¹ * h * g : ↥(GK K)) : GQ l) = 1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, hh, mul_one, ← map_mul, ← Subgroup.coe_mul,
      inv_mul_cancel, Subgroup.coe_one, map_one]
  exact (act_act_TW e z).trans (congrArg (TWact (AI.gRW LL (g : GQ l)) T g) ((mem_FonD.1 hz).2 _ hχ))

theorem map_mem_FonD {T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)} (f : ↥T.L.T →ₗ[↥(OL LL)] ↥T'.L.T)
    (hf : ∀ g t, f (T.actT g t) = T'.actT g (f t)) {z : TW (RW LL) T} (hz : z ∈ FonD AI K LL io T) :
    TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) f z ∈ FonD AI K LL io T' := by
  refine mem_FonD.2 ⟨?_, fun g hg => ?_⟩
  · refine (Submodule.span_le (p := (EurT LL io T').comap (TensorProduct.map
      (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) f))).2 ?_ (mem_FonD.1 hz).1
    rintro _ ⟨w, hw, t, rfl⟩
    exact tmul_mem_EurT hw (f t)
  · refine Eq.trans ?_ (congrArg (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) f)
      ((mem_FonD.1 hz).2 g hg))
    exact map_comm_gen (AI.gRW LL (g : GQ l)) f (T.actT g) (T'.actT g) (hf g) z

end Fon

example : phi 2 ℤ_[2] PowerSeries.X = PowerSeries.X ^ 2 + 2 * PowerSeries.X := by rw [phi_X]; ring

example : QQ 2 ℤ_[2] 2 = PowerSeries.X ^ 2 + 2 * PowerSeries.X + 2 := by
  simp [QQ, XX, Finset.sum_range_succ]; ring

example (io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l) (a : Cb l) (ha : a ^ l ^ 2 = a) :
    (l : WCb l) * WittVector.teichmuller l a ∈ Eur io :=
  (Eur io).mul_mem (natCast_mem _ l) (teichmuller_mem_Eur io two_pos ha)

example (O : Type) [CommRing O] [Algebra ℤ_[l] O] (n : ℕ) :
    phiEE l O n (toEE l O n letπ) = (1 + toEE l O n letπ) ^ l - 1 := by
  have h : letφ (phi l O) (letπ : LetA O n) = (1 + letπ) ^ l - 1 := funext fun _ => phi_X l O
  rw [phiEE_toEE, h]; simp

end GlobalTheory.Cyc
