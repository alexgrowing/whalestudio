import Mathlib
import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstantCoeffTeichSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsPolynomialSubMem
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism
open scoped Formalism.Per

namespace GlobalTheory.BKReal

section General

def liftInj {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* C) (g : B →+* C)
    (hg : Function.Injective g) (h : ∀ x, ∃ y, g y = f x) : A →+* B where
  toFun x := (h x).choose
  map_one' := hg (by rw [(h 1).choose_spec, map_one, map_one])
  map_mul' x y := hg (by
    rw [map_mul g, (h _).choose_spec, (h _).choose_spec, (h _).choose_spec, map_mul])
  map_zero' := hg (by rw [(h 0).choose_spec, map_zero, map_zero])
  map_add' x y := hg (by
    rw [map_add g, (h _).choose_spec, (h _).choose_spec, (h _).choose_spec, map_add])

theorem liftInj_spec {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* C) (g : B →+* C)
    (hg : Function.Injective g) (h : ∀ x, ∃ y, g y = f x) (x : A) : g (liftInj f g hg h x) = f x :=
  (h x).choose_spec

theorem isAdicComplete_of_pow_le {A : Type} [CommRing A] {I J : Ideal A} {N : ℕ} (h : I ^ (N + 1) ≤ J)
    (hJ : J ≤ I) [IsAdicComplete I A] : IsAdicComplete J A where
  haus' x hx := IsHausdorff.haus' (I := I) x fun n => by
    have := hx n
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this ⊢
    exact Ideal.pow_right_mono hJ n this
  prec' f hf := by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) f fun {m n} hmn => by
      simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact Ideal.pow_right_mono hJ m (hf hmn)
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL
    refine ⟨L, fun n => ?_⟩
    have h1 := hf (m := n) (n := (N + 1) * n) (Nat.le_mul_of_pos_left n N.succ_pos)
    have h2 := hL ((N + 1) * n)
    rw [pow_mul] at h2
    simpa using add_mem h1 (Ideal.pow_right_mono h n h2)

theorem ringHom_ext_of_sep {R B : Type} [CommRing R] [CommRing B] (f g : R⟦X⟧ →+* B)
    (hC : ∀ r, f (C r) = g (C r)) (hX : f X = g X) (hs : ∀ x : B, (∀ n, f X ^ n ∣ x) → x = 0) : f = g := by
  letI : Algebra R B := (f.comp C).toAlgebra
  exact congrArg AlgHom.toRingHom (GlobalTheory.Cyc.IoMap.algHom_unique (R := R)
    { toRingHom := f, commutes' := fun _ => rfl } { toRingHom := g, commutes' := fun r => (hC r).symm } hX hs)

end General

variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ)

def resSub : Subring (OCb l) := RingHom.eqLocus (iterateFrobenius (OCb l) l a) (RingHom.id _)

variable {l a} in

theorem mem_resSub {x : OCb l} : x ∈ resSub l a ↔ x ^ l ^ a = x := Iff.rfl

variable [NeZero a]

theorem one_lt_pow_l : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) hl.out.one_lt

theorem isUnit_resSub (x : ↥(resSub l a)) : IsUnit x ∨ x = 0 := by
  refine (eq_or_ne x 0).symm.imp (fun hx => ?_) id
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt (one_lt_pow_l l a)
  have h : x ^ l ^ a = x := Subtype.ext x.2
  refine IsUnit.of_mul_eq_one (x ^ m) (mul_left_cancel₀ hx ?_)
  rw [hm] at h
  linear_combination h

def Fq : Type := ↥(resSub l a)

instance : CommRing (Fq l a) := inferInstanceAs (CommRing ↥(resSub l a))

instance : Nontrivial (Fq l a) := inferInstanceAs (Nontrivial ↥(resSub l a))

instance : Field (Fq l a) := Field.ofIsUnitOrEqZero (isUnit_resSub l a)

def Fq.val : Fq l a →+* OCb l := (resSub l a).subtype

theorem Fq.val_injective : Function.Injective (Fq.val l a) := Subtype.val_injective

variable {l a} in

theorem Fq.pow_card (x : Fq l a) : x ^ l ^ a = x :=
  (Fq.val_injective l a) (by rw [map_pow]; exact x.2)

instance : CharP (Fq l a) l := (Fq.val l a).charP (Fq.val_injective l a) l

theorem finite_sol (R : Type) [CommRing R] [IsDomain R] : {x : R | x ^ l ^ a = x}.Finite := by
  have h : (Polynomial.X ^ l ^ a - Polynomial.X : Polynomial R) ≠ 0 := fun h => by
    have := congrArg (Polynomial.coeff · 1) h
    simp [Polynomial.coeff_X_pow, (one_lt_pow_l l a).ne] at this
  refine (Polynomial.finite_setOf_isRoot h).subset fun x hx => ?_
  simpa [sub_eq_zero] using hx

instance : Finite (Fq l a) := (finite_sol l a (OCb l)).to_subtype

theorem exists_gen : ∃ (z : Fq l a) (ω : Om l), IsPrimitiveRoot ω (l ^ a - 1) ∧
    IsTiltOf ω (l ^ a - 1) (Fq.val l a z) ∧ ∀ x : Fq l a, x ≠ 0 → ∃ k : ℕ, x = z ^ k := by
  have h1 := one_lt_pow_l l a
  have h0 : 0 < l ^ a - 1 := by omega
  have : NeZero (l ^ a - 1) := ⟨h0.ne'⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ a - 1)
  have hd : ¬ l ∣ l ^ a - 1 := fun h => hl.out.not_dvd_one
    ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne a))).1 h)
  obtain ⟨x, hx⟩ := GlobalTheory.MemLoc.exists_isTiltOf ω _ h0 hd hω.pow_eq_one
  have h2 : ∀ y : OCb l, y ^ l ^ a = y ^ (l ^ a - 1) * y := fun y => by
    rw [← pow_succ, Nat.sub_add_cancel h1.le]
  have h3 := GlobalTheory.MemLoc.IsTiltOf.pow_eq_one hx
  have h4 : IsPrimitiveRoot x (l ^ a - 1) := ⟨h3, fun k hk => hω.dvd_of_pow_eq_one k (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    have h5 := congrArg (fun y : OCb l => ((y.untilt : OC l) : ℂ_[l])) hk
    simp only [map_pow, map_one, SubmonoidClass.coe_pow, GlobalTheory.MemLoc.IsTiltOf.untilt_eq hx] at h5 ⊢
    exact h5)⟩
  refine ⟨⟨x, by rw [mem_resSub, h2, h3, one_mul]⟩, ω, hω, hx, fun y hy => ?_⟩
  have hy0 : Fq.val l a y ≠ 0 := (map_ne_zero _).2 hy
  have h6 : Fq.val l a y ^ (l ^ a - 1) = 1 :=
    mul_right_cancel₀ hy0 (by rw [← h2, one_mul, ← map_pow, Fq.pow_card])
  obtain ⟨k, -, hk⟩ := h4.eq_pow_of_pow_eq_one h6
  exact ⟨k, (Fq.val_injective l a) (hk.symm.trans
    (map_pow (Fq.val l a) (⟨x, by rw [mem_resSub, h2, h3, one_mul]⟩ : ↥(resSub l a)) k).symm)⟩

theorem card_Fq : Nat.card (Fq l a) = l ^ a := by
  obtain ⟨z, ω, hω, hz, h⟩ := exists_gen l a
  have h1 := one_lt_pow_l l a
  have hz0 : z ≠ 0 := fun h0 => by
    have := GlobalTheory.MemLoc.IsTiltOf.pow_eq_one hz
    rw [h0, map_zero, zero_pow (by omega)] at this
    exact zero_ne_one this
  have h2 : IsPrimitiveRoot (Units.mk0 z hz0) (l ^ a - 1) := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    refine ⟨Fq.val_injective l a (by rw [map_pow, map_one]; exact GlobalTheory.MemLoc.IsTiltOf.pow_eq_one hz),
      fun k hk => hω.dvd_of_pow_eq_one k ((algebraMap (Om l) ℂ_[l]).injective ?_)⟩
    have h5 := congrArg (fun y : Fq l a => (((Fq.val l a y).untilt : OC l) : ℂ_[l])) hk
    simp only [map_pow, map_one, SubmonoidClass.coe_pow, Units.val_mk0,
      GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz] at h5 ⊢
    exact h5
  have h3 : Nat.card (Fq l a)ˣ = l ^ a - 1 := by
    rw [h2.eq_orderOf]
    refine (orderOf_eq_card_of_forall_mem_powers fun x => ?_).symm
    obtain ⟨k, hk⟩ := h x x.ne_zero
    exact ⟨k, Units.ext (by simp [hk])⟩
  rw [Nat.card_units] at h3
  have := Nat.card_pos (α := Fq l a)
  omega

abbrev Wq : Type := WittVector l (Fq l a)

instance : Algebra ℤ_[l] (Wq l a) := (zlW l (Fq l a)).toAlgebra

def wA : Wq l a →ₐ[ℤ_[l]] Ainf l where
  toRingHom := WittVector.map (Fq.val l a)
  commutes' := map_zlW l _

theorem wA_injective : Function.Injective (wA l a) := WittVector.map_injective _ (Fq.val_injective l a)

theorem wA_teich (x : Fq l a) :
    wA l a (WittVector.teichmuller l x) = WittVector.teichmuller l (Fq.val l a x) :=
  WittVector.map_teichmuller l _ x

def sigma : Wq l a ≃ₐ[ℤ_[l]] Wq l a := mapAlgEquivW l (frobeniusEquiv (Fq l a) l)

theorem coeff_sigma (w : Wq l a) (n : ℕ) : (sigma l a w).coeff n = w.coeff n ^ l := rfl

theorem coeff_sigma_pow (k : ℕ) (w : Wq l a) (n : ℕ) : ((sigma l a ^ k) w).coeff n = w.coeff n ^ l ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, coeff_sigma, ih, ← pow_mul, ← pow_succ]

theorem sigma_pow_eq_one : sigma l a ^ a = 1 :=
  AlgEquiv.ext fun w => WittVector.ext fun n => (coeff_sigma_pow l a a w n).trans (Fq.pow_card _)

theorem sigma_pow_teich (k : ℕ) (x : Fq l a) :
    (sigma l a ^ k) (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l ^ k := by
  rw [← map_pow]
  refine WittVector.ext fun n => ?_
  rw [coeff_sigma_pow]
  rcases n with _ | n
  · rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
  · rw [WittVector.teichmuller_coeff_pos _ _ _ n.succ_pos, WittVector.teichmuller_coeff_pos _ _ _ n.succ_pos,
      zero_pow (pow_pos hl.out.pos k).ne']

theorem wA_sigma (w : Wq l a) : wA l a (sigma l a w) = WittVector.frobenius (wA l a w) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  exact WittVector.ext fun n => map_pow (Fq.val l a) (w.coeff n) l

theorem span_teich : Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l a → Wq l a)) = ⊤ := by
  classical
  have := Fintype.ofFinite (Fq l a)
  have hc : IsAdicComplete (Ideal.span {(l : ℤ_[l])}) (Wq l a) := by
    rw [← IsAdicComplete.map_algebraMap_iff (S := Wq l a), Ideal.map_span, Set.image_singleton, map_natCast]
    infer_instance
  have hz : IsAdicComplete (Ideal.span {(l : ℤ_[l])}) ℤ_[l] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]; infer_instance
  have hp : IsPrecomplete (Ideal.span {(l : ℤ_[l])}) (Fq l a → ℤ_[l]) :=
    GlobalTheory.CompleteBaseChange.isPrecomplete_pi _ (Submodule.fg_span_singleton _)
  rw [← Fintype.range_linearCombination, LinearMap.range_eq_top]
  refine surjective_of_mkQ_comp_surjective (I := Ideal.span {(l : ℤ_[l])}) fun G => ?_
  obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ G
  refine ⟨Pi.single (g.coeff 0) 1, ?_⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    Fintype.linearCombination_apply_single, one_smul]
  have h0 : WittVector.teichmuller l (g.coeff 0) - g ∈ Ideal.span {(l : Wq l a)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub]
    simp [WittVector.constantCoeff_apply]
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 h0
  have h1 : (l : Wq l a) * u = (l : ℤ_[l]) • u := by rw [Algebra.smul_def, map_natCast]
  rw [hu, h1]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem dvd_of_not_isUnit {w : Wq l a} (h : ¬ IsUnit w) : (l : Wq l a) ∣ w := by
  rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker]
  by_contra h0
  exact h (WittVector.isUnit_of_coeff_zero_ne_zero w h0)

omit [NeZero a] in

def Kunr : IntermediateField ℚ_[l] (Om l) := IntermediateField.adjoin ℚ_[l] {x | x ^ l ^ a = x}

def unrExt : FinExt l :=
  ⟨Kunr l a, by
    have := (finite_sol l a (Om l)).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩

theorem Kunr_le_Kur : Kunr l a ≤ MaximalUnramifiedExtension l := by
  refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
  rcases eq_or_ne x 0 with rfl | h0
  · exact zero_mem _
  have h1 := one_lt_pow_l l a
  refine IntermediateField.subset_adjoin _ _ ⟨l ^ a - 1, by omega, fun h => hl.out.not_dvd_one
    ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne a))).1 h), mul_right_cancel₀ h0 ?_⟩
  rw [← pow_succ, Nat.sub_add_cancel h1.le, one_mul]
  exact hx

structure PiSys (l : ℕ) [Fact l.Prime] (e : ℕ) where

  seq : ℕ → Om l
  seq_succ : ∀ n, seq (n + 1) ^ l = seq n
  seq_zero : seq 0 ^ e = -(l : Om l)

instance (e : ℕ) [NeZero e] : Nonempty (PiSys l e) := by
  choose r hr using fun x : Om l => IsAlgClosed.exists_pow_nat_eq x hl.out.pos
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (-(l : Om l)) (NeZero.pos e)
  exact ⟨⟨fun n => r^[n] π, fun n => by rw [Function.iterate_succ_apply', hr], hπ⟩⟩

namespace PiSys

variable {l} {e : ℕ} (ϖ : PiSys l e)

theorem seq_pow (n : ℕ) : ϖ.seq n ^ l ^ n = ϖ.seq 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ϖ.seq_succ, ih]

theorem seq_pow_mul (n : ℕ) : ϖ.seq n ^ (l ^ n * e) = -(l : Om l) := by
  rw [pow_mul, seq_pow, ϖ.seq_zero]

theorem seq_ne_zero [NeZero e] (n : ℕ) : ϖ.seq n ≠ 0 := fun h => by
  have := ϖ.seq_pow_mul n
  rw [h, zero_pow (mul_ne_zero (pow_pos hl.out.pos n).ne' (NeZero.ne e)), eq_comm, neg_eq_zero] at this
  exact Nat.cast_ne_zero.2 hl.out.ne_zero this

theorem norm_seq_lt_one (n : ℕ) : ‖(ϖ.seq n : ℂ_[l])‖ < 1 := by
  by_contra h
  have h1 := congrArg (fun x : Om l => ‖algebraMap (Om l) ℂ_[l] x‖) (ϖ.seq_pow_mul n)
  simp only [map_pow, norm_pow, map_neg, norm_neg, map_natCast] at h1
  exact absurd (h1 ▸ one_le_pow₀ (not_lt.1 h)) (not_le.2 GlobalTheory.RingBasics.norm_p_lt)

def seqO (n : ℕ) : OC l := ⟨(ϖ.seq n : ℂ_[l]), (GlobalTheory.RingBasics.mem_OC _).2 (ϖ.norm_seq_lt_one n).le⟩

@[simp] theorem coe_seqO (n : ℕ) : (ϖ.seqO n : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ϖ.seq n) := rfl

theorem seqO_succ (n : ℕ) : ϖ.seqO (n + 1) ^ l = ϖ.seqO n :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow, coe_seqO, ← map_pow, ϖ.seq_succ, coe_seqO])

theorem seqO_zero : ϖ.seqO 0 ^ e = -(l : OC l) :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow, coe_seqO, ← map_pow, ϖ.seq_zero]; simp)

def flat : OCb l :=
  (⟨fun n => Ideal.Quotient.mk _ (ϖ.seqO n), fun n => by rw [← map_pow, seqO_succ]⟩ :
    Perfection (ModP (OC l) l) l)

theorem coeff_flat (n : ℕ) :
    PreTilt.coeff n ϖ.flat = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (ϖ.seqO n) := rfl

theorem untilt_flat : ϖ.flat.untilt = ϖ.seqO 0 := by
  refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : OC l)}) fun n => ⟨ϖ.seqO n, rfl, ?_⟩
  have : ϖ.seqO n ^ l ^ n = ϖ.seqO 0 :=
    Subtype.ext (by rw [SubmonoidClass.coe_pow, coe_seqO, ← map_pow, ϖ.seq_pow, coe_seqO])
  rw [this]

def teich : Ainf l := WittVector.teichmuller l ϖ.flat

theorem theta_teich : Per.θ l ϖ.teich = ϖ.seqO 0 :=
  (WittVector.fontaineTheta_teichmuller _).trans ϖ.untilt_flat

theorem flat_ne_zero [NeZero e] : ϖ.flat ≠ 0 := fun h => by
  have h1 := ϖ.theta_teich
  rw [teich, h, WittVector.teichmuller_zero, map_zero] at h1
  exact ϖ.seq_ne_zero 0 ((map_eq_zero (algebraMap (Om l) ℂ_[l])).1 (congrArg Subtype.val h1).symm)

theorem not_isUnit_seqO (n : ℕ) : ¬ IsUnit (ϖ.seqO n) := fun h => by
  obtain ⟨u, hu⟩ := h.exists_right_inv
  have h1 := congrArg (fun x : OC l => ‖(x : ℂ_[l])‖) hu
  simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h1
  have h2 := (GlobalTheory.RingBasics.mem_OC _).1 u.2
  have h3 : ‖(ϖ.seqO n : ℂ_[l])‖ < 1 := ϖ.norm_seq_lt_one n
  nlinarith [norm_nonneg (u : ℂ_[l]), norm_nonneg (ϖ.seqO n : ℂ_[l])]

theorem not_isUnit_teich : ¬ IsUnit ϖ.teich := fun h =>
  ϖ.not_isUnit_seqO 0 (ϖ.theta_teich ▸ h.map (Per.θ l))

theorem isUnit_inclW_teich [NeZero e] : IsUnit (inclW l ϖ.teich) :=
  WittVector.isUnit_of_coeff_zero_ne_zero _ fun h => ϖ.flat_ne_zero
    (IsFractionRing.injective (OCb l) (Cb l) (h.trans (map_zero _).symm))

theorem complete_teich : IsAdicComplete (Ideal.span {ϖ.teich}) (Ainf l) :=
  (GlobalTheory.Per.AinfComplete.main l _ ϖ.not_isUnit_teich).2

theorem sep_teich (x : Ainf l) (h : ∀ n, ϖ.teich ^ n ∣ x) : x = 0 :=
  have := ϖ.complete_teich
  GlobalTheory.Per.AinfComplete.eq_zero_of_haus _ x fun n => Ideal.mem_span_singleton.2 (h n)

def field : FinExt l :=
  ⟨Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq 0}, by
    have : FiniteDimensional ℚ_[l] (Kunr l a) := (unrExt l a).2
    have := IntermediateField.adjoin.finiteDimensional (K := ℚ_[l]) (Algebra.IsIntegral.isIntegral (ϖ.seq 0))
    infer_instance⟩

theorem pi_mem_field : ϖ.seq 0 ∈ (ϖ.field a).1 :=
  (le_sup_right : _ ≤ Kunr l a ⊔ _) (IntermediateField.mem_adjoin_simple_self _ _)

theorem Kunr_le_field : Kunr l a ≤ (ϖ.field a).1 := le_sup_left

theorem gal_pi (g : ↥(GK (ϖ.field a))) : (g : GQ l) (ϖ.seq 0) = ϖ.seq 0 :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (ϖ.pi_mem_field a)

def Kinf : IntermediateField ℚ_[l] (Om l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range fun n => ϖ.seq n ^ e)

def fieldInf : IntermediateField ℚ_[l] (Om l) :=
  (ϖ.field a).1 ⊔ IntermediateField.adjoin ℚ_[l] (Set.range ϖ.seq)

theorem field_le_fieldInf : (ϖ.field a).1 ≤ ϖ.fieldInf a := le_sup_left

theorem seq_mem_fieldInf (n : ℕ) : ϖ.seq n ∈ ϖ.fieldInf a :=
  (le_sup_right : _ ≤ (ϖ.field a).1 ⊔ _) (IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩)

theorem fixing_fieldInf_le : (ϖ.fieldInf a).fixingSubgroup ≤ GK (ϖ.field a) :=
  IntermediateField.fixingSubgroup_antitone (ϖ.field_le_fieldInf a)

def GKinf : Subgroup (GQ l) := ϖ.Kinf.fixingSubgroup

def GfieldInf : Subgroup (GQ l) := (ϖ.fieldInf a).fixingSubgroup

theorem exists_ev : ∃ f : (Wq l a)⟦X⟧ →+* Ainf l, f X = ϖ.teich ∧ ∀ w, f (C w) = wA l a w := by
  letI : Algebra (Wq l a) (Ainf l) := (wA l a).toRingHom.toAlgebra
  have := ϖ.complete_teich
  obtain ⟨f, hf⟩ := GlobalTheory.Cyc.IoMap.algHom_exists (R := Wq l a) ϖ.teich
    (GlobalTheory.Per.AinfComplete.summ_of_precomplete _) ϖ.sep_teich
  exact ⟨f.toRingHom, hf, f.commutes⟩

def ev : (Wq l a)⟦X⟧ →+* Ainf l := (ϖ.exists_ev a).choose

@[simp] theorem ev_X : ϖ.ev a X = ϖ.teich := (ϖ.exists_ev a).choose_spec.1

@[simp] theorem ev_C (w : Wq l a) : ϖ.ev a (C w) = wA l a w := (ϖ.exists_ev a).choose_spec.2 w

theorem eq_ev (f : (Wq l a)⟦X⟧ →+* Ainf l) (hX : f X = ϖ.teich) (hC : ∀ w, f (C w) = wA l a w) :
    f = ϖ.ev a :=
  ringHom_ext_of_sep _ _ (fun w => by rw [hC, ev_C]) (by rw [hX, ev_X]) (by rw [hX]; exact ϖ.sep_teich)

end PiSys

def frobS : (Wq l a)⟦X⟧ →+* (Wq l a)⟦X⟧ :=
  (PowerSeries.map (sigma l a : Wq l a →+* Wq l a)).comp (PowerSeries.expand l hl.out.ne_zero).toRingHom

@[simp] theorem frobS_X : frobS l a X = X ^ l := by simp [frobS]

@[simp] theorem frobS_C (w : Wq l a) : frobS l a (C w) = C (sigma l a w) := by
  change PowerSeries.map (sigma l a : Wq l a →+* Wq l a) (PowerSeries.expand l hl.out.ne_zero (C w)) = _
  rw [expand_C, map_C]
  rfl

theorem dvd_of_map_eq_zero (g : (Wq l a)⟦X⟧)
    (h : PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l a)) g = 0) : (l : (Wq l a)⟦X⟧) ∣ g := by
  have : ∀ n, (l : Wq l a) ∣ coeff n g := fun n => by
    rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker]
    simpa using congrArg (coeff n) h
  choose c hc using this
  refine ⟨mk c, PowerSeries.ext fun n => ?_⟩
  rw [← map_natCast (C : Wq l a →+* (Wq l a)⟦X⟧), coeff_C_mul, coeff_mk, hc]

theorem l_eq_zero : (l : (Fq l a)⟦X⟧) = 0 := by
  rw [← map_natCast (C : Fq l a →+* (Fq l a)⟦X⟧)]; simp

theorem l_ne_zero : (l : (Wq l a)⟦X⟧) ≠ 0 := fun h =>
  WittVector.p_nonzero l (Fq l a) (by simpa using congrArg constantCoeff h)

theorem frobS_eq (x : (Wq l a)⟦X⟧) : ∃ b, frobS l a x = x ^ l + (l : (Wq l a)⟦X⟧) * b := by
  obtain ⟨b, hb⟩ := dvd_of_map_eq_zero l a (frobS l a x - x ^ l) (by
    rw [map_sub, map_pow, sub_eq_zero]
    have h1 := MvPowerSeries.map_frobenius_expand l hl.out.ne_zero
      (f := PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l a)) x)
    refine Eq.trans ?_ h1
    change _ = PowerSeries.map (frobenius (Fq l a) l) (PowerSeries.expand l hl.out.ne_zero _)
    rw [← PowerSeries.map_expand]
    ext n
    rfl)
  exact ⟨b, by rw [← sub_eq_iff_eq_add']; exact hb⟩

def deltaS : Delta l (Wq l a)⟦X⟧ :=
  Delta.ofLift l (frobS l a) (fun _ hx => (mul_eq_zero.1 hx).resolve_left (l_ne_zero l a)) (frobS_eq l a)

def eis (e : ℕ) : (Wq l a)⟦X⟧ := X ^ e + (l : (Wq l a)⟦X⟧)

variable (e : ℕ) [NeZero e]

theorem constantCoeff_eis : constantCoeff (eis l a e) = (l : Wq l a) := by
  simp [eis, NeZero.ne e]

theorem dvd_or_unit (x : (Wq l a)⟦X⟧) :
    eis l a e ∣ x ∨ ∃ (m : ℕ) (v y : (Wq l a)⟦X⟧), IsUnit v ∧ x = v * X ^ m + eis l a e * y := by
  by_contra h
  rw [not_or] at h
  have key : ∀ m : ℕ, ∃ v y : (Wq l a)⟦X⟧, x = v * X ^ m + eis l a e * y := by
    intro m
    induction m with
    | zero => exact ⟨x, 0, by simp⟩
    | succ m ih =>
      obtain ⟨v, y, hx⟩ := ih
      obtain ⟨c, hc⟩ := dvd_of_not_isUnit l a (w := constantCoeff v)
        fun hu => h.2 ⟨m, v, y, isUnit_iff_constantCoeff.2 hu, hx⟩
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne e)
      have hv := v.eq_X_mul_shift_add_const
      rw [hc, map_mul, map_natCast] at hv
      refine ⟨(mk fun p => coeff (p + 1) v) - X ^ k * C c, y + C c * X ^ m, ?_⟩
      rw [hx]
      conv_lhs => rw [hv]
      rw [eis, hk, Nat.succ_eq_add_one]
      ring
  have hH : IsHausdorff (Ideal.span {(X : (Wq l a)⟦X⟧)}) ((Wq l a)⟦X⟧ ⧸ Ideal.span {eis l a e}) :=
    IsHausdorff.of_isLocalRing _ _ (by
      rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_constantCoeff]; simp)
  refine h.1 (Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 (hH.haus _ fun m => ?_)))
  obtain ⟨v, y, hx⟩ := key m
  have h1 : Ideal.Quotient.mk (Ideal.span {eis l a e}) x =
      (X : (Wq l a)⟦X⟧) ^ m • Ideal.Quotient.mk (Ideal.span {eis l a e}) v := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq,
      Ideal.mem_span_singleton]
    exact ⟨y, by rw [hx]; ring⟩
  rw [SModEq.zero, h1]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) m) Submodule.mem_top

theorem complete_eis :
    IsAdicComplete (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {eis l a e}) (Wq l a)⟦X⟧ := by
  have h := ReciprocityTheory.P1.isAdicComplete_comap_constantCoeff (Ideal.span {(l : Wq l a)})
  rw [← ReciprocityTheory.P1.map_C_sup_span_X, Ideal.map_span, Set.image_singleton, map_natCast] at h
  have h1 : X ^ e ∈ Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {eis l a e} := by
    have : (X : (Wq l a)⟦X⟧) ^ e = eis l a e - l := by rw [eis]; ring
    rw [this]
    exact sub_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  refine isAdicComplete_of_pow_le (I := Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {X}) (N := e) ?_ ?_
  · rw [add_comm]
    refine Ideal.sup_pow_add_le_pow_sup_pow.trans (sup_le (by simp) ?_)
    rwa [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
  · refine sup_le le_sup_left ?_
    rw [Ideal.span_singleton_le_iff_mem]
    exact add_mem (Ideal.mem_sup_right (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
      (NeZero.pos e))) (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))

theorem l_mem_eis : (l : (Wq l a)⟦X⟧) ∈
    Ideal.span {eis l a e} ⊔ (Ideal.span {eis l a e}).map (deltaS l a).φ := by
  obtain ⟨k, hk⟩ : ∃ k, l = k + 2 := ⟨l - 2, by have := hl.out.two_le; omega⟩
  have hu : IsUnit (1 - (-(l : (Wq l a)⟦X⟧)) ^ (k + 1)) := by
    rw [isUnit_iff_constantCoeff]
    refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
    rw [← WittVector.constantCoeff_apply]
    simp only [map_sub, map_one, map_pow, map_neg, map_natCast, CharP.cast_eq_zero, neg_zero,
      zero_pow k.succ_ne_zero, sub_zero]
    exact one_ne_zero
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (X ^ e : (Wq l a)⟦X⟧) (-(l : (Wq l a)⟦X⟧)) l
  have h1 : frobS l a (eis l a e) = ((X : (Wq l a)⟦X⟧) ^ e) ^ l + l := by
    rw [eis, map_add, map_pow, frobS_X, map_natCast, ← pow_mul, ← pow_mul, mul_comm]
  have h2 : (-(l : (Wq l a)⟦X⟧)) ^ l = -(l : (Wq l a)⟦X⟧) * (-(l : (Wq l a)⟦X⟧)) ^ (k + 1) := by
    rw [← pow_succ' (-(l : (Wq l a)⟦X⟧)), show k + 1 + 1 = l by omega]
  have h3 : (l : (Wq l a)⟦X⟧) = eis l a e * (-(v * c)) + v * frobS l a (eis l a e) := by
    rw [h1, eis]
    linear_combination (-(l : (Wq l a)⟦X⟧)) * hv - v * hc - v * h2
  have h4 := Submodule.add_mem_sup (Ideal.mul_mem_right (-(v * c)) _ (Ideal.mem_span_singleton_self (eis l a e)))
    (Ideal.mul_mem_left _ v (Ideal.mem_map_of_mem (frobS l a) (Ideal.mem_span_singleton_self (eis l a e))))
  rwa [← h3] at h4

namespace PiSys

variable {l e} (ϖ : PiSys l e)

omit [NeZero e] in

theorem theta_ev_eis : Per.θ l (ϖ.ev a (eis l a e)) = 0 := by
  rw [eis, map_add, map_pow, ev_X, map_natCast, map_add, map_pow, theta_teich, seqO_zero, map_natCast,
    neg_add_cancel]

theorem theta_ev_eq_zero_iff (x : (Wq l a)⟦X⟧) : Per.θ l (ϖ.ev a x) = 0 ↔ eis l a e ∣ x := by
  refine ⟨fun h => (dvd_or_unit l a e x).resolve_right ?_, ?_⟩
  · rintro ⟨m, v, y, hv, rfl⟩
    simp only [map_add, map_mul, map_pow, ev_X, theta_teich, theta_ev_eis, zero_mul, add_zero] at h
    rcases mul_eq_zero.1 h with h | h
    · exact ((hv.map _).map _).ne_zero h
    · exact ϖ.seq_ne_zero 0 ((map_eq_zero (algebraMap (Om l) ℂ_[l])).1
        (congrArg Subtype.val (eq_zero_of_pow_eq_zero h)))
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_mul, theta_ev_eis, zero_mul]

end PiSys
end GlobalTheory.BKReal
end

section
namespace Bridge.RamInt

open Polynomial

theorem expand {l : ℕ} [Fact l.Prime] (F : IntermediateField ℚ_[l] (PadicAlgCl l))
    (π : PadicAlgCl l) {e : ℕ} (he : e ≠ 0) (hπ : π ^ e = -(l : PadicAlgCl l))
    (x : PadicAlgCl l) (hx : x ∈ F ⊔ IntermediateField.adjoin ℚ_[l] {π}) :
    ∃ c : ℕ → PadicAlgCl l, (∀ i, c i ∈ F) ∧ x = ∑ i ∈ Finset.range e, c i * π ^ i := by
  have hQ : (X ^ e + C (l : F) : F[X]).Monic := monic_X_pow_add_C _ he
  have hQ0 : aeval π (X ^ e + C (l : F) : F[X]) = 0 := by
    simp [hπ]
  have hint : IsIntegral F π := ⟨_, hQ, hQ0⟩
  have hle : F ⊔ IntermediateField.adjoin ℚ_[l] {π} ≤
      (IntermediateField.adjoin F {π}).restrictScalars ℚ_[l] := by
    apply sup_le
    · intro c hc
      exact (IntermediateField.adjoin F {π}).algebraMap_mem ⟨c, hc⟩
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.mem_adjoin_simple_self F π
  have h1 : x ∈ (IntermediateField.adjoin F {π}).toSubalgebra := hle hx
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at h1
  obtain ⟨P, hP⟩ := h1
  have hP' : aeval π P = x := hP
  have hne : (X ^ e + C (l : F) : F[X]) ≠ 1 := by
    intro h
    have := congrArg natDegree h
    rw [natDegree_X_pow_add_C, natDegree_one] at this
    exact he this
  have hdeg : (P %ₘ (X ^ e + C (l : F))).natDegree < e := by
    have := natDegree_modByMonic_lt P hQ hne
    rwa [natDegree_X_pow_add_C] at this
  have h2 : aeval π (P %ₘ (X ^ e + C (l : F))) = x := by
    rw [← hP']
    conv_rhs => rw [← modByMonic_add_div P (X ^ e + C (l : F))]
    rw [map_add, map_mul, hQ0, zero_mul, add_zero]
  refine ⟨fun i => ((P %ₘ (X ^ e + C (l : F))).coeff i : F), fun i => Subtype.property _, ?_⟩
  rw [← h2, aeval_eq_sum_range' hdeg]
  rfl

theorem norm_l_lt {l : ℕ} [Fact l.Prime] : ‖(l : PadicAlgCl l)‖ < 1 := by
  have := PadicAlgCl.norm_extends l (l : ℚ_[l])
  have h : ((l : ℚ_[l]) : PadicAlgCl l) = (l : PadicAlgCl l) := map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l
  rw [h] at this
  rw [this]
  exact Padic.norm_p_lt_one

theorem coeff_le_one {l : ℕ} [hl : Fact l.Prime]
    (π : PadicAlgCl l) {e : ℕ} (he : e ≠ 0) (hπ : π ^ e = -(l : PadicAlgCl l))
    (c : ℕ → PadicAlgCl l) (hc : ∀ i, c i ≠ 0 → ∃ n : ℤ, ‖c i‖ = ‖(l : PadicAlgCl l)‖ ^ n)
    (hx : ‖∑ i ∈ Finset.range e, c i * π ^ i‖ ≤ 1) (i : ℕ) (hi : i < e) : ‖c i‖ ≤ 1 := by
  classical
  by_cases hci : c i = 0
  · simp [hci]
  have hl0 : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  have ht : ‖π‖ ^ e = ‖(l : PadicAlgCl l)‖ := by rw [← norm_pow, hπ, norm_neg]
  have ht0 : 0 < ‖π‖ := by
    rw [norm_pos_iff]
    rintro rfl
    rw [zero_pow he] at hπ
    exact hl0 (neg_eq_zero.mp hπ.symm)
  have ht1 : ‖π‖ < 1 := by
    by_contra h
    have h1 := one_le_pow₀ (not_lt.mp h) (n := e)
    have := norm_l_lt (l := l)
    linarith
  have key : ∀ j, c j ≠ 0 → ∃ n : ℤ, ‖c j‖ = ‖π‖ ^ ((e : ℤ) * n) ∧
      ‖c j * π ^ j‖ = ‖π‖ ^ ((e : ℤ) * n + j) := by
    intro j hj
    obtain ⟨n, hn⟩ := hc j hj
    have h1 : ‖c j‖ = ‖π‖ ^ ((e : ℤ) * n) := by rw [hn, ← ht, zpow_mul, zpow_natCast]
    refine ⟨n, h1, ?_⟩
    rw [norm_mul, norm_pow, h1, zpow_add₀ ht0.ne', zpow_natCast]
  set s := (Finset.range e).filter (fun j => c j ≠ 0) with hs
  have hsum : ∑ i ∈ Finset.range e, c i * π ^ i = ∑ i ∈ s, c i * π ^ i := by
    rw [hs, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rfl
    · rw [not_not.mp h, zero_mul]
  have his : i ∈ s := by simp [hs, hi, hci]
  have hpw : Set.Pairwise (s : Set ℕ) (fun j k => ‖c j * π ^ j‖ ≠ ‖c k * π ^ k‖) := by
    intro j hj k hk hjk h
    simp only [hs, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hj hk
    obtain ⟨n, -, hn⟩ := key j hj.2
    obtain ⟨m, -, hm⟩ := key k hk.2
    rw [hn, hm] at h
    have h2 := zpow_right_injective₀ ht0 ht1.ne h
    have h3 := congrArg (fun z : ℤ => z % (e : ℤ)) h2
    simp only [Int.mul_add_emod_self_left] at h3
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hj.1),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hk.1)] at h3
    exact hjk (by exact_mod_cast h3)
  rw [hsum, IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne ⟨i, his⟩ hpw] at hx
  have h4 : ‖c i * π ^ i‖ ≤ 1 :=
    (Finset.le_sup' (fun j => ‖c j * π ^ j‖) his).trans hx
  obtain ⟨n, h5, h6⟩ := key i hci
  rw [h6, zpow_le_one_iff_right_of_lt_one₀ ht0 ht1] at h4
  rw [h5, zpow_le_one_iff_right_of_lt_one₀ ht0 ht1]
  have hie : (i : ℤ) < e := by exact_mod_cast hi
  have hn : 0 ≤ n := by
    by_contra hneg
    have : n ≤ -1 := by omega
    nlinarith
  positivity

theorem norm_l_lt' {l : ℕ} [Fact l.Prime] : ‖(l : ℂ_[l])‖ < 1 := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends]
  exact norm_l_lt

theorem mem_int_iff {l : ℕ} [Fact l.Prime] (x : ℂ_[l]) : x ∈ PadicComplexInt l ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm,
    Valuation.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe, PadicComplex.RankOne.hom_eq_embedding,
    Valuation.embedding_restrict]

theorem hom_padicInt {l : ℕ} [Fact l.Prime] (f : ℤ_[l] →+* ℂ_[l]) (hf : ∀ z, ‖f z‖ ≤ 1)
    (z : ℤ_[l]) : f z = algebraMap ℚ_[l] ℂ_[l] (z : ℚ_[l]) := by
  let g : ℤ_[l] →+* ℂ_[l] := (algebraMap ℚ_[l] ℂ_[l]).comp PadicInt.Coe.ringHom
  have hg : ∀ z, ‖g z‖ ≤ 1 := by
    intro z
    have : ‖g z‖ = ‖(z : ℚ_[l])‖ := PadicComplex.norm_extends' l (z : ℚ_[l])
    rw [this]
    exact z.2
  change f z = g z
  have hb : ∀ k : ℕ, ‖f z - g z‖ ≤ 2 * ‖(l : ℂ_[l])‖ ^ k := by
    intro k
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec k z)
    have hz : z = (PadicInt.appr z k : ℤ_[l]) + y * (l : ℤ_[l]) ^ k := by rw [hy]; ring
    have : f z - g z = (f y - g y) * (l : ℂ_[l]) ^ k := by
      conv_lhs => rw [hz]
      simp only [map_add, map_mul, map_pow, map_natCast]
      ring
    rw [this, norm_mul, norm_pow]
    have h1 := norm_sub_le (f y) (g y)
    have h2 := hf y
    have h3 := hg y
    gcongr
    linarith
  have ht : Filter.Tendsto (fun k : ℕ => 2 * ‖(l : ℂ_[l])‖ ^ k) Filter.atTop (nhds (2 * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_l_lt').const_mul 2
  have := ge_of_tendsto' ht hb
  rw [mul_zero] at this
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

theorem frac {l : ℕ} [hl : Fact l.Prime] {W : Type} [CommRing W] (g : ℤ_[l] →+* W)
    (φ : W →+* ℂ_[l]) (hφ : ∀ w, ‖φ w‖ ≤ 1) (S : Set (PadicAlgCl l))
    (hS : ∀ ζ ∈ S, ∃ w, φ w = algebraMap (PadicAlgCl l) ℂ_[l] ζ)
    (c : PadicAlgCl l) (hc : c ∈ IntermediateField.adjoin ℚ_[l] S) :
    ∃ (n : ℕ) (w : W), φ w = (l : ℂ_[l]) ^ n * algebraMap (PadicAlgCl l) ℂ_[l] c := by
  have h1 : c ∈ (IntermediateField.adjoin ℚ_[l] S).toSubalgebra := hc
  rw [IntermediateField.adjoin_toSubalgebra] at h1
  clear hc
  induction h1 using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨w, hw⟩ := hS x hx
    exact ⟨0, w, by simp [hw]⟩
  | algebraMap r =>
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(l : ℚ_[l]) ^ n * r‖ ≤ 1 := by
      have ht : Filter.Tendsto (fun k : ℕ => ‖(l : ℚ_[l])‖ ^ k * ‖r‖) Filter.atTop
          (nhds (0 * ‖r‖)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) Padic.norm_p_lt_one).mul_const _
      rw [zero_mul] at ht
      obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds one_pos)).exists
      exact ⟨n, by rwa [norm_mul, norm_pow]⟩
    refine ⟨n, g ⟨_, hn⟩, ?_⟩
    have := hom_padicInt (φ.comp g) (fun z => hφ _) ⟨_, hn⟩
    refine Eq.trans this ?_
    change algebraMap ℚ_[l] ℂ_[l] ((l : ℚ_[l]) ^ n * r) = _
    rw [← IsScalarTower.algebraMap_apply, map_mul, map_pow, map_natCast]
  | add x y _ _ hx hy =>
    obtain ⟨n, w, hw⟩ := hx
    obtain ⟨m, v, hv⟩ := hy
    refine ⟨n + m, (l : W) ^ m * w + (l : W) ^ n * v, ?_⟩
    simp only [map_add, map_mul, map_pow, map_natCast, hw, hv]
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨n, w, hw⟩ := hx
    obtain ⟨m, v, hv⟩ := hy
    refine ⟨n + m, w * v, ?_⟩
    simp only [map_mul, hw, hv]
    ring

theorem unram {l : ℕ} [hl : Fact l.Prime] {W : Type} [CommRing W]
    (hW : ∀ w : W, w ≠ 0 → ∃ (m : ℕ) (u : Wˣ), w = (l : W) ^ m * u)
    (φ : W →+* ℂ_[l]) (hφ : ∀ w, ‖φ w‖ ≤ 1) (c : PadicAlgCl l)
    (hc : ∃ (n : ℕ) (w : W), φ w = (l : ℂ_[l]) ^ n * algebraMap (PadicAlgCl l) ℂ_[l] c) :
    (c ≠ 0 → ∃ n : ℤ, ‖c‖ = ‖(l : PadicAlgCl l)‖ ^ n) ∧
      (‖c‖ ≤ 1 → ∃ w, φ w = algebraMap (PadicAlgCl l) ℂ_[l] c) := by
  by_cases hc0 : c = 0
  · exact ⟨fun h => (h hc0).elim, fun _ => ⟨0, by simp [hc0]⟩⟩
  obtain ⟨n, w, hw⟩ := hc
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [map_zero] at hw
    exact mul_ne_zero (pow_ne_zero _ hl0) ((_root_.map_ne_zero _).mpr hc0) hw.symm
  obtain ⟨m, u, rfl⟩ := hW w hw0
  have hu : ‖φ u‖ = 1 := by
    have h1 : ‖φ u‖ * ‖φ (u⁻¹ : Wˣ)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    have h2 := hφ u
    have h3 := hφ (u⁻¹ : Wˣ)
    have h4 := norm_nonneg (φ u)
    nlinarith
  rw [map_mul, map_pow, map_natCast] at hw
  have hcn : ‖algebraMap (PadicAlgCl l) ℂ_[l] c‖ = ‖c‖ := PadicComplex.norm_extends l c
  have hln : ‖(l : ℂ_[l])‖ = ‖(l : PadicAlgCl l)‖ := by
    rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends]
  have hp : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.mpr hl0
  have hn := congrArg norm hw
  rw [norm_mul, norm_mul, norm_pow, norm_pow, hu, mul_one, hcn] at hn
  have hcz : ‖c‖ = ‖(l : ℂ_[l])‖ ^ ((m : ℤ) - n) := by
    rw [zpow_sub₀ hp.ne', zpow_natCast, zpow_natCast, hn]
    field_simp
  refine ⟨fun _ => ⟨_, hln ▸ hcz⟩, fun h => ?_⟩
  rw [hcz, zpow_le_one_iff_right_of_lt_one₀ hp norm_l_lt'] at h
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  refine ⟨(l : W) ^ k * u, mul_left_cancel₀ (pow_ne_zero n hl0) ?_⟩
  rw [← hw, map_mul, map_pow, map_natCast]
  ring

open GlobalTheory.BKReal

theorem theta_seq {l : ℕ} [hl : Fact l.Prime] (s : ℕ → Formalism.BasicNotions.Loc.OC l)
    (hs : ∀ n, s (n + 1) ^ l = s n) (t : Formalism.BasicNotions.Loc.OCb l)
    (ht : ∀ n, t.1 n = Ideal.Quotient.mk (Ideal.span {(l : Formalism.BasicNotions.Loc.OC l)}) (s n)) :
    Formalism.Per.θ l (WittVector.teichmuller l t) = s 0 := by
  have h1 : t = Perfection.quotientMulEquiv l (Ideal.span {(l : Formalism.BasicNotions.Loc.OC l)}) ⟨s, hs⟩ :=
    Subtype.ext (funext fun n => ht n)
  refine (WittVector.fontaineTheta_teichmuller t).trans ?_
  have h2 := Perfection.coeff_zero_symm_quotientMulEquiv (p := l)
    (I := Ideal.span {(l : Formalism.BasicNotions.Loc.OC l)}) t
  refine Eq.trans h2.symm ?_
  rw [h1]
  exact congrArg (Perfection.coeffMonoidHom _ l 0) (MulEquiv.symm_apply_apply _ _)

theorem root_lift {l : ℕ} [hl : Fact l.Prime] (a : ℕ) [NeZero a] (ζ : PadicAlgCl l)
    (hζ : ζ ^ l ^ a = ζ) :
    ∃ w : Wq l a, ((Formalism.Per.θ l (wA l a w) : Formalism.Per.OC l) : ℂ_[l]) =
      algebraMap (PadicAlgCl l) ℂ_[l] ζ := by
  have hq : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) hl.out.one_lt
  have hn : ‖algebraMap (PadicAlgCl l) ℂ_[l] ζ‖ ≤ 1 := by
    have h0 : ‖algebraMap (PadicAlgCl l) ℂ_[l] ζ‖ = ‖ζ‖ := PadicComplex.norm_extends l ζ
    rw [h0]
    by_contra h
    have h1 := pow_lt_pow_right₀ (not_le.mp h) hq
    rw [← norm_pow, ← norm_pow, hζ, pow_one] at h1
    exact lt_irrefl _ h1
  let z : Formalism.BasicNotions.Loc.OC l := ⟨_, (mem_int_iff _).mpr hn⟩
  have hz : z ^ l ^ a = z := by
    apply Subtype.ext
    change (algebraMap (PadicAlgCl l) ℂ_[l] ζ) ^ l ^ a = algebraMap (PadicAlgCl l) ℂ_[l] ζ
    rw [← map_pow, hζ]
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by have := NeZero.ne a; omega⟩
  let s : ℕ → Formalism.BasicNotions.Loc.OC l := fun n => z ^ l ^ (b * n)
  have hs : ∀ n, s (n + 1) ^ l = s n := by
    intro n
    change (z ^ l ^ (b * (n + 1))) ^ l = z ^ l ^ (b * n)
    conv_rhs => rw [← hz]
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  have hs2 : ∀ n, s n ^ l ^ (b + 1) = s n := by
    intro n
    change (z ^ l ^ (b * n)) ^ l ^ (b + 1) = z ^ l ^ (b * n)
    rw [← pow_mul, mul_comm, pow_mul, hz]
  let y : Perfection (Formalism.BasicNotions.Loc.OC l) l := ⟨s, hs⟩
  have hy : y ^ l ^ (b + 1) = y := Subtype.ext (funext fun n => hs2 n)
  let t : Formalism.BasicNotions.Loc.OCb l :=
    Perfection.quotientMulEquiv l (Ideal.span {(l : Formalism.BasicNotions.Loc.OC l)}) y
  have ht : t ∈ resSub l (b + 1) := by
    change t ^ l ^ (b + 1) = t
    have := congrArg (Perfection.quotientMulEquiv l (Ideal.span {(l : Formalism.BasicNotions.Loc.OC l)})) hy
    rw [map_pow] at this
    exact this
  let t' : Fq l (b + 1) := ⟨t, ht⟩
  refine ⟨WittVector.teichmuller l t', ?_⟩
  have h1 : wA l (b + 1) (WittVector.teichmuller l t') = WittVector.teichmuller l t :=
    WittVector.map_teichmuller l (Fq.val l (b + 1)) t'
  rw [h1, theta_seq s hs t (fun n => rfl)]
  simp [s, z]

theorem wq_unit {l : ℕ} [hl : Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a) (hw : w ≠ 0) :
    ∃ (m : ℕ) (u : (Wq l a)ˣ), w = (l : Wq l a) ^ m * u :=
  WittVector.exists_eq_pow_p_mul' (k := Fq l a) w hw

end Bridge.RamInt

open GlobalTheory.BKReal Bridge.RamInt in
theorem Bridge.exists_powerSeries_eval_eq : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)] (a : ℕ) [inst : NeZero a] {e : ℕ} [NeZero e] (ϖ : GlobalTheory.BKReal.PiSys l e) (x : ↥(Formalism.BasicNotions.Loc.OL (GlobalTheory.BKReal.PiSys.field a ϖ))), ∃ (y : PowerSeries (GlobalTheory.BKReal.Wq l a)), (Formalism.Per.θ l) ((GlobalTheory.BKReal.PiSys.ev a ϖ) y) = (GlobalTheory.Prism.intToOC (GlobalTheory.BKReal.PiSys.field a ϖ)) x := by
  intro l hl a inst e _ ϖ x
  have hspec : PiSys.ev a ϖ PowerSeries.X = ϖ.teich ∧
      ∀ w : Wq l a, PiSys.ev a ϖ (PowerSeries.C w) = wA l a w := by
    unfold PiSys.ev
    exact Exists.choose_spec (PiSys.exists_ev a ϖ)
  let φ : Wq l a →+* ℂ_[l] :=
    (PadicComplexInt l).subtype.comp ((Formalism.Per.θ l).comp (wA l a).toRingHom)
  have hφ : ∀ w, ‖φ w‖ ≤ 1 := fun w => (mem_int_iff _).mp (Formalism.Per.θ l (wA l a w)).2
  have hF : ∀ c ∈ Kunr l a, (c ≠ 0 → ∃ n : ℤ, ‖c‖ = ‖(l : PadicAlgCl l)‖ ^ n) ∧
      (‖c‖ ≤ 1 → ∃ w, φ w = algebraMap (PadicAlgCl l) ℂ_[l] c) := fun c hc =>
    unram (wq_unit a) φ hφ c
      (frac (algebraMap ℤ_[l] (Wq l a)) φ hφ _ (fun ζ hζ => root_lift a ζ hζ) c hc)
  have hπ : ((Formalism.Per.θ l ϖ.teich : Formalism.Per.OC l) : ℂ_[l]) =
      algebraMap (PadicAlgCl l) ℂ_[l] (ϖ.seq 0) := by
    have hs : ∀ n, ϖ.seqO (n + 1) ^ l = ϖ.seqO n := by
      intro n
      apply Subtype.ext
      change (algebraMap (PadicAlgCl l) ℂ_[l] (ϖ.seq (n + 1))) ^ l =
        algebraMap (PadicAlgCl l) ℂ_[l] (ϖ.seq n)
      rw [← map_pow, ϖ.seq_succ]
    have := theta_seq ϖ.seqO hs ϖ.flat (fun n => rfl)
    exact congrArg Subtype.val this
  let x0 : PadicAlgCl l := x.1.1
  have hx0 : ((GlobalTheory.Prism.intToOC (PiSys.field a ϖ) x : Formalism.Per.OC l) : ℂ_[l]) =
      algebraMap (PadicAlgCl l) ℂ_[l] x0 := rfl
  have hxn : ‖x0‖ ≤ 1 := by
    have h0 : ‖algebraMap (PadicAlgCl l) ℂ_[l] x0‖ = ‖x0‖ := PadicComplex.norm_extends l x0
    rw [← h0, ← hx0]
    exact (mem_int_iff _).mp (Subtype.property _)
  have hxm : x0 ∈ Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq 0} := x.1.2
  obtain ⟨c, hc, hsum⟩ := expand (Kunr l a) (ϖ.seq 0) (NeZero.ne e) ϖ.seq_zero x0 hxm
  have hc1 : ∀ i, i < e → ‖c i‖ ≤ 1 :=
    coeff_le_one (ϖ.seq 0) (NeZero.ne e) ϖ.seq_zero c (fun i => (hF _ (hc i)).1) (hsum ▸ hxn)
  have hw : ∀ i, ∃ w : Wq l a, i < e → φ w = algebraMap (PadicAlgCl l) ℂ_[l] (c i) := by
    intro i
    by_cases hi : i < e
    · obtain ⟨w, hw⟩ := (hF _ (hc i)).2 (hc1 i hi)
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose w hw using hw
  refine ⟨∑ i ∈ Finset.range e, PowerSeries.C (w i) * PowerSeries.X ^ i, ?_⟩
  apply Subtype.ext
  rw [hx0, hsum, map_sum (algebraMap (PadicAlgCl l) ℂ_[l])]
  let Θ : PowerSeries (Wq l a) →+* ℂ_[l] :=
    (PadicComplexInt l).subtype.comp ((Formalism.Per.θ l).comp (PiSys.ev a ϖ))
  have hΘX : Θ PowerSeries.X = algebraMap (PadicAlgCl l) ℂ_[l] (ϖ.seq 0) := by
    rw [← hπ, ← hspec.1]; rfl
  have hΘC : ∀ v, Θ (PowerSeries.C v) = φ v := by
    intro v
    change ((Formalism.Per.θ l (PiSys.ev a ϖ (PowerSeries.C v)) : Formalism.Per.OC l) : ℂ_[l]) =
      ((Formalism.Per.θ l (wA l a v) : Formalism.Per.OC l) : ℂ_[l])
    rw [hspec.2]
  change Θ _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_mul, map_pow, hΘX, hΘC, hw i (Finset.mem_range.mp hi), map_mul, map_pow]
end

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism
open scoped Formalism.Per
namespace GlobalTheory.BKReal
variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ)
variable [NeZero a]

variable (e : ℕ) [NeZero e]
namespace PiSys
variable {l e} (ϖ : PiSys l e)

theorem exists_theta_ev_eq (x : ↥(OL (ϖ.field a))) :
    ∃ y, Per.θ l (ϖ.ev a y) = intToOC (ϖ.field a) x := by
  first | exact Bridge.exists_powerSeries_eval_eq | exact Bridge.exists_powerSeries_eval_eq .. | (intros; apply Bridge.exists_powerSeries_eval_eq <;> assumption)

def quotToOC : ((Wq l a)⟦X⟧ ⧸ Ideal.span {eis l a e}) →+* OC l :=
  Ideal.Quotient.lift _ ((Per.θ l).comp (ϖ.ev a)) fun x hx =>
    (ϖ.theta_ev_eq_zero_iff a x).2 (Ideal.mem_span_singleton.1 hx)

theorem quotToOC_mk (x : (Wq l a)⟦X⟧) :
    ϖ.quotToOC a (Ideal.Quotient.mk _ x) = Per.θ l (ϖ.ev a x) := rfl

theorem quotToOC_injective : Function.Injective (ϖ.quotToOC a) :=
  RingHom.lift_injective_of_ker_le_ideal _ _ fun x hx =>
    Ideal.mem_span_singleton.2 ((ϖ.theta_ev_eq_zero_iff a x).1 hx)

def strMap : ↥(OL (ϖ.field a)) →+* ((Wq l a)⟦X⟧ ⧸ Ideal.span {eis l a e}) :=
  liftInj (intToOC (ϖ.field a)) (ϖ.quotToOC a) (ϖ.quotToOC_injective a) fun x =>
    (ϖ.exists_theta_ev_eq a x).elim fun y hy => ⟨Ideal.Quotient.mk _ y, hy⟩

theorem quotToOC_strMap (x : ↥(OL (ϖ.field a))) :
    ϖ.quotToOC a (ϖ.strMap a x) = intToOC (ϖ.field a) x := liftInj_spec _ _ _ _ x

def prism : Obj l ↥(OL (ϖ.field a)) where
  A := (Wq l a)⟦X⟧
  D := deltaS l a
  I := Ideal.span {eis l a e}
  inv := invertible_span_singleton (mem_nonZeroDivisors_of_ne_zero fun h =>
    WittVector.p_nonzero l (Fq l a) (by rw [← constantCoeff_eis l a e, h, map_zero]))
  complete := complete_eis l a e
  l_mem := l_mem_eis l a e
  bdd := ⟨0, fun x ⟨m, hm⟩ => by
    have h := congrArg (ϖ.quotToOC a) hm
    rw [map_mul, map_pow, map_natCast, map_zero] at h
    have h2 := (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
    rw [pow_zero, one_mul]
    exact ϖ.quotToOC_injective a (h2.trans (map_zero _).symm)⟩
  str := ϖ.strMap a

omit [NeZero e] in

theorem ev_frobS (x : (Wq l a)⟦X⟧) : ϖ.ev a (frobS l a x) = WittVector.frobenius (ϖ.ev a x) := by
  have h1 : WittVector.frobenius ϖ.teich = ϖ.teich ^ l := by
    rw [WittVector.frobenius_eq_map_frobenius, teich, WittVector.map_teichmuller, frobenius_def, map_pow]
  refine RingHom.congr_fun (ringHom_ext_of_sep ((ϖ.ev a).comp (frobS l a))
    (WittVector.frobenius.comp (ϖ.ev a)) (fun w => ?_) ?_ fun y hy => ϖ.sep_teich y fun n => ?_) x
  · simp [wA_sigma]
  · simp [h1]
  · refine Dvd.dvd.trans ?_ (hy n)
    simp only [RingHom.comp_apply, frobS_X, map_pow, ev_X]
    exact pow_dvd_pow_of_dvd (dvd_pow_self _ hl.out.ne_zero) n

def toAinf : Hom (ϖ.prism a) (ainfObj (ϖ.field a)) where
  f := ϖ.ev a
  f_δ := (deltaS l a).map_δ_of_map_φ (ainfDelta l) ainf_torsionFree (ϖ.ev a) (ϖ.ev_frobS a)
  f_I x hx := (ϖ.theta_ev_eq_zero_iff a x).2 (Ideal.mem_span_singleton.1 hx)
  f_str r x h := ((isAinf_ainfObj _).mk_eq_str_iff r (ϖ.ev a x)).2
    ((congrArg (ϖ.quotToOC a) h).trans (ϖ.quotToOC_strMap a r))

theorem toAinf_f (x : (Wq l a)⟦X⟧) : (ϖ.toAinf a).f x = ϖ.ev a x := rfl

theorem span_ev_eis : Ideal.span {ϖ.ev a (eis l a e)} = RingHom.ker (Per.θ l) := by
  obtain ⟨ξ, h, -, h1⟩ := exists_generator l
  have h0 : Per.θ l ξ = 0 := by rw [← RingHom.mem_ker, h]; exact Ideal.mem_span_singleton_self ξ
  obtain ⟨c, hc⟩ : ξ ∣ ϖ.ev a (eis l a e) := by
    rw [← Ideal.mem_span_singleton, ← h]; exact ϖ.theta_ev_eis a
  have h2 := l_mem_eis l a e
  rw [Ideal.map_span, Set.image_singleton, ← Ideal.span_insert, Ideal.mem_span_pair] at h2
  obtain ⟨x, y, hxy⟩ := h2
  have h3 := congrArg (fun z => Per.θ l (ϖ.ev a z)) hxy
  simp only [map_add, map_mul, theta_ev_eis, mul_zero, zero_add, map_natCast] at h3
  rw [show (deltaS l a).φ (eis l a e) = frobS l a (eis l a e) from rfl, ev_frobS, hc, map_mul, map_mul,
    h1] at h3
  have h4 : ϖ.ev a y * WittVector.frobenius c - 1 ∈ Ideal.span {ξ} := by
    rw [← h, RingHom.mem_ker, map_sub, map_mul, map_one, sub_eq_zero]
    exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hl.out.ne_zero : (l : OC l) ≠ 0) (by linear_combination h3)
  have := (GlobalTheory.Per.AinfComplete.main l ξ fun hu => (hu.map (Per.θ l)).ne_zero h0).2
  have h5 := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ h4) 1
  rw [mul_one, sub_add_cancel] at h5
  have h6 : IsUnit c := by
    rw [← (WittVector.frobeniusEquiv l (OCb l)).symm_apply_apply c]
    exact (isUnit_of_mul_isUnit_right h5).map (WittVector.frobeniusEquiv l (OCb l)).symm
  rw [h, hc, Ideal.span_singleton_mul_right_unit h6]

theorem isUnit_inclW_ev_eis : IsUnit (inclW l (ϖ.ev a (eis l a e))) :=
  isUnit_inclW_of_span (ϖ.span_ev_eis a)

example : ((l : ℕ) : (Wq l a)⟦X⟧) ∉ (ϖ.prism a).I := fun h => by
  have h1 : Per.θ l (ϖ.ev a (l : (Wq l a)⟦X⟧)) = 0 := (ϖ.toAinf a).f_I _ h
  rw [map_natCast, map_natCast] at h1
  exact Nat.cast_ne_zero.2 hl.out.ne_zero h1

end PiSys

namespace PiSys

variable {l e} (ϖ : PiSys l e)

def ratio (g : GQ l) (n : ℕ) : OC l :=
  ⟨algebraMap (Om l) ℂ_[l] (g (ϖ.seq n) / ϖ.seq n), (GlobalTheory.RingBasics.mem_OC _).2 (by
    rw [show algebraMap (Om l) ℂ_[l] (g (ϖ.seq n) / ϖ.seq n) = ((g (ϖ.seq n) / ϖ.seq n : Om l) : ℂ_[l]) from rfl,
      PadicComplex.norm_extends, norm_div, GlobalTheory.RingBasics.norm_gal]
    exact div_self_le_one _)⟩

omit [NeZero e] in

theorem coe_ratio (g : GQ l) (n : ℕ) :
    (ϖ.ratio g n : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (g (ϖ.seq n) / ϖ.seq n) := rfl

omit [NeZero e] in

theorem ratio_succ (g : GQ l) (n : ℕ) : ϖ.ratio g (n + 1) ^ l = ϖ.ratio g n :=
  Subtype.ext (by
    rw [SubmonoidClass.coe_pow, coe_ratio, coe_ratio, ← map_pow, div_pow, ← map_pow, ϖ.seq_succ])

def kummer (g : GQ l) : OCb l :=
  (⟨fun n => Ideal.Quotient.mk _ (ϖ.ratio g n), fun n => by rw [← map_pow, ratio_succ]⟩ :
    Perfection (ModP (OC l) l) l)

omit [NeZero e] in

theorem coeff_kummer (g : GQ l) (n : ℕ) :
    PreTilt.coeff n (ϖ.kummer g) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (ϖ.ratio g n) := rfl

theorem gal_flat (g : GQ l) : Per.σF g ϖ.flat = ϖ.kummer g * ϖ.flat :=
  Perfection.ext fun n => by
    refine (GlobalTheory.AdicMaps.coeff_galois l g ϖ.flat n (ϖ.seqO n) rfl).trans ?_
    change Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (Per.σO g (ϖ.seqO n)) =
      Ideal.Quotient.mk _ (ϖ.ratio g n) * Ideal.Quotient.mk _ (ϖ.seqO n)
    rw [← map_mul]
    congr 1
    refine Subtype.ext (((GlobalTheory.RingIface.sigO_coe l g (ϖ.seqO n)).trans (GlobalTheory.RingBasics.σC_coe g (ϖ.seq n))).trans ?_)
    rw [MulMemClass.coe_mul, coe_ratio, coe_seqO, ← map_mul, div_mul_cancel₀ _ (ϖ.seq_ne_zero n)]
    rfl

omit [NeZero e] in

theorem untilt_kummer (g : GQ l) : (ϖ.kummer g).untilt = ϖ.ratio g 0 := by
  refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : OC l)}) fun n => ⟨ϖ.ratio g n, rfl, ?_⟩
  have : ϖ.ratio g n ^ l ^ n = ϖ.ratio g 0 :=
    Subtype.ext (by
      rw [SubmonoidClass.coe_pow, coe_ratio, coe_ratio, ← map_pow, div_pow, ← map_pow, ϖ.seq_pow])
  rw [this]

def mu (g : GQ l) : Ainf l := WittVector.teichmuller l (ϖ.kummer g) - 1

theorem gal_teich (g : GQ l) : Per.σA g ϖ.teich = (1 + ϖ.mu g) * ϖ.teich := by
  rw [mu, add_sub_cancel, teich, ← map_mul, ← gal_flat]
  exact GlobalTheory.RingIface.sigA_teich l g _

theorem theta_mu {g : GQ l} (hg : g (ϖ.seq 0) = ϖ.seq 0) : Per.θ l (ϖ.mu g) = 0 := by
  rw [mu, map_sub, map_one, WittVector.fontaineTheta_teichmuller, untilt_kummer, sub_eq_zero]
  exact Subtype.ext (by rw [coe_ratio, hg, div_self (ϖ.seq_ne_zero 0), map_one]; rfl)

def IsExponent (ζ : ℕ → Om l) (g : GQ l) (x : ℤ_[l]) : Prop :=
  ∀ n, g (ϖ.seq n) = ζ n ^ (PadicInt.toZModPow n x).val * ϖ.seq n

theorem existsUnique_isExponent (ζ : ℕ → Om l) (h0 : ζ 0 = 1) (hs : ∀ n, ζ (n + 1) ^ l = ζ n) (h1 : ζ 1 ≠ 1)
    {g : GQ l} (hg : g (ϖ.seq 0) = ϖ.seq 0) : ∃! x, ϖ.IsExponent ζ g x := by
  have hp : ∀ n k, ζ (n + k) ^ l ^ n = ζ k := fun n k => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_mul, show n + 1 + k = n + k + 1 by omega, hs, ih]
  have hprim : ∀ n, IsPrimitiveRoot (ζ n) (l ^ n) := fun n => by
    rcases n with _ | n
    · simp [h0]
    · rw [← orderOf_eq_prime_pow (x := ζ (n + 1)) (p := l) (n := n) (by rw [hp n 1]; exact h1)
        (by rw [← h0]; exact hp (n + 1) 0)]
      exact IsPrimitiveRoot.orderOf _
  have hN : ∀ n, NeZero (l ^ n) := fun n => ⟨(pow_pos hl.out.pos n).ne'⟩
  have hk : ∀ n, ∃ k : ℕ, ζ n ^ k = g (ϖ.seq n) / ϖ.seq n := fun n =>
    ((hprim n).eq_pow_of_pow_eq_one (by
      rw [div_pow, ← map_pow, seq_pow, hg, div_self (ϖ.seq_ne_zero 0)])).imp fun _ h => h.2
  choose k hk using hk
  have hd : ∀ n, (l : ℤ) ^ n ∣ (k (n + 1) : ℤ) - k n := fun n => by
    have h2 : ζ n ^ k (n + 1) = ζ n ^ k n := by
      rw [hk, ← hs n, ← pow_mul, mul_comm, pow_mul, hk, div_pow, ← map_pow, ϖ.seq_succ]
    have h3 := (hprim n).isUnit_unit (pow_pos hl.out.pos n).ne'
    have h4 : ((hprim n).isUnit (pow_pos hl.out.pos n).ne').unit ^ k n =
        ((hprim n).isUnit (pow_pos hl.out.pos n).ne').unit ^ k (n + 1) := Units.ext (by simpa using h2.symm)
    rw [pow_eq_pow_iff_modEq, ← h3.eq_orderOf] at h4
    exact_mod_cast h4.dvd
  refine ⟨PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => (k n : ℤ)) l hd),
    fun n => ?_, fun y hy => PadicInt.ext_of_toZModPow.1 fun n => ?_⟩
  · rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (k n : ℤ)) l hd n, Int.cast_natCast,
      ZMod.val_natCast, ← pow_eq_pow_mod _ (hprim n).pow_eq_one, hk, div_mul_cancel₀ _ (ϖ.seq_ne_zero n)]
  · rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (k n : ℤ)) l hd n, Int.cast_natCast]
    refine ZMod.val_injective _ ((hprim n).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ?_)
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hprim n).pow_eq_one, hk, hy n,
      mul_div_cancel_right₀ _ (ϖ.seq_ne_zero n)]

theorem IsExponent.coeff_kummer {ϖ : PiSys l e} {ζ : ℕ → Om l} {g : GQ l} {x : ℤ_[l]}
    (h : ϖ.IsExponent ζ g x) (n : ℕ) (z : OC l) (hz : (z : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ n)) :
    PreTilt.coeff n (ϖ.kummer g) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) z ^
      (PadicInt.toZModPow n x).val := by
  rw [PiSys.coeff_kummer, ← map_pow]
  congr 1
  exact Subtype.ext (by
    rw [coe_ratio, h n, mul_div_cancel_right₀ _ (ϖ.seq_ne_zero n), map_pow, SubmonoidClass.coe_pow, hz])

end PiSys

theorem gal_wA {g : GQ l} (hg : ∀ x ∈ Kunr l a, g x = x) (w : Wq l a) : Per.σA g (wA l a w) = wA l a w := by
  obtain ⟨z, ω, hω, hz, h⟩ := exists_gen l a
  have h1 := one_lt_pow_l l a
  have hω' : g ω = ω := hg ω (IntermediateField.subset_adjoin _ _ (show ω ^ l ^ a = ω by
    rw [← Nat.sub_add_cancel h1.le, pow_succ, hω.pow_eq_one, one_mul]))
  have hd : ¬ l ∣ l ^ a - 1 := fun h => hl.out.not_dvd_one
    ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne a))).1 h)
  have h2 : Per.σF g (Fq.val l a z) = Fq.val l a z := by
    refine (GlobalTheory.UnramIdem.tilt_pow (k := 1) hd dvd_rfl hz fun n => ?_).trans (pow_one _)
    obtain ⟨y, y1, y2, y3⟩ := hz n
    refine ⟨Per.σO g y, ?_, by rw [← map_pow, y2, map_one],
      GlobalTheory.AdicMaps.coeff_galois l g _ n y y3⟩
    rw [GlobalTheory.RingIface.sigO_coe l g y, ← map_pow, y1, GlobalTheory.RingBasics.σC_coe, hω', pow_one]
  refine WittVector.ext fun n => ?_
  refine (GlobalTheory.RingIface.sigA_coeff l g _ n).trans ?_
  change Per.σF g (Fq.val l a (w.coeff n)) = Fq.val l a (w.coeff n)
  rcases eq_or_ne (w.coeff n) 0 with h0 | h0
  · rw [h0, map_zero, map_zero]
  · obtain ⟨k, hk⟩ := h _ h0
    rw [hk, map_pow, map_pow, h2]

theorem PiSys.gal_ev {e : ℕ} [NeZero e] (ϖ : PiSys l e) {g : GQ l} (hg : g ∈ ϖ.GfieldInf a)
    (x : (Wq l a)⟦X⟧) : Per.σA g (ϖ.ev a x) = ϖ.ev a x := by
  have h := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg
  refine RingHom.congr_fun (ϖ.eq_ev a ((Per.σA g).comp (ϖ.ev a)) ?_ fun w => ?_) x
  · have : ϖ.kummer g = 1 := Perfection.ext fun n => by
      change Ideal.Quotient.mk _ (ϖ.ratio g n) = Ideal.Quotient.mk _ 1
      congr 1
      refine Subtype.ext ?_
      rw [PiSys.coe_ratio, h _ (ϖ.seq_mem_fieldInf a n),
        div_self (ϖ.seq_ne_zero n), map_one]
      rfl
    rw [RingHom.comp_apply, PiSys.ev_X, PiSys.gal_teich, PiSys.mu, this]
    simp
  · rw [RingHom.comp_apply, PiSys.ev_C]
    exact gal_wA l a (fun y hy => h y (ϖ.field_le_fieldInf a (ϖ.Kunr_le_field a hy))) w

end GlobalTheory.BKReal
