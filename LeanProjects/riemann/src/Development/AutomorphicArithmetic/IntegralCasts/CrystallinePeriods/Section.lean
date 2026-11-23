import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]

section Witt

variable {k : Type w} [CommRing k] [CharP k p] [PerfectRing k p]

def Tilt.ofPerfect (f : k →+* R ⧸ span {(p : R)}) : k →+* Tilt p R :=
  Perfection.lift p k (ModP R p) f

variable {p} in
theorem Tilt.coeff_ofPerfect (f : k →+* R ⧸ span {(p : R)}) (n : ℕ) (a : k) :
    PreTilt.coeff n (Tilt.ofPerfect p f a) = f ((frobeniusEquiv k p).symm^[n] a) := rfl

variable {p} in
theorem Tilt.eq_ofPerfect (f : k →+* R ⧸ span {(p : R)}) (g : k →+* Tilt p R)
    (h : ∀ a, PreTilt.coeff 0 (g a) = f a) : g = Tilt.ofPerfect p f :=
  Perfection.hom_ext p (S := ModP R p) h

variable {p} in
theorem Tilt.map_ofPerfect (e : R →+* S) (f : k →+* R ⧸ span {(p : R)}) (a : k) :
    Tilt.map p e (Tilt.ofPerfect p f a) =
      Tilt.ofPerfect p ((Ideal.quotientMap _ e (span_natCast_le_comap p e)).comp f) a :=
  Tilt.ext fun _ => rfl

def Ainf.ofWitt (f : k →+* R ⧸ span {(p : R)}) : WittVector p k →+* Ainf p R :=
  WittVector.map (Tilt.ofPerfect p f)

variable {p} in
@[simp] theorem Ainf.ofWitt_teichmuller (f : k →+* R ⧸ span {(p : R)}) (a : k) :
    Ainf.ofWitt p f (WittVector.teichmuller p a) = Ainf.teich p (Tilt.ofPerfect p f a) :=
  WittVector.map_teichmuller p _ a

variable {p} in

theorem Ainf.frob_ofWitt (f : k →+* R ⧸ span {(p : R)}) (x : WittVector p k) :
    Ainf.frob p R (Ainf.ofWitt p f x) = Ainf.ofWitt p f (WittVector.frobenius x) := by
  ext n
  simp [Ainf.ofWitt, Ainf.frob_eq_map, WittVector.frobenius_eq_map_frobenius, frobenius_def]

variable {p} in

theorem Ainf.map_ofWitt (e : R →+* S) (f : k →+* R ⧸ span {(p : R)}) (x : WittVector p k) :
    Ainf.map p e (Ainf.ofWitt p f x) =
      Ainf.ofWitt p ((Ideal.quotientMap _ e (span_natCast_le_comap p e)).comp f) x := by
  ext n
  simp [Ainf.ofWitt, Ainf.map, Tilt.map_ofPerfect]

omit [Fact ¬IsUnit (p : R)] in

def wittResidueMap (g : WittVector p k →+* R) : k →+* R ⧸ span {(p : R)} :=
  (Ideal.quotientMap _ g (span_natCast_le_comap p g)).comp
    (WittVector.quotientPEquiv (p := p) (k := k)).symm.toRingHom

omit [Fact ¬IsUnit (p : R)] in
variable {p} in
theorem wittResidueMap_coeff_zero (g : WittVector p k →+* R) (x : WittVector p k) :
    wittResidueMap p g (x.coeff 0) = Ideal.Quotient.mk _ (g x) := by
  have : (WittVector.quotientPEquiv (p := p) (k := k)).symm (x.coeff 0) =
      Ideal.Quotient.mk _ x := by
    rw [RingEquiv.symm_apply_eq]; rfl
  change Ideal.quotientMap _ g (span_natCast_le_comap p g) ((WittVector.quotientPEquiv (p := p) (k := k)).symm _) = _
  rw [this, Ideal.quotientMap_mk]

def Ainf.liftWitt (g : WittVector p k →+* R) : WittVector p k →+* Ainf p R :=
  Ainf.ofWitt p (wittResidueMap p g)

variable {p} in
theorem Ainf.map_liftWitt (e : R →+* S) (g : WittVector p k →+* R) (x : WittVector p k) :
    Ainf.map p e (Ainf.liftWitt p g x) = Ainf.liftWitt p (e.comp g) x := by
  rw [Ainf.liftWitt, Ainf.map_ofWitt, Ainf.liftWitt]
  congr 2

variable {p} in
theorem Ainf.frob_liftWitt (g : WittVector p k →+* R) (x : WittVector p k) :
    Ainf.frob p R (Ainf.liftWitt p g x) = Ainf.liftWitt p g (WittVector.frobenius x) :=
  Ainf.frob_ofWitt _ x

variable {p} in

theorem Ainf.theta_liftWitt [IsAdicComplete (span {(p : R)}) R] (g : WittVector p k →+* R)
    (x : WittVector p k) : Ainf.theta p R (Ainf.liftWitt p g x) = g x := by
  have key (a : k) : PreTilt.untilt (Tilt.ofPerfect p (wittResidueMap p g) a) =
      g (WittVector.teichmuller p a) := by
    refine Perfection.teichmuller_spec fun n => ?_
    refine ⟨g (WittVector.teichmuller p ((frobeniusEquiv k p).symm^[n] a)), ?_, ?_⟩
    · rw [← wittResidueMap_coeff_zero, WittVector.teichmuller_coeff_zero]
      rfl
    · rw [← map_pow, ← map_pow, ← iterate_frobenius,
        Function.RightInverse.iterate (frobenius_apply_frobeniusEquiv_symm k p) n]
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : R)})]
  intro n
  rw [smul_eq_mul, Ideal.mul_top, SModEq]
  have := WittVector.eq_of_apply_teichmuller_eq
    ((Ideal.Quotient.mk (span {(p : R)} ^ n)).comp ((Ainf.theta p R).comp (Ainf.liftWitt p g)))
    ((Ideal.Quotient.mk (span {(p : R)} ^ n)).comp g)
    (by
      refine ⟨n, ?_⟩
      rw [← map_natCast (Ideal.Quotient.mk (span {(p : R)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (mem_span_singleton_self _) _)
    (by intro y; simp [Ainf.liftWitt, key])
  exact RingHom.congr_fun this x

end Witt

section FracWitt

variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]

def fracWittLift {B : Type*} [CommRing B] (f : WittVector p k →+* B) (h : IsUnit (p : B)) :
    FractionRing (WittVector p k) →+* B :=
  IsLocalization.lift (M := nonZeroDivisors (WittVector p k)) (g := f) (by
    rintro ⟨x, hx⟩
    obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' x (nonZeroDivisors.ne_zero hx)
    change IsUnit (f _)
    rw [map_mul, map_pow, map_natCast]
    exact (h.pow _).mul ((Units.isUnit _).map f))

@[simp] theorem fracWittLift_algebraMap {B : Type*} [CommRing B] (f : WittVector p k →+* B)
    (h : IsUnit (p : B)) (a : WittVector p k) : fracWittLift p f h (algebraMap _ _ a) = f a :=
  IsLocalization.lift_eq _ a

variable {p} in
theorem fracWitt_hom_ext {B : Type*} [CommRing B] {f g : FractionRing (WittVector p k) →+* B}
    (h : ∀ a : WittVector p k, f (algebraMap _ _ a) = g (algebraMap _ _ a)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext h)

def AinfInv.liftFracWitt (g : WittVector p k →+* R) :
    FractionRing (WittVector p k) →+* AinfInv p R :=
  fracWittLift p ((algebraMap (Ainf p R) (AinfInv p R)).comp (Ainf.liftWitt p g))
    (AinfInv.isUnit_p p)

variable {p} in
@[simp] theorem AinfInv.liftFracWitt_algebraMap (g : WittVector p k →+* R) (a : WittVector p k) :
    AinfInv.liftFracWitt p g (algebraMap _ _ a) = algebraMap _ _ (Ainf.liftWitt p g a) :=
  fracWittLift_algebraMap p _ _ a

variable {p} in
theorem AinfInv.map_liftFracWitt (e : R →+* S) (g : WittVector p k →+* R)
    (x : FractionRing (WittVector p k)) :
    AinfInv.map p e (AinfInv.liftFracWitt p g x) = AinfInv.liftFracWitt p (e.comp g) x :=
  RingHom.congr_fun (fracWitt_hom_ext (f := (AinfInv.map p e).comp (AinfInv.liftFracWitt p g))
    (g := AinfInv.liftFracWitt p (e.comp g)) (by simp [Ainf.map_liftWitt])) x

variable {p} in
theorem AinfInv.theta_liftFracWitt [IsAdicComplete (span {(p : R)}) R] (g : WittVector p k →+* R)
    (a : WittVector p k) :
    AinfInv.theta p R (AinfInv.liftFracWitt p g (algebraMap _ _ a)) = algebraMap R _ (g a) := by
  simp [Ainf.theta_liftWitt]

end FracWitt

variable [IsAdicComplete (span {(p : R)}) R]

variable {p} in

theorem Ainf.theta_algebraMap_padicInt (g : ℤ_[p] →+* R) (a : ℤ_[p]) :
    Ainf.theta p R (algebraMap ℤ_[p] _ a) = g a := by
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : R)})]
  intro n
  rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n a)
  have ha : a = (PadicInt.appr a n : ℤ_[p]) + c * (p : ℤ_[p]) ^ n := by rw [hc]; ring
  rw [ha, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  simp only [map_add, map_mul, map_pow, map_natCast]
  exact ⟨Ainf.theta p R (algebraMap ℤ_[p] _ c) - g c, by ring⟩

variable {p} in

theorem AinfInv.theta_algebraMap_padic (g : ℤ_[p] →+* R) (j : ℚ_[p] →+* Localization.Away (p : R))
    (hj : ∀ a : ℤ_[p], j (algebraMap _ _ a) = algebraMap R _ (g a)) (x : ℚ_[p]) :
    AinfInv.theta p R (algebraMap ℚ_[p] _ x) = j x :=
  RingHom.congr_fun (padic_hom_ext (f := (AinfInv.theta p R).comp (algebraMap ℚ_[p] _)) (g := j)
    (fun a => by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply ℤ_[p] (Ainf p R) (AinfInv p R), AinfInv.theta_algebraMap,
        Ainf.theta_algebraMap_padicInt g, hj])) x

theorem evalₐ_mem_map_of_evalOne {A : Type*} [CommRing A] (I : Ideal A) {y : AdicCompletion I A}
    (hy : AdicCompletion.evalOneₐ I y = 0) (n : ℕ) :
    AdicCompletion.evalₐ I n y ∈ I.map (Ideal.Quotient.mk (I ^ n)) := by
  rcases n with _ | n
  · rw [Subsingleton.elim
      (h := Ideal.Quotient.subsingleton_iff.2 (by simp)) (AdicCompletion.evalₐ I 0 y) 0]
    exact zero_mem _
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
  have h1 := factorPow_evalₐ I (show 1 ≤ n + 1 by omega) y
  rw [← AdicCompletion.factorₐ_evalₐ_one, ← h1, ← ha] at hy
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    Ideal.Quotient.eq_zero_iff_mem] at hy
  rw [← ha]
  exact Ideal.mem_map_of_mem _ hy

namespace BdRPlus

variable {p}

theorem eval_eq_zero_of_mem_ker_theta_pow {n : ℕ} {x : BdRPlus p R} (hx : x ∈ fil p R n) :
    eval p R n x = 0 := by
  have h1 : RingHom.ker (theta p R) ≤
      ((AinfInv.kerTheta p R).map (Ideal.Quotient.mk (AinfInv.kerTheta p R ^ n))).comap
        (eval p R n) := by
    intro y hy
    rw [RingHom.mem_ker, theta_eq_zero_iff] at hy
    exact evalₐ_mem_map_of_evalOne _ hy n
  have h2 := pow_le_comap_pow h1 n hx
  rw [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_comap, Ideal.mem_bot] at h2
  exact h2

theorem iInf_ker_theta_pow : ⨅ n, fil p R n = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_iInf] at hx
  exact ext_eval fun n => by rw [eval_eq_zero_of_mem_ker_theta_pow (hx n), map_zero]

variable {F : Type v} {L : Type w} [CommRing F] [CommRing L] [Algebra F L]

theorem hom_ext_of_formallyUnramified [Algebra.FormallyUnramified F L] {s₁ s₂ : L →+* BdRPlus p R}
    (hF : ∀ a : F, s₁ (algebraMap F L a) = s₂ (algebraMap F L a))
    (hθ : ∀ x, theta p R (s₁ x) = theta p R (s₂ x)) : s₁ = s₂ := by
  letI : Algebra F (BdRPlus p R) := (s₁.comp (algebraMap F L)).toAlgebra
  have := Algebra.FormallyUnramified.ext_of_iInf (R := F) (I := RingHom.ker (theta p R))
    iInf_ker_theta_pow (g₁ := { s₁ with commutes' := fun _ => rfl })
    (g₂ := { s₂ with commutes' := fun a => (hF a).symm }) (fun x => by
      rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
      exact hθ x)
  exact RingHom.ext fun x => AlgHom.congr_fun this x

theorem exists_section [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) :
    ∃ s : L →+* BdRPlus p R, (∀ x, theta p R (s x) = j x) ∧
      ∀ a : F, s (algebraMap F L a) = algebraMap (AinfInv p R) _ (ι a) := by
  letI : Algebra F (AinfInv p R) := ι.toAlgebra
  let e := RingHom.quotientKerEquivOfSurjective hθ
  let f : L →ₐ[F] AinfInv p R ⧸ AinfInv.kerTheta p R :=
    { e.symm.toRingHom.comp j with
      commutes' := fun a => by
        change e.symm (j (algebraMap F L a)) = Ideal.Quotient.mk _ (ι a)
        rw [RingEquiv.symm_apply_eq, hj]
        rfl }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq f
  refine ⟨g.toRingHom, fun x => ?_, fun a => g.commutes a⟩
  have h1 : AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) (g x) = e.symm (j x) :=
    AlgHom.congr_fun hg x
  change e (AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) (g x)) = j x
  rw [h1, RingEquiv.apply_symm_apply]

def «section» [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) : L →+* BdRPlus p R :=
  (exists_section hθ ι j hj).choose

theorem theta_section [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) (x : L) :
    theta p R («section» hθ ι j hj x) = j x := (exists_section hθ ι j hj).choose_spec.1 x

theorem section_algebraMap [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) (a : F) :
    «section» hθ ι j hj (algebraMap F L a) = algebraMap (AinfInv p R) _ (ι a) :=
  (exists_section hθ ι j hj).choose_spec.2 a

theorem eq_section [Algebra.FormallyEtale F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) (s : L →+* BdRPlus p R)
    (h₁ : ∀ x, theta p R (s x) = j x)
    (h₂ : ∀ a : F, s (algebraMap F L a) = algebraMap (AinfInv p R) _ (ι a)) :
    s = «section» hθ ι j hj :=
  hom_ext_of_formallyUnramified (F := F) (fun a => by rw [h₂, section_algebraMap])
    (fun x => by rw [h₁, theta_section])

end BdRPlus

theorem formallyEtale_of_isAlgebraic (F : Type v) (L : Type w) [Field F] [Field L] [Algebra F L]
    [CharZero F] [Algebra.IsAlgebraic F L] : Algebra.FormallyEtale F L :=
  Algebra.FormallyEtale.of_isSeparable F L

theorem AinfInv.theta_surjective_of_frobenius
    (hF : Function.Surjective (frobenius (ModP R p) p)) :
    Function.Surjective (AinfInv.theta p R) := by
  intro y
  obtain ⟨⟨a, _, n, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers (p : R)) y
  obtain ⟨b, rfl⟩ := surjective_fontaineTheta hF a
  obtain ⟨u, hu⟩ := (AinfInv.isUnit_p p (R := R)).pow n
  refine ⟨algebraMap _ _ b * ↑u⁻¹, ?_⟩
  simp only [map_pow, map_natCast] at h
  have h2 : AinfInv.theta p R ↑u = (p : Localization.Away (p : R)) ^ n := by
    rw [hu, map_pow, map_natCast]
  rw [map_mul, AinfInv.theta_algebraMap, Ainf.theta, ← h, ← h2, mul_assoc, ← map_mul,
    Units.mul_inv, map_one, mul_one]

end Reformulated.AutPerF
