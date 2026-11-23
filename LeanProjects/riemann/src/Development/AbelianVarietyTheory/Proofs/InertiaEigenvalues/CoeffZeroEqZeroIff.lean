import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Decompl

section Near

variable {A R : Type} [CommRing A] [CommRing R] (ι : A →+* R) (p : ℕ) (t : R)

def Near (m : ℕ) (x : R) : Prop := ∃ (a : A) (r : R), x = t ^ m * ι a + (p : R) * r

variable {ι p t}

theorem Near.of_mul (m : ℕ) (r : R) : Near ι p t m ((p : R) * r) := ⟨0, r, by simp⟩

theorem Near.zero (m : ℕ) : Near ι p t m 0 := ⟨0, 0, by simp⟩

theorem Near.pow_mul (m : ℕ) (a : A) : Near ι p t m (t ^ m * ι a) := ⟨a, 0, by simp⟩

theorem Near.add {m : ℕ} {x y : R} (hx : Near ι p t m x) (hy : Near ι p t m y) :
    Near ι p t m (x + y) := by
  obtain ⟨a, r, rfl⟩ := hx
  obtain ⟨b, s, rfl⟩ := hy
  exact ⟨a + b, r + s, by rw [map_add]; ring⟩

theorem Near.neg {m : ℕ} {x : R} (hx : Near ι p t m x) : Near ι p t m (-x) := by
  obtain ⟨a, r, rfl⟩ := hx
  exact ⟨-a, -r, by rw [map_neg]; ring⟩

theorem Near.sub {m : ℕ} {x y : R} (hx : Near ι p t m x) (hy : Near ι p t m y) :
    Near ι p t m (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem Near.sum {I : Type} {m : ℕ} (s : Finset I) {f : I → R} (h : ∀ i ∈ s, Near ι p t m (f i)) :
    Near ι p t m (∑ i ∈ s, f i) :=
  Finset.sum_induction f _ (fun _ _ => Near.add) (Near.zero m) h

theorem Near.mul {m n : ℕ} {x y : R} (hx : Near ι p t m x) (hy : Near ι p t n y) :
    Near ι p t (m + n) (x * y) := by
  obtain ⟨a, r, rfl⟩ := hx
  obtain ⟨b, s, rfl⟩ := hy
  exact ⟨a * b, t ^ m * ι a * s + r * (t ^ n * ι b + p * s), by rw [map_mul]; ring⟩

theorem Near.mul_ι {m : ℕ} {x : R} (hx : Near ι p t m x) (b : A) : Near ι p t m (ι b * x) := by
  obtain ⟨a, r, rfl⟩ := hx
  exact ⟨b * a, ι b * r, by rw [map_mul]; ring⟩

theorem Near.mono {τ : A} (ht : ι τ = t) {m n : ℕ} (h : m ≤ n) {x : R} (hx : Near ι p t n x) :
    Near ι p t m x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨a, r, rfl⟩ := hx
  exact ⟨τ ^ k * a, r, by rw [map_mul, map_pow, ht]; ring⟩

theorem Near.cancel (ht : IsUnit t) {k m : ℕ} {x : R} (hx : Near ι p t (k + m) (t ^ k * x)) :
    Near ι p t m x := by
  obtain ⟨u, hu⟩ := ht.exists_right_inv
  obtain ⟨a, r, h⟩ := hx
  have h1 : t ^ k * u ^ k = 1 := by rw [← mul_pow, hu, one_pow]
  refine ⟨a, u ^ k * r, ?_⟩
  rw [pow_add] at h
  linear_combination u ^ k * h - (x - t ^ m * ι a) * h1

end Near

variable {l : ℕ} [Fact l.Prime]

def piW {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : Ainf l :=
  WittVector.teichmuller l (AI.εroot s) - 1

def piR {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) : RW LL :=
  inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piW AI s)

abbrev NearPi {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s m : ℕ) (x : RW LL) : Prop :=
  Near (inclR LL : RA LL →+* RW LL) l (piR AI LL s) m x

def fixSub {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (H : Set (GQ l)) : Subring (RW LL) :=
  ⨅ g ∈ H, RingHom.eqLocus (AI.gRW LL g : RW LL →+* RW LL) (RingHom.id _)

theorem mem_fixSub {P : LocPrime l} {AI : LocAinf l P} {LL : FinExt l} {H : Set (GQ l)}
    {x : RW LL} : x ∈ fixSub AI LL H ↔ ∀ g ∈ H, AI.gRW LL g x = x := by
  simp only [fixSub, Subring.mem_iInf]
  rfl

abbrev Wach (P : LocPrime l) (K LL : FinExt l) : Type 1 :=
  LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))

theorem finite_OL (LL : FinExt l) : Module.Finite ℤ_[l] ↥(OL LL) :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem free_OL (LL : FinExt l) : Module.Free ℤ_[l] ↥(OL LL) :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : Module.IsTorsionFree ℤ_[l] ↥LL.1 :=
    Module.IsTorsionFree.trans_faithfulSMul ℤ_[l] ℚ_[l] ↥LL.1
  IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

def basisO (LL : FinExt l) : Module.Basis (Fin (Module.finrank ℤ_[l] ↥(OL LL))) ℤ_[l] ↥(OL LL) :=
  haveI := finite_OL LL
  haveI := free_OL LL
  Module.finBasis ℤ_[l] ↥(OL LL)

section Coord

variable {Z O : Type} [CommRing Z] [CommRing O] [Algebra Z O] {I : Type} [Fintype I]
  (b : Module.Basis I Z O) {W W' : Type} [CommRing W] [Algebra Z W] [CommRing W'] [Algebra Z W']

def crd (i : I) : O ⊗[Z] W →ₗ[Z] W :=
  TensorProduct.lift ((LinearMap.lsmul Z W).comp (b.coord i))

omit [Fintype I] in
@[simp] theorem crd_tmul (i : I) (o : O) (w : W) : crd b i (o ⊗ₜ[Z] w) = b.repr o i • w := rfl

theorem sum_crd (x : O ⊗[Z] W) : ∑ i, b i ⊗ₜ[Z] crd b i x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    simp only [crd_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [← TensorProduct.sum_tmul, b.sum_repr]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

theorem crd_sum (w : I → W) (i : I) : crd b i (∑ j, b j ⊗ₜ[Z] w j) = w i := by
  classical
  simp [map_sum, Finsupp.single_apply]

theorem ext_crd {x y : O ⊗[Z] W} (h : ∀ i, crd b i x = crd b i y) : x = y := by
  rw [← sum_crd b x, ← sum_crd b y]
  simp only [h]

omit [Fintype I] in
theorem crd_map (f : W →ₐ[Z] W') (i : I) (x : O ⊗[Z] W) :
    crd b i (Algebra.TensorProduct.map (AlgHom.id O O) f x) = f (crd b i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o w => simp
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Fintype I] in
theorem crd_mul (w : W) (i : I) (x : O ⊗[Z] W) :
    crd b i (((1 : O) ⊗ₜ[Z] w) * x) = w * crd b i x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o w => simp
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]

omit [Fintype I] in
theorem crd_natCast_mul (n : ℕ) (i : I) (x : O ⊗[Z] W) :
    crd b i ((n : O ⊗[Z] W) * x) = (n : W) * crd b i x := by
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

end Coord

instance perfectRing_Cb : PerfectRing (Cb l) l :=
  haveI := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  inferInstance

instance valuationRing_OCb : ValuationRing (OCb l) :=
  (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).2

theorem coeff_zero_eq_zero_iff (w : WCb l) : w.coeff 0 = 0 ↔ ∃ r, w = (l : WCb l) * r := by
  rw [← WittVector.constantCoeff_apply, ← RingHom.mem_ker, WittVector.ker_constantCoeff,
    Ideal.mem_span_singleton]
  rfl

theorem sub_coeff_zero (x y : WCb l) : (x - y).coeff 0 = x.coeff 0 - y.coeff 0 :=
  map_sub (WittVector.constantCoeff : WCb l →+* Cb l) x y

theorem piR_eq {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) :
    piR AI LL s = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (piW AI s) := rfl

theorem coeff_zero_piW {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    (inclW l (piW AI s)).coeff 0 = algebraMap (OCb l) (Cb l) (AI.εroot s - 1) := by
  rw [inclW, WittVector.map_coeff, piW, ← WittVector.constantCoeff_apply, map_sub, map_one,
    WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem crd_inclR (LL : FinExt l) (i) (a : RA LL) :
    crd (basisO LL) i (inclR LL a) = inclW l (crd (basisO LL) i a) :=
  crd_map (basisO LL) (inclWA l) i a

theorem crd_φRW (LL : FinExt l) (i) (x : RW LL) :
    crd (basisO LL) i (φRW LL x) = frobW l (crd (basisO LL) i x) :=
  crd_map (basisO LL) (frobW l) i x

theorem crd_gRW {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l) (i) (x : RW LL) :
    crd (basisO LL) i (AI.gRW LL g x) = AI.actWCbHom g (crd (basisO LL) i x) :=
  crd_map (basisO LL) (AI.actWCbHom g).toAlgHom i x

theorem coeff_actWCbHom {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (w : WCb l) (n : ℕ) :
    (AI.actWCbHom g w).coeff n = autCb l (AI.actT g) (w.coeff n) :=
  WittVector.map_coeff (autCb l (AI.actT g)).toRingHom w n

theorem coeff_frobW (w : WCb l) (n : ℕ) : (frobW l w).coeff n = w.coeff n ^ l :=
  WittVector.map_coeff (frobenius (Cb l) l) w n

theorem coeff_inclW (a : Ainf l) (n : ℕ) :
    (inclW l a).coeff n = algebraMap (OCb l) (Cb l) (a.coeff n) :=
  WittVector.map_coeff _ a n

theorem dvd_iff_crd (LL : FinExt l) (x : RW LL) :
    (∃ r, x = (l : RW LL) * r) ↔ ∀ i, (crd (basisO LL) i x).coeff 0 = 0 := by
  constructor
  · rintro ⟨r, rfl⟩ i
    rw [crd_natCast_mul, coeff_zero_eq_zero_iff]
    exact ⟨_, rfl⟩
  · intro h
    choose r hr using fun i => (coeff_zero_eq_zero_iff _).1 (h i)
    refine ⟨∑ j, basisO LL j ⊗ₜ[ℤ_[l]] r j, ext_crd (basisO LL) fun i => ?_⟩
    rw [crd_natCast_mul, crd_sum, hr]

theorem nearPi_iff_crd {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s m : ℕ) (x : RW LL) :
    NearPi AI LL s m x ↔ ∀ i, ∃ c : OCb l,
      (crd (basisO LL) i x).coeff 0 = algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ m * c) := by
  have key : ∀ (a : RA LL) i, (crd (basisO LL) i (piR AI LL s ^ m * inclR LL a)).coeff 0 =
      algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ m * (crd (basisO LL) i a).coeff 0) := by
    intro a i
    have h1 : piR AI LL s ^ m = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (inclW l (piW AI s) ^ m) := by
      rw [piR_eq, Algebra.TensorProduct.tmul_pow, one_pow]
    have h2 : crd (basisO LL) i (inclR LL a) = inclW l (crd (basisO LL) i a) :=
      crd_map (basisO LL) (inclWA l) i a
    have h3 : (inclW l (crd (basisO LL) i a)).coeff 0 =
        algebraMap (OCb l) (Cb l) ((crd (basisO LL) i a).coeff 0) := WittVector.map_coeff _ _ _
    have h4 : (inclW l (piW AI s) ^ m).coeff 0 = (inclW l (piW AI s)).coeff 0 ^ m :=
      map_pow (WittVector.constantCoeff : WCb l →+* Cb l) _ _
    rw [h1, crd_mul, h2, WittVector.mul_coeff_zero, h3, h4, coeff_zero_piW, map_mul, map_pow]
  constructor
  · rintro ⟨a, r, h⟩ i
    refine ⟨(crd (basisO LL) i a).coeff 0, ?_⟩
    have h' : x - piR AI LL s ^ m * inclR LL a = (l : RW LL) * r := sub_eq_of_eq_add' h
    have h5 := (dvd_iff_crd LL _).1 ⟨r, h'⟩ i
    rw [LinearMap.map_sub, sub_coeff_zero] at h5
    exact (sub_eq_zero.1 h5).trans (key a i)
  · intro h
    choose c hc using h
    obtain ⟨a, ha⟩ : ∃ a : RA LL, ∀ i, (crd (basisO LL) i a).coeff 0 = c i :=
      ⟨∑ j, basisO LL j ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (c j), fun i => by
        rw [crd_sum, WittVector.teichmuller_coeff_zero]⟩
    obtain ⟨r, hr⟩ := (dvd_iff_crd LL (x - piR AI LL s ^ m * inclR LL a)).2 fun i => by
      have h6 := key a i
      rw [ha] at h6
      rw [LinearMap.map_sub, sub_coeff_zero]
      exact sub_eq_zero.2 ((hc i).trans h6.symm)
    exact ⟨a, r, eq_add_of_sub_eq' hr⟩

end GlobalTheory.Decompl
