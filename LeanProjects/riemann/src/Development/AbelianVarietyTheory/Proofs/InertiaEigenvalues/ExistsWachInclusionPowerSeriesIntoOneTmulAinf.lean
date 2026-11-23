import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbWInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS
open scoped Formalism.Per

namespace GlobalTheory.PrismS.IoDescent

section General

variable {Z O A : Type} [CommRing Z] [CommRing O] [CommRing A] [Algebra Z O] [Algebra Z A]

theorem exists_retraction [IsLocalRing Z] [Module.Free Z O] (p : Z)
    (hp : IsLocalRing.maximalIdeal Z = Ideal.span {p}) (hu : ¬ IsUnit (algebraMap Z O p)) :
    ∃ r : O →ₗ[Z] Z, r 1 = 1 := by
  let b := Module.Free.chooseBasis Z O
  by_cases h : ∃ i, IsUnit (b.repr 1 i)
  · obtain ⟨i, hi⟩ := h
    obtain ⟨v, hv⟩ := hi.exists_left_inv
    exact ⟨v • b.coord i, by simpa using hv⟩
  · exfalso
    apply hu
    have h1 : ∀ i, p ∣ b.repr 1 i := fun i => by
      rw [← Ideal.mem_span_singleton, ← hp, IsLocalRing.mem_maximalIdeal]
      exact fun hi => h ⟨i, hi⟩
    refine isUnit_of_dvd_one ?_
    rw [← b.linearCombination_repr 1, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.dvd_sum fun i _ => ?_
    rw [Algebra.smul_def]
    exact (map_dvd _ (h1 i)).mul_right _

theorem exists_factor {W : Type} [CommRing W] (r : O →ₗ[Z] Z) (hr : r 1 = 1)
    (f : PowerSeries W →+* O ⊗[Z] A) (π : A) (hX : f PowerSeries.X = (1 : O) ⊗ₜ[Z] π)
    (hC : ∀ w, ∃ a, f (PowerSeries.C w) = (1 : O) ⊗ₜ[Z] a)
    (hs : IsHausdorff (Ideal.span {(1 : O) ⊗ₜ[Z] π}) (O ⊗[Z] A)) :
    (∀ a b : A, (1 : O) ⊗ₜ[Z] a = (1 : O) ⊗ₜ[Z] b → a = b) ∧
      ∃ io : PowerSeries W →+* A, ∀ x, f x = (1 : O) ⊗ₜ[Z] io x := by
  let p : O ⊗[Z] A →ₗ[Z] A := (TensorProduct.lid Z A).toLinearMap ∘ₗ r.rTensor A
  have hp : ∀ o a, p (o ⊗ₜ a) = r o • a := fun o a => by simp [p]
  have hp1 : ∀ a, p (1 ⊗ₜ a) = a := fun a => by rw [hp, hr, one_smul]
  let j : A →+* O ⊗[Z] A := (Algebra.TensorProduct.includeRight (R := Z) (A := O) (B := A)).toRingHom
  have hj : ∀ a, j a = (1 : O) ⊗ₜ[Z] a := fun _ => rfl
  have hpm : ∀ a y, p (j a * y) = a * p y := fun a y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul o b => rw [hj, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hp, hp, mul_smul_comm]
    | add y z hy hz => rw [mul_add, map_add, map_add, hy, hz, mul_add]
  have hinj : Function.Injective j := fun a b h => by
    rw [← hp1 a, ← hp1 b, ← hj, ← hj, h]
  have hpoly : ∀ q : Polynomial W, f (q : PowerSeries W) ∈ j.range := fun q => by
    induction q using Polynomial.induction_on' with
    | add q q' h h' => rw [Polynomial.coe_add, map_add]; exact add_mem h h'
    | monomial n w =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C,
        Polynomial.coe_X, map_mul, map_pow]
      obtain ⟨a, ha⟩ := hC w
      exact mul_mem (RingHom.mem_range.2 ⟨a, ha.symm⟩) (pow_mem (RingHom.mem_range.2 ⟨π, hX.symm⟩) _)
  have hall : ∀ x, f x ∈ j.range := fun x => by
    refine ⟨p (f x), ?_⟩
    rw [← sub_eq_zero]
    refine hs.haus _ fun m => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨x', hx'⟩ : ∃ x', x = ((PowerSeries.trunc m x : Polynomial W) : PowerSeries W) + PowerSeries.X ^ m * x' :=
      ⟨_, PowerSeries.eq_X_pow_mul_shift_add_trunc m x |>.trans (add_comm _ _)⟩
    obtain ⟨a, ha⟩ := hpoly (PowerSeries.trunc m x)
    have e : f x = j a + j (π ^ m) * f x' := by
      conv_lhs => rw [hx']
      rw [map_add, map_mul, map_pow, hX, ha, map_pow, hj]
    refine ⟨j (p (f x')) - f x', ?_⟩
    rw [e, map_add, hpm, hj a, hp1, map_add, map_mul, ← hj a, ← hj π, map_pow]
    ring
  refine ⟨fun a b h => hinj h, ?_⟩
  let e : A ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (f.codRestrict j.range hall), fun x => ?_⟩
  have := congrArg Subtype.val (e.apply_symm_apply (f.codRestrict j.range hall x))
  exact this.symm

theorem tmul_algebraMap (c : Z) :
    algebraMap O (O ⊗[Z] A) (algebraMap Z O c) = (1 : O) ⊗ₜ[Z] algebraMap Z A c := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]

theorem exists_sum {W C : Type} [CommRing W] [CommRing C] (F : W →+* O ⊗[Z] A) (θ : A →+* C) (g : W →+* C)
    {n : ℕ} (z u : Fin n → W) (hz : ∀ i, ∃ a, F (z i) = (1 : O) ⊗ₜ[Z] a ∧ θ a = g (z i))
    (hu : ∀ i, ∃ a, F (u i) = (1 : O) ⊗ₜ[Z] a ∧ θ a = g (u i)) :
    ∃ a, F (∑ i, z i * u i) = (1 : O) ⊗ₜ[Z] a ∧ θ a = g (∑ i, z i * u i) := by
  choose a a1 a2 using hz
  choose b b1 b2 using hu
  refine ⟨∑ i, a i * b i, ?_, ?_⟩
  · rw [map_sum, tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, a1, b1, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, a2, b2]

end General

variable {l : ℕ} [Fact l.Prime]

theorem εroot_pow {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : AI.εroot s ^ l ^ s = AI.ε := by
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ s ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem εroot_sub_not_unit {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : ¬ IsUnit (AI.εroot s - 1) := by
  intro h
  have h1 := (h.pow (l ^ s)).map (PreTilt.coeff (O := OC l) (p := l) 0)
  rw [sub_pow_char_pow, εroot_pow, one_pow, map_sub, AI.ε_coeff, AI.ζ_zero, map_one, map_one,
    sub_self] at h1
  exact not_isUnit_zero h1

theorem letEmb_C {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (w : WK K) :
    letEmb emb (PowerSeries.C w) = fun k => PowerSeries.C (embW (emb k) w) := by
  funext k
  rw [letEmb_apply, PowerSeries.map_C]
  rfl

theorem letEmb_X {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) :
    letEmb emb PowerSeries.X = letπ := by
  funext k
  rw [letEmb_apply, PowerSeries.map_X]
  rfl

theorem letEmb_scalar {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (c : ℤ_[l]) :
    letEmb emb (PowerSeries.C (algebraMap ℤ_[l] (WK K) c)) =
      algebraMap ↥(OL LL) (LetA ↥(OL LL) n) (algebraMap ℤ_[l] ↥(OL LL) c) := by
  rw [letEmb_C]
  funext k
  rw [(embW (emb k)).commutes c]
  rfl

theorem map_scalar {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (φ : LetA ↥(OL LL) n →ₐ[↥(OL LL)] RA LL) (c : ℤ_[l]) :
    φ (letEmb emb (PowerSeries.C (algebraMap ℤ_[l] (WK K) c))) =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] algebraMap ℤ_[l] (Ainf l) c := by
  rw [letEmb_scalar, AlgHom.commutes, tmul_algebraMap]

theorem theta_scalar (K : FinExt l) (c : ℤ_[l]) :
    Formalism.Per.θ l (algebraMap ℤ_[l] (Ainf l) c) = intToOC K (algebraMap ℤ_[l] ↥(OL K) c) :=
  Subtype.ext ((GlobalTheory.UnramIdem.ringHom_eq ((Formalism.Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) c).trans
    (GlobalTheory.UnramIdem.ringHom_eq ((intToOC K).comp (algebraMap ℤ_[l] ↥(OL K))) c).symm)

theorem exists_span (K : FinExt l) (w : WK K) : ∃ (n : ℕ) (z : Fin n → ℤ_[l]) (u : Fin n → WK K),
    (∀ i, ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ((u i : ↥(K0 K)) : Om l) ^ m = 1) ∧
      w = ∑ i, algebraMap ℤ_[l] (WK K) (z i) * u i := by
  obtain ⟨n, z, ω, hω, hsum⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K ((w : ↥(K0 K)) : Om l)
    (w : ↥(K0 K)).2 (norm_le_one_of_mem_OL (unr K) w)
  choose h0 m hm hl h1 using hω
  refine ⟨n, z, fun i => ⟨⟨ω i, h0 i⟩, IsIntegral.of_pow (hm i) (by
    rw [show (⟨ω i, h0 i⟩ : ↥(K0 K)) ^ m i = 1 from Subtype.ext (h1 i)]; exact isIntegral_one)⟩,
    fun i => ⟨m i, hm i, hl i, h1 i⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rw [hsum]
  push_cast
  rfl

theorem exists_const {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (φ : LetA ↥(OL LL) n →ₐ[↥(OL LL)] RA LL)
    (hI : ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → ∀ xb : OCb l,
      IsTiltOf (c : Om l) m xb → ∀ o : ZMod n → ↥(OL LL), (∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = emb i c) →
      φ (fun i => PowerSeries.C (o i)) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l xb) (w : WK K) :
    ∃ a : Ainf l, φ (letEmb emb (PowerSeries.C w)) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] a ∧
      Formalism.Per.θ l a = intToOC (unr K) w := by
  obtain ⟨r, z, u, hu, rfl⟩ := exists_span K w
  refine exists_sum ((φ.toRingHom.comp (letEmb emb)).comp PowerSeries.C) (Formalism.Per.θ l)
    (intToOC (unr K)) (fun i => algebraMap ℤ_[l] (WK K) (z i)) u
    (fun i => ⟨_, map_scalar emb φ (z i), theta_scalar (unr K) (z i)⟩) (fun i => ?_)
  obtain ⟨m, hm, hl, h1⟩ := hu i
  obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf _ m hm hl h1
  refine ⟨WittVector.teichmuller l xb, ?_, ?_⟩
  · change φ (letEmb emb (PowerSeries.C (u i))) = _
    rw [letEmb_C]
    exact hI _ m hm hl h1 xb hxb _ (fun k => rfl)
  · apply Subtype.ext
    exact (congrArg Subtype.val (WittVector.fontaineTheta_teichmuller xb)).trans
      (GlobalTheory.MemLoc.IsTiltOf.untilt_eq hxb)

theorem exists_io {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (φ : LetA ↥(OL LL) n →ₐ[↥(OL LL)] RA LL) (e : OCb l) (he : ¬ IsUnit (e - 1))
    (hπ : φ letπ = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1))
    (hC : ∀ w : WK K, ∃ a : Ainf l, φ (letEmb emb (PowerSeries.C w)) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] a ∧
      Formalism.Per.θ l a = intToOC (unr K) w) :
    ∃ io : PowerSeries (WK K) →+* Ainf l, (∀ x, φ (letEmb emb x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] io x) ∧
      io PowerSeries.X = WittVector.teichmuller l e - 1 ∧
      ∀ w : WK K, Formalism.Per.θ l (io (PowerSeries.C w)) = intToOC (unr K) w := by
  obtain ⟨_, -, -, hu, hfree, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨r, hr⟩ := exists_retraction (Z := ℤ_[l]) (O := ↥(OL LL)) (l : ℤ_[l])
    PadicInt.maximalIdeal_eq_span_p (by rwa [map_natCast])
  have hX : φ (letEmb emb PowerSeries.X) =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1) := by
    rw [letEmb_X, hπ]
  obtain ⟨hinj, io, hio⟩ := exists_factor r hr (φ.toRingHom.comp (letEmb emb)) _ hX
    (fun w => (hC w).imp fun a h => h.1)
    ((GlobalTheory.HWL.TensorWitt.main l LL).2.2.2.2 e he).toIsHausdorff
  refine ⟨io, hio, hinj _ _ ((hio _).symm.trans hX), fun w => ?_⟩
  obtain ⟨a, h1, h2⟩ := hC w
  rw [hinj _ _ ((hio _).symm.trans h1), h2]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∃ io : PowerSeries (WK K) →+* Ainf l, (∀ x, I.io (letEmb Γ.emb x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] io x) ∧ io PowerSeries.X = WittVector.teichmuller l (AI.εroot s) - 1 ∧ ∀ w : WK K, Formalism.Per.θ l (io (PowerSeries.C w)) = intToOC (unr K) w :=
  fun _ _ _ AI _ s _ Γ _ I hI =>
    exists_io Γ.emb I.io _ (εroot_sub_not_unit AI s) I.io_π (exists_const Γ.emb I.io hI)

end GlobalTheory.PrismS.IoDescent
