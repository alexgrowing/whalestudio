import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HeckeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FinDim
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped MatrixGroups ModularForm

noncomputable section

namespace UpperTheory.V.Sd

private theorem one_mem_per (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
  rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1

private theorem coef_smul {N : ℕ} {k : ℤ} (c : ℂ) (f : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (c • f : CuspForm (Gamma1 N) k) n = c * coef f n := by
  unfold coef
  rw [show ((c • f : CuspForm (Gamma1 N) k) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl,
    ModularForm.qExpansion_smul one_pos (one_mem_per N) c f]
  simp

private theorem coef_add {N : ℕ} {k : ℤ} (f g : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (f + g : CuspForm (Gamma1 N) k) n = coef f n + coef g n := by
  unfold coef
  rw [← map_add]
  congr 1
  exact ModularForm.qExpansion_add one_pos (one_mem_per N) f g

private def fT {K : Type} [Field K] (p : ℕ) (e : K) : Module.End K (ℕ → K) where
  toFun c n := c (p * n) + e * (if p ∣ n then c (n / p) else 0)
  map_add' c d := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring
  map_smul' a c := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring

private theorem fT_apply {K : Type} [Field K] (p : ℕ) (e : K) (c : ℕ → K) (n : ℕ) :
    fT p e c n = c (p * n) + e * (if p ∣ n then c (n / p) else 0) := rfl

private theorem fT_comm {K : Type} [Field K] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (e e' : K)
    (c : ℕ → K) : fT p e (fT q e' c) = fT q e' (fT p e c) := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  funext n
  simp only [fT_apply]
  have h1 : q ∣ p * n ↔ q ∣ n := hc.symm.dvd_mul_left
  have h2 : p ∣ q * n ↔ p ∣ n := hc.dvd_mul_left
  by_cases a : p ∣ n <;> by_cases b : q ∣ n
  · obtain ⟨m, rfl⟩ : p * q ∣ n := hc.mul_dvd_of_dvd_of_dvd a b
    have e1 : p * q * m / p = q * m := by rw [mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    have e2 : p * q * m / q = p * m := by rw [mul_comm p q, mul_assoc, Nat.mul_div_cancel_left _ hq.pos]
    simp only [h1, h2, a, b, if_true, e1, e2, dvd_mul_right, Nat.mul_div_cancel_left _ hp.pos,
      Nat.mul_div_cancel_left _ hq.pos, Nat.mul_div_assoc _ a, Nat.mul_div_assoc _ b, mul_left_comm q p]
    ring
  · have b' : ¬ q ∣ n / p := fun h => b (h.trans (Nat.div_dvd_of_dvd a))
    simp only [h1, h2, a, b, b', if_true, if_false, Nat.mul_div_assoc _ a, mul_left_comm q p]
    ring
  · have a' : ¬ p ∣ n / q := fun h => a (h.trans (Nat.div_dvd_of_dvd b))
    simp only [h1, h2, a, b, a', if_true, if_false, Nat.mul_div_assoc _ b, mul_left_comm q p]
    ring
  · simp only [h1, h2, a, b, if_false, mul_left_comm q p]
    ring

private theorem eq_zero_of_eig {K : Type} [Field K] (e b : Nat.Primes → K) (c : ℕ → K) (h0 : c 0 = 0) (h1 : c 1 = 0)
    (h : ∀ p : Nat.Primes, fT p.1 (e p) c = b p • c) : c = 0 := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact h0
    by_cases hn1 : n = 1
    · subst hn1; exact h1
    obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
    have hm : 0 < m := Nat.pos_of_mul_pos_left hn
    have hlt : m < p * m := by nlinarith [hp.two_le]
    have := congrFun (h ⟨p, hp⟩) m
    have i1 := ih m hlt
    have i2 := ih (m / p) ((Nat.div_le_self _ _).trans_lt hlt)
    simp only [Pi.zero_apply] at i1 i2
    simpa [fT_apply, i1, i2] using this

private def chSub (N k : ℕ) (χ : DirichletCharacter ℂ N) : Submodule ℂ (CuspForm (Gamma1 N) (k : ℤ)) where
  carrier := {g | HasChar k χ g}
  add_mem' := by
    intro f g hf hg γ hγ
    rw [show ((f + g : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = (f : ℍ → ℂ) + g from rfl, SlashAction.add_slash,
      hf γ hγ, hg γ hγ, smul_add]
  zero_mem' := by
    intro γ _
    rw [show ((0 : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = 0 from rfl, SlashAction.zero_slash, smul_zero]
  smul_mem' := by
    intro c f hf γ hγ
    rw [show ((c • f : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl, ModularForm.SL_smul_slash,
      hf γ hγ, smul_comm]

section
open Module
variable {K M : Type} [Field K] [IsAlgClosed K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

end

private theorem normV_rat {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  have h : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hN : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
    simp
  have hd : Ideal.absNorm w.asIdeal ∣ p :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [h]
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact w.isPrime.ne_top

private def Phi (N : ℕ) (k : ℤ) : CuspForm (Gamma1 N) k →ₗ[ℂ] (ℕ → ℂ) where
  toFun g n := if n = 0 then 0 else coef g n
  map_add' f g := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_add, Pi.add_apply, add_zero]
  map_smul' a f := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_smul, Pi.smul_apply, smul_eq_mul, mul_zero]
    rfl

private theorem Phi_apply (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k) (n : ℕ) :
    Phi N k g n = if n = 0 then 0 else coef g n := rfl

private theorem fT_Phi (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k)
    {p : ℕ} (hp : p.Prime) (e : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    fT p e (Phi N k g) n = coef g (p * n) + e * (if p ∣ n then coef g (n / p) else 0) := by
  have h1 : p * n ≠ 0 := mul_ne_zero hp.ne_zero (by omega)
  rw [fT_apply, Phi_apply, if_neg h1]
  by_cases h : p ∣ n
  · have : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn h) hp.pos).ne'
    rw [if_pos h, if_pos h, Phi_apply, if_neg this]
  · rw [if_neg h, if_neg h]

private theorem eig_iff (N k : ℕ) (χ : DirichletCharacter ℂ N) (g : CuspForm (Gamma1 N) (k : ℤ)) {p : ℕ} (hp : p.Prime) (c : ℂ) :
    fT p (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) (Phi N k g) = c • Phi N k g ↔ IsEigAt k χ g p c := by
  constructor
  · intro h n hn
    have := congrFun h n
    rwa [fT_Phi N k g hp _ hn, Pi.smul_apply, Phi_apply, if_neg (show ¬ n = 0 by omega), smul_eq_mul] at this
  · intro h
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [fT_apply, Phi_apply]
    · rw [fT_Phi N k g hp _ hn, Pi.smul_apply, Phi_apply, if_neg hn.ne', smul_eq_mul]
      exact h n hn

private theorem exists_eigenform (N k : ℕ) [NeZero N] (hk : 1 ≤ k) (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) (k : ℤ)) (hf : HasChar k χ f) (hf0 : f ≠ 0) (a : ℕ → ℂ) :
    ∃ g : Eigenform k N χ, ∀ p : ℕ, p.Prime → IsEigAt k χ f p (a p) → g.a p = a p := by
  haveI := (finDim N k).1
  set V : Submodule ℂ (ℕ → ℂ) := (chSub N k χ).map (Phi N k) with hV
  let e : Nat.Primes → ℂ := fun p => χ ((p.1 : ℕ) : ZMod N) * ((p.1 : ℕ) : ℂ) ^ (k - 1)
  have hmem : ∀ p : Nat.Primes, ∀ v ∈ V, fT p.1 (e p) v ∈ V := by
    rintro p _ ⟨g, hg, rfl⟩
    obtain ⟨g', hg', hc⟩ := heckeEx N k hk χ g hg p.1 p.2
    refine ⟨g', hg', ?_⟩
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [fT_apply, Phi_apply]
    · rw [fT_Phi N k g p.2 _ hn, Phi_apply, if_neg hn.ne', hc n hn]
  let T : Nat.Primes → Module.End ℂ V := fun p => (fT p.1 (e p)).restrict (hmem p)
  have hT : ∀ p (v : V), (T p v).1 = fT p.1 (e p) v.1 := fun _ _ => rfl
  have hc : ∀ p q, T p * T q = T q * T p := by
    intro p q
    by_cases hpq : p = q
    · rw [hpq]
    · ext1 v
      apply Subtype.ext
      simp only [Module.End.mul_apply, hT]
      exact fT_comm p.2 q.2 (fun h => hpq (Subtype.ext h)) _ _ _
  let U : Submodule ℂ V := ⨅ p : {p : Nat.Primes // IsEigAt k χ f p.1 (a p.1)}, Module.End.eigenspace (T p.1) (a p.1.1)
  have hU : ∀ v : V, v ∈ U ↔ ∀ p : Nat.Primes, IsEigAt k χ f p.1 (a p.1) → T p v = a p.1 • v := fun v => by
    simp only [U, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Subtype.forall]
  obtain ⟨h, hhU, hne, heig⟩ := UpperTheory.V.LinAlg.simEig T hc _ U rfl
    ((Submodule.ne_bot_iff U).2 ⟨⟨Phi N k f, f, hf, rfl⟩,
      (hU _).2 fun p hp => Subtype.ext ((eig_iff N k χ f p.2 _).2 hp), fun h0 => hf0 ((finDim N k).2 f fun n hn => by
        have := congrFun (congrArg Subtype.val h0) n
        change Phi N k f n = 0 at this
        rwa [Phi_apply, if_neg (by omega)] at this)⟩)
    (by
      intro q x hx
      rw [hU] at hx ⊢
      intro p hp
      have h2 : T p (T q x) = T q (T p x) := congrArg (fun S : Module.End ℂ V => S x) (hc p q)
      rw [h2, hx p hp, map_smul])
  choose b hb using heig
  have hab : ∀ p : Nat.Primes, IsEigAt k χ f p.1 (a p.1) → b p = a p.1 := fun p hp =>
    smul_left_injective ℂ hne ((hb p).symm.trans ((hU h).1 hhU p hp))
  obtain ⟨_, g, hg, rfl⟩ := h
  have heig' : ∀ p : Nat.Primes, fT p.1 (e p) (Phi N k g) = b p • Phi N k g :=
    fun p => congrArg Subtype.val (hb p)
  have hg1 : coef g 1 ≠ 0 := by
    intro h0
    apply hne
    apply Subtype.ext
    exact eq_zero_of_eig e b _ (by simp [Phi_apply]) (by simp [Phi_apply, h0]) heig'
  have hE : ∀ p : Nat.Primes, IsEigAt k χ g p.1 (b p) := fun p => (eig_iff N k χ g p.2 _).1 (heig' p)
  have hp : ∀ p : Nat.Primes, coef ((coef g 1)⁻¹ • g : CuspForm (Gamma1 N) (k : ℤ)) p.1 = b p := by
    intro p
    have := hE p 1 le_rfl
    rw [if_neg p.2.not_dvd_one, mul_zero, add_zero, mul_one] at this
    rw [coef_smul, this]
    field_simp
  refine ⟨⟨(coef g 1)⁻¹ • g, (chSub N k χ).smul_mem _ hg, ?_, ?_⟩, ?_⟩
  · rw [coef_smul, inv_mul_cancel₀ hg1]
  · intro p hpp n hn
    rw [hp ⟨p, hpp⟩]
    have := hE ⟨p, hpp⟩ n hn
    simp only [coef_smul]
    split_ifs with hd
    · rw [if_pos hd] at this
      linear_combination (coef g 1)⁻¹ * this
    · rw [if_neg hd] at this
      linear_combination (coef g 1)⁻¹ * this
  · intro p hpp h
    exact (hp ⟨p, hpp⟩).trans (hab ⟨p, hpp⟩ h)

private theorem normV_prime (w : HeightOneSpectrum (𝓞 ℚ)) : (normV w).Prime := by
  have key : ∀ n : ℕ, n ≠ 0 → (n : 𝓞 ℚ) ∈ w.asIdeal → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 ℚ) ∈ w.asIdeal := by
    intro n
    induction n using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one => intro _ h; exact absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) w.isPrime.ne_top
    | prime p hp => intro _ h; exact ⟨p, hp, h⟩
    | mul a b iha ihb =>
      intro h0 h
      rw [Nat.cast_mul] at h
      exact (w.isPrime.mem_or_mem h).elim (iha (left_ne_zero_of_mul h0)) (ihb (right_ne_zero_of_mul h0))
  obtain ⟨p, hp, h⟩ := key _ (Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot) (Ideal.absNorm_mem w.asIdeal)
  rwa [normV_rat hp w h]

private theorem normV_surj {p : ℕ} (hp : p.Prime) : ∃ w : HeightOneSpectrum (𝓞 ℚ), normV w = p := by
  have h0 : Prime ((p : ℕ) : 𝓞 ℚ) := by
    have h : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : ((p : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((p : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h
  exact ⟨⟨Ideal.span {((p : ℕ) : 𝓞 ℚ)}, (Ideal.span_singleton_prime h0.ne_zero).mpr h0,
    by rw [Ne, Ideal.span_singleton_eq_bot]; exact h0.ne_zero⟩, normV_rat hp _ (Ideal.mem_span_singleton_self _)⟩

private theorem normV_finite {S : Set ℕ} (hS : S.Finite) : {w : HeightOneSpectrum (𝓞 ℚ) | normV w ∈ S}.Finite := by
  refine (hS.biUnion fun n _ => (Ideal.finite_setOf_absNorm_eq (S := 𝓞 ℚ) n).preimage
    (f := HeightOneSpectrum.asIdeal) (fun _ _ _ _ h => HeightOneSpectrum.ext h)).subset fun w hw => ?_
  simp only [Set.mem_iUnion]
  refine ⟨_, hw, ?_⟩
  show Ideal.absNorm w.asIdeal = normV w
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

private theorem tr_det {K : Type} [Field K] (ι : K ≃+* ℂ) {A : Matrix (Fin 2) (Fin 2) K} {a d : ℂ}
    (h : A.charpoly.map ι.toRingHom = X ^ 2 - C a * X + C d) : ι A.trace = a ∧ ι A.det = d := by
  rw [Matrix.charpoly_fin_two] at h
  have h0 := congrArg (Polynomial.coeff · 0) h
  have h1 := congrArg (Polynomial.coeff · 1) h
  simp at h0 h1
  exact ⟨h1, h0⟩

private theorem two_det {K : Type} [CommRing K] (A : Matrix (Fin 2) (Fin 2) K) :
    2 * A.det = A.trace ^ 2 - (A * A).trace := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem char_eq (H : Published.HidaGal) {k N M : ℕ} [NeZero N] [NeZero M] (hk : 2 ≤ k) {χ : DirichletCharacter ℂ N}
    {ψ : DirichletCharacter ℂ M} (g : Eigenform k N χ) (h : Eigenform k M ψ)
    (he : ∀ᶠ p : ℕ in Filter.cofinite, p.Prime → h.a p = g.a p) {p : ℕ} (hp : p.Prime) (h1 : ¬ p ∣ 2 * N) (h2 : ¬ p ∣ 2 * M) :
    χ (p : ZMod N) = ψ (p : ZMod M) := by
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨r, hr, -, hF⟩ := H k N hk χ g 2 (AlgebraicClosure ℚ) ι
  obtain ⟨r', hr', -, hF'⟩ := H k M hk ψ h 2 (AlgebraicClosure ℚ) ι
  have hfin := normV_finite (((Filter.eventually_cofinite.1 he).union
    (Set.finite_le_nat (2 * N))).union (Set.finite_le_nat (2 * M)))
  have htr : (fun s => (r s : Matrix (Fin 2) (Fin 2) (Qbar 2)).trace) = fun s => (r' s : Matrix (Fin 2) (Fin 2) (Qbar 2)).trace := by
    refine GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne' hfin
      (Units.continuous_val.comp hr).matrix_trace (Units.continuous_val.comp hr').matrix_trace ?_
    intro v hv _ B hB σ hσ
    simp only [Set.mem_setOf_eq, Set.mem_union, not_or, not_not] at hv
    have e1 := (tr_det ι (((hF v B hB).1 fun hd => hv.1.2 (Nat.le_of_dvd (by have := NeZero.pos N; omega) hd)).2 σ hσ)).1
    have e2 := (tr_det ι (((hF' v B hB).1 fun hd => hv.2 (Nat.le_of_dvd (by have := NeZero.pos M; omega) hd)).2 σ hσ)).1
    exact ι.injective (by rw [e1, e2, hv.1.1 (normV_prime v)])
  obtain ⟨w, rfl⟩ := normV_surj hp
  obtain ⟨A, hA⟩ := exists_isPlaceOver (AlgebraicClosure ℚ) w
  obtain ⟨σ, hσ⟩ := exists_isFrob hA
  have e1 := (tr_det ι (((hF w A hA).1 h1).2 σ hσ)).2
  have e2 := (tr_det ι (((hF' w A hA).1 h2).2 σ hσ)).2
  have t1 := congrFun htr σ
  have t2 := congrFun htr (σ * σ)
  simp only [map_mul, Units.val_mul] at t1 t2
  have hd : (r σ : Matrix (Fin 2) (Fin 2) (Qbar 2)).det = (r' σ : Matrix (Fin 2) (Fin 2) (Qbar 2)).det :=
    mul_left_cancel₀ (two_ne_zero) (by rw [two_det, two_det, t1, t2])
  rw [hd, e2] at e1
  exact (mul_right_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)) e1).symm

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.toNewform :
    UpperTheory.V.Sd.Hypotheses₂ → UpperTheory.V.Sd.ToNewform := by
  intro H k N _ hk χ hχ g
  refine ⟨⟨N, NeZero.pos N, g.f, χ, g.char, g.one, fun p hp _ => g.eig p hp, ?_⟩, rfl, fun _ => rfl, fun _ => rfl⟩
  intro M hM hne f ψ hf he
  by_contra hf0
  haveI : NeZero M := ⟨fun h => NeZero.ne N (by simpa [h] using hM)⟩
  obtain ⟨h, hh⟩ := exists_eigenform M k (by omega) ψ f hf hf0 (coef g.f)
  have he' : ∀ᶠ p : ℕ in Filter.cofinite, p.Prime → h.a p = g.a p := he.mono fun p hp hpp => hh p hpp (hp hpp)
  have hc : χ = DirichletCharacter.changeLevel hM ψ := by
    ext a
    obtain ⟨p, hp2, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod a.isUnit (2 * N)
    have hN := NeZero.pos N
    have hMN := Nat.le_of_dvd hN hM
    have e := char_eq H.hida hk g h he' hp (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
      (fun hd => absurd (Nat.le_of_dvd (by have := NeZero.pos M; omega) hd) (by omega))
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ← hpa, ZMod.cast_natCast hM, e]
  have h1 : χ.conductor ≤ M := Nat.sInf_le ⟨hM, ψ, hc⟩
  rw [hχ] at h1
  exact hne (le_antisymm (Nat.le_of_dvd (NeZero.pos N) hM) h1)
