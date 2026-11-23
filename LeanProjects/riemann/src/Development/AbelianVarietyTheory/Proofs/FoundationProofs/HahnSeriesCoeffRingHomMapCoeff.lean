import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KroneckerCongruence

section Frob

variable {R : Type} [CommRing R]

theorem pow_coeff_lt (y : HahnSeries ℚ R) (N : ℚ) (hy : ∀ t, y.coeff t ≠ 0 → t < N) :
    ∀ k : ℕ, ∀ t, (y ^ (k + 1)).coeff t ≠ 0 → t < (k + 1) * N := by
  intro k
  induction k with
  | zero => intro t ht; simpa using hy t (by simpa using ht)
  | succ k ih =>
    intro t ht
    rw [pow_succ] at ht
    have hmem : t ∈ (y ^ (k + 1) * y).support := ht
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.1 (HahnSeries.support_mul_subset hmem)
    have h1 := ih u hu
    have h2 := hy v hv
    push_cast; linarith

theorem pow_coeff_gt (y : HahnSeries ℚ R) (N : ℚ) (hy : ∀ t, y.coeff t ≠ 0 → N < t) :
    ∀ k : ℕ, ∀ t, (y ^ (k + 1)).coeff t ≠ 0 → (k + 1) * N < t := by
  intro k
  induction k with
  | zero => intro t ht; simpa using hy t (by simpa using ht)
  | succ k ih =>
    intro t ht
    rw [pow_succ] at ht
    have hmem : t ∈ (y ^ (k + 1) * y).support := ht
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.1 (HahnSeries.support_mul_subset hmem)
    have h1 := ih u hu
    have h2 := hy v hv
    push_cast; linarith

theorem coeff_pow_char (p : ℕ) [hp : Fact p.Prime] [CharP R p] (x : HahnSeries ℚ R) (n : ℚ) :
    (x ^ p).coeff n = (x.coeff (n / p)) ^ p := by
  classical
  haveI : CharP (HahnSeries ℚ R) p :=
    charP_of_injective_ringHom (HahnSeries.C_injective) p
  set N : ℚ := n / p with hN
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpN : (p : ℚ) * N = n := by rw [hN]; field_simp
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
  have hkq : ((k : ℚ) + 1) * N = n := by rw [← hpN, hk]; push_cast; ring
  set a := HahnSeries.truncLT N x with ha_def
  set c := HahnSeries.single N (x.coeff N) with hc_def
  set b := x - a - c with hb_def
  have hx : x = a + c + b := by rw [hb_def]; abel
  have ha : ∀ t, a.coeff t ≠ 0 → t < N := by
    intro t ht; by_contra h; push_neg at h; exact ht (HahnSeries.coeff_truncLT_of_le h x)
  have hb : ∀ t, b.coeff t ≠ 0 → N < t := by
    intro t ht; by_contra h; push_neg at h; apply ht
    rw [hb_def, HahnSeries.coeff_sub, HahnSeries.coeff_sub, ha_def, hc_def, HahnSeries.coeff_truncLT]
    rcases h.lt_or_eq with h | h
    · rw [if_pos h, HahnSeries.coeff_single_of_ne h.ne]; simp
    · subst h; simp
  rw [show x ^ p = (a + c + b) ^ p by rw [← hx], add_pow_char, add_pow_char, HahnSeries.coeff_add, HahnSeries.coeff_add]
  have h1 : (a ^ p).coeff n = 0 := by
    by_contra h
    rw [hk] at h
    have := pow_coeff_lt a N ha k n h
    linarith
  have h3 : (b ^ p).coeff n = 0 := by
    by_contra h
    rw [hk] at h
    have := pow_coeff_gt b N hb k n h
    linarith
  have h2 : (c ^ p).coeff n = x.coeff N ^ p := by
    rw [hc_def, HahnSeries.single_pow, nsmul_eq_mul, hpN]; simp
  rw [h1, h2, h3]; simp

end Frob

section Roots

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

theorem eOm_spec (hε : Function.Injective ε) (y : ℚ) :
    ε (eOm ε y) = Complex.exp (2 * Real.pi * Complex.I * (y : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff hε).2 inferInstance
  have hn : 0 < y.den := y.den_pos
  haveI : NeZero y.den := ⟨hn.ne'⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω y.den
  have hεω := hω.map_of_injective hε
  have hz : (Complex.exp (2 * Real.pi * Complex.I * (y : ℂ))) ^ y.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨y.num, ?_⟩
    have e : (y.den : ℂ) * (y : ℂ) = (y.num : ℂ) := by
      have := Rat.mul_den_eq_num y
      exact_mod_cast (by rw [mul_comm]; exact this)
    linear_combination (2 * Real.pi * Complex.I) * e
  obtain ⟨i, -, hi⟩ := hεω.eq_pow_of_pow_eq_one hz
  have hr : ∃ w, ε w = Complex.exp (2 * Real.pi * Complex.I * (y : ℂ)) := ⟨ω ^ i, by rw [map_pow, hi]⟩
  exact Function.invFun_eq hr

theorem eOm_zero (hε : Function.Injective ε) : eOm ε 0 = 1 := by
  apply hε; rw [eOm_spec hε, map_one]; simp

theorem eOm_mul_nat (hε : Function.Injective ε) (n : ℕ) (y : ℚ) : eOm ε (n * y) = eOm ε y ^ n := by
  apply hε; rw [map_pow, eOm_spec hε, eOm_spec hε, ← Complex.exp_nat_mul]; push_cast; ring_nf

theorem eOm_intCast (hε : Function.Injective ε) (z : ℤ) : eOm ε z = 1 := by
  apply hε; rw [eOm_spec hε, map_one, Complex.exp_eq_one_iff]; exact ⟨z, by push_cast; ring⟩

end Roots

end GlobalTheory.KroneckerCongruence

namespace GlobalTheory.KroneckerCongruence

section Mat

theorem ent_toGQ (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (i j : Fin 2) : ent (toGQ m) i j = (m i j : ℚ) := by
  simp [ent, toGQ, h]

theorem ent_ofSL (γ : SL(2, ℤ)) (i j : Fin 2) : ent (ofSL γ) i j = ((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := by
  simp [ent, ofSL]

theorem toGQ_mul (γ : SL(2, ℤ)) (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) :
    toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * m) = ofSL γ * toGQ m := by
  have hd : 0 < ((γ : Matrix (Fin 2) (Fin 2) ℤ) * m).det := by
    rw [Matrix.det_mul, γ.det_coe, one_mul]; exact h
  apply Subtype.ext; apply Units.ext
  ext i j
  simp [toGQ, hd, h, ofSL, Matrix.mul_apply]

end Mat

section Val

variable {Ω : Type} [Field Ω] (V : ValuationSubring Ω)

def liftV (x : HahnSeries ℚ Ω) (h : ∀ r, x.coeff r ∈ V) : HahnSeries ℚ V where
  coeff r := ⟨x.coeff r, h r⟩
  isPWO_support' := x.isPWO_support.mono fun r hr h0 => hr (Subtype.ext h0)

def hahnSeriesCoeffRingHomMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : HahnSeries ℚ R →+* HahnSeries ℚ S where
  toFun x := x.map f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

theorem hahnSeriesCoeffRingHomMap_coeff {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : HahnSeries ℚ R) (r : ℚ) :
    (hahnSeriesCoeffRingHomMap f x).coeff r = f (x.coeff r) := HahnSeries.map_coeff x f r

theorem map_liftV (x : HahnSeries ℚ Ω) (h : ∀ r, x.coeff r ∈ V) : hahnSeriesCoeffRingHomMap V.subtype (liftV V x h) = x := by
  ext r; rw [hahnSeriesCoeffRingHomMap_coeff]; rfl

theorem mem_of_pow_eq_one {w : Ω} {n : ℕ} (hn : n ≠ 0) (hw : w ^ n = 1) : w ∈ V := by
  rw [← ValuationSubring.valuation_le_one_iff]
  by_contra h
  push_neg at h
  have := one_lt_pow₀ h hn
  rw [← map_pow, hw, map_one] at this
  exact lt_irrefl _ this

end Val

end GlobalTheory.KroneckerCongruence

namespace GlobalTheory.KroneckerCongruence

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem eOm_level (X : Tower Ω ε) (M : ℕ) (f : X.K) (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f)
    (r : ℚ) (hr : (X.exp f).coeff r ≠ 0) : eOm ε (r * M) = 1 := by
  let γ : SL(2, ℤ) := ⟨!![1, (M : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩
  have hγ : γ ∈ CongruenceSubgroup.Gamma M := by
    rw [CongruenceSubgroup.Gamma_mem]; simp [γ]
  have h := X.exp_upper (ofSL γ) (by rw [ent_ofSL]; simp [γ]) f r
  rw [hf γ hγ, ent_ofSL, ent_ofSL, ent_ofSL] at h
  simp [γ] at h
  have h2 : (eOm ε (r * M) - 1) * (X.exp f).coeff r = 0 := by rw [sub_mul, ← h]; ring
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact sub_eq_zero.1 h3
  · exact absurd h3 hr

end GlobalTheory.KroneckerCongruence

namespace GlobalTheory.KZ

open GlobalTheory.KroneckerCongruence in

theorem kronecker_congruence_tower : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (M q : ℕ) (f : X.K), 0 < M → q.Prime → Nat.Coprime q M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ∀ (σ : SL(2, ℤ)), ((en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), ((q : ℕ) : Ω) ∈ V.nonunits → (∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1) → (∀ r, (X.exp f).coeff r ∈ V) → (∀ r, (X.exp (X.sl (ofSL σ) f)).coeff r ∈ V) → ∀ r, (X.exp ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f - X.gal s f * (X.gal s.symm (X.sl (ofSL σ) f)) ^ q)).coeff r ∈ V.nonunits := by
  intro Ω _ _ _ ε X hε _ M q f hM hq _ hf σ _ V s hqV hs hfV hσV r
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ x : V, ρ x = 0 ↔ V.valuation (x : Ω) < 1 := fun x => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  haveI : CharP (IsLocalRing.ResidueField V) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    have : ρ (q : V) = 0 := (hρ0 _).2 (by simpa [ValuationSubring.mem_nonunits_iff] using hqV)
    simpa using this)
  have hfrob : ∀ x : V, ρ ⟨s x, (hs x x.2).1⟩ = ρ x ^ q := by
    intro x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, hρ0]
    simpa using (hs x x.2).2.2

  set c := X.exp f with hc
  set c' := X.exp (X.sl (ofSL σ) f) with hc'
  have hdet : ∀ j : ℕ, 0 < (!![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    intro j; simp [Matrix.det_fin_two]; exact_mod_cast hq.pos
  have hFj : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t =
      eOm ε (t * j * M) * c.coeff (t * q) := by
    intro j t
    have h := X.exp_upper (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) (by rw [ent_toGQ _ (hdet j)]; simp) f (t * q)
    rw [ent_toGQ _ (hdet j), ent_toGQ _ (hdet j), ent_toGQ _ (hdet j)] at h
    simp at h
    convert h using 2 <;> first | field_simp | (congr 1; field_simp)
  have hdq : 0 < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; exact_mod_cast hq.pos
  have hB : ∀ t : ℚ, (X.exp (X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f)).coeff t =
      c'.coeff (t / q) := by
    intro t
    rw [toGQ_mul σ _ hdq, X.sl_mul]
    have h := X.exp_upper (toGQ !![(q : ℤ), 0; 0, 1]) (by rw [ent_toGQ _ hdq]; simp) (X.sl (ofSL σ) f) (t / q)
    rw [ent_toGQ _ hdq, ent_toGQ _ hdq, ent_toGQ _ hdq] at h
    simp [eOm_zero hε] at h
    rw [← h]

  have hw : ∀ (j : ℕ) (t : ℚ), c.coeff (t * q) ≠ 0 → ∃ h : eOm ε (t * j * M) ∈ V, ρ ⟨_, h⟩ = 1 := by
    intro j t ht
    have h1 : eOm ε (t * j * M) ^ q = 1 := by
      rw [← eOm_mul_nat hε, show (q : ℚ) * (t * j * M) = j * (t * q * M) by ring, eOm_mul_nat hε,
        eOm_level X M f hf _ ht, one_pow]
    have hmem : eOm ε (t * j * M) ∈ V := mem_of_pow_eq_one V hq.ne_zero h1
    refine ⟨hmem, ?_⟩
    have h2 : (⟨_, hmem⟩ : V) ^ q = 1 := Subtype.ext (by simpa using h1)
    have h3 : (ρ ⟨_, hmem⟩ - 1) ^ q = 0 := by rw [sub_pow_char, ← map_pow, h2, map_one, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff hq.ne_zero |>.1 h3)
  have memF : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t ∈ V := by
    intro j t
    rw [hFj]
    by_cases h0 : c.coeff (t * q) = 0
    · rw [h0, mul_zero]; exact zero_mem V
    · exact mul_mem (hw j t h0).1 (hfV _)
  have redF : ∀ (j : ℕ) (t : ℚ), ρ ⟨_, memF j t⟩ = ρ ⟨_, hfV (t * q)⟩ := by
    intro j t
    by_cases h0 : c.coeff (t * q) = 0
    · exact congrArg ρ (Subtype.ext (by simp only; rw [hFj, h0, mul_zero]))
    · obtain ⟨hm, h1⟩ := hw j t h0
      have e : (⟨_, memF j t⟩ : V) = ⟨_, hm⟩ * ⟨_, hfV (t * q)⟩ := Subtype.ext (by simp only [MulMemClass.mk_mul_mk]; rw [hFj])
      rw [e, map_mul, h1, one_mul]
  have memB : ∀ t : ℚ, (X.exp (X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f)).coeff t ∈ V := by
    intro t; rw [hB]; exact hσV _
  have memC : ∀ t : ℚ, (X.exp (X.gal s f)).coeff t ∈ V := by
    intro t; rw [X.gal_exp]; exact (hs _ (hfV t)).1
  have memD : ∀ t : ℚ, (X.exp (X.gal s.symm (X.sl (ofSL σ) f))).coeff t ∈ V := by
    intro t; rw [X.gal_exp]; exact (hs _ (hσV t)).2.1

  set LF : ℕ → HahnSeries ℚ V := fun j => liftV V _ (memF j) with hLF
  set LB := liftV V _ memB with hLB
  set LC := liftV V _ memC with hLC
  set LD := liftV V _ memD with hLD
  have h1 : ∀ j, hahnSeriesCoeffRingHomMap ρ (LF j) = hahnSeriesCoeffRingHomMap ρ (LF 0) := by
    intro j; ext t; rw [hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]; exact (redF j t).trans (redF 0 t).symm
  have h2 : hahnSeriesCoeffRingHomMap ρ (LF 0) ^ q = hahnSeriesCoeffRingHomMap ρ LC := by
    ext t
    rw [coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]
    show ρ ⟨_, memF 0 (t / q)⟩ ^ q = ρ ⟨_, memC t⟩
    rw [redF 0 (t / q), ← hfrob]
    exact congrArg ρ (Subtype.ext (by simp only; rw [X.gal_exp, div_mul_cancel₀ t hq0]))
  have h3 : hahnSeriesCoeffRingHomMap ρ LD ^ q = hahnSeriesCoeffRingHomMap ρ LB := by
    ext t
    rw [coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]
    show ρ ⟨_, memD (t / q)⟩ ^ q = ρ ⟨_, memB t⟩
    rw [← hfrob]
    exact congrArg ρ (Subtype.ext (by simp only; rw [X.gal_exp, hB, AlgEquiv.apply_symm_apply]))
  have hexp : X.exp ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f) *
      X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f -
      X.gal s f * (X.gal s.symm (X.sl (ofSL σ) f)) ^ q) =
      hahnSeriesCoeffRingHomMap V.subtype ((∏ j ∈ Finset.range q, LF j) * LB - LC * LD ^ q) := by
    simp only [map_sub, map_mul, map_prod, map_pow, hLF, hLB, hLC, hLD, map_liftV]
  have hW : hahnSeriesCoeffRingHomMap ρ ((∏ j ∈ Finset.range q, LF j) * LB - LC * LD ^ q) = 0 := by
    rw [map_sub, map_mul, map_prod, map_mul, map_pow, Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_const,
      Finset.card_range, h2, h3, sub_self]
  rw [hexp, hahnSeriesCoeffRingHomMap_coeff, ValuationSubring.mem_nonunits_iff]
  refine (hρ0 (((∏ j ∈ Finset.range q, LF j) * LB - LC * LD ^ q).coeff r)).1 ?_
  rw [← hahnSeriesCoeffRingHomMap_coeff, hW]
  rfl

end GlobalTheory.KZ
