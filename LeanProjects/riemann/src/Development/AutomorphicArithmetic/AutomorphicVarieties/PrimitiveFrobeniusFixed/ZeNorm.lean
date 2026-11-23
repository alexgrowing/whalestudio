import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GenBUnits
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.GeneralizedBernoulliChangeLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primeq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Condmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BNzany

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem ze_norm {l : ℕ} [Fact l.Prime] (c : HV.Coef l) :
    (∀ x : c.O, ‖(x : PadicAlgCl l)‖ ≤ 1) ∧ ∀ x y : c.O, ‖(y : PadicAlgCl l)‖ ≤ ‖(x : PadicAlgCl l)‖ → x ∣ y := by
  obtain ⟨hinj, -, -, -, -, h0, hfin, -, -⟩ := dvrFacts l c.O
  have hE : (eO l c.O).toNat ≠ 0 := by
    rw [Ne, ENat.toNat_eq_zero, not_or]
    exact ⟨h0, ne_top_of_le_ne_top (ENat.coe_ne_top _) hfin⟩
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  refine ⟨fun x => ?_, fun x y h => ?_⟩
  · rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have := normO l c.O x hx
      rw [← pow_le_one_iff_of_nonneg (norm_nonneg _) hE, this]
      exact pow_le_one₀ hl0.le hl1.le
  · rcases eq_or_ne y 0 with rfl | hy
    · exact dvd_zero _
    have hx : x ≠ 0 := by
      rintro rfl
      apply hy
      have : (y : PadicAlgCl l) = 0 := by simpa using h
      exact Subtype.ext this
    have h1 := pow_le_pow_left₀ (norm_nonneg _) h (eO l c.O).toNat
    rw [normO l c.O x hx, normO l c.O y hy, pow_le_pow_iff_right_of_lt_one₀ hl0 hl1] at h1
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd]
    have a1 : IsDiscreteValuationRing.addVal c.O x ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hx
    have a2 : IsDiscreteValuationRing.addVal c.O y ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hy
    rw [← ENat.coe_toNat a1, ← ENat.coe_toNat a2]
    exact_mod_cast h1

private theorem ze_chi {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] {F m k : ℕ} (h : l ^ m ∣ F) {g : G ℚ Ω} (hg : Pows F k g) :
    (l : O) ^ m ∣ (chiO ℚ Ω l O g : O) - k := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
  have h1 : g ζ = ζ ^ (PadicInt.toZModPow m ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec l g.toRingEquiv ζ hζ.pow_eq_one
  have h2 : g ζ = ζ ^ k := hg ζ (by obtain ⟨d, rfl⟩ := h; rw [pow_mul, hζ.pow_eq_one, one_pow])
  have h3 : (PadicInt.toZModPow m ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l])).val ≡ k [MOD l ^ m] := by
    have ho : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨_, NeZero.pos _, hζ.pow_eq_one⟩
    have := h1.symm.trans h2
    rwa [ho.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at this
  have h4 : ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) - k ∈ Ideal.span {(l : ℤ_[l]) ^ m} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ← (ZMod.natCast_eq_natCast_iff _ _ _).2 h3,
      ZMod.natCast_zmod_val, sub_self]
  have h5 := map_dvd (algebraMap ℤ_[l] O) (Ideal.mem_span_singleton.1 h4)
  simpa [chiO] using h5

private theorem ze_dir {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O]
    {f F k : ℕ} [NeZero f] (ψ : DirichletCharacter O f) (h : f ∣ F) (hk : k.Coprime F) {g : G ℚ Ω} (hg : Pows F k g) :
    (Chr.dirG ℚ Ω ψ g : O) = ψ k := by
  have h1 : Chr.cls ℚ Ω f g = ZMod.unitOfCoprime k (hk.of_dvd_right h) := by
    refine (Chr.clsFacts ℚ Ω f).2.2.1 g _ fun ζ hζ => ?_
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod k hζ]
    exact hg ζ (by obtain ⟨d, rfl⟩ := h; rw [pow_mul, hζ, one_pow])
  rw [Chr.dirG, MonoidHom.comp_apply, h1, MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]

private theorem ze_psi {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] {f F m k : ℕ} [NeZero f] (ψ : DirichletCharacter O f) (e : ℕ) (hl : l ^ m ∣ F) (h : f ∣ F)
    (hk : k.Coprime F) {g : G ℚ Ω} (hg : Pows F k g) :
    (l : O) ^ m ∣ (Chr.Psi l e (Chr.dirG ℚ Ω ψ) g : O) - (k : O) ^ e * ψ k := by
  have h1 := (ze_chi l O hl hg).trans (sub_dvd_pow_sub_pow _ _ e)
  have h2 : (Chr.Psi l e (Chr.dirG ℚ Ω ψ) g : O) = (chiO ℚ Ω l O g : O) ^ e * ψ k := by
    rw [← ze_dir ψ h hk hg]
    simp [Chr.Psi]
  rw [h2, ← sub_mul]
  exact h1.mul_right _

private theorem ze_dat {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] {f F m : ℕ} [NeZero f] [NeZero F] (ψ : DirichletCharacter O f) (e : ℕ) (hl : l ^ m ∣ F) (h : f ∣ F)
    (hψ : ψ (-1) = (-1) ^ (e + 1)) :
    (∀ g ∈ fixMu ℚ Ω F, (l : O) ^ m ∣ (((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ g : Oˣ) : O) - 1) ∧
    ∀ g : G ℚ Ω, Lifts F (-1) g → (l : O) ^ m ∣ (((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ g : Oˣ) : O) + 1 := by
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · have h1 := ze_psi l ψ e hl h (Nat.coprime_one_left F) (g := g) (fun x hx => by rw [pow_one]; exact hg x hx)
    rw [MonoidHom.inv_apply]
    set u := Chr.Psi l e (Chr.dirG ℚ Ω ψ) g
    have e1 : ((u⁻¹ : Oˣ) : O) - 1 = (u - ((1 : ℕ) : O) ^ e * ψ (1 : ℕ)) * (-(u⁻¹ : Oˣ)) := by
      simp [sub_mul]
    rw [e1]; exact h1.mul_right _
  · have h1 := ze_psi l ψ e hl h (ZMod.val_coe_unit_coprime _) hg
    set k := (((-1 : (ZMod F)ˣ) : ZMod F)).val with hk
    have h2 : F ∣ k + 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, hk, ZMod.natCast_zmod_val]; simp
    have h3 : (k : ZMod f) = -1 := by
      have := (ZMod.natCast_eq_zero_iff _ _).2 (h.trans h2)
      rw [Nat.cast_add, Nat.cast_one] at this
      exact eq_neg_of_add_eq_zero_left this
    have h4 : (l : O) ^ m ∣ (k : O) - (-1) := by
      have := Nat.cast_dvd_cast (α := O) (hl.trans h2)
      simpa using this
    have h5 := h1.add ((h4.trans (sub_dvd_pow_sub_pow _ _ e)).mul_right (ψ k))
    rw [h3, hψ] at h5
    rw [MonoidHom.inv_apply]
    set u := Chr.Psi l e (Chr.dirG ℚ Ω ψ) g
    have e0 : (-1 : O) ^ e * (-1) ^ (e + 1) = -1 := by
      rw [← pow_add]; exact Odd.neg_one_pow ⟨e, by ring⟩
    have e1 : ((u⁻¹ : Oˣ) : O) + 1 = (u - (k : O) ^ e * (-1) ^ (e + 1) + ((k : O) ^ e - (-1) ^ e) * (-1) ^ (e + 1)) *
        ((u⁻¹ : Oˣ) : O) := by
      linear_combination ((u⁻¹ : Oˣ) : O) * e0 - u.mul_inv
    rw [e1]; exact h5.mul_right _

private theorem ze_gen {l : ℕ} [Fact l.Prime] {f F e : ℕ} [NeZero F] (h : f ∣ F) (he : 1 ≤ e)
    (hF : ∀ p : ℕ, p.Prime → p ∣ F → p = l ∨ p ∣ f) (χ : DirichletCharacter (PadicAlgCl l) f)
    (hχ : ∀ x, ‖χ x‖ ≤ 1) :
    ‖Bern.genB (e + 1) (DirichletCharacter.changeLevel h χ : ZMod F → PadicAlgCl l)‖ =
      ‖Bern.genB (e + 1) (χ : ZMod f → PadicAlgCl l)‖ := by
  rw [Bern.b_level h (e + 1) χ (NeZero.pos F) (by omega), norm_mul, norm_prod, Finset.prod_eq_one, mul_one]
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  rcases hF p hpp (Nat.dvd_of_mem_primeFactors hp) with rfl | hd
  · have h1 : ‖(p : PadicAlgCl p)‖ < 1 := by
      have : (p : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by simp
      rw [this, norm_algebraMap']; exact Padic.norm_p_lt_one
    have h2 : ‖-(χ p * (p : PadicAlgCl p) ^ (e + 1 - 1))‖ < ‖(1 : PadicAlgCl p)‖ := by
      rw [norm_neg, norm_mul, norm_pow, norm_one]
      exact mul_lt_one_of_nonneg_of_lt_one_right (hχ _) (by positivity) (pow_lt_one₀ (norm_nonneg _) h1 (by omega))
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2.ne', max_eq_left h2.le, norm_one]
  · rw [MulChar.map_nonunit χ (a := (p : ZMod f)) (by
      rw [ZMod.isUnit_iff_coprime]
      exact fun hc => hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hd))]
    simp

private theorem ze_eq {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have : x = (x - y) + y := by ring
  rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne, max_eq_right h.le]

private theorem ze_an {K : Type} [NormedField K] [IsUltrametricDist K] {z S v u T d : K} {ε : ℝ} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (h2 : ‖(2 : K)‖ = 1) (hd : ‖d‖ ≤ 1) (h : ‖d * (v * S - 2 * u * T)‖ ≤ ε) (hz : ‖z - S‖ ≤ ε) (hε : ε < ‖d‖ * ‖T‖) :
    ‖z‖ = ‖T‖ := by
  have hw : ‖2 * u * T‖ = ‖T‖ := by rw [norm_mul, norm_mul, h2, hu, one_mul, one_mul]
  have h3 : ‖v * S‖ = ‖2 * u * T‖ := by
    apply ze_eq
    rw [hw]
    rw [norm_mul] at h
    exact lt_of_mul_lt_mul_left (h.trans_lt hε) (norm_nonneg d)
  rw [hw, norm_mul, hv, one_mul] at h3
  rw [← h3]
  apply ze_eq
  rw [h3]
  exact (hz.trans_lt hε).trans_le (mul_le_of_le_one_left (norm_nonneg _) hd)

theorem UpperTheory.V.ML.zEval :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l), l ≠ 2 → ∀ (f : ℕ) [NeZero f] (ψ : DirichletCharacter c.O f) (e : ℕ), 1 ≤ e → ψ.IsPrimitive → ψ (-1) = (-1) ^ (e + 1) →
    (∃ g : G ℚ Ω, IsUnit ((((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ g : c.Oˣ) : c.O) - (chiO ℚ Ω l c.O g : c.O))) →
    ∀ a : c.O, (a : PadicAlgCl l) = alN (e + 1) (ψ.ringHomComp c.O.val.toRingHom) → ∀ a₀ : c.O, a₀ ≠ 0 →
    ∃ (m b : ℕ) (_ : NeZero (ordCompl[l] f * l ^ m)) (σ : (ZMod (ordCompl[l] f * l ^ m))ˣ → G ℚ Ω), Dat l (ordCompl[l] f) m (ordCompl[l] f * l ^ m) (Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ ∧
      b < ordCompl[l] f * l ^ m ∧ (∀ t, Lifts (ordCompl[l] f * l ^ m) t (σ t)) ∧ a₀ * zVal (Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ σ b ∣ (l : c.O) ^ m ∧ zVal (Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ σ b ∣ a := by
  intro Ω _ _ _ l hlp c hl2 f _ ψ e he hprim hpar hg a ha a₀ ha₀
  have hp : l.Prime := hlp.out
  obtain ⟨hle, hdvd⟩ := ze_norm c
  have hunit : ∀ x : c.O, IsUnit x → ‖(x : PadicAlgCl l)‖ = 1 := by
    rintro _ ⟨u, rfl⟩
    have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((u⁻¹ : c.Oˣ) : c.O).1‖ = 1 := by
      rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : c.Oˣ)
    have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
    nlinarith
  have hdn : ∀ x y : c.O, x ∣ y → ‖(y : PadicAlgCl l)‖ ≤ ‖(x : PadicAlgCl l)‖ := by
    rintro x _ ⟨y, rfl⟩
    rw [Subalgebra.coe_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hle y)
  have hnat : ∀ n : ℕ, ‖(n : PadicAlgCl l)‖ ≤ 1 := fun n => by simpa using hle n
  have hnu : ∀ n : ℕ, ¬ l ∣ n → ‖(n : PadicAlgCl l)‖ = 1 := fun n hn => by
    simpa using hunit n ((dvrFacts l c.O).2.2.2.2.2.2.2.2 n hn)
  have hl1 : ‖(l : PadicAlgCl l)‖ < 1 := by
    have : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']; exact Padic.norm_p_lt_one
  set ψ' : DirichletCharacter (PadicAlgCl l) f := ψ.ringHomComp c.O.val.toRingHom with hψ'
  have hv : ∀ x, ψ' x = ((ψ x : c.O) : PadicAlgCl l) := fun x => rfl
  have hpar' : ψ' (-1) = (-1) ^ (e + 1) := by rw [hv, hpar]; simp
  have hprim' : ψ'.IsPrimitive := ((Bern.b_condmap c.O.val.toRingHom Subtype.val_injective ψ).1).trans hprim
  have hB : Bern.Bprim (e + 1) ψ' = Bern.genB (e + 1) (ψ' : ZMod f → PadicAlgCl l) :=
    ((Bern.b_primeq (e + 1) ψ').1 hprim').1
  have hB0 := (Bern.b_nzany ψ' (e + 1) (by omega) hpar').1
  have he0 : ((e : PadicAlgCl l) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero e
  have hd0 : (Stk.dk (e + 1) : PadicAlgCl l) ≠ 0 := by exact_mod_cast (Stk.dk_pos (Nat.succ_pos e)).ne'
  have ha0 : (a₀ : PadicAlgCl l) ≠ 0 := fun h => ha₀ (Subtype.ext h)
  set T : ℝ := ‖Bern.Bprim (e + 1) ψ' / (e + 1)‖ with hT
  have hTpos : 0 < T := norm_pos_iff.2 (div_ne_zero hB0 he0)
  have hpos : 0 < ‖(a₀ : PadicAlgCl l)‖ * (‖(Stk.dk (e + 1) : PadicAlgCl l)‖ * T) :=
    mul_pos (norm_pos_iff.2 ha0) (mul_pos (norm_pos_iff.2 hd0) hTpos)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hl1
  obtain ⟨m, hm1, hmf, hm⟩ : ∃ m : ℕ, 1 ≤ m ∧ f.factorization l ≤ m ∧
      ‖(l : PadicAlgCl l) ^ m‖ < ‖(a₀ : PadicAlgCl l)‖ * (‖(Stk.dk (e + 1) : PadicAlgCl l)‖ * T) :=
    ⟨n + f.factorization l + 1, by omega, by omega, by
      rw [norm_pow]
      exact (pow_le_pow_of_le_one (norm_nonneg _) hl1.le (by omega)).trans_lt hn⟩
  have hF0 : NeZero (ordCompl[l] f * l ^ m) :=
    ⟨mul_ne_zero (Nat.ordCompl_pos l (NeZero.ne f)).ne' (pow_ne_zero _ hp.ne_zero)⟩
  have hfF : f ∣ ordCompl[l] f * l ^ m := by
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self f l, mul_comm]
    exact Nat.mul_dvd_mul_left _ (pow_dvd_pow l hmf)
  have hlF : l ^ m ∣ ordCompl[l] f * l ^ m := dvd_mul_left _ _
  have hFp : ∀ p : ℕ, p.Prime → p ∣ ordCompl[l] f * l ^ m → p = l ∨ p ∣ f := fun p hpp hd =>
    (hpp.dvd_mul.1 hd).elim (fun h => Or.inr (h.trans (Nat.ordCompl_dvd f l)))
      fun h => Or.inl ((Nat.prime_dvd_prime_iff_eq hpp hp).1 (hpp.dvd_of_dvd_pow h))
  have hcop : (ordCompl[l] f).Coprime l := (Nat.coprime_ordCompl hp (NeZero.ne f)).symm
  refine ⟨m, ?_⟩
  generalize hF : ordCompl[l] f * l ^ m = F at hF0 hfF hlF hFp ⊢
  obtain ⟨hd1, hd2⟩ := ze_dat (Ω := Ω) l ψ e hlF hfF hpar
  choose σ hσ' using (galBasic Ω F (NeZero.ne F)).2.2.2.1
  obtain ⟨g, hg'⟩ := id hg
  set b := ((Chr.cls ℚ Ω F g : (ZMod F)ˣ) : ZMod F).val with hb
  have hbc : b.Coprime F := ZMod.val_coe_unit_coprime _
  have hgb : Pows F b g := fun x hx => Chr.cls_spec F g x hx
  have hχ : ∀ k : ℕ, k.Coprime F → DirichletCharacter.changeLevel hfF ψ' (k : ZMod F) = ψ' (k : ZMod f) := fun k hk => by
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ' hfF (ZMod.unitOfCoprime k hk)
    rwa [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hfF] at this
  have hχ1 : DirichletCharacter.changeLevel hfF ψ' (-1) = (-1) ^ (e + 1) := by
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ' hfF (-1)
    rw [Units.val_neg, Units.val_one, ZMod.cast_neg hfF, ZMod.cast_one hfF] at this
    rw [this, hpar']
  have hc := zCong l F m e b hlF hm1 he hbc _ hχ1
  have hlb : ¬ l ∣ b := fun h =>
    hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hbc h ((dvd_pow_self l (by omega)).trans hlF))
  have hψb : ‖ψ' (b : ZMod f)‖ = 1 := by
    rw [hv, ← ze_dir ψ hfF hbc hgb]; exact hunit _ (Units.isUnit _)
  have hlm : ‖(l : PadicAlgCl l) ^ m‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hl1 (by omega)
  have hu : ‖ψ' (b : ZMod f) * (b : PadicAlgCl l) ^ (e + 1) - 1‖ = 1 := by
    have h1 := ze_psi l ψ e hlF hfF hbc hgb
    have h2 := ze_chi l c.O hlF hgb
    rw [MonoidHom.inv_apply] at hg'
    set u := Chr.Psi l e (Chr.dirG ℚ Ω ψ) g
    set w := (chiO ℚ Ω l c.O g : c.O)
    have h3 := hunit _ (hg'.mul u.isUnit).neg
    have h4 : (l : c.O) ^ m ∣ (ψ (b : ZMod f) * (b : c.O) ^ (e + 1) - 1) - -((((u⁻¹ : c.Oˣ) : c.O) - w) * u) := by
      have := ((h1.mul_right (b : c.O)).add (h2.mul_right (u : c.O))).neg_right
      convert this using 1
      linear_combination u.inv_mul
    have h5 := hdn _ _ h4
    rw [← h3]
    apply ze_eq
    rw [h3]
    refine lt_of_le_of_lt ?_ hlm
    simpa [hv] using h5
  have hz : ‖((zVal (Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ σ b : c.O) : PadicAlgCl l) - ∑ t : (ZMod F)ˣ, (th F b t : PadicAlgCl l) *
      (((t : ZMod F).val : PadicAlgCl l) ^ e * DirichletCharacter.changeLevel hfF ψ' t)‖ ≤ ‖(l : PadicAlgCl l) ^ m‖ := by
    have h1 : (l : c.O) ^ m ∣ zVal (Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ σ b - ∑ t : (ZMod F)ˣ, (th F b t : c.O) *
        (((t : ZMod F).val : c.O) ^ e * ψ (t : ZMod F).val) := by
      rw [zVal, zSum, ← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun t _ => ?_
      rw [← mul_sub, MonoidHom.inv_apply, inv_inv]
      exact (ze_psi l ψ e hlF hfF (ZMod.val_coe_unit_coprime t) (hσ' t)).mul_left _
    have h2 : ∀ t : (ZMod F)ˣ, DirichletCharacter.changeLevel hfF ψ' t = ((ψ (t : ZMod F).val : c.O) : PadicAlgCl l) := fun t => by
      rw [← hv, ← hχ _ (ZMod.val_coe_unit_coprime t), ZMod.natCast_zmod_val]
    have h3 := hdn _ _ h1
    simp only [h2]
    push_cast at h3
    exact h3
  have hT' : ‖Bern.genB (e + 1) (DirichletCharacter.changeLevel hfF ψ' : ZMod F → PadicAlgCl l) / (e + 1)‖ = T := by
    rw [hT, norm_div, norm_div, ze_gen hfF he hFp ψ' (fun x => hle _), hB]
  have hzT := ze_an (by rw [hχ b hbc, norm_mul, norm_pow, hnu b hlb, hψb, one_pow, one_mul]) (by rw [hχ b hbc]; exact hu)
    (by simpa using hnu 2 fun h => hl2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)) (hnat _) hc hz
    (by rw [hT']; exact hm.trans_le (mul_le_of_le_one_left (by positivity) (hle _)))
  rw [hT'] at hzT
  refine ⟨b, hF0, σ, ⟨hl2, hcop, hm1, hF.symm, hd1, hd2, hg⟩, ZMod.val_lt _, hσ', hdvd _ _ ?_, hdvd _ _ ?_⟩
  · rw [Subalgebra.coe_mul, norm_mul, hzT]
    push_cast
    exact hm.le.trans (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hTpos.le (hnat _)) (norm_nonneg _))
  · rw [hzT, ha, alN, hT, norm_mul, norm_div, le_div_iff₀ (norm_pos_iff.2 he0)]
    have h1 := hnat (Bern.den f (e + 1))
    have h2 := hnat (e + 1)
    push_cast at h2
    exact (mul_le_of_le_one_right (by positivity) h2).trans (mul_le_of_le_one_left (norm_nonneg _) h1)
