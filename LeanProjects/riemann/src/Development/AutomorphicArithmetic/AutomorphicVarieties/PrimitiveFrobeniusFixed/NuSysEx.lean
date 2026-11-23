import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.SysOfLax
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.DerInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.DerBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolInit
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.HasOrdP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ZSumPKey
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ValAddSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IneTau
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IneRad
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.AdmProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem exists_cycZ_eq_add_pow_mul_of_pows (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (m k : ℕ) (g : G ℚ Ω) (hg : Pows (l ^ m) k g) : ∃ e : ℤ_[l], (cycZ ℚ Ω l g : ℤ_[l]) = k + (l : ℤ_[l]) ^ m * e := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
  have h1 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) ζ hζ.pow_eq_one
  have h2 := hg ζ hζ.pow_eq_one
  have h3 : ζ ^ k = ζ ^ ((PadicInt.toZModPow m (cycZ ℚ Ω l g : ℤ_[l])).val) := h2.symm.trans h1
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨l ^ m, pow_pos (Fact.out : l.Prime).pos m, hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h3
  have h4 : (k : ZMod (l ^ m)) = PadicInt.toZModPow m (cycZ ℚ Ω l g : ℤ_[l]) := by
    rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow m (cycZ ℚ Ω l g : ℤ_[l])), ZMod.natCast_eq_natCast_iff]
    exact h3
  have h5 : (cycZ ℚ Ω l g : ℤ_[l]) - k ∈ RingHom.ker (PadicInt.toZModPow (p := l) m) := by
    rw [RingHom.mem_ker, map_sub, ← h4, map_natCast, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h5
  obtain ⟨e, he⟩ := h5
  exact ⟨e, by rw [← he]; ring⟩

private theorem isUnit_add_pow_mul_of_isUnit_of_one_le (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (m : ℕ) (hm : 1 ≤ m) (u y : O) (hu : IsUnit u) : IsUnit (u + (l : O) ^ m * y) := by
  by_contra h
  have hl : (l : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hlu
    have h1 : IsUnit (algebraMap ℤ_[l] O (l : ℤ_[l])) := by rwa [map_natCast]
    have h2 := (isUnit_map_iff (algebraMap ℤ_[l] O) _).mp h1
    rw [PadicInt.isUnit_iff, PadicInt.norm_p] at h2
    have h3 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have h4 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h3
    rw [h2] at h4
    exact lt_irrefl _ h4
  have h1 : u + (l : O) ^ m * y ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact h
  have h5 : (l : O) ^ m * y ∈ IsLocalRing.maximalIdeal O := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, pow_one, mul_assoc]
    exact Ideal.mul_mem_right _ _ hl
  have h6 : u ∈ IsLocalRing.maximalIdeal O := by
    have := Ideal.sub_mem _ h1 h5
    simpa using this
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h6
  exact h6 hu

private theorem intCast_smul_eq_of_zmod_eq_of_nsmul_eq_zero (O W : Type) [CommRing O] [AddCommGroup W] [Module O W] (N : ℕ) (v : W) (hv : N • v = 0) (z₁ z₂ : ℤ) (h : (z₁ : ZMod N) = z₂) : (z₁ : O) • v = (z₂ : O) • v := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨j, hj⟩ := h
  rw [← sub_eq_zero, ← sub_smul, ← Int.cast_sub, ← neg_sub, hj]
  rw [Int.cast_neg, neg_smul, neg_eq_zero, Int.cast_mul, mul_comm, mul_smul, Int.cast_natCast, Nat.cast_smul_eq_nsmul, hv, smul_zero]

private theorem isUnit_natCast_of_not_dvd' (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (n : ℕ) (h : ¬ l ∣ n) : IsUnit (n : O) := by
  have h1 : IsUnit (n : ℤ_[l]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr (((Fact.out : l.Prime).coprime_iff_not_dvd).mpr h))
  simpa using h1.map (algebraMap ℤ_[l] O)

theorem UpperTheory.V.ML.nuSysEx :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N₀ m F r b : ℕ) [NeZero F] (α : G ℚ Ω →* Oˣ), Dat l N₀ m F α → r.Prime → r ≡ 1 [MOD F] → b < F →
    ∀ A₀ : ValuationSubring Ω, Over A₀ r → ∀ σ : (ZMod F)ˣ → G ℚ Ω, (∀ t, Lifts F t (σ t)) → ∀ w : QO l O, (l ^ m) • w = 0 →
    ∃ ν : List ℕ → G ℚ Ω → QO l O, NuSys l (l ^ m) F r (dualChar l α) A₀ (zVal α σ b • w) ν := by
  intro Ω _ _ _ l _ O _ _ _ _ _ N₀ m F r b _ α hD hr hrF hb A₀ hA₀ σ hσ w hw
  classical
  obtain ⟨hl2, hcop, hm, hF, htriv, hodd, ⟨g0, hg0⟩⟩ := hD
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast hl.ne_zero⟩
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hMF : l ^ m ∣ F := hF ▸ dvd_mul_left _ _
  have hF0 : F ≠ 0 := NeZero.ne F
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
  obtain ⟨a0, ha0⟩ := (galBasic Ω (l ^ m) (pow_ne_zero _ hl.ne_zero)).2.2.2.2.1 g0
  have hPows : Pows (l ^ m) (a0 : ZMod (l ^ m)).val g0 := ha0
  obtain ⟨e0, he0⟩ := exists_cycZ_eq_add_pow_mul_of_pows Ω l m _ g0 hPows
  obtain ⟨X, s, hLax, hOrd⟩ := laxEx Ω l F r b hl hr hrF hb A₀ hA₀
  have hSys := sysOfLax Ω l N₀ m F r _ hl hl2 hcop hm hF X s hLax g0 hPows
  let τ : ℕ → G ℚ Ω := fun q => if h : q.Prime then Classical.choose (ineTau Ω q h).2 else 1
  have hτ : ∀ q, q.Prime → IsTau q (τ q) := by
    intro q hq
    simp only [τ, dif_pos hq]
    exact Classical.choose_spec (ineTau Ω q hq).2
  have hkol : ∀ L, AdmL l F r L → ∃ κ : G ℚ Ω → ZMod (l ^ m), IsKol (l ^ m) F L.prod ζ g0 (a0 : ZMod (l ^ m)).val (der τ L ((fun d => opP g0 (a0 : ZMod (l ^ m)).val (X d) ^ (2 * N₀ * d)) L.prod)) κ := by
    intro L hL
    obtain ⟨hAdm, hprod0, -, -⟩ := isCrys_isDR_prod l F r L hL
    have hD := derBasic Ω (F * L.prod) r (mul_ne_zero hF0 hprod0) τ L _ (hSys.ne _ hAdm) (hSys.fix _ hAdm)
    exact kolEx Ω (l ^ m) F L.prod _ (mul_ne_zero hF0 hprod0) ζ hζ g0 hPows _ hD.1 hD.2.1
      (derInv Ω l (l ^ m) F r hF0 hMF _ _ hSys τ L hL (fun q hq => hτ q (hL.2 q hq).1))
  let κ : List ℕ → G ℚ Ω → ZMod (l ^ m) := fun L => if h : AdmL l F r L then Classical.choose (hkol L h) else 0
  have hκ : ∀ L (h : AdmL l F r L), IsKol (l ^ m) F L.prod ζ g0 (a0 : ZMod (l ^ m)).val (der τ L ((fun d => opP g0 (a0 : ZMod (l ^ m)).val (X d) ^ (2 * N₀ * d)) L.prod)) (κ L) := by
    intro L h
    simp only [κ, dif_pos h]
    exact Classical.choose_spec (hkol L h)
  have hchiO : ∀ (g : G ℚ Ω) (k : ℕ), Pows (l ^ m) k g → ∃ e : O, ((chiO ℚ Ω l O g : Oˣ) : O) = k + (l : O) ^ m * e := by
    intro g k hg
    obtain ⟨e, he⟩ := exists_cycZ_eq_add_pow_mul_of_pows Ω l m k g hg
    refine ⟨algebraMap ℤ_[l] O e, ?_⟩
    show algebraMap ℤ_[l] O (cycZ ℚ Ω l g : ℤ_[l]) = _
    rw [he, map_add, map_mul, map_pow, map_natCast, map_natCast]
  have hβ : ∀ g ∈ fixMu ℚ Ω F, ((l ^ m : ℕ) : O) ∣ ((dualChar l α g : Oˣ) : O) - 1 := by
    intro g hg
    have hP : Pows (l ^ m) 1 g := by
      intro y hy
      rw [pow_one]
      exact ((galBasic Ω F hF0).2.2.2.2.2.2.2.2.1 (l ^ m) hMF) hg y hy
    obtain ⟨e, he⟩ := hchiO g 1 hP
    obtain ⟨c, hc⟩ := htriv g hg
    have hinv : ((α g)⁻¹ : Oˣ) * (α g : O) = 1 := Units.inv_mul _
    refine ⟨((α g)⁻¹ : Oˣ) * (e - c), ?_⟩
    show ((chiO ℚ Ω l O g : Oˣ) : O) * ((α g)⁻¹ : Oˣ) - 1 = _
    rw [he, Nat.cast_pow, Nat.cast_one]
    linear_combination hinv - (((α g)⁻¹ : Oˣ) : O) * hc
  refine ⟨fun L => nu (dualChar l α) σ w (κ L), ⟨?_, ?_, ?_⟩⟩
  · intro L hL
    obtain ⟨hAdm, hprod0, -, -⟩ := isCrys_isDR_prod l F r L hL
    have hD := derBasic Ω (F * L.prod) r (mul_ne_zero hF0 hprod0) τ L _ (hSys.ne _ hAdm) (hSys.fix _ hAdm)
    have hK := hκ L hL
    have hH := kolHom Ω (l ^ m) F L.prod _ (mul_ne_zero hF0 hprod0) hMF ζ hζ g0 hPows _ hD.1 hD.2.1 (κ L) hK
    have hU := kolUnr Ω (l ^ m) F L.prod r _ (mul_ne_zero hF0 hprod0) hMF ζ hζ g0 hPows _ hD.1 hD.2.1
      (hD.2.2.2.1 (hSys.unit _ hAdm)) (κ L) hK
    exact nuIs Ω O (QO l O) (l ^ m) F (F * r * L.prod) ⟨r * L.prod, by ring⟩ (dualChar l α) hβ σ hσ w hw
      (κ L) hH.1 hH.2.1 hU
  · intro q L hqL A hA φ hφ
    have hq : q.Prime := (hqL.2 q List.mem_cons_self).1
    have hL : AdmL l F r L :=
      ⟨(List.nodup_cons.mp hqL.1).2, fun p hp => hqL.2 p (List.mem_cons_of_mem _ hp)⟩
    obtain ⟨hAdmq, -, -, -⟩ := isCrys_isDR_prod l F r (q :: L) hqL
    rw [List.prod_cons] at hAdmq
    have hcopq : ¬ l ∣ q * s L.prod q := hSys.cop L.prod q hq hAdmq
    have hUn : IsUnit (((-((q * s L.prod q : ℕ) : ℤ) : ℤ) : O)) := by
      rw [Int.cast_neg, IsUnit.neg_iff, Int.cast_natCast]
      exact isUnit_natCast_of_not_dvd' l O _ hcopq
    obtain ⟨b0, -, hb0⟩ := (hτ q hq).2
    obtain ⟨t, htI, ht⟩ := (ineTau Ω q hq).1 A hA b0
    refine ⟨t, htI, hUn.unit, ?_⟩
    simp only [nu, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro c _
    have pb := (placeBasic Ω).2.2.2.2.2.2.2.2.2 A (σ c)⁻¹
    have hA' : Over ((σ c)⁻¹ • A) q := by
      have h1 := (pb.2.2.2.1 (q : Ω)).mpr hA
      rwa [map_natCast] at h1
    have hI' : (σ c)⁻¹ * t * σ c ∈ Ine ((σ c)⁻¹ • A) := by
      rw [pb.2.1]
      simpa [mul_assoc] using htI
    have hφ' : IsFrob ((σ c)⁻¹ • A) q ((σ c)⁻¹ * φ * σ c) := by
      rw [pb.2.2.1]
      simpa [mul_assoc] using hφ
    have ht' : ∀ y : Ω, y ^ q = 1 → ((σ c)⁻¹ * t * σ c) y = (τ q) y := by
      intro y hy
      have hcomm := (galBasic Ω q hq.ne_zero).2.2.2.2.2.1 y (fun g hg => hg y hy) t (σ c)
      have hback : (σ c)⁻¹ (σ c (t y)) = t y := by
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hcomm, hback]
      exact (ht y hy).trans (hb0 y hy).symm
    have key := kolStep Ω l (l ^ m) F r _ hF0 hMF hr ζ hζ g0 hPows _ _ hSys τ q L hqL
      (fun p hp => hτ p (hqL.2 p hp).1) (κ L) (κ (q :: L)) (hκ L hL) (hκ (q :: L) hqL)
      ((σ c)⁻¹ • A) hA' _ hI' ht' _ hφ'
    rw [key]
    have hv : (l ^ m) • ((((dualChar l α) (σ c) : Oˣ) : O) • w) = 0 := by
      rw [smul_comm, hw, smul_zero]
    generalize ((((dualChar l α) (σ c) : Oˣ) : O) • w) = v at hv ⊢
    generalize κ L ((σ c)⁻¹ * φ * σ c) = k
    rw [IsUnit.unit_spec, ← Nat.cast_smul_eq_nsmul O, ← Nat.cast_smul_eq_nsmul O, smul_smul]
    have h3 := intCast_smul_eq_of_zmod_eq_of_nsmul_eq_zero O _ (l ^ m) v hv
      (((-(((q * s L.prod q : ℕ) : ZMod (l ^ m)) * k)).val : ℕ) : ℤ)
      (-((q * s L.prod q : ℕ) : ℤ) * (k.val : ℤ)) (by push_cast; simp)
    push_cast at h3 ⊢
    exact h3
  · have hL0 : AdmL l F r [] := ⟨List.nodup_nil, fun p hp => absurd hp List.not_mem_nil⟩
    obtain ⟨hAdm1, -, -, -⟩ := isCrys_isDR_prod l F r [] hL0
    have hx0 := hSys.ne _ hAdm1
    have hxfix := hSys.fix _ hAdm1
    have hK0 := hκ [] hL0
    simp only [List.prod_nil] at hAdm1 hx0 hxfix hK0
    have hrcop : r.Coprime F := by
      have := hrF.gcd_eq
      rw [Nat.gcd_one_left] at this
      exact this
    have hMr : (l ^ m).Coprime r := (Nat.Coprime.coprime_dvd_right hMF hrcop).symm
    obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (r : Ω) (pow_pos hl.pos m)
    obtain ⟨t, htI, htρ⟩ := ineRad Ω r (l ^ m) hr hMr A₀ hA₀ ρ ζ hρ hζ.pow_eq_one
    obtain ⟨d, hd⟩ := (galBasic Ω F hF0).2.2.2.2.1 g0
    have hO := hasOrdP Ω F r (a0 : ZMod (l ^ m)).val hr.ne_zero A₀ (X 1) _ hOrd
    have hO1 := hO.1 d g0 hd
    have hO2 := ((hasOrdP Ω F r (a0 : ZMod (l ^ m)).val hr.ne_zero A₀ _ _ hO1).2 (2 * N₀ * 1))
    have hO3 := ((hasOrdP Ω F r (a0 : ZMod (l ^ m)).val hr.ne_zero A₀ _ _ hO2).1 d g0 hd)
    have hinit := kolInit Ω (l ^ m) F r (a0 : ZMod (l ^ m)).val hMF hr hrcop ζ hζ g0 hPows _ hx0
      (by simpa using hxfix) (κ []) hK0 A₀ hA₀ _ hO3 ρ hρ t htI htρ
    obtain ⟨e1, he1⟩ := hchiO g0 _ hPows
    have hU1 : IsUnit (((α g0 : Oˣ) : O) - (((a0 : ZMod (l ^ m)).val : ℕ) : O)) := by
      have heq : ((α g0 : Oˣ) : O) - (((a0 : ZMod (l ^ m)).val : ℕ) : O) =
          (((α g0 : Oˣ) : O) - ((chiO ℚ Ω l O g0 : Oˣ) : O)) + (l : O) ^ m * e1 := by
        linear_combination he1
      rw [heq]
      exact isUnit_add_pow_mul_of_isUnit_of_one_le l O m hm _ _ hg0
    have hU2 : IsUnit (((2 * N₀ * 1 : ℕ) : ℤ) : O) := by
      rw [Int.cast_natCast]
      apply isUnit_natCast_of_not_dvd' l O
      intro hdvd
      rw [mul_one] at hdvd
      rcases (Nat.Prime.dvd_mul hl).mp hdvd with h2 | h2
      · exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h2)
      · exact hl.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm h2)
    have hU := (hU1.pow 2).mul hU2
    refine ⟨t, htI, hU.unit, ?_⟩
    rw [IsUnit.unit_spec]
    have hwO : ((l : O) ^ m) • w = 0 := by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hw]
    have hsum : ∀ K : (ZMod F)ˣ → ℤ, (∀ (c : (ZMod F)ˣ) (σ' : G ℚ Ω), Lifts F c σ' →
        κ [] (σ'⁻¹ * t * σ') * (ZMod.castHom hMF (ZMod (l ^ m))) (c : ZMod F) = K c) →
        nu (dualChar l α) σ w (κ []) t = zSum α σ K • w := by
      intro K hK
      simp only [nu, zSum, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro c _
      have hc := hK c (σ c) (hσ c)
      have hP : Pows (l ^ m) ((c : ZMod F).val) (σ c) := by
        intro y hy
        apply hσ c y
        obtain ⟨j, hj⟩ := hMF
        rw [hj, pow_mul, hy, one_pow]
      obtain ⟨e, he⟩ := hchiO (σ c) _ hP
      have hv : (l ^ m) • ((((α (σ c))⁻¹ : Oˣ) : O) • w) = 0 := by
        rw [smul_comm, hw, smul_zero]
      show (κ [] ((σ c)⁻¹ * t * σ c)).val • ((((chiO ℚ Ω l O (σ c)) * (α (σ c))⁻¹ : Oˣ) : O) • w) = _
      have hz : ((l : O) ^ m * e) • ((((α (σ c))⁻¹ : Oˣ) : O) • w) = 0 := by
        rw [mul_comm, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul O (l ^ m), hv, smul_zero]
      rw [Units.val_mul, mul_smul, he, add_smul, hz, add_zero]
      rw [← Nat.cast_smul_eq_nsmul O, smul_smul]
      have h3 := intCast_smul_eq_of_zmod_eq_of_nsmul_eq_zero O _ (l ^ m) _ hv (((κ [] ((σ c)⁻¹ * t * σ c)).val : ℤ) * ((c : ZMod F).val : ℤ)) (K c)
        (by rw [← hc, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.castHom_apply, ZMod.cast_eq_val])
      push_cast at h3
      exact h3.trans (mul_smul _ _ _).symm
    rw [hsum _ hinit]
    have zp := fun k => zSumP Ω O F (a0 : ZMod (l ^ m)).val ((l : O) ^ m) α htriv σ hσ k
    obtain ⟨j1, hj1⟩ := (zp (fun t : (ZMod F)ˣ => th F b ↑t)).1 d g0 hd
    have h2 := (zp (fun t : (ZMod F)ˣ => th F b ↑(t * d) - ↑(a0 : ZMod (l ^ m)).val * th F b ↑t)).2
      ((2 * N₀ * 1 : ℕ) : ℤ)
    obtain ⟨j3, hj3⟩ := (zp (fun t : (ZMod F)ˣ => ((2 * N₀ * 1 : ℕ) : ℤ) *
      (th F b ↑(t * d) - ↑(a0 : ZMod (l ^ m)).val * th F b ↑t))).1 d g0 hd
    have E := hj3
    rw [h2] at E
    have E2 : zSum α σ (fun t : (ZMod F)ˣ => ((2 * N₀ * 1 : ℕ) : ℤ) * (th F b ↑(t * d * d) -
        ↑(a0 : ZMod (l ^ m)).val * th F b ↑(t * d)) - ↑(a0 : ZMod (l ^ m)).val *
        (((2 * N₀ * 1 : ℕ) : ℤ) * (th F b ↑(t * d) - ↑(a0 : ZMod (l ^ m)).val * th F b ↑t))) =
        (((α g0 : Oˣ) : O) - (((a0 : ZMod (l ^ m)).val : ℕ) : O)) ^ 2 * (((2 * N₀ * 1 : ℕ) : ℤ) : O) *
          zVal α σ b + (l : O) ^ m * ((((α g0 : Oˣ) : O) - (((a0 : ZMod (l ^ m)).val : ℕ) : O)) *
          (((2 * N₀ * 1 : ℕ) : ℤ) : O) * j1 + j3) := by
      linear_combination E + (((α g0 : Oˣ) : O) - (((a0 : ZMod (l ^ m)).val : ℕ) : O)) * (((2 * N₀ * 1 : ℕ) : ℤ) : O) * hj1
    show zSum α σ (fun t : (ZMod F)ˣ => ((2 * N₀ * 1 : ℕ) : ℤ) * (th F b ↑(t * d * d) -
        ↑(a0 : ZMod (l ^ m)).val * th F b ↑(t * d)) - ↑(a0 : ZMod (l ^ m)).val *
        (((2 * N₀ * 1 : ℕ) : ℤ) * (th F b ↑(t * d) - ↑(a0 : ZMod (l ^ m)).val * th F b ↑t))) • w = _
    rw [E2, add_smul, mul_comm ((l : O) ^ m) _, mul_smul _ ((l : O) ^ m), hwO, smul_zero, add_zero, mul_smul]
