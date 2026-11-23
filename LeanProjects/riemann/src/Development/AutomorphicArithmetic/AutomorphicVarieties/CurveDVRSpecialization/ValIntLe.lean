import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnramIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Base UpperTheory.V.Pr

section

variable {Ω : Type} [Field Ω]

private theorem val_int_le (A : ValuationSubring Ω) (a : ℤ) : A.valuation (a : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (intCast_mem A a)

private theorem val_dvd (A : ValuationSubring Ω) {a b : ℕ} (h : a ∣ b) (ha : A.valuation (a : Ω) < 1) :
    A.valuation (b : Ω) < 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_lt_one_of_lt_of_le ha (by simpa using val_int_le A (c : ℤ))

private theorem val_prime (A : ValuationSubring Ω) (n : ℕ) (hn : n ≠ 0) (h : A.valuation (n : Ω) < 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ A.valuation (p : Ω) < 1 := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => simp at h
  | prime p hp => exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    rw [Nat.cast_mul, map_mul] at h
    by_cases ha : A.valuation (a : Ω) < 1
    · obtain ⟨p, hp, hd, hv⟩ := iha (left_ne_zero_of_mul hn) ha
      exact ⟨p, hp, hd.mul_right _, hv⟩
    · have h1 : A.valuation (a : Ω) = 1 := le_antisymm (by simpa using val_int_le A (a : ℤ)) (not_lt.1 ha)
      rw [h1, one_mul] at h
      obtain ⟨p, hp, hd, hv⟩ := ihb (right_ne_zero_of_mul hn) h
      exact ⟨p, hp, hd.mul_left _, hv⟩

private theorem val_cop (A : ValuationSubring Ω) {a b : ℕ} (h : a.Coprime b) (ha : A.valuation (a : Ω) < 1) :
    ¬ A.valuation (b : Ω) < 1 := by
  intro hb
  obtain ⟨u, v, e⟩ := Nat.isCoprime_iff_coprime.2 h
  have e' : (a : Ω) * (u : Ω) + (b : Ω) * (v : Ω) = 1 := by
    have := congrArg (Int.cast : ℤ → Ω) e
    push_cast at this
    rw [← this]; ring
  have h1 : A.valuation ((a : Ω) * (u : Ω) + (b : Ω) * (v : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]
    · exact mul_lt_one_of_lt_of_le ha (val_int_le A u)
    · exact mul_lt_one_of_lt_of_le hb (val_int_le A v)
  rw [e', map_one] at h1
  exact lt_irrefl _ h1

variable [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem algClo (K : Type) [Field K] [NumberField K] [Algebra K Ω] : IsAlgClosure K Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩

private theorem exists_alg (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K Ω] [Algebra L Ω]
    (h : galOf ℚ L Ω ≤ galOf ℚ K Ω) : ∃ _ : Algebra K L, IsScalarTower K L Ω := by
  haveI := algClo (Ω := Ω) L
  have h1 : ∀ x : K, ∃ y : L, algebraMap L Ω y = algebraMap K Ω x := fun x =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) _).2 fun f => h (galEmb_mem ℚ L Ω f) x
  choose f hf using h1
  have hi := (algebraMap L Ω).injective
  let g : K →+* L :=
    { toFun := f
      map_one' := hi (by simp [hf])
      map_mul' := fun a b => hi (by simp [hf])
      map_zero' := hi (by simp [hf])
      map_add' := fun a b => hi (by simp [hf]) }
  letI := g.toAlgebra
  exact ⟨_, IsScalarTower.of_algebraMap_eq fun x => (hf x).symm⟩

private theorem discr_over (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsGalois ℚ K] (M : ℕ)
    (h : ∀ B : ValuationSubring Ω, ¬ Ine (F := ℚ) B ≤ galOf ℚ K Ω → B.valuation (M : Ω) < 1)
    (A : ValuationSubring Ω) (hA : A.valuation ((discr K : ℤ) : Ω) < 1) : A.valuation (M : Ω) < 1 := by
  haveI := algClo (Ω := Ω) K
  have hA' : A.valuation (((discr K).natAbs : ℕ) : Ω) < 1 := by
    rcases Int.natAbs_eq (discr K) with e | e
    · rwa [e, Int.cast_natCast] at hA
    · rwa [e, Int.cast_neg, Valuation.map_neg, Int.cast_natCast] at hA
  obtain ⟨p, hp, hd, hv⟩ := val_prime A _ (Int.natAbs_ne_zero.2 (discr_ne_zero K)) hA'
  by_cases hM : p ∣ M
  · exact val_dvd A hM hv
  exfalso
  refine (CF.unramIff.2.1 K p hp).1 ((CF.unramIff.1 K p hp).2 fun w hw => ?_) (Int.natCast_dvd.2 hd)
  obtain ⟨B, hB⟩ : ∃ B : ValuationSubring Ω, IsPlaceOver B w := exists_isPlaceOver Ω w
  have hpB : B.valuation (p : Ω) < 1 := by
    have := (hB (p : 𝓞 K)).2 hw
    simpa using this
  have hI : Ine (F := ℚ) B ≤ galOf ℚ K Ω := by
    by_contra hc
    exact val_cop B ((Nat.Prime.coprime_iff_not_dvd hp).2 hM) hpB (h B hc)
  rw [← CF.ineAbs ℚ K Ω B w hB, eq_bot_iff]
  rintro _ ⟨s, hs, rfl⟩
  refine Subgroup.mem_bot.2 (AlgEquiv.ext fun x => (algebraMap K Ω).injective ?_)
  rw [CF.resTo_commutes]
  exact hI hs x

end

theorem UpperTheory.V.Pr.kaOf :
    UpperTheory.V.Sd.AlgCyc → UpperTheory.V.Sd.AlgRes → UpperTheory.V.Pr.KaOf := by
  intro hC hR Ω _ _ _ l hl ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k
  have hlM : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ¬ A.valuation (l : Ω) < 1 :=
    fun A h h' => h (val_dvd A ((Dvd.intro _ rfl).trans H.dvd) h')
  have hcyc : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := L) A, (cycBar L Ω l)⁻¹ s = 1 := by
    intro A hA s hs
    have h1 : cycZ L Ω l s = 1 := (places L Ω l A).2.2.2 hA hs
    simp [cycBar, h1]
  refine ⟨⟨?_, ?_, fun A hA => hcyc A (hlM A hA), 1, fun h => hl.out.one_lt.ne' (Nat.dvd_one.1 h),
    fun A hA s hs => by rw [pow_one]; exact hcyc A hA s hs⟩, fun K _ _ _ hK κ hκ => ?_⟩
  · have h := (hC L Ω l ι).1 (-1) 1 (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ)
    rwa [mul_one, zpow_neg_one] at h
  · intro s s' h
    have h1 : cycBar L Ω l s' = cycBar L Ω l s := by
      change cycBar ℚ Ω l (galEmb ℚ L Ω s') = cycBar ℚ Ω l (galEmb ℚ L Ω s)
      rw [h, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply, h1, ← zpow_neg_one, ← zpow_add]
    norm_num
  · have hle : galOf ℚ L Ω ≤ galOf ℚ K Ω := by
      rw [k.gal, hK]
      exact inf_le_right
    obtain ⟨_, _⟩ := exists_alg K L hle
    haveI := algClo (Ω := Ω) K
    haveI := k.ab
    haveI : IsAbelianGalois ℚ K := IsAbelianGalois.tower_bot ℚ K L
    have hI : ∀ (A : ValuationSubring Ω) (s : G L Ω), s ∈ Ine (F := L) A → galEmb K L Ω s ∈ Ine (F := K) A :=
      fun A s hs => ⟨hs.1, hs.2⟩
    refine ⟨κ.comp (galEmb K L Ω), ⟨hR K L Ω l ι κ ⟨hκ.cont, ?_⟩, fun s s' h => ?_, fun A hA s hs => ?_, ?_⟩,
      fun s s' h => ?_⟩
    · obtain ⟨art, Y, a, -, h1, h2, h3, -⟩ := hκ.alg
      exact ⟨art, Y, a, h1, h2, h3⟩
    · rw [show (1 : ℤ) - ((2 : ℕ) : ℤ) = -1 by norm_num, zpow_neg_one]
      exact hκ.conj (galEmb K L Ω s) (galEmb K L Ω s') h
    · exact hκ.unr A (hlM A hA) (fun h => hA (discr_over K M (fun B' hB' => H.ram B' (hK ▸ hB')) A h)) _ (hI A s hs)
    · obtain ⟨m, -, h1, h2⟩ := hκ.ord
      exact ⟨m, h1, fun A hA s hs => h2 A hA _ (hI A s hs)⟩
    · exact congrArg κ (AlgEquiv.ext fun x => AlgEquiv.congr_fun h x)
