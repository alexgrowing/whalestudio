import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.Tw.extIdeal_inj {H G : Type} [CommGroup H] [CommGroup G] {k : Type} [Field k] [IsAlgClosed k]
    (i : H →* G) (hi : Function.Injective i) (g : H →* kˣ) : ∃ F : G →* kˣ, ∀ x, F (i x) = g x := by
  have hdiv : ∀ {n : ℤ}, n ≠ 0 → Function.Surjective (fun a : Additive kˣ => n • a) := by
    intro n hn y
    have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul y : kˣ) : k) hpos
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hpos.ne'] at hx
      exact (Additive.toMul y).ne_zero hx.symm
    have hu : Units.mk0 x hx0 ^ n.natAbs = Additive.toMul y := by
      ext
      simp [hx]
    rcases Int.natAbs_eq n with h | h
    · refine ⟨Additive.ofMul (Units.mk0 x hx0), ?_⟩
      apply Additive.toMul.injective
      simp only [toMul_zsmul, toMul_ofMul]
      rw [h, zpow_natCast, hu]
    · refine ⟨Additive.ofMul (Units.mk0 x hx0)⁻¹, ?_⟩
      apply Additive.toMul.injective
      simp only [toMul_zsmul, toMul_ofMul]
      rw [h, zpow_neg, zpow_natCast, inv_pow, inv_inv, hu]
  letI : DivisibleBy (Additive kˣ) ℤ := divisibleByOfSMulRightSurj _ _ hdiv
  obtain ⟨F, hF⟩ := (Module.Baer.of_divisible (Additive kˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive i) hi (MonoidHom.toAdditive g)
  refine ⟨MonoidHom.toAdditive.symm F, fun x => ?_⟩
  exact congrArg Additive.toMul (DFunLike.congr_fun hF (Additive.ofMul x))

private theorem UpperTheory.V.Ws.Tw.extIdeal_mon {S G : Type} [CommMonoid S] [CommGroup G] {k : Type} [Field k] [IsAlgClosed k]
    (φ : S →* G) (g : S →* kˣ) (h : ∀ a b, φ a = φ b → g a = g b) : ∃ F : G →* kˣ, ∀ x, F (φ x) = g x := by
  classical
  have key : ∀ a b c d, φ a / φ b = φ c / φ d → g a / g b = g c / g d := by
    intro a b c d e
    rw [div_eq_div_iff_mul_eq_mul] at e ⊢
    have := h (a * d) (c * b) (by rw [map_mul, map_mul, e])
    rwa [map_mul, map_mul] at this
  let Hs : Subgroup G :=
    { carrier := {x | ∃ a b, φ a / φ b = x}
      mul_mem' := by
        rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
        exact ⟨a * c, b * d, by rw [map_mul, map_mul, div_mul_div_comm]⟩
      one_mem' := ⟨1, 1, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, b, rfl⟩
        exact ⟨b, a, by rw [inv_div]⟩ }
  have hmem : ∀ x : Hs, ∃ a b, φ a / φ b = (x : G) := fun x => x.2
  choose A B hAB using hmem
  let hh : Hs →* kˣ :=
    { toFun := fun x => g (A x) / g (B x)
      map_one' := by
        have := key (A 1) (B 1) 1 1 (by rw [hAB]; simp)
        simpa using this
      map_mul' := by
        intro x y
        have := key (A (x * y)) (B (x * y)) (A x * A y) (B x * B y)
          (by rw [hAB, map_mul, map_mul, ← div_mul_div_comm, hAB, hAB]; rfl)
        show g (A (x * y)) / g (B (x * y)) = g (A x) / g (B x) * (g (A y) / g (B y))
        rw [this, map_mul, map_mul, div_mul_div_comm] }
  obtain ⟨F, hF⟩ := UpperTheory.V.Ws.Tw.extIdeal_inj Hs.subtype Subtype.val_injective hh
  refine ⟨F, fun x => ?_⟩
  let y : Hs := ⟨φ x, x, 1, by simp⟩
  have e1 : F (φ x) = hh y := hF y
  rw [e1]
  have := key (A y) (B y) x 1 (by rw [hAB]; simp [y])
  simpa [hh] using this

theorem UpperTheory.V.Ws.Tw.extIdeal :
    ∀ (K : Type) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ → ∀ (k : Type) [Field k] [IsAlgClosed k] (g : 𝓞 K → kˣ), (∀ a b, a ≠ 0 → b ≠ 0 → IsCoprime (Ideal.span {a}) 𝔪 → IsCoprime (Ideal.span {b}) 𝔪 → g (a * b) = g a * g b) → (∀ u : (𝓞 K)ˣ, g u = 1) → ∃ f : Ideal (𝓞 K) → kˣ, (∀ I J, I ≠ ⊥ → J ≠ ⊥ → IsCoprime I 𝔪 → IsCoprime J 𝔪 → f (I * J) = f I * f J) ∧ ∀ a, a ≠ 0 → IsCoprime (Ideal.span {a}) 𝔪 → f (Ideal.span {a}) = g a := by
  intro K _ _ 𝔪 _ k _ _ g hg hu
  classical
  let ι : Ideal (𝓞 K) → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ := fun I =>
    if hI : I = ⊥ then 1
    else Units.mk0 (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (FractionalIdeal.coeIdeal_ne_zero.mpr hI)
  have hιv : ∀ I : Ideal (𝓞 K), I ≠ ⊥ → ((ι I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) = I := by
    intro I hI
    simp only [ι, dif_neg hI, Units.val_mk0]
  have hι : ∀ I J : Ideal (𝓞 K), I ≠ ⊥ → J ≠ ⊥ → ι (I * J) = ι I * ι J := by
    intro I J hI hJ
    have hIJ : I * J ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim hI hJ
    apply Units.ext
    rw [Units.val_mul, hιv _ hIJ, hιv _ hI, hιv _ hJ, FractionalIdeal.coeIdeal_mul]
  have hspan : ∀ a : 𝓞 K, a ≠ 0 → Ideal.span {a} ≠ ⊥ :=
    fun a ha h => ha (Ideal.span_singleton_eq_bot.mp h)
  have hcopU : ∀ u : (𝓞 K)ˣ, IsCoprime (Ideal.span {(u : 𝓞 K)}) 𝔪 := by
    intro u
    rw [Ideal.span_singleton_eq_top.mpr u.isUnit, ← Ideal.one_eq_top]
    exact isCoprime_one_left
  let S : Submonoid (𝓞 K) :=
    { carrier := {a | a ≠ 0 ∧ IsCoprime (Ideal.span {a}) 𝔪}
      mul_mem' := by
        rintro a b ⟨ha, ca⟩ ⟨hb, cb⟩
        refine ⟨mul_ne_zero ha hb, ?_⟩
        rw [← Ideal.span_singleton_mul_span_singleton]
        exact ca.mul_left cb
      one_mem' := ⟨one_ne_zero, by
        rw [Ideal.span_singleton_one, ← Ideal.one_eq_top]
        exact isCoprime_one_left⟩ }
  let φ : S →* (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ :=
    { toFun := fun a => ι (Ideal.span {(a : 𝓞 K)})
      map_one' := by
        apply Units.ext
        show ((ι (Ideal.span {(1 : 𝓞 K)}) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) = 1
        rw [hιv _ (hspan 1 one_ne_zero), Ideal.span_singleton_one, FractionalIdeal.coeIdeal_top]
      map_mul' := by
        intro a b
        show ι (Ideal.span {(a : 𝓞 K) * b}) = ι (Ideal.span {(a : 𝓞 K)}) * ι (Ideal.span {(b : 𝓞 K)})
        rw [← Ideal.span_singleton_mul_span_singleton]
        exact hι _ _ (hspan _ a.2.1) (hspan _ b.2.1) }
  let g' : S →* kˣ :=
    { toFun := fun a => g a
      map_one' := by simpa using hu 1
      map_mul' := fun a b => hg a b a.2.1 b.2.1 a.2.2 b.2.2 }
  have hcompat : ∀ a b : S, φ a = φ b → g' a = g' b := by
    intro a b e
    have e2 : ((ι (Ideal.span {(a : 𝓞 K)}) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
        = ((ι (Ideal.span {(b : 𝓞 K)}) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) := congrArg Units.val e
    rw [hιv _ (hspan _ a.2.1), hιv _ (hspan _ b.2.1)] at e2
    obtain ⟨u, hu'⟩ := Ideal.span_singleton_eq_span_singleton.mp (FractionalIdeal.coeIdeal_injective e2)
    show g a = g b
    rw [← hu', hg _ _ a.2.1 u.ne_zero a.2.2 (hcopU u), hu u, mul_one]
  obtain ⟨F, hF⟩ := UpperTheory.V.Ws.Tw.extIdeal_mon φ g' hcompat
  refine ⟨fun I => F (ι I), ?_, ?_⟩
  · intro I J hI hJ _ _
    show F (ι (I * J)) = F (ι I) * F (ι J)
    rw [hι I J hI hJ, map_mul]
  · intro a ha hca
    exact hF ⟨a, ha, hca⟩
