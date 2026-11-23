import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.adic_char_unipotent_pgroup_quotient :
    ∀ {l : ℕ} [Fact l.Prime] {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] [IsNoetherianRing Q] [CharP Q l] [Finite (ResidueField Q)] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* Q) (h : ℕ), h ≠ 0 → AdicCont (maximalIdeal Q) χ → (∀ g, χ g - 1 ∈ maximalIdeal Q) → (∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ ψ : G →* A, IsOpen (ψ.ker : Set G) → (∀ g g', χ g = χ g' → ψ g = ψ g') → ∀ g, ψ g ^ h = 1) → ∀ g, χ g = 1 := by
  intro l hl Q _ _ _ _ _ hfin G _ _ χ h hh hc hm H g
  have hp : l.Prime := hl.out
  have krull : ∀ x : Q, (∀ N : ℕ, Ideal.Quotient.mk (maximalIdeal Q ^ N) x = 1) → x = 1 := by
    intro x hx
    have h0 : x - 1 ∈ (⨅ N : ℕ, maximalIdeal Q ^ N) := by
      rw [Ideal.mem_iInf]
      intro N
      rw [← Ideal.Quotient.eq, hx N, map_one]
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal Q).ne_top, Ideal.mem_bot] at h0
    exact sub_eq_zero.mp h0
  have unip : ∀ (N : ℕ) (g : G), Ideal.Quotient.mk (maximalIdeal Q ^ N) (χ g) ^ (l ^ N) = 1 := by
    intro N g
    rw [← map_pow, ← map_one (Ideal.Quotient.mk (maximalIdeal Q ^ N)), Ideal.Quotient.eq]
    have : χ g ^ l ^ N - 1 = (χ g - 1) ^ l ^ N := by rw [sub_pow_char_pow, one_pow]
    rw [this]
    exact Ideal.pow_le_pow_right (Nat.lt_pow_self hp.one_lt).le (Ideal.pow_mem_pow (hm g) _)
  have hpow : χ g ^ h = 1 := by
    apply krull
    intro N
    haveI : Finite (Q ⧸ maximalIdeal Q) := hfin
    haveI : Finite (Q ⧸ maximalIdeal Q ^ N) :=
      Ideal.finite_quotient_pow (IsNoetherian.noetherian _) N
    let φ : G →* (Q ⧸ maximalIdeal Q ^ N)ˣ :=
      ((Ideal.Quotient.mk (maximalIdeal Q ^ N)).toMonoidHom.comp χ).toHomUnits
    have hφ : ∀ g, (φ g : Q ⧸ maximalIdeal Q ^ N) = Ideal.Quotient.mk _ (χ g) := fun g => rfl
    have hP : IsPGroup l φ.range := by
      rintro ⟨_, g, rfl⟩
      refine ⟨N, Subtype.ext (Units.ext ?_)⟩
      simpa [hφ] using unip N g
    have hO : IsOpen (φ.rangeRestrict.ker : Set G) := by
      have := (hc N).isOpen_fiber 1
      convert this using 1
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq]
      rw [← hφ, Units.val_eq_one, Subtype.ext_iff]
      rfl
    have := H φ.range hP φ.rangeRestrict hO
      (fun g g' e => Subtype.ext (Units.ext (by
        change (φ g : Q ⧸ maximalIdeal Q ^ N) = φ g'
        rw [hφ, hφ, e]))) g
    have h2 : φ g ^ h = 1 := congrArg Subtype.val this
    rw [map_pow, ← hφ, ← Units.val_pow_eq_pow_val, h2, Units.val_one]
  obtain ⟨a, h', hnd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hh l hp.ne_one
  have h3 : χ g ^ h' = 1 := by
    have : (χ g ^ h' - 1) ^ l ^ a = 0 := by
      rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm, hpow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ hp.ne_zero) |>.mp this)
  apply krull
  intro N
  have h4 : Ideal.Quotient.mk (maximalIdeal Q ^ N) (χ g) ^ h' = 1 := by
    rw [← map_pow, h3, map_one]
  have hcop : Nat.Coprime (l ^ N) h' := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
  have h5 : orderOf (Ideal.Quotient.mk (maximalIdeal Q ^ N) (χ g)) ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (unip N g)) (orderOf_dvd_of_pow_eq_one h4)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)
