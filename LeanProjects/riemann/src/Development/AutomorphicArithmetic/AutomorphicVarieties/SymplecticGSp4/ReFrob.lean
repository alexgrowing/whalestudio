import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PrimeTo
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem re_two {Γ M : Type} [Group Γ] [Monoid M] (a b : Γ →* M) :
    ∃ g, (∃ x, a x ≠ 1) → (∃ y, b y ≠ 1) → a g ≠ 1 ∧ b g ≠ 1 := by
  by_cases h : (∃ x, a x ≠ 1) ∧ ∃ y, b y ≠ 1
  · obtain ⟨⟨x, hx⟩, y, hy⟩ := h
    by_cases h1 : b x = 1
    · by_cases h2 : a y = 1
      · exact ⟨x * y, fun _ _ => ⟨by rwa [map_mul, h2, mul_one], by rwa [map_mul, h1, one_mul]⟩⟩
      · exact ⟨y, fun _ _ => ⟨h2, hy⟩⟩
    · exact ⟨x, fun _ _ => ⟨hx, h1⟩⟩
  · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩

private theorem re_unit (l : ℕ) [hl : Fact l.Prime] : ∃ u : ℤ_[l]ˣ, ¬ IsOfFinOrder u := by
  have hu : IsUnit ((l + 1 : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    simp
  refine ⟨hu.unit, fun h => ?_⟩
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have h1 : ((l + 1 : ℕ) : ℤ_[l]) ^ n = 1 := by
    have := congrArg Units.val e
    rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at this
  have h2 : (l + 1) ^ n = 1 := by exact_mod_cast h1
  have h3 := hl.out.pos
  rw [pow_eq_one_iff_left hn.ne'] at h2
  omega

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem re_cc : ∃ σ : G ℚ Ω, IsCC σ := by
  obtain ⟨σ, h⟩ := exists_isConjOm (E := ℚ) (Ω := Ω)
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun x => by rw [eq_ratCast (algebraMap ℚ Ω), map_ratCast], ?_⟩
  exact h

private theorem re_mul {A : ValuationSubring Ω} {q : ℕ} {t g : G ℚ Ω} (ht : t ∈ Ine (F := ℚ) A)
    (hg : IsFrob (F := ℚ) A q g) : IsFrob (F := ℚ) A q (t * g) := by
  refine ⟨mul_mem ht.1 hg.1, fun x hx => ?_⟩
  have hy : A.valuation (g x) ≤ 1 :=
    (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec hg.1 x).2 ((A.valuation_le_one_iff _).1 hx))
  have h3 := Valuation.map_add_lt A.valuation (ht.2 _ hy) (hg.2 x hx)
  rw [sub_add_sub_cancel] at h3
  exact h3

private theorem re_frob (l : ℕ) [hl : Fact l.Prime] (v : ℕ) :
    ∃ (A : ValuationSubring Ω) (σ : G ℚ Ω), v.Prime → A.valuation (v : Ω) < 1 ∧ IsFrob (F := ℚ) A v σ ∧
      (v = l → cycZ ℚ Ω l σ = 1) := by
  by_cases hv : v.Prime
  · obtain ⟨A, hA⟩ := (ML.placeBasic Ω).1 v hv
    obtain ⟨g, hg⟩ := (ML.placeBasic Ω).2.1 A v hv hA
    by_cases e : v = l
    · subst e
      obtain ⟨t, ht, e⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω v A hA (cycZ ℚ Ω v g)⁻¹
      exact ⟨A, t * g, fun _ => ⟨hA, re_mul ht hg, fun _ => by rw [map_mul, e, inv_mul_cancel]⟩⟩
    · exact ⟨A, g, fun _ => ⟨hA, hg, fun h => absurd h e⟩⟩
  · exact ⟨⊤, 1, fun h => absurd h hv⟩

end

theorem UpperTheory.V.GradeZeroInterpolatingElement.rawEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}, l ≠ 2 → ∀ (S : Finset ℕ) (e : ℕ) (ψ ξ : G ℚ Ω →* c.Oˣ), IsOpen (ψ.ker : Set (G ℚ Ω)) → ∃ D : Raw Ω c, D.S = S ∧ D.e = e ∧ D.ψ = ψ ∧ D.ξ = ξ ∧ (∀ p : ℕ, p.Prime → (D.pl p).valuation (p : Ω) < 1) ∧ IsCC D.cc ∧ D.om ^ (l - 1) = 1 ∧ (∀ g, Raw.bar D.om g = Raw.bar (chiO ℚ Ω l c.O) g) ∧ (∀ v : ℕ, v.Prime → IsFrob (D.pl v) v (D.sg v)) ∧ cycZ ℚ Ω l (D.sg l) = 1 ∧ Filter.Tendsto (fun n : ℕ => D.sg l ^ l ^ n.factorial) Filter.atTop (nhds D.ph) ∧ ((∃ g, Raw.bar D.al g ≠ 1) → (∃ g, Raw.bar D.Psi g ≠ 1) → Raw.bar D.al D.g0 ≠ 1 ∧ Raw.bar D.Psi D.g0 ≠ 1) ∧ (D.s0 : G ℚ Ω) ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker ∧ ¬ IsOfFinOrder (cycZ ℚ Ω l D.s0) := by
  intro Ω _ _ _ l hl c _ S e ψ ξ hψ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hl2 : 2 ≤ l := hl.out.two_le
  obtain ⟨om, hom, -⟩ := (omT Ω l c).1
  obtain ⟨cc, hcc⟩ := re_cc (Ω := Ω)
  choose pl sg h using re_frob (Ω := Ω) l
  obtain ⟨ph, hph⟩ := (primeTo l (G ℚ Ω) (sg l)).1
  let red : c.Oˣ →* ResidueField c.O := (residue c.O).toMonoidHom.comp (Units.coeHom c.O)
  obtain ⟨g0, hg0⟩ := re_two (red.comp (chiO ℚ Ω l c.O * om⁻¹ * ξ)) (red.comp (Chr.Psi l e ψ))
  obtain ⟨u, hu⟩ := re_unit l
  obtain ⟨s, hs, hsu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l (pl l) (h l hl.out).1 u
  have : Finite (G ℚ Ω ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hψ
  have hi : ψ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hI : s ^ (ψ.ker.index * (l - 1)) ∈ Ine (F := ℚ) (pl l) := pow_mem hs _
  refine ⟨⟨S, e, ψ, ξ, om, cc, pl, sg, ph, g0, ⟨_, hI.1⟩⟩, rfl, rfl, rfl, rfl, fun p hp => (h p hp).1, hcc, hom.1,
    fun g => Ideal.Quotient.eq.2 (hom.2 g), fun v hv => (h v hv).2.1, (h l hl.out).2.2 rfl, hph, hg0, ⟨⟨hI, ?_⟩, ?_⟩, ?_⟩
  · show s ^ (ψ.ker.index * (l - 1)) ∈ ψ.ker
    rw [pow_mul]
    exact pow_mem (Subgroup.pow_index_mem _ s) _
  · show om (s ^ (ψ.ker.index * (l - 1))) = 1
    rw [pow_mul, map_pow]
    exact DFunLike.congr_fun hom.1 _
  · show ¬ IsOfFinOrder (cycZ ℚ Ω l (s ^ (ψ.ker.index * (l - 1))))
    rw [map_pow, hsu]
    exact fun h => hu (h.of_pow (mul_ne_zero hi (by omega)))
