import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem exp_tors (K : Type) [Field K] [NumberField K] :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ a : K, IsOfFinOrder a → a ^ m = 1 := by
  refine ⟨Units.torsionOrder K, Units.torsionOrder_ne_zero K, fun a ha => ?_⟩
  obtain ⟨k, hk, hak⟩ := isOfFinOrder_iff_pow_eq_one.1 ha
  have hi : IsIntegral ℤ a := IsIntegral.of_pow hk (by rw [hak]; exact isIntegral_one)
  let x : 𝓞 K := ⟨a, hi⟩
  have hx : x ^ k = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, map_one]
    exact hak
  let y : (𝓞 K)ˣ := Units.ofPowEqOne x k hx hk.ne'
  have hy : y ∈ Units.torsion K :=
    (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, Units.ext (by simpa [y] using hx)⟩)
  rw [← Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at hy
  have h2 := congrArg (fun z : (𝓞 K)ˣ => algebraMap (𝓞 K) K z) hy
  simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h2
  exact h2

private theorem conj_root {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (g u : Ω ≃ₐ[F] Ω) (β : Ω)
    (hβ : IsOfFinOrder β) : g (u (g.symm β)) = u β := by
  have hp := IsPrimitiveRoot.orderOf β
  haveI : NeZero (orderOf β) := ⟨hβ.orderOf_pos.ne'⟩
  have key : ∀ s : Ω ≃ₐ[F] Ω, ∃ i : ℕ, β ^ i = s β := fun s => by
    obtain ⟨i, -, hi⟩ := hp.eq_pow_of_pow_eq_one (ξ := s β) (by rw [← map_pow, pow_orderOf_eq_one, map_one])
    exact ⟨i, hi⟩
  obtain ⟨i, hi⟩ := key g.symm
  obtain ⟨j, hj⟩ := key u
  rw [← hi, map_pow, ← hj, ← pow_mul, mul_comm, pow_mul, hi, map_pow, g.apply_symm_apply]

private theorem exists_gen (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (n : ℕ) [NeZero n] :
    ∃ (ξ : Ωˣ) (b : K), (ξ : Ω) ^ n = algebraMap K Ω b ∧
      ∀ (β : Ω) (a : Kˣ), β ^ n = algebraMap K Ω a → IsOfFinOrder β → ∃ j : ℤ, (ξ : Ω) ^ j = β := by
  obtain ⟨m, hm, hK⟩ := exp_tors K
  haveI : NeZero (n * m) := ⟨mul_ne_zero (NeZero.ne n) hm⟩
  let T : Subgroup Ωˣ := rootsOfUnity (n * m) Ω ⊓
    ((Units.map (algebraMap K Ω).toMonoidHom).range).comap (powMonoidHom n)
  haveI : Finite T := Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left : T ≤ _))
  obtain ⟨⟨ξ, hξ⟩, hg⟩ := (isCyclic_subgroup_units T).exists_generator
  obtain ⟨b, hb⟩ := hξ.2
  refine ⟨ξ, b, ?_, fun β a h hβ => ?_⟩
  · have := congrArg Units.val hb
    simpa using this.symm
  · have h0 : β ≠ 0 := by
      rintro rfl
      rw [zero_pow (NeZero.ne n)] at h
      exact a.ne_zero ((map_eq_zero _).1 h.symm)
    have ha : IsOfFinOrder (a : K) := by
      have := hβ.pow (n := n)
      rw [h] at this
      obtain ⟨k, hk, hak⟩ := isOfFinOrder_iff_pow_eq_one.1 this
      exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, (algebraMap K Ω).injective (by rw [map_pow, hak, map_one])⟩
    have hT : Units.mk0 β h0 ∈ T := by
      refine ⟨(mem_rootsOfUnity _ _).2 (Units.ext ?_), a, Units.ext (by simpa using h.symm)⟩
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      rw [pow_mul, h, ← map_pow, hK a ha, map_one]
    obtain ⟨j, hj⟩ := hg ⟨_, hT⟩
    refine ⟨j, ?_⟩
    have := congrArg (fun z : T => ((z : Ωˣ) : Ω)) hj
    simpa using this

private theorem exists_generator_kummer_cocycle {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (U : Subgroup (Ω ≃ₐ[F] Ω)) (n : ℕ) [NeZero n]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ n) (hU : ∀ u : U, u.1 ζ = ζ) (ξ : Ωˣ) (hξ : ∀ u : U, u.1 (ξ ^ n) = ξ ^ n) :
    ∃ u0 : U, ∀ u : U, ∃ k : ℤ, u.1 ξ / ξ = (u0.1 ξ / ξ) ^ k := by
  have h1 : ∀ u : U, (u.1 ξ / ξ) ^ n = 1 := fun u => by
    rw [div_pow, ← map_pow, hξ, div_self (pow_ne_zero _ ξ.ne_zero)]
  have h2 : ∀ u v : U, u.1 (v.1 ξ / ξ) = v.1 ξ / ξ := fun u v => by
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (h1 v)
    rw [← hi, map_pow, hU]
  have h3 : ∀ u : U, u.1 ξ ≠ 0 := fun u => (map_ne_zero _).2 ξ.ne_zero
  let f : U →* Ωˣ := MonoidHom.mk' (fun u => Units.mk0 (u.1 ξ / ξ) (div_ne_zero (h3 u) ξ.ne_zero)) fun u v => by
    apply Units.ext
    have := h2 u v
    rw [map_div₀, div_eq_iff (h3 u)] at this
    simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul, AlgEquiv.mul_apply, this]
    ring
  have hle : f.range ≤ rootsOfUnity n Ω := by
    rintro _ ⟨u, rfl⟩
    exact (mem_rootsOfUnity _ _).2 (Units.ext (by simpa [f] using h1 u))
  haveI : Finite f.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  obtain ⟨⟨_, u0, rfl⟩, hg⟩ := (isCyclic_subgroup_units f.range).exists_generator
  refine ⟨u0, fun u => ?_⟩
  obtain ⟨k, hk⟩ := hg ⟨f u, u, rfl⟩
  refine ⟨k, ?_⟩
  have := congrArg (fun z : f.range => ((z : Ωˣ) : Ω)) hk
  simpa [f] using this.symm

theorem UpperTheory.V.Kum.reflRoot :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K) [Normal F K] (ψ : G F Ω →* (ZMod n)ˣ), U = galOf F K Ω → IsPrimitiveRoot ζ n →
    Nat.card {φ : U → ZMod n // φ ∈ EqHom N U (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β} ≤ Nat.card (scalRep (ZMod n) ψ).invariants ∧
    Finite {φ : U → ZMod n // φ ∈ EqHom N U (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β} := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U n _ N ζ _ ψ hU hζ
  subst hU
  have hζ' : IsPrimitiveRoot (algebraMap K Ω ζ) n := hζ.map_of_injective (algebraMap K Ω).injective
  have hinj : ∀ x y : ZMod n, algebraMap K Ω ζ ^ x.val = algebraMap K Ω ζ ^ y.val → x = y := fun x y h =>
    ZMod.val_injective n (hζ'.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h)
  obtain ⟨ξ, b, hb, hξ⟩ := exists_gen K Ω n
  obtain ⟨u0, hu0⟩ := exists_generator_kummer_cocycle (galOf F K Ω) n _ hζ' (fun u => u.2 ζ) ξ (fun u => by rw [hb]; exact u.2 b)
  have hinv : ∀ φ : galOf F K Ω → ZMod n, φ ∈ EqHom N (galOf F K Ω) (scalRep (ZMod n) ψ) → ∀ β : Ω,
      IsRad (algebraMap K Ω ζ) _ φ β → IsOfFinOrder β → φ u0 ∈ (scalRep (ZMod n) ψ).invariants := by
    intro φ hφ β hr hβ g
    let u' : galOf F K Ω := ⟨g * u0.1 * g⁻¹, (galOf_normal F K Ω).conj_mem _ u0.2 g⟩
    have h1 : φ u' = scalRep (ZMod n) ψ g (φ u0) :=
      (Submodule.mem_iInf _).1 hφ.2 g u0 u' fun x => by
        show g (u0.1 (g.symm (g x))) = g (u0.1 x)
        rw [g.symm_apply_apply]
    rw [← h1]
    apply hinj
    have h2 : u'.1 β = u0.1 β := conj_root g u0.1 β hβ
    rw [hr.2, hr.2] at h2
    exact mul_right_cancel₀ hr.1 h2
  have hval : ∀ (φ : galOf F K Ω → ZMod n) (j : ℤ), IsRad (algebraMap K Ω ζ) _ φ ((ξ : Ω) ^ j) →
      ∀ u, algebraMap K Ω ζ ^ (φ u).val = (u.1 ξ / ξ) ^ j := fun φ j hr u => by
    rw [div_zpow, ← map_zpow₀, hr.2, mul_div_cancel_right₀ _ hr.1]
  let e : {φ : galOf F K Ω → ZMod n // φ ∈ EqHom N _ (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ),
      IsRad (algebraMap K Ω ζ) _ φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β} →
      (scalRep (ZMod n) ψ).invariants := fun φ => ⟨φ.1 u0, by
    obtain ⟨h, β, a, hr, -, hβ⟩ := φ.2
    exact hinv _ h β hr hβ⟩
  have he : Function.Injective e := by
    rintro ⟨φ, hφ, β, a, hr, ha, hβ⟩ ⟨φ', hφ', β', a', hr', ha', hβ'⟩ h
    have h0 : φ u0 = φ' u0 := congrArg Subtype.val h
    obtain ⟨j, rfl⟩ := hξ β a ha hβ
    obtain ⟨j', rfl⟩ := hξ β' a' ha' hβ'
    refine Subtype.ext (funext fun u => hinj _ _ ?_)
    obtain ⟨k, hk⟩ := hu0 u
    show algebraMap K Ω ζ ^ (φ u).val = algebraMap K Ω ζ ^ (φ' u).val
    rw [hval φ j hr, hval φ' j' hr', hk, ← zpow_mul, ← zpow_mul, mul_comm k, mul_comm k, zpow_mul, zpow_mul,
      ← hval φ j hr, ← hval φ' j' hr', h0]
  exact ⟨Nat.card_le_card_of_injective e he, Finite.of_injective e he⟩
