import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem aux_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0) {ζ : Ω}
    (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_left hm).1 h1

private theorem power_bounds_of_between {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {η : Ω} (h1 : A.valuation η = 1)
    (h : A.valuation (η - 1) < 1) (i : ℕ) : A.valuation (1 - η ^ i) < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : 1 - η ^ (i + 1) = η * (1 - η ^ i) - (η - 1) := by ring
    rw [e]
    refine A.valuation.map_sub_lt ?_ h
    rw [map_mul, h1, one_mul]; exact ih

private theorem root_of_unity_eq_one_of_close_residue {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1) (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hv
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have e : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => power_bounds_of_between A (aux_one A hm hη) h i

private theorem inertia_fixes_prime_to_roots {Ω : Type} [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hA : ¬ A.valuation (m : Ω) < 1) {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) {ζ : Ω} (hζ : ζ ^ m = 1) : g ζ = ζ := by
  have hv := aux_one A hm hζ
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp at hv
  have e : g ζ / ζ - 1 = (g ζ - ζ) / ζ := by field_simp
  have : g ζ / ζ = 1 := by
    refine root_of_unity_eq_one_of_close_residue A hm hA (by rw [div_pow, ← map_pow, hζ, map_one, div_one]) ?_
    rw [e, map_div₀, hv, div_one]; exact hg.2 ζ hv.le
  exact (div_eq_one_iff_eq h0).1 this

private theorem open_kernel_killing_roots_of_unity {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {w : ℕ} (hw : w ≠ 0) {C : Type} [Group C]
    (θ : G ℚ Ω →* C) (hk : KillsMu w θ) : IsOpen (θ.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ w = 1}.Finite := by
    refine (nthRoots w (1 : Ω)).finite_toSet.subset fun ζ hζ => ?_
    exact (mem_nthRoots (Nat.pos_of_ne_zero hw)).2 hζ
  haveI : Finite {ζ : Ω | ζ ^ w = 1} := hfin
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ w = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ w = 1}).fixingSubgroup) (fun g hg => ?_)
    (IntermediateField.fixingSubgroup_isOpen _)
  refine hk g fun ζ hζ => ?_
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ (IntermediateField.subset_adjoin _ _ hζ)

theorem UpperTheory.theta_unramified_of_kills_roots_of_unity :
    UpperTheory.V.Sd.S3.ThetaUnr := by
  intro Ω _ _ _ l hl w hw θ hθ hk
  have h1 : ∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker := fun A hA g hg =>
    hk g fun ζ hζ => inertia_fixes_prime_to_roots A hw.ne_zero (hA w (Finset.mem_singleton_self w)) hg hζ
  refine ⟨h1, fun F hF => ?_⟩
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  haveI : NeZero (l : Qbar l) := ⟨Nat.cast_ne_zero.2 hl.out.ne_zero⟩
  have hc : Nat.card (rootsOfUnity l (Qbar l)) = Nat.card (Multiplicative (ZMod l)) := by
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity]; simp
  let e := mulEquivOfCyclicCardEq hc
  have hm : ∀ g, θ g ∈ rootsOfUnity l (Qbar l) := fun g => by
    rw [mem_rootsOfUnity]
    exact DFunLike.congr_fun hθ g
  have hker : (e.toMonoidHom.comp (θ.codRestrict _ hm)).ker = θ.ker := by
    ext g
    simp [MonoidHom.mem_ker, Subtype.ext_iff]
  have := hF (e.toMonoidHom.comp (θ.codRestrict _ hm))
  rw [hker] at this
  exact this (open_kernel_killing_roots_of_unity hw.ne_zero θ hk) h1
