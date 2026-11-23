import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsLatticeIffFixedPointQuadraticTorus

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.exists_unit_smul_order_of_mem_gs :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ (t : Kˣ) (S : Set (Etau K τ)), S ∈ PS.Gs O τ t 1 → ∃ (m : ℕ) (r : Kˣ) (u : (Etau K τ)ˣ), u ∈ Gu O τ ∧ S = PS.ml (PS.sc τ r * u) (Ord O (yy π m x)) := by
  intro O K _ _ _ _ _ Δ τ hL hτ π n e h x hC t S hS
  obtain ⟨hfix, c, hc, hgen⟩ := hS
  rw [one_mul] at hgen
  obtain ⟨r, u, hu1, hu2, hcu⟩ := hC.gen.cint hL hc
  obtain ⟨s0, hs0⟩ := hfix.fg
  subst hs0
  set N : Submodule O (Etau K τ) := Submodule.span O (s0 : Set (Etau K τ)) with hN
  have hcS : (c : Etau K τ) ∈ N := hgen.1
  have hint : ∀ w ∈ N, ∃ a b : O, ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w
      = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * x :=
    fun w hw => (hC.gen.int_iff hL _).1 (hgen.2 w hw)
  let B : Ideal O :=
    { carrier := {b | ∃ a : O,
        (c : Etau K τ) * (algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * x) ∈ N}
      add_mem' := by
        rintro b1 b2 ⟨a1, h1⟩ ⟨a2, h2⟩
        refine ⟨a1 + a2, ?_⟩
        have key : (c : Etau K τ) * (algebraMap O (Etau K τ) (a1 + a2) + algebraMap O (Etau K τ) (b1 + b2) * x)
            = (c : Etau K τ) * (algebraMap O (Etau K τ) a1 + algebraMap O (Etau K τ) b1 * x)
              + (c : Etau K τ) * (algebraMap O (Etau K τ) a2 + algebraMap O (Etau K τ) b2 * x) := by
          simp only [map_add]
          ring
        rw [key]
        exact N.add_mem h1 h2
      zero_mem' := by
        refine ⟨0, ?_⟩
        simp only [map_zero, zero_mul, add_zero, mul_zero]
        exact N.zero_mem
      smul_mem' := by
        rintro k b ⟨a, hab⟩
        refine ⟨k * a, ?_⟩
        have key : (c : Etau K τ) * (algebraMap O (Etau K τ) (k * a) + algebraMap O (Etau K τ) (k • b) * x)
            = k • ((c : Etau K τ) * (algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * x)) := by
          rw [smul_eq_mul, Algebra.smul_def, map_mul, map_mul]
          ring
        rw [key]
        exact N.smul_mem k hab }
  have hB : B ≠ ⊥ := by
    have hωc : ω * (c : Etau K τ) ∈ N := hfix.stab _ hcS
    obtain ⟨a, b, hab⟩ := hint _ hωc
    have hω : (ω : Etau K τ) = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * x := by
      rw [← hab, mul_left_comm, Units.inv_mul, mul_one]
    have hb : b ∈ B := ⟨a, by rw [← hω, mul_comm]; exact hωc⟩
    intro hbot
    rw [hbot] at hb
    have hb0 : b = 0 := (Submodule.mem_bot O).1 hb
    rw [hb0, map_zero, zero_mul, add_zero] at hω
    have him := congrArg QuadraticAlgebra.im hω
    rw [algebraMap_etau, QuadraticAlgebra.algebraMap_im] at him
    exact one_ne_zero him
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hB hC.irr
  have hyy : yy π m x = algebraMap O (Etau K τ) (π ^ m) * x := by
    rw [yy, Algebra.smul_def, algebraMap_etau (O := O) (π ^ m)]
  have hpm : π ^ m ∈ B := by
    rw [hm]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨a0, ha0⟩ := hpm
  refine ⟨m, r, u, ⟨hu1, hu2⟩, ?_⟩
  rw [← hcu]
  ext w
  rw [PS.mem_ml]
  show w ∈ N ↔ _ ∈ Submodule.span O {1, yy π m x}
  rw [Submodule.mem_span_pair]
  constructor
  · intro hw
    obtain ⟨a, b, hab⟩ := hint w hw
    have hbB : b ∈ B := ⟨a, by rw [← hab, ← mul_assoc, Units.mul_inv, one_mul]; exact hw⟩
    rw [hm, Ideal.mem_span_singleton'] at hbB
    obtain ⟨k, rfl⟩ := hbB
    refine ⟨a, k, ?_⟩
    rw [hab, hyy, Algebra.smul_def, Algebra.smul_def, map_mul]
    ring
  · rintro ⟨a, k, hak⟩
    have hw : w = (c : Etau K τ) * (a • 1 + k • yy π m x) := by
      rw [hak, ← mul_assoc, Units.mul_inv, one_mul]
    rw [hw, mul_add, hyy]
    apply N.add_mem
    · rw [mul_smul_comm, mul_one]
      exact N.smul_mem a hcS
    · rw [mul_smul_comm]
      apply N.smul_mem
      have key : (c : Etau K τ) * (algebraMap O (Etau K τ) (π ^ m) * x)
          = (c : Etau K τ) * (algebraMap O (Etau K τ) a0 + algebraMap O (Etau K τ) (π ^ m) * x)
            - a0 • (c : Etau K τ) := by
        rw [Algebra.smul_def]
        ring
      rw [key]
      exact N.sub_mem ha0 (N.smul_mem a0 hcS)
