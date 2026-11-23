import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

section
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K}

private theorem ord_mem {y z : Etau K τ} :
    z ∈ Ord O y ↔ ∃ a b : O, a • (1 : Etau K τ) + b • y = z :=
  Submodule.mem_span_pair

private theorem ord_one (y : Etau K τ) : (1 : Etau K τ) ∈ Ord O y :=
  ord_mem.2 ⟨1, 0, by simp⟩

private theorem ord_mul {y : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c)
    {z z' : Etau K τ} (hz : z ∈ Ord O y) (hz' : z' ∈ Ord O y) : z * z' ∈ Ord O y := by
  obtain ⟨a, b, rfl⟩ := ord_mem.1 hz
  obtain ⟨p, q, rfl⟩ := ord_mem.1 hz'
  refine ord_mem.2 ⟨a * p + b * q * c, a * q + b * p, ?_⟩
  simp only [Algebra.smul_def, map_add, map_mul]
  linear_combination (-(algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) q)) * hy

private theorem ord_sub {y y' : Etau K τ} {c c' : O} (hy : y * y = algebraMap O (Etau K τ) c)
    (hy' : y' * y' = algebraMap O (Etau K τ) c') {w : (Etau K τ)ˣ}
    (hw : PS.ml w (Ord O y) = Ord O y') {z : Etau K τ} (hz : z ∈ Ord O y) : z ∈ Ord O y' := by
  have hw1 : ((w⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y := by
    have := ord_one (O := O) y'
    rw [← hw, PS.mem_ml, mul_one] at this
    exact this
  rw [← hw, PS.mem_ml]
  exact ord_mul hy hw1 hz
end

private theorem lvl_le {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] {τ : K} {π : O} (hπ : Irreducible π) {x : Etau K τ}
    (hx : x.im ≠ 0) {m m' : ℕ} (h : yy π m x ∈ Ord O (yy π m' x)) : m' ≤ m := by
  obtain ⟨a, b, hab⟩ := ord_mem.1 h
  have him := congrArg QuadraticAlgebra.im hab
  simp only [yy, ← algebraMap_smul K a, ← algebraMap_smul K b, im_add, im_smul, im_one, mul_zero, zero_add,
    smul_eq_mul] at him
  have hk : algebraMap O K (b * π ^ m') = algebraMap O K (π ^ m) := by
    rw [map_mul]
    exact mul_right_cancel₀ hx (by rw [← him]; ring)
  have hd : π ^ m' ∣ π ^ m := ⟨b, by rw [IsFractionRing.injective O K hk.symm, mul_comm]⟩
  exact (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).1 hd

theorem UpperTheory.order_level_injective_of_smul_eq :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ (w : (Etau K τ)ˣ) (m m' : ℕ), PS.ml w (Ord O (yy π m x)) = Ord O (yy π m' x) → m = m' := by
  intro O K _ _ _ _ _ Δ τ L hD π n e h x hc w m m' hw
  haveI := L.frac
  have hx : x.im ≠ 0 := hc.gen.im_ne
  have hsq : ∀ j : ℕ, yy π j x * yy π j x = algebraMap O (Etau K τ) (π ^ j * π ^ j * e) := by
    intro j
    simp only [yy, smul_mul_smul_comm, hc.sq]
    rw [IsScalarTower.algebraMap_apply O K (Etau K τ), IsScalarTower.algebraMap_apply O K (Etau K τ),
      Algebra.smul_def, ← map_mul, map_mul (algebraMap O K) (π ^ j * π ^ j), map_mul (algebraMap O K) (π ^ j)]
  have self_mem : ∀ j : ℕ, yy π j x ∈ Ord O (yy π j x) := fun j => ord_mem.2 ⟨0, 1, by simp⟩
  have hw' : PS.ml w⁻¹ (Ord O (yy π m' x)) = Ord O (yy π m x) := by
    rw [← hw, ← PS.ml_mul, inv_mul_cancel, PS.ml_one]
  have h1 : m' ≤ m := lvl_le hc.irr hx (ord_sub (hsq m) (hsq m') hw (self_mem m))
  have h2 : m ≤ m' := lvl_le hc.irr hx (ord_sub (hsq m') (hsq m) hw' (self_mem m'))
  omega
