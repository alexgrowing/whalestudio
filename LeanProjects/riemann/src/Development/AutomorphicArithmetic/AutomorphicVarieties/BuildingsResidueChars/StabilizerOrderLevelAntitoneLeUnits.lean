import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

section

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K}

private theorem yy_val (π : O) (m : ℕ) (x : Etau K τ) :
    yy π m x = algebraMap O (Etau K τ) (π ^ m) * x := by
  rw [yy, algebraMap_etau (O := O), Algebra.smul_def]

private theorem mem_ord {y w : Etau K τ} :
    w ∈ Ord O y ↔ ∃ a b : O, w = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y := by
  change w ∈ (Submodule.span O {1, y} : Submodule O (Etau K τ)) ↔ _
  rw [Submodule.mem_span_pair]
  simp only [Algebra.smul_def, mul_one, eq_comm]

private theorem one_mem_ord (y : Etau K τ) : (1 : Etau K τ) ∈ Ord O y :=
  mem_ord.2 ⟨1, 0, by simp⟩

private theorem ord_mul {y : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c)
    {v w : Etau K τ} (hv : v ∈ Ord O y) (hw : w ∈ Ord O y) : v * w ∈ Ord O y := by
  obtain ⟨a, b, rfl⟩ := mem_ord.1 hv
  obtain ⟨p, q, rfl⟩ := mem_ord.1 hw
  refine mem_ord.2 ⟨a * p + b * q * c, a * q + b * p, ?_⟩
  simp only [map_add, map_mul]
  linear_combination (algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) q) * hy

private theorem ord_mono (π : O) (m : ℕ) (x : Etau K τ) :
    Ord O (yy π (m + 1) x) ⊆ Ord O (yy π m x) := by
  intro w hw
  obtain ⟨a, b, rfl⟩ := mem_ord.1 hw
  refine mem_ord.2 ⟨a, b * π, ?_⟩
  simp only [yy_val, pow_succ, map_mul]
  ring

private theorem yy_sq {π e : O} {x : Etau K τ} (h : x * x = algebraMap O (Etau K τ) e) (m : ℕ) :
    yy π m x * yy π m x = algebraMap O (Etau K τ) (π ^ m * π ^ m * e) := by
  simp only [yy_val, map_mul]
  linear_combination (algebraMap O (Etau K τ) (π ^ m) * algebraMap O (Etau K τ) (π ^ m)) * h

private theorem unit_mem {y : Etau K τ} {u : (Etau K τ)ˣ} (hu : u ∈ Hu O y) :
    (u : Etau K τ) ∈ Ord O y ∧ ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y := by
  have h : PS.ml u (Ord O y) = Ord O y := hu
  refine ⟨h.subset ⟨1, one_mem_ord y, mul_one _⟩, ?_⟩
  have := PS.mem_ml.1 (h.symm.subset (one_mem_ord (O := O) y))
  rwa [mul_one] at this

private theorem hu_of_mem {y : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c)
    {u : (Etau K τ)ˣ} (h1 : (u : Etau K τ) ∈ Ord O y)
    (h2 : ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y) : u ∈ Hu O y := by
  change PS.ml u (Ord O y) = Ord O y
  ext w
  rw [PS.mem_ml]
  refine ⟨fun hw => ?_, fun hw => ord_mul hy h2 hw⟩
  have := ord_mul hy h1 hw
  rwa [Units.mul_inv_cancel_left] at this

private theorem ord_int {y w : Etau K τ} (hy : IsIntegral O y) (hw : w ∈ Ord O y) :
    IsIntegral O w := by
  obtain ⟨a, b, rfl⟩ := mem_ord.1 hw
  exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul hy)

end

theorem UpperTheory.stabilizer_order_level_antitone_le_units :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ m : ℕ, Hu O (yy π (m + 1) x) ≤ Hu O (yy π m x) ∧ Hu O (yy π m x) ≤ Gu O τ := by
  intro O K _ _ _ _ _ Δ τ _ _ π n e h x c m
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨h1, h2⟩ := unit_mem hu
    exact hu_of_mem (yy_sq c.sq m) (ord_mono π m x h1) (ord_mono π m x h2)
  · obtain ⟨h1, h2⟩ := unit_mem hu
    have hi : IsIntegral O (yy π m x) := by
      rw [yy_val]
      exact isIntegral_algebraMap.mul c.gen.int
    exact ⟨ord_int hi h1, ord_int hi h2⟩
