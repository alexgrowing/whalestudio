import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem ev_iff {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ} {Z : Matrix (Fin n) (Fin n) R} :
    Z ∈ Ev A R n a ↔ ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j = 0 := by
  show (∀ i j : Fin n, ((((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊤ : Submodule A R)) ∧
      (¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊥ : Submodule A R))) ↔ _
  simp only [Submodule.mem_top, Submodule.mem_bot, implies_true, true_and]

private theorem od_iff {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ} {Z : Matrix (Fin n) (Fin n) R} :
    Z ∈ Od A R n a ↔ ∀ i j : Fin n, (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j = 0 := by
  show (∀ i j : Fin n, ((((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊥ : Submodule A R)) ∧
      (¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊤ : Submodule A R))) ↔ _
  simp only [Submodule.mem_top, Submodule.mem_bot, implies_true, and_true]

private theorem sandwich {R : Type} [CommRing R] {n a : ℕ} {P Q Z : Matrix (Fin n) (Fin n) R}
    (hP : ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → P i j = 0)
    (hQ : ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Q i j = 0) (i j : Fin n)
    (hZ : ∀ i' j' : Fin n, (((i : ℕ) < a) ↔ ((i' : ℕ) < a)) → (((j' : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i' j' = 0) :
    (P * Z * Q) i j = 0 := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun m _ => ?_
  by_cases h1 : (((i : ℕ) < a) ↔ ((m : ℕ) < a))
  · by_cases h2 : (((k : ℕ) < a) ↔ ((j : ℕ) < a))
    · rw [hZ m k h1 h2]
      ring
    · rw [hQ k j h2]
      ring
  · rw [hP i m h1]
    ring

theorem UpperTheory.V.Pa.okX :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (χ : G.Γ →* x.A), AdOk G.frame (fun g => x.ρX X (h.p₀ g)) (fun g => algebraMap x.A X (χ g)) (Ev x.A X n x.a) ∧ AdOk G.frame (fun g => x.ρX X (h.p₀ g)) (fun g => algebraMap x.A X (χ g)) (Od x.A X n x.a) := by
  intro l _ L G G0 h n x X _ _ χ
  classical
  have hblk : ∀ g : G0.frame.G₀, ∀ i j : Fin n, ¬ (((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)) →
      x.ρX X g i j = 0 := by
    intro g i j hij
    have hz := ev_iff.mp (x.blk g) i j hij
    simp [NP.ρX, Matrix.map_apply, hz]
  have hconj : ∀ g : G.frame.G₀, h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := by
    intro g
    apply Subtype.ext
    simp [GFrame.conj, Glob.Hom.p₀, map_mul, map_inv, h.c]
  have key : ∀ (M : Matrix (Fin n) (Fin n) x.A) (E : (x.A)ˣ),
      M = (E : x.A) • (1 : Matrix (Fin n) (Fin n) x.A) →
        ∃ u : Xˣ, M.map (algebraMap x.A X) = (u : X) • (1 : Matrix (Fin n) (Fin n) X) := by
    rintro M E rfl
    refine ⟨Units.map (algebraMap x.A X).toMonoidHom E, ?_⟩
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hform : ∀ g : G.frame.G₀, ∃ u : Xˣ,
      (x.ρX X (h.p₀ g))ᵀ * x.ρX X (h.p₀ (G.frame.conj g)) =
        (u : X) • (1 : Matrix (Fin n) (Fin n) X) := by
    intro g
    have hf := x.form (h.p₀ g)
    simp only [Units.val_one, Matrix.mul_one] at hf
    obtain ⟨u, hu⟩ := key _ _ hf
    refine ⟨u, ?_⟩
    rw [← hu, hconj]
    simp only [NP.ρX, Matrix.transpose_map, Matrix.map_mul]
  refine ⟨⟨?_, ?_, hform, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, hform, ?_, ?_, ?_, ?_⟩⟩
  all_goals try (simp [NP.ρX, Matrix.map_mul]; done)
  · intro g Z hZ
    rw [ev_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, sandwich (hblk _) (hblk _) i j
      (fun i' j' h1 h2 => hZ i' j' (fun h3 => hij (h1.trans (h3.trans h2)))), smul_zero]
  · intro Z hZ
    rw [ev_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, Matrix.transpose_apply, hZ j i (fun h3 => hij h3.symm), smul_zero]
  · intro g Z hZ
    rw [od_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, sandwich (hblk _) (hblk _) i j
      (fun i' j' h1 h2 => hZ i' j' (h1.symm.trans (hij.trans h2.symm))), smul_zero]
  · intro Z hZ
    rw [od_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, Matrix.transpose_apply, hZ j i hij.symm, smul_zero]
