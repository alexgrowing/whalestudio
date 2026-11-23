import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem adic_lin {G R : Type} [TopologicalSpace G] [CommRing R] (I : Ideal R) (c : R) {f f' : G → R}
    (h : AdicCont I f) (h' : AdicCont I f') : AdicCont I fun g => c * f g + f' g := by
  intro N
  have e : (fun g => (Ideal.Quotient.mk (I ^ N)) (c * f g + f' g)) =
      fun g => Ideal.Quotient.mk (I ^ N) c * Ideal.Quotient.mk (I ^ N) (f g) + Ideal.Quotient.mk (I ^ N) (f' g) := by
    funext g
    simp only [map_add, map_mul]
  rw [e]
  exact ((IsLocallyConstant.const _).mul (h N)).add (h' N)

private theorem adic_zero {G R : Type} [TopologicalSpace G] [CommRing R] (I : Ideal R) :
    AdicCont I fun _ : G => (0 : R) := fun _ => IsLocallyConstant.const _

section

variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R]
  (ρ : F.G₀ → Matrix (Fin n) (Fin n) R)

private theorem dY_lin (c : A) (Y Y' : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    dY F ρ (c • Y + Y') g = c • dY F ρ Y g + dY F ρ Y' g := by
  simp only [dY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  abel

private theorem dY_zero (g : F.G₀) : dY F ρ 0 g = 0 := by simp [dY]

private theorem locAt_lin (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (c : A) {z z' : F.G₀ → Matrix (Fin n) (Fin n) R}
    {v : F.Vl} {Y Y' : Matrix (Fin n) (Fin n) R} (h : LocAt F ρ w wi z v Y) (h' : LocAt F ρ w wi z' v Y') :
    LocAt F ρ w wi (c • z + z') v (c • Y + Y') := by
  intro g
  obtain ⟨h1, h2⟩ := h g
  obtain ⟨h1', h2'⟩ := h' g
  have key : wi v * ((c • z + z') ((F.φ v) g) - dY F ρ (c • Y + Y') ((F.φ v) g)) * w v =
      c • (wi v * (z ((F.φ v) g) - dY F ρ Y ((F.φ v) g)) * w v) +
        wi v * (z' ((F.φ v) g) - dY F ρ Y' ((F.φ v) g)) * w v := by
    rw [dY_lin]
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    abel
  refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
  · rw [key, Matrix.add_apply, Matrix.smul_apply, h1 i j hij, h1' i j hij, smul_zero, add_zero]
  · rw [key, Matrix.add_apply, Matrix.smul_apply, h2 hg i, h2' hg i, smul_zero, add_zero]

end

private theorem sub_of_lin {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (s : Set M) (h0 : (0 : M) ∈ s)
    (h : ∀ (c : A) x y, x ∈ s → y ∈ s → c • x + y ∈ s) : ∃ S : Submodule A M, (S : Set M) = s := by
  refine ⟨{ carrier := s, add_mem' := ?_, zero_mem' := h0, smul_mem' := ?_ }, rfl⟩
  · intro x y hx hy
    have := h 1 x y hx hy
    rwa [one_smul] at this
  · intro c x hx
    have := h c x 0 hx h0
    rwa [add_zero] at this

theorem UpperTheory.V.Pa.sel_lin :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)), (∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = SelZ F t ρ w wi V) ∧ ∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = Bd F ρ V := by
  intro l _ F n A R _ _ _ t ρ w wi V
  constructor
  · apply sub_of_lin
    · refine ⟨fun _ => V.zero_mem, fun i j => ?_, fun g h => by simp, fun g => by simp, fun u g _ => rfl,
        fun v => ⟨0, V.zero_mem, fun g => ?_⟩⟩
      · exact adic_zero _
      · simp [dY_zero]
    · intro c x y hx hy
      obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hx
      obtain ⟨y1, y2, y3, y4, y5, y6⟩ := hy
      refine ⟨fun g => V.add_mem (V.smul_mem c (x1 g)) (y1 g), fun i j => ?_, fun g h => ?_, fun g => ?_,
        fun u g hg => ?_, fun v => ?_⟩
      · have e : (fun g => (c • x + y) g i j) = fun g => algebraMap A R c * x g i j + y g i j := by
          funext g
          rw [Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, Algebra.smul_def]
        rw [e]
        exact adic_lin _ _ (x2 i j) (y2 i j)
      · simp only [Pi.add_apply, Pi.smul_apply, x3 g h, y3 g h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
          Matrix.smul_mul, smul_add]
        abel
      · simp only [Pi.add_apply, Pi.smul_apply, x4 g, y4 g, Matrix.transpose_add, Matrix.transpose_smul,
          Matrix.transpose_neg, smul_neg]
        abel
      · simp [x5 u g hg, y5 u g hg]
      · obtain ⟨Y, hY, hYl⟩ := x6 v
        obtain ⟨Y', hY', hYl'⟩ := y6 v
        exact ⟨c • Y + Y', V.add_mem (V.smul_mem c hY) hY', locAt_lin F ρ w wi c hYl hYl'⟩
  · apply sub_of_lin
    · exact ⟨0, V.zero_mem, by simp, funext fun g => (dY_zero F ρ g).symm⟩
    · rintro c x y ⟨Y, hY, hYt, rfl⟩ ⟨Y', hY', hYt', rfl⟩
      refine ⟨c • Y + Y', V.add_mem (V.smul_mem c hY) hY', ?_, ?_⟩
      · rw [Matrix.transpose_add, Matrix.transpose_smul, hYt, hYt', smul_neg, neg_add]
      · funext g
        rw [dY_lin]
        rfl
