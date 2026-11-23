import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R]

private theorem dY_add (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (Y Y' : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    dY F ρ (Y + Y') g = dY F ρ Y g + dY F ρ Y' g := by
  simp only [dY, Matrix.mul_add, Matrix.add_mul]
  abel

private theorem dY_zero (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (g : F.G₀) : dY F ρ 0 g = 0 := by
  simp [dY]

private theorem dY_smul (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (c : A) (Y : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    dY F ρ (c • Y) g = c • dY F ρ Y g := by
  simp only [dY, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

private theorem ac_add {Γ : Type} [TopologicalSpace Γ] {I : Ideal R} {f f' : Γ → R} (h : AdicCont I f)
    (h' : AdicCont I f') : AdicCont I fun g => f g + f' g := by
  intro N
  have key := (h N).add (h' N)
  convert key using 1
  funext g
  simp [map_add]

private theorem ac_smul {Γ : Type} [TopologicalSpace Γ] {I : Ideal R} {f : Γ → R} (c : A) (h : AdicCont I f) :
    AdicCont I fun g => c • f g := by
  intro N
  have key := (h N).comp (fun x => Ideal.Quotient.mk (I ^ N) (algebraMap A R c) * x)
  convert key using 1
  funext g
  simp [Function.comp, Algebra.smul_def, map_mul]

end

theorem UpperTheory.V.Pa.Det.selSub :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)), (∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = SelZ F t ρ w wi V) ∧ ∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = Bd F ρ V := by
  intro l _ F n A R _ _ _ t ρ w wi V
  refine ⟨⟨⟨⟨⟨SelZ F t ρ w wi V, ?_⟩, ?_⟩, ?_⟩, rfl⟩, ⟨⟨⟨⟨Bd F ρ V, ?_⟩, ?_⟩, ?_⟩, rfl⟩⟩
  · intro z z' hz hz'
    simp only [SelZ, Set.mem_setOf_eq] at hz hz' ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz
    obtain ⟨h1', h2', h3', h4', h5', h6'⟩ := hz'
    refine ⟨fun g => V.add_mem (h1 g) (h1' g), fun i j => ?_, fun g k => ?_, fun g => ?_,
      fun u g hg => ?_, fun v => ?_⟩
    · have e := ac_add (h2 i j) (h2' i j)
      simpa only [Pi.add_apply, Matrix.add_apply] using e
    · rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, h3, h3', Matrix.mul_add, Matrix.add_mul]
      abel
    · rw [Pi.add_apply, Pi.add_apply, h4, h4', Matrix.transpose_add, neg_add]
    · rw [Pi.add_apply, h5 u g hg, h5' u g hg, add_zero]
    · obtain ⟨Y, hY, hl⟩ := h6 v
      obtain ⟨Y', hY', hl'⟩ := h6' v
      refine ⟨Y + Y', V.add_mem hY hY', ?_⟩
      intro g
      obtain ⟨a, b⟩ := hl g
      obtain ⟨a', b'⟩ := hl' g
      have e : ∀ x, (z + z') x - dY F ρ (Y + Y') x = (z x - dY F ρ Y x) + (z' x - dY F ρ Y' x) := by
        intro x
        rw [Pi.add_apply, dY_add]
        abel
      refine ⟨fun i j hij => ?_, fun hm i => ?_⟩
      · rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, a i j hij, a' i j hij, add_zero]
      · rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, b hm i, b' hm i, add_zero]
  · simp only [SelZ, Set.mem_setOf_eq]
    refine ⟨fun g => V.zero_mem, fun i j => ?_, fun g k => ?_, fun g => ?_, fun u g hg => rfl, fun v => ?_⟩
    · intro N
      simp only [Pi.zero_apply, Matrix.zero_apply, map_zero]
      exact IsLocallyConstant.const 0
    · simp
    · simp
    · refine ⟨0, V.zero_mem, ?_⟩
      intro g
      simp [dY_zero]
  · intro c z hz
    simp only [SelZ, Set.mem_setOf_eq] at hz ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz
    refine ⟨fun g => V.smul_mem c (h1 g), fun i j => ?_, fun g k => ?_, fun g => ?_,
      fun u g hg => ?_, fun v => ?_⟩
    · have e := ac_smul c (h2 i j)
      simpa only [Pi.smul_apply, Matrix.smul_apply] using e
    · rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, h3, smul_add, Matrix.mul_smul, Matrix.smul_mul]
    · rw [Pi.smul_apply, Pi.smul_apply, h4, Matrix.transpose_smul, smul_neg]
    · rw [Pi.smul_apply, h5 u g hg, smul_zero]
    · obtain ⟨Y, hY, hl⟩ := h6 v
      refine ⟨c • Y, V.smul_mem c hY, ?_⟩
      intro g
      obtain ⟨a, b⟩ := hl g
      have e : ∀ x, (c • z) x - dY F ρ (c • Y) x = c • (z x - dY F ρ Y x) := by
        intro x
        rw [Pi.smul_apply, dY_smul, smul_sub]
      refine ⟨fun i j hij => ?_, fun hm i => ?_⟩
      · rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, a i j hij, smul_zero]
      · rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, b hm i, smul_zero]
  · rintro z z' ⟨Y, hY, hT, rfl⟩ ⟨Y', hY', hT', rfl⟩
    refine ⟨Y + Y', V.add_mem hY hY', by rw [Matrix.transpose_add, hT, hT', neg_add], ?_⟩
    funext g
    rw [Pi.add_apply, dY_add]
  · exact ⟨0, V.zero_mem, by simp, by funext g; rw [dY_zero]; rfl⟩
  · rintro c z ⟨Y, hY, hT, rfl⟩
    refine ⟨c • Y, V.smul_mem c hY, by rw [Matrix.transpose_smul, hT, smul_neg], ?_⟩
    funext g
    rw [Pi.smul_apply, dY_smul]
