import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCoefOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem cf_small {l : ℕ} [hl : Fact l.Prime] (C : ℝ) : ∃ N : ℕ, ‖((l : PadicAlgCl l)) ^ N‖ * C ≤ 1 := by
  have hn : ‖((l : ℕ) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have h := PadicAlgCl.valuation_coe l (l : PadicAlgCl l)
    rw [PadicAlgCl.valuation_p] at h
    rw [← h]
    simp
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hr : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    rw [hn]
    exact inv_lt_one_of_one_lt₀ hl1
  rcases le_or_gt C 0 with hC | hC
  · exact ⟨0, by simp; linarith⟩
  · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hC) hr
    refine ⟨N, ?_⟩
    rw [norm_pow]
    calc ‖((l : ℕ) : PadicAlgCl l)‖ ^ N * C ≤ C⁻¹ * C :=
          mul_le_mul_of_nonneg_right hN.le hC.le
      _ = 1 := inv_mul_cancel₀ hC.ne'

private theorem padicAlgCl_norm_le_one_of_isIntegral {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 := by
  obtain ⟨p, hpm, hp⟩ := hx
  by_contra h
  push_neg at h
  rw [← Polynomial.aeval_def, Polynomial.aeval_eq_sum_range, Finset.sum_range_succ,
    hpm.coeff_natDegree, one_smul] at hp
  have hn0 : p.natDegree ≠ 0 := by
    intro h0
    rw [h0] at hp
    simp at hp
  have hxn : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, p.coeff i • x ^ i := by
    linear_combination hp
  have h1 : 1 ≤ ‖x‖ := h.le
  have hb : ‖∑ i ∈ Finset.range p.natDegree, p.coeff i • x ^ i‖ ≤ ‖x‖ ^ (p.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Algebra.smul_def, norm_mul, norm_pow]
    have ha : ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
      simpa using PadicInt.norm_le_one (p.coeff i)
    calc ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ * ‖x‖ ^ i
        ≤ 1 * ‖x‖ ^ (p.natDegree - 1) :=
          mul_le_mul ha (pow_le_pow_right₀ h1 (by omega)) (by positivity) zero_le_one
      _ = ‖x‖ ^ (p.natDegree - 1) := one_mul _
  have h2 : ‖x‖ ^ p.natDegree ≤ ‖x‖ ^ (p.natDegree - 1) := by
    rw [← norm_pow, hxn, norm_neg]
    exact hb
  have h3 : ‖x‖ ^ (p.natDegree - 1) < ‖x‖ ^ p.natDegree := pow_lt_pow_right₀ h (by omega)
  linarith

private theorem cf_field {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ x ∈ c.O, x ∈ E ∧ ‖x‖ ≤ 1 := by
  haveI := c.fin
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := c.O)
  let T : Set (PadicAlgCl l) := Subtype.val '' (S : Set c.O)
  haveI : Finite T := (S.finite_toSet.image _).to_subtype
  refine ⟨IntermediateField.adjoin ℚ_[l] T,
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x), ?_⟩
  have key : ∀ y ∈ Submodule.span ℤ_[l] (S : Set c.O),
      ((y : c.O) : PadicAlgCl l) ∈ IntermediateField.adjoin ℚ_[l] T := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => simpa using add_mem hy hz
    | smul a y _ hy =>
        rw [Subalgebra.coe_smul, Algebra.smul_def,
          IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) hy
  intro x hx
  refine ⟨key ⟨x, hx⟩ (hS ▸ Submodule.mem_top), padicAlgCl_norm_le_one_of_isIntegral x ?_⟩
  have hi := IsIntegral.of_finite ℤ_[l] (⟨x, hx⟩ : c.O)
  simpa using hi.map c.O.val

private theorem cf_entries {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] {m : ℕ} (s : G →* Matrix (Fin m) (Fin m) (PadicAlgCl l)) (z : G → Fin m → PadicAlgCl l)
    (hs : Continuous s) (hz : Continuous z) (hc : ∀ g h, z (g * h) = z g + s g *ᵥ z h) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ g i, z g i ∈ E := by
  classical
  let e : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  let B : G → Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) (PadicAlgCl l) := fun g =>
    Matrix.fromBlocks (s g) (Matrix.replicateCol (Fin 1) (z g)) 0 1
  have hz1 : z 1 = 0 := by simpa using hc 1 1
  have hB1 : B 1 = 1 := by
    have hcol : Matrix.replicateCol (Fin 1) (z 1) = 0 := by
      ext i j
      simp [hz1]
    simp only [B, map_one, hcol, Matrix.fromBlocks_one]
  have hBmul : ∀ g h, B (g * h) = B g * B h := by
    intro g h
    simp only [B, Matrix.fromBlocks_multiply, map_mul]
    congr 1
    · simp
    · ext i j
      simp [hc, Matrix.mul_apply, Matrix.mulVec, dotProduct, add_comm]
    · simp
    · simp
  let f : G →* Matrix (Fin (m + 1)) (Fin (m + 1)) (PadicAlgCl l) :=
    { toFun := fun g => Matrix.reindexAlgEquiv ℚ_[l] (PadicAlgCl l) e (B g)
      map_one' := by simp only [hB1, map_one]
      map_mul' := fun g h => by simp only [hBmul, map_mul] }
  obtain ⟨K, hK, hmem⟩ :=
    GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l G (m + 1) f.toHomUnits (by
      intro i j
      change Continuous fun g => B g (e.symm i) (e.symm j)
      generalize e.symm i = a
      generalize e.symm j = b
      rcases a with a | a <;> rcases b with b | b
      · simp only [B, Matrix.fromBlocks_apply₁₁]
        exact hs.matrix_elem a b
      · simp only [B, Matrix.fromBlocks_apply₁₂, Matrix.replicateCol_apply]
        exact (continuous_apply a).comp hz
      · simp only [B, Matrix.fromBlocks_apply₂₁]
        exact continuous_const
      · simp only [B, Matrix.fromBlocks_apply₂₂]
        exact continuous_const)
  refine ⟨K, hK, fun g i => ?_⟩
  have h := hmem g (e (Sum.inl i)) (e (Sum.inr 0))
  change B g (e.symm (e (Sum.inl i))) (e.symm (e (Sum.inr 0))) ∈ K at h
  simpa [B] using h

theorem UpperTheory.V.Th.Det.cocField :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] {m : ℕ} (σ : G →* GL (Fin m) (Qbar l)) (z : G → Fin m → Qbar l), Continuous σ → Continuous z → (∀ g h, z (g * h) = z g + W.mat σ g *ᵥ z h) → ∃ (c' : Coef l) (a : Qbar l), c.O ≤ c'.O ∧ a ≠ 0 ∧ ∀ g i, a * z g i ∈ c'.O := by
  intro l _ c G _ _ _ _ _ m σ z hσ hz hc
  obtain ⟨E1, hE1, hz1⟩ := cf_entries (W.mat σ) z (Units.continuous_val.comp hσ) hz hc
  obtain ⟨E2, hE2, hO⟩ := cf_field c
  haveI := hE1
  haveI := hE2
  obtain ⟨c', hc'⟩ := X.So.coefOf l (E1 ⊔ E2)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hz.continuousOn
  obtain ⟨N, hN⟩ := cf_small (l := l) C
  refine ⟨c', ((l : ℕ) : PadicAlgCl l) ^ N, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := hO x hx
    exact (hc' x).mpr ⟨(le_sup_right : E2 ≤ E1 ⊔ E2) h1, h2⟩
  · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  · intro g i
    rw [hc']
    constructor
    · exact mul_mem (pow_mem (natCast_mem _ l) N) ((le_sup_left : E1 ≤ E1 ⊔ E2) (hz1 g i))
    · rw [norm_mul]
      calc ‖((l : ℕ) : PadicAlgCl l) ^ N‖ * ‖z g i‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ N‖ * C :=
            mul_le_mul_of_nonneg_left
              ((norm_le_pi_norm (z g) i).trans (hC g (Set.mem_univ _))) (norm_nonneg _)
        _ ≤ 1 := hN
