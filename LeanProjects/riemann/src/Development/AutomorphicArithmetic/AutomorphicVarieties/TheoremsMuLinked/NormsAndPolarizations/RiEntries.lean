import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCoefOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IntModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.CocField
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem ri_small {l : ℕ} [hl : Fact l.Prime] (C : ℝ) : ∃ N : ℕ, ‖((l : PadicAlgCl l)) ^ N‖ * C ≤ 1 := by
  have h1 : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h1).mul_const C
  rw [zero_mul] at h2
  obtain ⟨N, hN⟩ := (h2.eventually_le_const zero_lt_one).exists
  exact ⟨N, by rwa [norm_pow]⟩

private theorem ri_entries {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] {m : ℕ} (s : G →* Matrix (Fin m) (Fin m) (PadicAlgCl l))
    (z : G → Matrix (Fin m) (Fin m) (PadicAlgCl l))
    (hs : Continuous s) (hz : Continuous z) (hc : ∀ g h, z (g * h) = z g + s g * z h * s g⁻¹) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ (∀ g i j, s g i j ∈ E) ∧
      ∀ g i j, z g i j ∈ E := by
  have h1 : z 1 = 0 := by
    have h := hc 1 1
    rw [mul_one, inv_one, map_one, Matrix.one_mul, Matrix.mul_one] at h
    exact left_eq_add.1 h
  let b : G →* Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (PadicAlgCl l) :=
    { toFun := fun g => Matrix.fromBlocks (s g) (z g * s g) 0 (s g)
      map_one' := by
        rw [map_one, h1, Matrix.zero_mul, Matrix.fromBlocks_one]
      map_mul' := fun g h => by
        have e : s g⁻¹ * (s g * s h) = s h := by rw [← map_mul, ← map_mul, inv_mul_cancel_left]
        rw [Matrix.fromBlocks_multiply, map_mul, hc]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.add_mul, Matrix.mul_assoc, e]
        rw [add_comm] }
  have hb : Continuous b :=
    Continuous.matrix_fromBlocks hs (hz.matrix_mul hs) continuous_const hs
  let r : G →* Matrix (Fin (m + m)) (Fin (m + m)) (PadicAlgCl l) :=
    (Matrix.reindexAlgEquiv (PadicAlgCl l) (PadicAlgCl l) finSumFinEquiv).toRingEquiv.toMonoidHom.comp b
  have hr : ∀ g i j, r g i j = b g (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := fun _ _ _ => rfl
  obtain ⟨E, fE, mE⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l G (m + m) r.toHomUnits
    fun i j => hb.matrix_elem (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  have hA : ∀ g i j, s g i j ∈ E := fun g i j => by
    have h : r g (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ∈ E := mE g _ _
    rw [hr, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h
    exact h
  have hB : ∀ g i j, (z g * s g) i j ∈ E := fun g i j => by
    have h : r g (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) ∈ E := mE g _ _
    rw [hr, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h
    exact h
  refine ⟨E, fE, hA, fun g i j => ?_⟩
  have e : z g = z g * s g * s g⁻¹ := by
    rw [Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
  rw [e, Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hB g i k) (hA _ k j)

theorem UpperTheory.V.Th.Nm.repIn :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)), Continuous ρ → (∀ g, IntM (mat ρ g)) → Continuous z → (∀ g g', z (g * g') = z g + mat ρ g * z g' * mat ρ g⁻¹) → ∃ (c' : Coef l) (a : Qbar l), c.O ≤ c'.O ∧ a ≠ 0 ∧ (∀ g, InO c' (mat ρ g)) ∧ ∀ g, InO c' (a • z g) := by
  intro l hl n F c ρ z hρ hi hz hc
  haveI : CompactSpace F.G₀ := isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  haveI : T2Space F.G₀ := inferInstance
  obtain ⟨E, fE, m₁, m₂⟩ := ri_entries (l := l) ((Units.coeHom _).comp ρ) z (Units.continuous_val.comp hρ) hz hc
  obtain ⟨d, hd⟩ := UpperTheory.V.X.So.coefOf l E
  obtain ⟨c', h1, h2⟩ := (UpperTheory.V.HV.coefSup l).1 c d
  have hn : Continuous fun g => ∑ i, ∑ j, ‖z g i j‖ :=
    continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => (hz.matrix_elem i j).norm
  obtain ⟨C, hC⟩ := (isCompact_range hn).bddAbove
  obtain ⟨N, hN⟩ := ri_small (l := l) C
  refine ⟨c', (l : PadicAlgCl l) ^ N, h1, pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero),
    fun g i j => h2 ((hd _).2 ⟨m₁ g i j, hi g i j⟩), fun g i j => h2 ((hd _).2 ⟨?_, ?_⟩)⟩
  · rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (pow_mem (natCast_mem _ _) _) (m₂ g i j)
  · rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
    have hb : ‖z g i j‖ ≤ C :=
      ((Finset.single_le_sum (f := fun j => ‖z g i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i => ∑ j, ‖z g i j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))).trans (hC ⟨g, rfl⟩)
    exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans hN
