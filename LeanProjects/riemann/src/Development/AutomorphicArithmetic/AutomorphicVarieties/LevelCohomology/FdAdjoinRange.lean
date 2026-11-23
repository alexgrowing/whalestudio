import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.IntIffNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

private theorem fd_adjoin_range (l : ℕ) [Fact l.Prime] {ι : Type} [Finite ι] (f : ι → PadicAlgCl l) :
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) := by
  haveI : Finite (Set.range f) := (Set.finite_range _).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral

private theorem char_finext (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] (ψ : Γ →* (PadicAlgCl l)ˣ) (hψ : IsOpen (ψ.ker : Set Γ)) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ g, (ψ g : PadicAlgCl l) ∈ K := by
  haveI : Finite (Γ ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hψ
  refine ⟨_, fd_adjoin_range l (fun q : Γ ⧸ ψ.ker => (ψ q.out : PadicAlgCl l)), fun g => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ψ.ker g
  refine IntermediateField.subset_adjoin _ _ ⟨(g : Γ ⧸ ψ.ker), ?_⟩
  have h1 : ψ (h : Γ) = 1 := h.2
  simp only [hh, map_mul, h1, mul_one]

private theorem coc_finext (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (K₀ : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K₀]
    (θ c : Γ → PadicAlgCl l) (hθ : ∀ g, θ g ∈ K₀) (hθ1 : θ 1 = 1) (hc : Continuous c)
    (hcoc : ∀ g h, c (g * h) = c g + θ g * c h) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ K₀ ≤ E ∧ ∀ g, c g ∈ E := by
  obtain ⟨ι, _, K, hK, hcov⟩ := GlobalTheory.CompactRepField.exists_countable_family l
  have hc1 : c 1 = 0 := by
    have := hcoc 1 1
    rw [one_mul, hθ1, one_mul] at this
    exact left_eq_add.1 this
  let H : ι → Subgroup Γ := fun i =>
    { carrier := {g | c g ∈ K₀ ⊔ K i}
      one_mem' := by
        show c 1 ∈ K₀ ⊔ K i
        rw [hc1]; exact zero_mem _
      mul_mem' := fun {g h} hg hh => by
        show c (g * h) ∈ K₀ ⊔ K i
        rw [hcoc]
        exact add_mem hg (mul_mem ((le_sup_left : K₀ ≤ _) (hθ g)) hh)
      inv_mem' := fun {g} hg => by
        show c g⁻¹ ∈ K₀ ⊔ K i
        have h1 := hcoc g⁻¹ g
        rw [inv_mul_cancel, hc1] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm]
        exact neg_mem (mul_mem ((le_sup_left : K₀ ≤ _) (hθ _)) hg) }
  have hcl : ∀ i, IsClosed (H i : Set Γ) := fun i => by
    haveI := hK i
    haveI : FiniteDimensional ℚ_[l] (K₀ ⊔ K i).toSubalgebra.toSubmodule :=
      (inferInstance : FiniteDimensional ℚ_[l] (K₀ ⊔ K i : IntermediateField ℚ_[l] (PadicAlgCl l)))
    exact (Submodule.closed_of_finiteDimensional (K₀ ⊔ K i).toSubalgebra.toSubmodule).preimage hc
  have hun : ⋃ i, (H i : Set Γ) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨i, hi⟩ := hcov {c g} (Set.finite_singleton _)
    exact Set.mem_iUnion.2 ⟨i, (le_sup_right : K i ≤ K₀ ⊔ K i) (hi rfl)⟩
  obtain ⟨i, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hun
  have hop : IsOpen (H i : Set Γ) := Subgroup.isOpen_of_mem_nhds _ (mem_interior_iff_mem_nhds.1 hx)
  haveI : Finite (Γ ⧸ H i) := Subgroup.quotient_finite_of_isOpen _ hop
  haveI := fd_adjoin_range l (fun q : Γ ⧸ H i => c q.out)
  haveI := hK i
  refine ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun q : Γ ⧸ H i => c q.out) ⊔ (K₀ ⊔ K i), inferInstance,
    le_sup_left.trans le_sup_right, fun g => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H i) g
  have hg : g = (g : Γ ⧸ H i).out * (h : Γ)⁻¹ := by
    rw [hh, mul_inv_cancel_right]
  rw [hg, hcoc]
  refine add_mem ?_ (mul_mem ?_ ?_)
  · exact (le_sup_left : IntermediateField.adjoin ℚ_[l] (Set.range fun q : Γ ⧸ H i => c q.out) ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨(g : Γ ⧸ H i), rfl⟩)
  · exact (le_sup_left.trans le_sup_right : K₀ ≤ _) (hθ _)
  · exact (le_sup_right : K₀ ⊔ K i ≤ _) ((H i).inv_mem h.2)

theorem UpperTheory.V.X.soBar :
    ∀ CK : ℝ, LemmaK CK → GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (ψ : G k Ω →* (PadicAlgCl l)ˣ), IsOpen (ψ.ker : Set (G k Ω)) →
    ∀ e : ℕ, 1 ≤ e → ∀ θ : G k Ω → PadicAlgCl l, (∀ g, θ g * (ψ g : PadicAlgCl l) * algebraMap ℤ_[l] (PadicAlgCl l) (cycZ k Ω l g : ℤ_[l]) ^ e = 1) →
    ∀ c : G k Ω → PadicAlgCl l, Continuous c → (∀ g h, c (g * h) = c g + θ g * c h) →
    (∀ A : ValuationSubring Ω, ∃ m, ∀ g ∈ Ine (F := k) A, c g = θ g * m - m) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ m, ∀ g ∈ Dec (F := k) A, c g = θ g * m - m) → ∃ m, ∀ g, c g = θ g * m - m := by
  intro CK hK hPT hLF hLT k Ω _ _ _ _ _ l _ ψ hψ e he θ hθ c hc hcoc h1 h2
  obtain ⟨K₀, hK₀, hψK⟩ := char_finext l (G k Ω) ψ hψ
  have hθK : ∀ g, θ g ∈ K₀ := fun g => by
    have h := hθ g
    rw [mul_assoc] at h
    rw [eq_inv_of_mul_eq_one_left h]
    refine inv_mem (mul_mem (hψK g) (pow_mem ?_ _))
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact K₀.algebraMap_mem _
  have hθ1 : θ 1 = 1 := by simpa using hθ 1
  obtain ⟨E, hE, hle, hcE⟩ := coc_finext l (G k Ω) K₀ θ c hθK hθ1 hc hcoc
  obtain ⟨m, -, hm⟩ := UpperTheory.V.X.soVec CK hK hPT hLF hLT k Ω l E ψ hψ (fun g => hle (hψK g)) e he θ hθ c hc hcE hcoc h1 h2
  exact ⟨m, hm⟩
