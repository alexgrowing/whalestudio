import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  rw [Units.continuous_iff]
  refine ⟨h, ?_⟩
  have : (fun x => ((f x)⁻¹ : Rˣ).val) = (fun s => (f s : R)) ∘ (fun x => x⁻¹) := by
    funext x
    simp [map_inv]
  rw [this]
  exact h.comp continuous_inv

private theorem cont_of_ker {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : Γ →* H) (U : Set Γ) (hU : IsOpen U) (h1 : 1 ∈ U)
    (h : ∀ s ∈ U, f s = 1) : Continuous f := by
  apply continuous_of_continuousAt_one
  have hev : (fun _ : Γ => (1 : H)) =ᶠ[nhds 1] f :=
    Filter.eventually_of_mem (hU.mem_nhds h1) fun s hs => (h s hs).symm
  exact (continuousAt_const (y := (1 : H))).congr hev

private theorem cont_kills {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (M : ℕ) (hM : 1 ≤ M) (φ : G ℚ Ω →* (Qbar l)ˣ) (hφ : KillsMu M φ) : Continuous φ := by
  classical
  have hS : {ζ : Ω | ζ ^ M = 1} = ((Polynomial.nthRoots M (1 : Ω)).toFinset : Set Ω) := by
    ext ζ
    simp [Polynomial.mem_nthRoots (by omega : 0 < M)]
  haveI : Finite ↥{ζ : Ω | ζ ^ M = 1} := by
    rw [hS]
    infer_instance
  let E := IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ M = 1}
  haveI : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine cont_of_ker φ (E.fixingSubgroup : Set (G ℚ Ω)) E.fixingSubgroup_isOpen E.fixingSubgroup.one_mem ?_
  intro s hs
  apply hφ
  intro ζ hζ
  exact (IntermediateField.mem_fixingSubgroup_iff E s).mp hs ζ (IntermediateField.subset_adjoin ℚ _ hζ)

theorem UpperTheory.V.X.Kato.twCont :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (W : G ℚ Ω →* GL (Fin n) (Qbar l)), Continuous W → ∀ (M : ℕ), 1 ≤ M → ∀ φ : G ℚ Ω →* (Qbar l)ˣ, KillsMu M φ → ∀ j : ℤ, Continuous (tw W (cycBar ℚ Ω l ^ j * φ)) := by
  intro l _ Ω _ _ _ n W hW M hM φ hφ j
  have hc1 : Continuous fun s : G ℚ Ω => ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    (Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l)
  have hc2 : Continuous fun x : ℤ_[l] => (x : ℚ_[l]) := continuous_subtype_val
  have hcyc : Continuous (cycBar ℚ Ω l) := by
    apply cont_units
    exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (hc2.comp hc1)
  have hχ : Continuous (cycBar ℚ Ω l ^ j * φ) := by
    have e : ⇑(cycBar ℚ Ω l ^ j * φ) = fun s => (cycBar ℚ Ω l s) ^ j * φ s := by
      funext s
      simp
    rw [e]
    exact (hcyc.zpow j).mul (cont_kills M hM φ hφ)
  apply cont_units
  have e2 : (fun s => (((tw W (cycBar ℚ Ω l ^ j * φ)) s : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))) =
      fun s => ((cycBar ℚ Ω l ^ j * φ) s : Qbar l) • (W s : Matrix (Fin n) (Fin n) (Qbar l)) :=
    funext (tw_val W _)
  rw [e2]
  exact (Units.continuous_val.comp hχ).smul (Units.continuous_val.comp hW)
