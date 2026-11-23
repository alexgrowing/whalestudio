import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem open_bar {Γ O : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommRing O] [IsLocalRing O]
    (γ : Γ →* Oˣ) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) (h : ∀ g ∈ H, residue O (γ g : O) = 1) :
    IsOpen {g : Γ | residue O (γ g : O) = 1} := by
  have h2 : H ≤ ((Units.map (residue O).toMonoidHom).comp γ).ker := fun g hg => Units.ext (h g hg)
  have h3 := Subgroup.isOpen_mono h2 hH
  convert h3 using 1
  ext g
  exact ⟨fun h => Units.ext h, fun h => congrArg Units.val h⟩

theorem UpperTheory.V.Ws.Lk.barFacts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}, D.Good → (∀ i, IsOpen {g : G ℚ Ω | Raw.bar (D.ps i) g = 1}) ∧ IsOpen {g : G ℚ Ω | Raw.bar D.om g = 1} ∧ ∀ A, Raw.Away D.S A → ∀ g ∈ Ine (F := ℚ) A, (∀ i, D.ps i g = 1) ∧ D.rbar g = 1 := by
  intro Ω _ _ _ l _ c D h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hr, ho, hu⟩ := facts D h
  refine ⟨fun i => open_bar _ _ hr fun g hg => ?_, open_bar _ _ ho fun g hg => ?_, fun A hA g hg => ?_⟩
  · have h1 : D.rbar g = 1 := hg
    simpa [Raw.rbar, Raw.r0, diagRep, mapRep] using congrFun (congrFun h1 i) i
  · rw [MonoidHom.mem_ker.1 hg, Units.val_one, map_one]
  · have h2 : ∀ i, D.ps i g = 1 := fun i => hu i A hA hg
    refine ⟨h2, ?_⟩
    ext i j
    by_cases e : i = j
    · subst e
      simp [Raw.rbar, Raw.r0, diagRep, mapRep, h2]
    · simp [Raw.rbar, Raw.r0, diagRep, mapRep, e]
