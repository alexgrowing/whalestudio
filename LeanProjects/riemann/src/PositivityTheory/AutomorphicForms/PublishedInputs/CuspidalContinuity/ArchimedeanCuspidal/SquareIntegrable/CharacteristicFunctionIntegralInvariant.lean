import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.Imports

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel NNReal

namespace Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

variable (F) in

abbrev phi0 : (Fin 2 → F) → ℂ := Set.indicator {x : Fin 2 → F | ∀ i, x i ∈ 𝒪[F]} 1

omit [MeasurableSpace F] [BorelSpace F] in
theorem characteristic_function_integral_apply (v : Fin 2 → F) :
    phi0 F v = (𝒪[F] : Set F).indicator 1 (v 0) * (𝒪[F] : Set F).indicator 1 (v 1) := by
  by_cases h0 : v 0 ∈ 𝒪[F] <;> by_cases h1 : v 1 ∈ 𝒪[F] <;>
    simp [phi0, Set.indicator_apply, Fin.forall_fin_two, h0, h1]

omit [MeasurableSpace F] [BorelSpace F] in
theorem characteristic_function_integral_invariant {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) (v : Fin 2 → F) :
    phi0 F (v ᵥ* (k : Matrix (Fin 2) (Fin 2) F)) = phi0 F v := by
  have hs : {x : Fin 2 → F | ∀ i, x i ∈ 𝒪[F]} = (GodementSectionLocal.box F 0 : Set (Fin 2 → F)) := by
    ext x
    simp [GodementSectionLocal.mem_box, mem_valBall_zero_iff]
  simp only [phi0]
  rw [hs]
  by_cases h : v ∈ GodementSectionLocal.box F 0
  · rw [Set.indicator_of_mem h,
      Set.indicator_of_mem ((GodementSectionLocal.vecMul_mem_box_iff hk 0 v).2 h)]
    rfl
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (mt (GodementSectionLocal.vecMul_mem_box_iff hk 0 v).1 h)]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem unip_entries {u : GL (Fin 2) F} (hu : u ∈ Iwasawa.unipotent F 2) :
    (u : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧ (u : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 ∧
      (u : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
  ⟨hu.2 0, hu.2 1, hu.1 (show id (0 : Fin 2) < id 1 by decide)⟩

omit [MeasurableSpace F] [BorelSpace F] in
theorem vec_eq {u k : GL (Fin 2) F} (hu : u ∈ Iwasawa.unipotent F 2)
    (hk : k ∈ GLnLocal.integralGL F 2) (l : Fin 2 → ℤ) (h x : F) :
    phi0 F (![h, h * x] ᵥ* ((u * Iwasawa.torusPow F 2 l * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
      (𝒪[F] : Set F).indicator 1 (h * (GLnLocal.uniformizer F : F) ^ (l 0)) *
        (𝒪[F] : Set F).indicator 1 ((h * (GLnLocal.uniformizer F : F) ^ (l 1)) *
          ((u : Matrix (Fin 2) (Fin 2) F) 0 1 + x)) := by
  rw [Units.val_mul, Units.val_mul, ← vecMul_vecMul, characteristic_function_integral_invariant hk, ← vecMul_vecMul,
    Iwasawa.coe_torusPow, characteristic_function_integral_apply]
  obtain ⟨h00, h11, h10⟩ := unip_entries hu
  simp only [vecMul_diagonal]
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h00, h11, h10]
  left
  congr 1
  ring

end Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2
