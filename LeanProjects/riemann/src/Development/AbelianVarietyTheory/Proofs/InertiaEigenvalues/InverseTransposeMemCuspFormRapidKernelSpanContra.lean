import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContraIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem invT_invT_gl {R : Type} [CommRing R] (g : GL (Fin a) R) : invT a R (invT a R g) = g := by
  apply Units.ext
  change ((invT a R g)⁻¹).valᵀ = g.val
  rw [← map_inv]
  change ((g⁻¹)⁻¹).valᵀᵀ = g.val
  rw [inv_inv, Matrix.transpose_transpose]

theorem map_invT_gl {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (invT a R g) = invT a S (GeneralLinearGroup.map p g) := by
  apply Units.ext
  change p.mapMatrix ((g⁻¹).valᵀ) = ((GeneralLinearGroup.map p g)⁻¹).valᵀ
  rw [← map_inv]
  ext i j
  rfl

theorem invT_infGL (y : GL (Fin a) (Cinf E)) : invT a (Ad E) (infGL E a y) = infGL E a (invT a (Cinf E) y) := by
  apply ga_ext
  · rw [map_invT_gl, pInf_infGL, pInf_infGL]
  · rw [map_invT_gl, pFin_infGL, pFin_infGL, map_one]

theorem norm_toL_transpose (x : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL xᵀ‖ = ‖toL x‖ := by
  have key : ∀ y : Matrix (Fin a) (Fin a) (Cinf E), ‖toL yᵀ‖ ≤ ‖toL y‖ := fun y =>
    pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun i => pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun j =>
      (norm_le_pi_norm (toL y j) i).trans (norm_le_pi_norm (toL y) j)
  refine le_antisymm (key x) ?_
  simpa using key xᵀ

theorem height_invT (y : GL (Fin a) (Cinf E)) : height (invT a (Cinf E) y) = height y := by
  change 1 + ‖toL (y⁻¹).valᵀ‖ + ‖toL ((invT a (Cinf E) y)⁻¹).val‖ = 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖
  rw [← map_inv]
  change 1 + ‖toL (y⁻¹).valᵀ‖ + ‖toL ((y⁻¹)⁻¹).valᵀ‖ = _
  rw [inv_inv, norm_toL_transpose, norm_toL_transpose]
  ring

theorem isRapidInf_invT {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)}
    (hk : IsRapidInf ν k γ) : IsRapidInf ν k (fun x => invT a (Cinf E) (γ x)) := by
  refine ⟨hk.1, ?_, fun N => ?_⟩
  · refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun w => ?_
    set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ :=
      Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
    have e : (fun x => ((invT a (Cinf E) (γ x) : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w) =
        fun x => (((p (γ x))⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) j i := by
      funext x
      rw [← map_inv]; rfl
    rw [e]
    have hγ : ∀ i' j', Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)) i' j' := fun i' j' =>
      (measurable_pi_apply j').comp ((measurable_pi_apply i').comp hk.2.1)
    exact measurable_comp_GL (F := fun g : GL (Fin a) ℂ => ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) j i)
      ((Units.continuous_coe_inv : Continuous fun g : GL (Fin a) ℂ =>
        ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)).matrix_elem j i)
      fun i' j' => (measurable_pi_apply w).comp (hγ i' j')
  · simp only [height_invT]
    exact hk.2.2 N

theorem kerInf_comp_invT {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E))
    (F : GA E a → ℂ) (g : GA E a) :
    kerInf ν k γ F (invT a (Ad E) g) =
      kerInf ν k (fun x => invT a (Cinf E) (γ x)) (fun h => F (invT a (Ad E) h)) g := by
  unfold kerInf
  congr 1
  funext x
  show k x * F (invT a (Ad E) g * infGL E a (γ x)) =
    k x * F (invT a (Ad E) (g * infGL E a (invT a (Cinf E) (γ x))))
  rw [map_mul, invT_infGL, invT_invT_gl]

theorem comp_invT_mem_mspanR (π : CuspSub E a) (F : GA E a → ℂ) (hF : F ∈ mspanR π) :
    (fun g => F (invT a (Ad E) g)) ∈ mspanR π.contra := by
  let T : Submodule ℂ (GA E a → ℂ) :=
    (rspan π.contra).comap (LinearMap.funLeft ℂ ℂ (invT a (Ad E)))
  have memT : ∀ G : GA E a → ℂ, G ∈ T ↔ (fun g => G (invT a (Ad E) g)) ∈ rspan π.contra := fun G =>
    Submodule.mem_comap
  have hle : rspan π ≤ T := by
    refine rspan_le (fun φ hφ => ?_) (fun F hF h => ?_) fun F hF X _ ν _ k γ hk => ?_
    · rw [memT]
      have h1 : UpperTheory.V.TC.dualFn E a φ ∈ π.contra.V := Submodule.mem_map_of_mem hφ
      exact mem_rspan h1
    · rw [memT] at hF ⊢
      have h2 := rt_mem_rspan hF (invT a (Ad E) h)
      have e : (fun g => F (invT a (Ad E) g * h)) = fun g => F (invT a (Ad E) (g * invT a (Ad E) h)) := by
        funext g; rw [map_mul, invT_invT_gl]
      rw [e]; exact h2
    · rw [memT] at hF ⊢
      have h3 := kerInf_mem_rspan hF ν (isRapidInf_invT hk)
      have e : (fun g => kerInf ν k γ F (invT a (Ad E) g)) =
          kerInf ν k (fun x => invT a (Cinf E) (γ x)) (fun h => F (invT a (Ad E) h)) :=
        funext fun g => kerInf_comp_invT ν k γ F g
      rw [e]; exact h3
  rw [← rspan_eq_mspanR] at hF ⊢
  exact (memT F).1 (hle hF)

example (π : CuspSub E a) {φ : Sm E a} (hφ : φ ∈ π.V) :
    (fun g => φ.1 (invT a (Ad E) g)) ∈ mspanR π.contra ∧ mspanR π.contra ≠ ⊥ :=
  ⟨comp_invT_mem_mspanR π φ.1 (rspan_eq_mspanR π ▸ mem_rspan hφ), rspan_eq_mspanR π.contra ▸ rspan_ne_bot _⟩

theorem invT_mem_mspanR_contra : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → (fun g => F (invT a (Ad E) g)) ∈ GlobalTheory.JSW.mspanR π.contra :=
  fun _ _ _ _ _ π F hF => comp_invT_mem_mspanR π F hF

end GlobalTheory.JSW
