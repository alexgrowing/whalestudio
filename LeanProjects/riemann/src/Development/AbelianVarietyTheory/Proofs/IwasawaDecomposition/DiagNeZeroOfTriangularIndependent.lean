import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem tri_diag_ne_zero : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (ι : Type) (c c' : Let m → ι → K)
    (d : Let m → K), (∀ τ, LinearIndependent K fun j : Fin (m τ) => c' ⟨τ, j⟩) → Tri c c' d → ∀ z, d z ≠ 0 := by
  classical
  intro T m K _ ι c c' d hli htri z hz
  obtain ⟨τ, i⟩ := z
  set f : Fin (m τ) → ι → K := fun j => c ⟨τ, j⟩ with hf
  let w : Finset (ι → K) := (Finset.Iio i).image f
  have hsub : ∀ j : Fin (m τ), j ≤ i → c' ⟨τ, j⟩ ∈ Submodule.span K (w : Set (ι → K)) := by
    have hspan : ∀ j : Fin (m τ), j ≤ i →
        Submodule.span K (f '' {j' | j' < j}) ≤ Submodule.span K (w : Set (ι → K)) := by
      intro j hj
      refine Submodule.span_mono ?_
      rintro _ ⟨j', hj', rfl⟩
      simp only [w, Finset.coe_image, Finset.coe_Iio]
      exact ⟨j', lt_of_lt_of_le hj' hj, rfl⟩
    intro j hj
    have ht := htri ⟨τ, j⟩
    rcases lt_or_eq_of_le hj with hlt | heq
    · have h1 : c' ⟨τ, j⟩ - d ⟨τ, j⟩ • c ⟨τ, j⟩ ∈ Submodule.span K (w : Set (ι → K)) := hspan j hj ht
      have h2 : c ⟨τ, j⟩ ∈ Submodule.span K (w : Set (ι → K)) := by
        refine Submodule.subset_span ?_
        simp only [w, Finset.coe_image, Finset.coe_Iio]
        exact ⟨j, hlt, rfl⟩
      have := Submodule.add_mem _ h1 (Submodule.smul_mem _ (d ⟨τ, j⟩) h2)
      simpa using this
    · subst heq
      have h1 := hspan j le_rfl ht
      simpa [hz] using h1
  let v : (Finset.Iic i) → ι → K := fun j => c' ⟨τ, j.1⟩
  have hv : LinearIndependent K v := (hli τ).comp (fun j : Finset.Iic i => j.1) Subtype.val_injective
  have hle := linearIndependent_le_span_aux' v hv (w : Set (ι → K)) (by
    rintro _ ⟨j, rfl⟩
    exact hsub j.1 (Finset.mem_Iic.1 j.2))
  have hw : Fintype.card (w : Set (ι → K)) ≤ (i : ℕ) := by
    simp only [Finset.coe_sort_coe, Fintype.card_coe]
    exact (Finset.card_image_le).trans (by simp)
  have hv' : Fintype.card (Finset.Iic i) = (i : ℕ) + 1 := by
    rw [Fintype.card_coe]; simp
  omega

end GlobalTheory.FlagEmb
