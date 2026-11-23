import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoordNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigFrame

theorem tri_of_coord_lowerTriangular : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (V : (gen s.T.Z).Opens) (hV : IsAffineOpen V) (φ : κ.c.F →+* Γ(gen s.T.Z, V)) (g : EigFrame s.T.Z φ (hV.fromSpec ≫ genι s.T.Z)) (K : Type) [Field K] (c : Γ(gen s.T.Z, V) →+* K) (h h' : EigFrame s.T.Z (c.comp φ) ((spMap c ≫ hV.fromSpec) ≫ genι s.T.Z)) (M M' : GlobalTheory.FlagBundle.Mat S.Dw.mult K), g.Coord c h M → g.Coord c h' M' → (∀ τ, IsUnit (M τ).det) → (∀ τ, IsUnit (M' τ).det) → (∀ τ, ∃ L : Matrix (Fin (S.Dw.mult τ)) (Fin (S.Dw.mult τ)) K, M τ = L * M' τ ∧ ∀ i l, i < l → L i l = 0) → ∃ d, h'.Tri (RingHom.id K) h d := by
  intro D A N j S κ s V hV φ g K _ c h h' M M' hM hM' hdet hdet' hL
  choose L hLM hLt using hL
  have hx : ((spMap c ≫ hV.fromSpec) ≫ genι s.T.Z) = spMap c ≫ (hV.fromSpec ≫ genι s.T.Z) := Category.assoc _ _ _
  obtain ⟨gK, hgK⟩ := g.exists_isMap c rfl hx
  have eM : ∀ τ, gK.co h τ = (M τ)ᵀ := fun τ => co_eq fun i => by
    rw [funext (hgK τ)]; exact hM.2.2 τ i
  have eM' : ∀ τ, gK.co h' τ = (M' τ)ᵀ := fun τ => co_eq fun i => by
    rw [funext (hgK τ)]; exact hM'.2.2 τ i
  have eX : ∀ τ, h'.co h τ = (L τ)ᵀ := fun τ => by
    have e1 : (M' τ)ᵀ * h'.co h τ = (M' τ)ᵀ * (L τ)ᵀ := by
      rw [← eM', co_mul, eM, hLM τ, transpose_mul, eM']
    have hu : IsUnit ((M' τ)ᵀ).det := by rw [det_transpose]; exact hdet' τ
    calc h'.co h τ = ((M' τ)ᵀ)⁻¹ * ((M' τ)ᵀ * h'.co h τ) := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = (L τ)ᵀ := by rw [e1, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
  have hdiag : ∀ τ i, IsUnit (L τ i i) := fun τ i => by
    have h1 : IsUnit (L τ).det := by
      have := hdet τ
      rw [hLM τ, det_mul] at this
      exact isUnit_of_mul_isUnit_left this
    rw [det_of_lowerTriangular (L τ) (fun a b hab => hLt τ a b (OrderDual.toDual_lt_toDual.1 hab))] at h1
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun a => L τ a a) (Finset.mem_univ i)) h1
  have h1 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have h2 : spMap (RingHom.id K) = 𝟙 _ := Spec.map_id _
  refine ⟨fun τ i => (hdiag τ i).unit, by rw [h2, Category.id_comp], rfl, fun τ i => ⟨fun a => L τ i a, by simp,
    fun k hk => hLt τ i k hk, ?_⟩⟩
  simp only [h1, Category.id_comp]
  have := h'.co_spec h τ i
  simpa only [eX, transpose_apply] using this

end GlobalTheory.ShFam.EigFrame
