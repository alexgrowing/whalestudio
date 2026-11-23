import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly

theorem rename_perm_invForm {ι : Type} [Fintype ι] (N j : ℕ) (σ : ι ≃ ι) (al be : ι → ℝ) :
    rename (fun x : ι × Fin N => (σ x.1, x.2)) (invForm (N := N) j al be)
      = invForm j (fun τ => al (σ.symm τ)) (fun τ => be (σ.symm τ)) := by
  unfold invForm
  rw [map_sum]
  conv_rhs => rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [pLow, pHigh, map_sum]

theorem CoefLe.rename_perm {ι : Type} {N : ℕ} (σ : ι ≃ ι) {P : Pol ι N} {e : ℝ} (h : CoefLe P e) :
    CoefLe (rename (fun x : ι × Fin N => (σ x.1, x.2)) P) e := by
  intro m
  let E : ι × Fin N ≃ ι × Fin N := σ.prodCongr (Equiv.refl _)
  have hE : (fun x : ι × Fin N => (σ x.1, x.2)) = E := by
    funext x; rfl
  rw [hE]
  have hm : m = Finsupp.mapDomain E (Finsupp.mapDomain E.symm m) := by
    rw [← Finsupp.mapDomain_comp]; simp
  rw [hm, coeff_rename_mapDomain _ E.injective]
  exact h _

theorem sum_inv_smul_const {ι G : Type} [Group G] [Fintype G] [MulAction G ι]
    [MulAction.IsPretransitive G ι] (f : ι → ℝ) :
    ∃ a : ℝ, ∀ τ : ι, ∑ g : G, f (g⁻¹ • τ) = a := by
  rcases isEmpty_or_nonempty ι with h | ⟨⟨τ₀⟩⟩
  · exact ⟨0, fun τ => h.elim τ⟩
  refine ⟨∑ g : G, f (g⁻¹ • τ₀), fun τ => ?_⟩
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq G τ₀ τ
  rw [← Equiv.sum_comp (Equiv.mulLeft h)]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp [smul_smul]

end GlobalTheory.FlagPoly
