import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LandherrStOfHasseNormSt

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped Matrix ComplexConjugate

namespace GlobalTheory.CuspExist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_congr_diagonal (H : GlobalTheory.Published.Landherr) (X : Data E r) (k : Fin r) :
    ∃ (d : E) (P : Matrix (Fin r) (Fin r) E), P.det ≠ 0 ∧
      Matrix.diagonal (fun a : Fin r => (if (a : ℕ) < X.p0 then (1 : E) else -1) *
        (if a = k then d else 1)) = Pᵀ * X.Gm * P.map cc := by
  classical
  set s : Fin r → E := fun a => if (a : ℕ) < X.p0 then (1 : E) else -1 with hs
  have hs0 : ∀ a, s a ≠ 0 := fun a => by
    simp only [hs]; split_ifs <;> simp
  have hscc : ∀ a, cc (s a) = s a := fun a => by
    simp only [hs]; split_ifs <;> simp [cc]
  have hsτ : ∀ (τ : E →+* ℂ) a, τ (s a) = ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := fun τ a => by
    simp only [hs, sgn]; split_ifs <;> simp
  have hS0 : (Matrix.diagonal s).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hs0 a
  have hSh : ∀ a b, cc (Matrix.diagonal s a b) = Matrix.diagonal s b a := by
    intro a b
    by_cases h : a = b
    · subst h; simpa using hscc a
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]; simp [cc]
  set d : E := X.Gm.det / (Matrix.diagonal s).det with hd
  have hd0 : d ≠ 0 := div_ne_zero X.Gm_det hS0
  have hdcc : cc d = d := by
    have h1 := GlobalTheory.Published.cc_det_of_herm X.Gm_herm
    have h2 := GlobalTheory.Published.cc_det_of_herm hSh
    unfold cc at h1 h2 ⊢
    rw [hd, map_div₀, h1, h2]
  have hdet : (Matrix.diagonal fun a : Fin r => s a * (if a = k then d else 1)).det = X.Gm.det := by
    rw [Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ _),
      ← Matrix.det_diagonal, hd]
    field_simp
  refine ⟨d, GlobalTheory.Published.Landherr.of_signature H X.Gm_herm ?_ X.Gm_det (hdet ▸ X.Gm_det)
    (X.Ψ : Set (E →+* ℂ)) (fun τ => ?_) (fun τ hτ => ⟨X.p0, X.signature ⟨τ, hτ⟩, ?_⟩) ⟨1, ?_⟩⟩
  · intro a b
    by_cases h : a = b
    · subst h
      have h1 := hscc a
      unfold cc at h1 hdcc ⊢
      rw [Matrix.diagonal_apply_eq, map_mul, h1]
      congr 1
      split_ifs
      · exact hdcc
      · exact map_one _
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]; simp [cc]
  · by_cases h : ComplexEmbedding.conjugate τ ∈ X.Ψ
    · exact Or.inr h
    · exact Or.inl ((X.cmType τ).mpr h)
  · obtain ⟨Q, hQ, hg⟩ := X.signature ⟨τ, hτ⟩
    have hpos : 0 < (τ d).re := by
      refine GlobalTheory.Published.Landherr.re_det_div_pos X.Gm_det τ ⟨Q, hQ, ?_⟩
      rw [← GlobalTheory.Published.gram_eq, hg, Matrix.diagonal_map (map_zero τ)]
      simp only [hsτ]
    have hre : ((τ d).re : ℂ) = τ d := by
      rw [← Complex.conj_eq_iff_re, ← GlobalTheory.Published.embedding_cc, hdcc]
    set t : ℝ := (Real.sqrt (τ d).re)⁻¹ with ht
    have ht0 : t ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hpos).ne'
    have htt : (t : ℂ) * τ d * t = 1 := by
      rw [← hre, mul_right_comm, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ht, ← mul_inv,
        Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
    refine ⟨Matrix.diagonal fun a => if a = k then (t : ℂ) else 1, ?_, ?_⟩
    · rw [Matrix.det_diagonal, Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]
      exact_mod_cast ht0
    · rw [GlobalTheory.Published.gram_eq, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero τ),
        Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      rw [map_mul, hsτ]
      split_ifs
      · rw [Complex.conj_ofReal]
        linear_combination ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * htt
      · simp
  · rw [hdet, div_self X.Gm_det]; simp [cc]

omit [NumberField E] [IsCMField E] in

theorem linearIndependent_single_add {ρ : ℕ} {i j : Fin ρ → Fin r} (hi : Function.Injective i)
    (hij : ∀ a b, i a ≠ j b) :
    LinearIndependent E fun a => (Pi.single (i a) 1 + Pi.single (j a) 1 : Fin r → E) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have := congrFun hg (i a)
  simpa [Finset.sum_apply, Pi.single_apply, hij, hi.eq_iff] using this

theorem herm_diagonal_single_add {ρ : ℕ} {i j : Fin ρ → Fin r} (hi : Function.Injective i)
    (hj : Function.Injective j) (hij : ∀ a b, i a ≠ j b) (g : Fin r → E)
    (hg : ∀ a, g (i a) + g (j a) = 0) (a b : Fin ρ) :
    herm (Matrix.diagonal g) (Pi.single (i a) 1 + Pi.single (j a) 1)
      (Pi.single (i b) 1 + Pi.single (j b) 1) = 0 := by
  classical
  have hji : ∀ a b, j a ≠ i b := fun a b => (hij b a).symm
  rw [GlobalTheory.Published.LandherrSt.herm_eq, add_dotProduct, single_dotProduct, single_dotProduct,
    Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]
  by_cases h : a = b
  · subst h
    simpa [cc, Pi.single_apply, hij, hji] using hg a
  · simp [cc, hij, hji, hi.eq_iff, hj.eq_iff, h]

theorem nonempty_cuspFD : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r), ρ ≤ X.p0 → ρ + X.p0 ≤ r → 2 * ρ < r → Nonempty (FJ.CuspFD X ρ) := by
  intro HN E _ _ _ r ρ X h1 h2 h3
  classical
  have H := GlobalTheory.Published.landherr_of_landherrSt (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt HN)
  obtain ⟨k, hk⟩ : ∃ k : Fin r, (k : ℕ) + ρ < X.p0 ∨ X.p0 + ρ ≤ k := by
    by_cases h : ρ < X.p0
    · exact ⟨⟨0, by omega⟩, Or.inl (by simpa using h)⟩
    · exact ⟨⟨r - 1, by omega⟩, Or.inr (by simp only; omega)⟩
  obtain ⟨d, P, hP, hG⟩ := exists_congr_diagonal H X k
  let i : Fin ρ → Fin r := fun a => ⟨X.p0 - 1 - a, by have := a.2; omega⟩
  let j : Fin ρ → Fin r := fun a => ⟨X.p0 + a, by have := a.2; omega⟩
  have hi : Function.Injective i := fun a b h => by
    have := a.2; have := b.2
    simp only [i, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  have hj : Function.Injective j := fun a b h => by
    simp only [j, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  have hij : ∀ a b, i a ≠ j b := fun a b h => by
    have := a.2
    simp only [i, j, Fin.mk.injEq] at h
    omega
  refine ⟨⟨fun a => P *ᵥ (Pi.single (i a) 1 + Pi.single (j a) 1), ?_, fun a b => ?_⟩⟩
  · refine (linearIndependent_single_add (E := E) hi hij).map' (Matrix.toLin' P) ?_
    rw [LinearMap.ker_eq_bot]
    exact Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr hP))
  · rw [GlobalTheory.Published.LandherrSt.herm_mulVec, ← hG]
    refine herm_diagonal_single_add hi hj hij _ (fun c => ?_) a b
    have := c.2
    have e1 : i c ≠ k := fun h => by
      have := congrArg Fin.val h
      simp only [i] at this
      omega
    have e2 : j c ≠ k := fun h => by
      have := congrArg Fin.val h
      simp only [j] at this
      omega
    have e3 : (i c : ℕ) < X.p0 := by simp only [i]; omega
    have e4 : ¬ (j c : ℕ) < X.p0 := by simp only [j]; omega
    simp only [if_pos e3, if_neg e4, if_neg e1, if_neg e2]
    ring

end GlobalTheory.CuspExist
