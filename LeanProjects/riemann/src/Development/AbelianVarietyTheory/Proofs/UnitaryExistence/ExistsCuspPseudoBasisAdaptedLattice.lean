import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SpanRatSmulMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemOfMemSpanFraction
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem herm_comb_eq_zero_of_iso {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (e : Fin ρ → Fin r → E)
    (h : ∀ a b, herm G (e a) (e b) = 0) (u v : Fin ρ → E) :
    herm G (∑ i, u i • e i) (∑ j, v j • e j) = 0 := by
  have key : herm G (∑ i, u i • e i) (∑ j, v j • e j)
      = ∑ i, ∑ j, u i * cc (v j) * herm G (e i) (e j) := by
    have h1 : ∀ (y : Fin r → E), herm G (∑ i, u i • e i) y = ∑ i, u i * herm G (e i) y := by
      intro y
      simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin ρ)))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have h2 : ∀ (x : Fin r → E), herm G x (∑ j, v j • e j) = ∑ j, cc (v j) * herm G x (e j) := by
      intro x
      simp only [herm, cc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin ρ)))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    simp only [h1, h2, Finset.mul_sum, mul_assoc]
  rw [key]
  simp [h]

theorem exists_cusp_pseudoBasis :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu₀ : FJ.CuspFD X ρ), ∃ (cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), IsUnit P.det ∧ (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) ∧ (∀ b, cc' b ≠ 0) ∧ (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) := by
  intro E _ _ _ r ρ X cu₀
  classical
  let T : (Fin ρ → E) →ₗ[E] (Fin r → E) := Fintype.linearCombination E cu₀.e
  have hT : ∀ v, T v = ∑ i, v i • cu₀.e i := fun v => Fintype.linearCombination_apply E cu₀.e v
  obtain ⟨Ψ, hΨ⟩ := FJ.exists_crdMap cu₀
  have hinj : Function.Injective T := by
    refine Function.LeftInverse.injective (g := Ψ) fun v => ?_
    rw [hT, hΨ]
  let L : Submodule (𝓞 E) (Fin ρ → E) := X.Λ.comap (T.restrictScalars (𝓞 E))
  have hL : ∀ v, v ∈ L ↔ T v ∈ X.Λ := fun v => Iff.rfl
  have hfg : L.FG := by
    refine Submodule.FG.of_le (X.Λ_fg.map (Ψ.restrictScalars (𝓞 E))) fun v hv => ?_
    refine ⟨T v, (hL v).1 hv, ?_⟩
    show Ψ (T v) = v
    rw [hT, hΨ]
  have hsp : Submodule.span E (L : Set (Fin ρ → E)) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨c, hc, hcw⟩ := FJ.exists_smul_mem X (T w)
    have hcE : algebraMap (𝓞 E) E c ≠ 0 := fun h =>
      hc (IsFractionRing.injective (𝓞 E) E (by rw [map_zero]; exact h))
    have hm : algebraMap (𝓞 E) E c • w ∈ L := by
      rw [hL, map_smul, algebraMap_smul]
      exact hcw
    have := Submodule.smul_mem (Submodule.span E (L : Set (Fin ρ → E))) (algebraMap (𝓞 E) E c)⁻¹
      (Submodule.subset_span hm)
    rwa [smul_smul, inv_mul_cancel₀ hcE, one_smul] at this
  obtain ⟨s, e, c, hc, hmem, -⟩ := exists_pseudoBasis_adapted E ρ L ⊤ hfg hsp
  have hsum : ∀ a : Fin ρ → E, ∑ b, a b • T (e b) = T (∑ b, a b • e b) := by
    intro a
    simp only [map_sum, map_smul]
  refine ⟨⟨fun b => T (e b), e.linearIndependent.map' T (LinearMap.ker_eq_bot.2 hinj), ?_⟩,
    (e.toMatrix (Pi.basisFun E (Fin ρ)))ᵀ, c, ?_, ?_, hc, ?_⟩
  · intro a b
    simp only [hT]
    exact herm_comb_eq_zero_of_iso _ _ cu₀.iso _ _
  · rw [Matrix.det_transpose]
    exact e.isUnit_det _
  · intro a
    show cu₀.e a = ∑ b, e.repr (Pi.basisFun E (Fin ρ) a) b • T (e b)
    rw [hsum, e.sum_repr, hT]
    simp [Pi.single_apply]
  · intro a
    show ∑ b, a b • T (e b) ∈ X.Λ ↔ _
    rw [hsum, ← hL, hmem]
    simp only [e.repr_sum_self]

end GlobalTheory
