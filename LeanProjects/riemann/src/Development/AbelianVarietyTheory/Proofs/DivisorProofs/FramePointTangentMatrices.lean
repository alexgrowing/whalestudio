import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FrameChangePair

theorem isCombAt_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {a : Fin m → S}
    {w₁ w₂ : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h₁ : IsCombAt x v a w₁) (h₂ : IsCombAt x v a w₂) :
    w₁ = w₂ := by
  obtain ⟨u₁, hu₁, hw₁⟩ := h₁
  obtain ⟨u₂, hu₂, hw₂⟩ := h₂
  have hu : u₁ = u₂ := funext fun i => Over.OverMorphism.ext ((hu₁ i).trans (hu₂ i).symm)
  rw [← hw₁, ← hw₂, hu]

theorem psi_ne_conjEmb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (τ : Psi H) :
    τ.1 ≠ conjEmb τ.1 := by
  intro h
  have hτ : τ.1 (H.rt : E) = H.rt0 := τ.2
  have hc : (starRingEnd ℂ) H.rt0 = H.rt0 := by
    have := congrArg (fun σ : E →+* ℂ => σ (H.rt : E)) h
    simp only [conjEmb, RingHom.comp_apply, hτ] at this
    exact this.symm
  have h1 : (H.rt0.re : ℂ) ^ 2 = -(H.d : ℂ) := by rw [Complex.conj_eq_iff_re.1 hc]; exact H.sqrt_neg_disc_sq
  have h2 : H.rt0.re ^ 2 = -(H.d : ℝ) := by exact_mod_cast h1
  have h3 : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
  nlinarith [sq_nonneg H.rt0.re]

theorem exists_frPt_comb_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (L : Type) [CommRing L] [Algebra c.F L] (z₀ : FrPt Xo c L)
    (τ : Psi H) (g₁ : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) L)
    (g₂ : Matrix (Fin (Dw.mult (conjEmb τ.1))) (Fin (Dw.mult (conjEmb τ.1))) L)
    (v₁ : Fin (Dw.mult τ.1) → (Sp (DualNumber L) ⟶ Xo.univ.t.G.left))
    (v₂ : Fin (Dw.mult (conjEmb τ.1)) → (Sp (DualNumber L) ⟶ Xo.univ.t.G.left)),
    IsUnit g₁.det → IsUnit g₂.det → (∀ i, IsCombAt z₀.x (z₀.u τ.1) (g₁ i) (v₁ i)) →
    (∀ i, IsCombAt z₀.x (z₀.u (conjEmb τ.1)) (g₂ i) (v₂ i)) →
    ∃ z : FrPt Xo c L, z.x = z₀.x ∧ (∀ i, z.u τ.1 i = v₁ i) ∧ ∀ i, z.u (conjEmb τ.1) i = v₂ i := by
  classical
  intro E _ _ _ H Dw l Xo c L _ _ z₀ τ g₁ g₂ v₁ v₂ hg₁ hg₂ hv₁ hv₂
  have hne : τ.1 ≠ conjEmb τ.1 := psi_ne_conjEmb τ
  let G : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) L :=
    Function.update (Function.update (fun σ => (1 : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) L)) τ.1 g₁)
      (conjEmb τ.1) g₂
  have hG₂ : G (conjEmb τ.1) = g₂ := Function.update_self _ _ _
  have hG₁ : G τ.1 = g₁ := by
    dsimp only [G]
    rw [Function.update_of_ne hne, Function.update_self]
  have hdet : ∀ σ, IsUnit (G σ).det := by
    intro σ
    by_cases h1 : σ = conjEmb τ.1
    · subst h1; rw [hG₂]; exact hg₂
    · by_cases h2 : σ = τ.1
      · subst h2; rw [hG₁]; exact hg₁
      · dsimp only [G]
        rw [Function.update_of_ne h1, Function.update_of_ne h2, Matrix.det_one]
        exact isUnit_one
  obtain ⟨z, hz, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c L z₀ G 1 hdet
  obtain ⟨hx, hc, -⟩ := hz
  refine ⟨z, hx, fun i => ?_, fun i => ?_⟩
  · have h := hc τ.1 i
    rw [hG₁] at h
    exact isCombAt_unique h (hv₁ i)
  · have h := hc (conjEmb τ.1) i
    rw [hG₂] at h
    exact isCombAt_unique h (hv₂ i)

end GlobalTheory.FrameChangePair
