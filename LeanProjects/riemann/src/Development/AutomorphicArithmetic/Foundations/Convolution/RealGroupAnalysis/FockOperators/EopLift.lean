import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FockOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingEquivPlaceCorrespondencePlaceUnder

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem coord_half {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (σ τ : E →+* ℂ) :
    (1 / 2 : ℂ) * (coord σ (atEmb τ 1) - Complex.I * coord σ (atEmb τ Complex.I)) = if σ = τ then 1 else 0 := by
  by_cases h : InfinitePlace.mk σ = InfinitePlace.mk τ
  · rcases InfinitePlace.mk_eq_iff.1 h with e | e
    · subst e
      rw [if_pos rfl, coord_atEmb, coord_atEmb, Complex.I_mul_I]
      norm_num
    · have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h' =>
        InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
          (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h'))
      obtain rfl : σ = ComplexEmbedding.conjugate τ := by
        rw [← e]; exact (star_star σ).symm
      rw [if_neg hne, GlobalTheory.IsoPull.coord_conj, GlobalTheory.IsoPull.coord_conj, coord_atEmb, coord_atEmb]
      simp
  · rw [GlobalTheory.IsoPull.coord_atEmb_of_ne h, GlobalTheory.IsoPull.coord_atEmb_of_ne h, if_neg (fun e => h (by rw [e]))]
    simp

private theorem coord_single {E : Type} [Field E] (σ : E →+* ℂ) (i j k l : Fin 2) (c : Cinf E) :
    coord σ ((toL (Matrix.single i j c) : Lie E 2) k l) = if k = i ∧ l = j then coord σ c else 0 := by
  change coord σ (Matrix.single i j c k l) = _
  rw [Matrix.single_apply]
  by_cases h : k = i ∧ l = j
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg (fun e => h ⟨e.1.symm, e.2.symm⟩), map_zero]

private theorem half_comb {E N : Type} [Field E] [NumberField E] [IsTotallyComplex E] [AddCommGroup N] [Module ℂ N]
    (R : (E →+* ℂ) → Fin 2 → Fin 2 → N) (τ : E →+* ℂ) (i j : Fin 2) (x y : N)
    (hx : x = ∑ σ : E →+* ℂ, ∑ k, ∑ l, coord σ ((toL (Matrix.single i j (atEmb τ 1)) : Lie E 2) k l) • R σ k l)
    (hy : y = ∑ σ : E →+* ℂ, ∑ k, ∑ l, coord σ ((toL (Matrix.single i j (atEmb τ Complex.I)) : Lie E 2) k l) • R σ k l) :
    (1 / 2 : ℂ) • (x - Complex.I • y) = R τ i j := by
  have e : ∀ c : Cinf E, ∀ σ : E →+* ℂ, ∑ k, ∑ l, coord σ ((toL (Matrix.single i j c) : Lie E 2) k l) • R σ k l = coord σ c • R σ i j := by
    intro c σ
    simp only [coord_single, ite_smul, zero_smul, ite_and]
    simp
  simp only [e] at hx hy
  have hz : ∀ σ : E →+* ℂ, (1 / 2 : ℂ) • (coord σ (atEmb τ 1) • R σ i j - Complex.I • coord σ (atEmb τ Complex.I) • R σ i j) =
      if σ = τ then R σ i j else 0 := by
    intro σ
    rw [smul_smul, ← sub_smul, smul_smul, coord_half]
    split_ifs <;> simp
  rw [hx, hy, Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
  simp only [hz]
  simp

theorem UpperTheory.ConvolutionTheory.R2.Fo.eopLift :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (O : Ops F) (Λ : TR.Sm F 2 →ₗ[ℂ] S4 F →ₗ[ℂ] Sm E 2), (∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, (Λ f φ).1 = lift W M f.1 φ) → LieLift O W M π →
    ∀ (τ : E →+* ℂ) i j, ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, Eop τ i j (Λ f φ) = Λ f (O.dE D τ i j φ) + if i = j then Λ (TR.Eop (pl F τ) 1 1 f) φ else 0 := by
  intro F E _ _ _ _ _ _ _ D W M π O Λ hΛ hL τ i j f hf φ hφ
  have hE : ∀ σ : E →+* ℂ, TR.Eop (pl F σ) 1 1 f ∈ π.V := fun σ => π.stable (.lie _) f hf
  have key : ∀ Y : Lie E 2, lie E 2 Y (Λ f φ) = ∑ σ : E →+* ℂ, ∑ k, ∑ l, coord σ (Y k l) •
      (Λ f (O.dE D σ k l φ) + if k = l then Λ (TR.Eop (pl F σ) 1 1 f) φ else 0) := by
    intro Y
    have h1 := (fockOps F E D O φ hφ).2.2.2.2.2.2 Y
    have h2 : lie E 2 Y (Λ f φ) = Λ f (O.dL D Y φ) +
        ∑ σ : E →+* ℂ, coord σ (Y 0 0 + Y 1 1) • Λ (TR.Eop (pl F σ) 1 1 f) φ := by
      refine Subtype.ext (funext fun h => ?_)
      rw [hL f hf φ hφ (Λ f φ) (hΛ f hf φ hφ) Y h]
      simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, hΛ _ (hE _) φ hφ, hΛ f hf _ h1]
    have h3 : Λ f (O.dL D Y φ) = ∑ σ : E →+* ℂ, ∑ k, ∑ l, coord σ (Y k l) • Λ f (O.dE D σ k l φ) := by
      simp only [Ops.dL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    rw [h2, h3, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Fin.sum_univ_two, smul_add, map_add, add_smul]
    simp
    abel
  have hEop : Eop τ i j = (1 / 2 : ℂ) • (lie E 2 (toL (Matrix.single i j (atEmb τ 1))) -
      Complex.I • lie E 2 (toL (Matrix.single i j (atEmb τ Complex.I)))) := rfl
  rw [hEop]
  exact half_comb (fun σ k l => Λ f (O.dE D σ k l φ) + if k = l then Λ (TR.Eop (pl F σ) 1 1 f) φ else 0) τ i j _ _
    (key _) (key _)
