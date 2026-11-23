import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistFactor

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.ConvolutionTheory.C

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {n : ℕ} {q : Pl F} {w₀ : PlacesOver E q}

def nsS (T : Ty σ n q w₀) : Finset (Pl F) := T.S.filter fun v => ¬ GM.Split E v

def offN (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (T : Ty σ n q w₀) : Submodule ℂ (LL μ) :=
  ⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ (nsS T : Set (Pl F))), eigL μ w (T.J w) (T.χ w)

def lvN (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀) (v : Pl F) : Subgroup (Gw n (T.mk' v).1) :=
  (L.UE v).map (GM.cmp (T.mk' v))

end

def kerChr {G : Type} [Group G] [TopologicalSpace G] (J : Subgroup G) (χ : G → ℂ) (h : IsChr J χ) : Subgroup G where
  carrier := {x | x ∈ J ∧ χ x = 1}
  one_mem' := by
    have h1 := h.2.2 1 J.one_mem 1 J.one_mem
    have h2 : χ 1 ≠ 0 := fun h0 => by
      have := h.2.1 1 J.one_mem
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    rw [mul_one] at h1
    exact ⟨J.one_mem, mul_left_cancel₀ h2 (by rw [← h1, mul_one])⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨J.mul_mem ha hb, by rw [h.2.2 a ha b hb, ha', hb', one_mul]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 := h.2.2 1 J.one_mem 1 J.one_mem
    have h2 : χ 1 ≠ 0 := fun h0 => by
      have := h.2.1 1 J.one_mem
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    rw [mul_one] at h1
    have h3 : χ 1 = 1 := mul_left_cancel₀ h2 (by rw [← h1, mul_one])
    refine ⟨J.inv_mem ha, ?_⟩
    have h4 := h.2.2 a ha a⁻¹ (J.inv_mem ha)
    rwa [mul_inv_cancel, h3, ha', one_mul, eq_comm] at h4

end UpperTheory.ConvolutionTheory.C
