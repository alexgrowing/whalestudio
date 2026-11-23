import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.NormMod

noncomputable section

open MeasureTheory ValuativeRel IsDedekindDomain NumberField

namespace PI.ProdFormulaE

section Local

variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (ι : F →+* K)

theorem iota_mem_integer (hv : ∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y)
    (a : 𝓞 F) : ι (a : F) ∈ 𝒪[K] := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation K), ← Valuation.Compatible.vle_iff_le,
    ← map_one ι, hv, map_one]
  exact p.valuation_le_one a

theorem modF_iota_int (hI : IndexFormula) (hC : CardStep) (hd : DenseRange ι)
    (hv : ∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) (a : 𝓞 F) (ha : a ≠ 0) :
    modF K (ι (a : F)) = HeightOneSpectrum.adicAbv F p (a : F) := by
  set t : 𝒪[K] := ⟨ι (a : F), iota_mem_integer p ι hv a⟩ with ht
  have ht0 : t ≠ 0 := by
    intro h
    have : ι (a : F) = 0 := congrArg Subtype.val h
    rw [map_eq_zero_iff ι ι.injective] at this
    exact ha (by exact_mod_cast this)
  have h1 := hI K t ht0
  rw [hC F p K ι hd hv a ha t rfl] at h1
  have h3 := HeightOneSpectrum.embedding_mul_absNorm (K := F) p ha
  rw [FinitePlace.norm_embedding] at h3
  have hN : ((Ideal.absNorm (p.maxPowDividing (Ideal.span {a})) : ℕ) : ℝ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
  exact mul_right_cancel₀ hN (h1.trans h3.symm)

theorem modF_iota (hI : IndexFormula) (hC : CardStep) (hd : DenseRange ι)
    (hv : ∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) (z : F) :
    modF K (ι z) = HeightOneSpectrum.adicAbv F p z := by
  by_cases hz : z = 0
  · simp [hz, modF_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hz
  rw [map_div₀, modF_div, map_div₀]
  have e1 := modF_iota_int p ι hI hC hd hv a ha0
  have e2 := modF_iota_int p ι hI hC hd hv b hb0
  simp only [RingOfIntegers.coe_eq_algebraMap] at e1 e2 ⊢
  rw [e1, e2]

end Local

section Global

variable {F : Type} [Field F] [NumberField F]

end Global

section LocAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem modF_locAt (hI : IndexFormula) (hC : CardStep) (L : Formalism.MainNotions.S.Loc.LocAt F E sig p)
    [IsNonarchimedeanLocalField L.Fp] (z : F) :
    modF L.Fp (L.ιF z) = HeightOneSpectrum.adicAbv F p z :=
  modF_iota p L.ιF hI hC L.dense L.val z

end LocAt

theorem modF_iota_finitePlace {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ι : F →+* K) (hI : IndexFormula) (hC : CardStep) (hd : DenseRange ι)
    (hv : ∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) (z : F) :
    modF K (ι z) = FinitePlace.mk p z := by
  rw [modF_iota p ι hI hC hd hv z, FinitePlace.mk_apply, FinitePlace.norm_embedding]

end PI.ProdFormulaE
