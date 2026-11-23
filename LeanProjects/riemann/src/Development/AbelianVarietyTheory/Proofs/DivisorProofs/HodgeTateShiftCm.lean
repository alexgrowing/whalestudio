import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapToModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfFlatWtSome
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbAtSurj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceBelowExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAlgebraMapLtOneIffValuationLtOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivPointValuationPropertyStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.HTShiftPf

attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

theorem prime_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 K) ∈ la.asIdeal := by
  have : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
  have : la.asIdeal.IsMaximal := la.isMaximal
  let _ : Field (𝓞 K ⧸ la.asIdeal) := Ideal.Quotient.field _
  refine ⟨ringChar (𝓞 K ⧸ la.asIdeal), CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem prime_unique {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (h1 : (p : 𝓞 K) ∈ la.asIdeal) (h2 : (q : 𝓞 K) ∈ la.asIdeal) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ : IsCoprime (p : 𝓞 K) (q : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem norm_eq_v (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) : ‖x‖ = ((Valued.v x : ℝ≥0) : ℝ) := by
  rw [PadicComplex.norm_eq_norm, Valuation.norm_def, PadicComplex.RankOne.hom_eq_embedding,
    Valuation.embedding_restrict]

open Classical in

theorem htShift : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.FlatCM.PlaceShiftSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H →
    ∀ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), HTShift Xo c := by
  intro hP2 hPS E _ _ _ H hH Dw l Xo c τ la
  obtain ⟨ℓ, hℓ, hℓla⟩ := prime_mem la
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨w, hw⟩ := GlobalTheory.placeBelow_exists c τ.1 la
  obtain ⟨κ₁, κ₂, hκ⟩ := hPS E H hH ℓ w
  refine ⟨(vLa la (ℓ : c.F) : ℝ) * (-((Dw.mult τ.1 : ℝ) * κ₁ + (Dw.mult (conjEmb τ.1) : ℝ) * κ₂) /
    Real.log ((Valued.v (ℓ : ℂ_[ℓ]) : ℝ≥0) : ℝ)), ?_⟩
  intro T io e y₀ ho hAlg wv hwv f hf
  obtain ⟨p, hp, _, k, y, hy, rfl⟩ := hwv
  obtain rfl : p = ℓ := prime_unique hp.out hℓ (hy.mem ho) hℓla
  letI := H.starRing
  letI := io.toAlgebra
  have hy' : IsHTFrame p (Valued.v : Valuation ℂ_[p] ℝ≥0) 𝓞_ℂ_[p] y₀ k y := hy
  have hm := hy'.val_vw_map ho
  obtain ⟨-, kO, P, ψ, z, hPO, hz, g, a, x, hfc, hg, ha, hx, hb⟩ := hy'
  have hdet : ∀ σ, IsUnit (g σ).det := fun σ =>
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1
      (LinearIndependent.of_comp (Fintype.linearCombination ℂ_[p] fun j => P.bLie (x σ j)) (hb σ).1))
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hA := GlobalTheory.FlatFrameLaw.evR_flat_frChg τ hf g a z y hfc hg hdet ha0
  have hB : evR Xo c f z = k (evI y₀ f) := GlobalTheory.FlagTan.evR_frMap hf.1 hz

  have hs : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  have hplace : ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ ‖embAt c ℂ_[p] τ.1 (a : E)‖ < 1 := fun a => by
    rw [hw, embAt, RingHom.comp_apply]
    exact (GlobalTheory.CompHt.norm_algebraMap_lt_one_iff_valuation_lt_one c.F la p hℓla T io e ho k.toRingHom (fun b => k.commutes b) hm _).symm
  have hsig : ∀ φ : E →+* ℂ_[p], Module.finrank ℂ_[p] (P.eigW (embO P.integers φ)) =
      if φ (H.rt : E) = embAt c ℂ_[p] τ.1 (H.rt : E) then Dw.mult τ.1 else Dw.mult (conjEmb τ.1) := fun φ => by
    obtain ⟨σ, rfl⟩ := GlobalTheory.EmbOnto.embAt_surj c ℂ_[p] φ
    have e1 := GlobalTheory.T.pdiv_point_valuation_property hP2 E H Dw l Xo c p ℂ_[p] Valued.v 𝓞_ℂ_[p] T io y₀ hAlg k kO P ψ z hPO hz σ
    refine e1.trans ?_
    have hinj : σ (H.rt : E) = τ.1 (H.rt : E) ↔ embAt c ℂ_[p] σ (H.rt : E) = embAt c ℂ_[p] τ.1 (H.rt : E) := by
      constructor
      · intro h
        simp only [embAt, RingHom.comp_apply]
        congr 1
        exact Subtype.ext h
      · intro h
        simp only [embAt, RingHom.comp_apply] at h
        exact congrArg Subtype.val ((algebraMap c.F ℂ_[p]).injective h)
    rw [Datum.mult, Datum.mult, Datum.mult, if_pos τ.2, if_neg (conj_not_mem τ), ← hinj, τ.2]
  have hs1 := GlobalTheory.CompHt.RecSpan.span_bLie_eq_wRec E H Dw l Xo c p ℂ_[p] Valued.v 𝓞_ℂ_[p] T io y₀ k kO P ψ z hPO hz
    τ.1 (x τ.1) (hx τ.1)
  have hs2 := GlobalTheory.CompHt.RecSpan.span_bLie_eq_wRec E H Dw l Xo c p ℂ_[p] Valued.v 𝓞_ℂ_[p] T io y₀ k kO P ψ z hPO hz
    (conjEmb τ.1) (x (conjEmb τ.1)) (hx (conjEmb τ.1))
  rw [embInt_conj hs] at hs2
  have hb1 := hb τ.1
  rw [htLat_psi P τ] at hb1
  have hb2 := hb (conjEmb τ.1)
  rw [htLat_conj P τ, embInt_conj hs] at hb2
  have hlog := hκ (embAt c ℂ_[p] τ.1) hplace P (Dw.mult τ.1) (Dw.mult (conjEmb τ.1)) hsig (x τ.1) (x (conjEmb τ.1))
    (g τ.1) (g (conjEmb τ.1)) hs1 hs2 hb1 hb2
  rw [norm_eq_v, norm_eq_v] at hlog

  have hd1 : (g τ.1).det ≠ 0 := (hdet τ.1).ne_zero
  have hd2 : (g (conjEmb τ.1)).det ≠ 0 := (hdet (conjEmb τ.1)).ne_zero
  show val_vw la p Valued.v (evR Xo c f y) = _
  rw [hA, hB, val_vw_mul, val_vw_mul, hm, val_vw_of_ne la p _ (inv_ne_zero hd1), val_vw_of_ne la p _ hd2,
    ← EReal.coe_add, add_comm]
  congr 2
  rw [map_inv₀, NNReal.coe_inv, Real.log_inv, ← hlog]
  ring

end GlobalTheory.HTShiftPf

end
