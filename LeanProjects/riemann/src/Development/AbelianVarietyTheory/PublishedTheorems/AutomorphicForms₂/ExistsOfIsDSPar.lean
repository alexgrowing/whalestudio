import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Development.AbelianVarietyTheory.Proofs.HeightProofs.BlockOrderedSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFdegSmulOfIsDS
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters GlobalTheory.RealPar Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.Published.CoverSeries

variable {p q n : ℕ}

def pull {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) : URep T where
  H := H
  π := { toFun := fun x => σ (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q))
         map_one' := by simpa using hσ.1.1
         map_mul' := fun x y => by
           rw [ContinuousLinearMap.mul_def, ← hσ.1.2 _ (h.cov_mem T x) _ (h.cov_mem T y)]
           simp [Matrix.submatrix_mul_equiv] }
  isom x v := hσ.2.1 _ (h.cov_mem T x) v
  cont v := (hσ.2.2 v).comp_continuous
    ((Units.continuous_val.comp (continuous_fst.comp T.emb.continuous)).matrix_reindex e e) (h.cov_mem T)

theorem exists_of_isDSPar (T : GrpData p q)
    (hM : ∀ U : URep T, Formalism.MainNotions.SchurIrreducible.IrrU U → ∃ (M : GKMod p q) (io : M.V →ₗ[ℂ] U.H), Formalism.MainNotions.SchurIrreducible.IsHCMod U M io)
    (P : SignedPar n) {e : Ix p q ≃ Fin n} (h : BlockOrd e P.sgn) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDSPar P σ) :
    ∃ R : DSRep T, HasParam R (blockPar P e) := by
  haveI : CompleteSpace H := hσ.1
  have hU := hσ.2.2.1
  have hirr : Formalism.MainNotions.SchurIrreducible.IrrU (pull h T hU) := ⟨hσ.2.1, fun S hS hst => hσ.2.2.2.1 S hS fun g hg v hv => by
    obtain ⟨x, rfl⟩ := h.cov_surj T hg
    exact hst x v hv⟩
  obtain ⟨M, io, m1, m2, m3⟩ := hM _ hirr
  haveI := SqInt.isHaarMeasure_map_covU h T
  have hμ := Measure.isMulLeftInvariant_eq_smul (T.haar.map (SqInt.covU h T)) (Formalism.REAL.muG P.sgn)
  obtain ⟨d, hd, hI⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS n P.sgn P.lam H σ hσ _
    (Measure.haarScalarFactor_pos_of_isHaarMeasure (T.haar.map (SqInt.covU h T)) (Formalism.REAL.muG P.sgn))
  refine ⟨⟨pull h T hU, hirr.1, hirr.2, d, hd, fun x y => ?_, M, io, m1, m2, m3⟩, ?_⟩
  · change H at x y
    obtain ⟨i1, i2⟩ := hI x y x y
    rw [← ENNReal.smul_def, ← hμ] at i1 i2
    have hf : (fun g => coefOn (ε := P.sgn) σ x y g * star (coefOn (ε := P.sgn) σ x y g)) =
        fun g => ((‖coefOn (ε := P.sgn) σ x y g‖ ^ 2 : ℝ) : ℂ) := by
      funext g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hf] at i1 i2
    have hm := (SqInt.continuous_covU h T).measurable.aemeasurable (μ := T.haar)
    rw [integral_map hm i1.aestronglyMeasurable] at i2
    have i3 := (integrable_map_measure i1.aestronglyMeasurable hm).1 i1
    refine ⟨i3.re.congr (Filter.Eventually.of_forall fun g => Complex.ofReal_re _), ?_⟩
    rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at i2
    have i4 : ((∫ g, ‖coefOn (ε := P.sgn) σ x y (SqInt.covU h T g)‖ ^ 2 ∂T.haar : ℝ) : ℂ) =
        ((‖x‖ ^ 2 * ‖y‖ ^ 2 / d : ℝ) : ℂ) := by
      push_cast
      exact i2
    exact_mod_cast i4
  · exact (hasParam_iff_isDSPar _ P h (σ := σ) fun _ => rfl).2 hσ

theorem of_upq (hE : DiscreteSeriesUpqExists)
    (hM : ∀ p q : ℕ, 1 ≤ p + q → ∀ (T : GrpData p q) (U : URep T), Formalism.MainNotions.SchurIrreducible.IrrU U →
      ∃ (M : GKMod p q) (io : M.V →ₗ[ℂ] U.H), Formalism.MainNotions.SchurIrreducible.IsHCMod U M io) :
    DiscreteSeriesCoverExists := by
  intro p q T lam hl
  rcases Nat.eq_zero_or_pos (p + q) with h0 | h0
  · obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.1 h0
    exact ⟨Cover.trivZero T, GlobalTheory.SignedParTest.hasParam_zero _ _⟩
  have key : ∀ lam : Ix p q → ℚ, IsParam lam → (∀ a, ∃ m : ℤ, lam a - (((p + q : ℕ) : ℚ) - 1) / 2 = m) →
      ∃ R : DSRep T, HasParam R lam := by
    intro lam hl hi
    obtain ⟨P, e, -, h, rfl⟩ := exists_blockPar hl hi
    obtain ⟨H, _, _, σ, hσ⟩ := hE _ P.sgn P.lam P.hc
    exact exists_of_isDSPar T (hM p q h0 T) P h hσ
  obtain ⟨P, e, -, h, rfl | rfl⟩ := isParam_cases hl
  · exact key _ hl fun a => ⟨(P.hc.2 (e a)).choose, by simp [blockPar, ratEntry]⟩
  · obtain ⟨R, hR⟩ := key (fun a => blockPar P e a + 1 / 2 + 1 / 2)
      ⟨fun x y e => hl.1 (add_left_injective _ e), fun x y e => by simpa using hl.2.1 x y e,
        fun x => by
          obtain ⟨k, hk⟩ := hl.2.2.1 x
          exact ⟨k + 1, by push_cast; linarith⟩,
        fun x y => by simpa using hl.2.2.2 x y⟩
      fun a => ⟨(P.hc.2 (e a)).choose + 1, by simp only [blockPar, ratEntry]; push_cast; ring⟩
    exact ⟨Cover.twist R, (Cover.hasParam_twist R _).2 hR⟩

end GlobalTheory.Published.CoverSeries

end
