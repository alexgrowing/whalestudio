import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound

set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

namespace GlobalTheory

open scoped TensorProduct in

theorem natCard_quot_smul_top_of_projective {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  classical
  have hA : Finite (Ideal (R ⧸ I)) :=
    Finite.of_injective (fun J : Ideal (R ⧸ I) => (J : Set (R ⧸ I))) SetLike.coe_injective
  have hMS : Finite (MaximalSpectrum (R ⧸ I)) :=
    Finite.of_injective (fun m : MaximalSpectrum (R ⧸ I) => m.asIdeal) (fun a b h => MaximalSpectrum.ext h)
  have rk : ∀ P : MaximalSpectrum (R ⧸ I), Module.finrank ((R ⧸ I) ⧸ P.1)
      (((R ⧸ I) ⧸ P.1) ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] N)) = Module.finrank R N := by
    intro P
    have hP := P.2
    let _ : Field ((R ⧸ I) ⧸ P.1) := Ideal.Quotient.field P.1
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.1) ((R ⧸ I) ⧸ P.1) N).finrank_eq]
    have h1 := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := (R ⧸ I) ⧸ P.1)
      (M := ((R ⧸ I) ⧸ P.1) ⊗[R] N)) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_baseChange, Pi.natCast_apply, Nat.cast_id] at h1
    rw [← h1]
    generalize PrimeSpectrum.comap (algebraMap R ((R ⧸ I) ⧸ P.1)) ⟨⊥, Ideal.isPrime_bot⟩ = q
    obtain ⟨p, hp⟩ := q
    rw [← Ideal.finrank_fiber_eq_rankAtStalk, Ideal.finrank_fiber_eq_finrank]
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N)
    (Module.finrank R N) rk
  calc Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card ((R ⧸ I) ⊗[R] N) :=
        Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv.symm
    _ = Nat.card (Fin (Module.finrank R N) → R ⧸ I) := Nat.card_congr b.equivFun.toEquiv
    _ = Nat.card (R ⧸ I) ^ Module.finrank R N := by simp [Nat.card_fun]

theorem absNorm_level_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    Ideal.absNorm l.Mb = l.M ^ FD.fdeg E := by
  have h1 : Ideal.absNorm (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) = Ideal.absNorm l.Mb := by
    simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv l.Mb _ H.bar rfl).toEquiv.symm
  have h2 := congrArg Ideal.absNorm l.prod
  rw [map_mul, h1, Ideal.absNorm_span_singleton] at h2
  have h3 : (Algebra.norm ℤ ((l.M : ℕ) : 𝓞 E)).natAbs = l.M ^ Module.finrank ℚ E := by
    have : ((l.M : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (l.M : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have hev : Module.finrank ℚ E = 2 * FD.fdeg E := by
    have h := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h
    unfold FD.fdeg
    omega
  rw [h3, hev, pow_mul', ← sq] at h2
  exact Nat.pow_left_injective two_ne_zero h2

theorem card_levQ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H),
    Finite (LevQ Dw l) ∧ Nat.card (LevQ Dw l) = l.M ^ (FD.fdeg E * (Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw l
  unfold LevQ
  have := Dw.fin
  have := Dw.proj
  have hN := absNorm_level_half l
  have : Finite (𝓞 E ⧸ l.Mb) := by
    rw [← Ideal.absNorm_ne_zero_iff, hN]
    exact pow_ne_zero _ (by have := l.three_le; omega)
  have hc := natCard_quot_smul_top_of_projective (N := Dw.La) l.Mb
  have hq : Nat.card (𝓞 E ⧸ l.Mb) = l.M ^ FD.fdeg E := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Dw.rank, hq, ← pow_mul] at hc
  refine ⟨?_, hc⟩
  apply Nat.finite_of_card_ne_zero
  rw [hc]
  exact pow_ne_zero _ (by have := l.three_le; omega)

end GlobalTheory
