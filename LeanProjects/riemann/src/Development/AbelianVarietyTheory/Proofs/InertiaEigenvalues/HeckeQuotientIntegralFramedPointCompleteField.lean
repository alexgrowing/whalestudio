import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCpStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCDVRFractionFieldReadingInCpFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientFrameChangeOfTriangularFrameChangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitHeckePrimeOffLevelOfHeckeIndexPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePointIntegralUpToUnitsAnyAlgClosedFieldStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HeckeStableAt

theorem heckeStable : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type)
    (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL]
    (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw)
    (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw)
    (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]),
    (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) →
    ∀ (b : Bool) (j : Fin D.R.m), HeckeStable YS iC b j := by
  intro hI D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j k P hk z C
  obtain ⟨hHP, hne⟩ := GlobalTheory.T.isSplitHeckePrimeOffLevel_of_heckeIndexPlace D T0 fw.laws i k P hk
  have hP' := GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 hHP
  obtain ⟨z', hz'⟩ := GlobalTheory.HeckePointLaw.heckePointLaws.2.1 D.host.E T0.Q.H (T0.Q.Dw ((j : ℕ) + 1)) T0.Q.l
    (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c P.asIdeal (charAt P) k hP' (PAt (embC YS iC b)) z.1 C
  obtain ⟨T, io, kk, h, y, u, hy, hu, w, hw, hb⟩ := z.2
  obtain ⟨C₀, w', hw', hb'⟩ := GlobalTheory.T.heckeQuotient_frame_change_of_triangular_frame_change _ _ _ _ _ _ P.asIdeal (charAt P) k hHP _ u w z.1 hb C z' hz'
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_ramification_overPlace_of_cdvrReadingInCp (D.ntw.l i) T0.Q.c.F (embC YS iC b) T io kk h
  have hpla : ((charAt P : ℕ) : 𝓞 T0.Q.c.F) ∉ (placeAt (embC YS iC b)).asIdeal := by
    intro hm
    have hl := natCast_mem_placeAt (embC YS iC b)
    have hcop : Nat.Coprime (charAt P) (D.ntw.l i) :=
      (Nat.coprime_primes (charAt_prime P) (Fact.out : (D.ntw.l i).Prime)).2 hne
    obtain ⟨a, c, hac⟩ : IsCoprime ((charAt P : ℕ) : 𝓞 T0.Q.c.F) ((D.ntw.l i : ℕ) : 𝓞 T0.Q.c.F) :=
      Nat.Coprime.cast hcop
    exact (placeAt (embC YS iC b)).isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hac ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hl)))
  letI := io.toAlgebra
  have hint := GlobalTheory.T.heckePoint_integral_upToUnits_anyAlgClosedField hI D.host.E T0.Q.H (T0.Q.Dw ((j : ℕ) + 1)) T0.Q.l (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c
    (placeAt (embC YS iC b)) P.asIdeal (charAt P) k hHP hpla T io e he y hy (PAt (embC YS iC b)) h.alg w hw C₀ w' hw'
  obtain ⟨T', i', hi', j', hj', y', hy', -, w2, u2, hw2, hb2⟩ := hint
  letI := (i'.comp io).toAlgebra
  let jj : T'.Fr →+* ℂ_[D.ntw.l i] := (toCp (embC YS iC b)).comp j'.toRingHom
  have hjj : jj.comp i' = kk := RingHom.ext fun a => congrArg (toCp (embC YS iC b)) (DFunLike.congr_fun hj' a)
  have hR := GlobalTheory.T.isCDVRFractionFieldReadingInCp_finite_extension (D.ntw.l i) T0.Q.c.F (embC YS iC b) T io kk h T' i' hi' jj hjj
  have hRa : hR.alg = j' := AlgHom.ext fun _ => rfl
  let u2' : Ix (T0.Q.Dw ((j : ℕ) + 1)) → (PAt (embC YS iC b))ˣ :=
    fun a => Units.map (j'.toRingHom.comp (algebraMap T'.V T'.Fr)).toMonoidHom (u2 a)
  have hbor := (GlobalTheory.Frames.frBor_calculus _ _ _ _ _ _ _ w2 w' z').2.2.1 u2' u hb2 hb'
  have hunit : ∀ a, ‖toCp (embC YS iC b) (u2' a)‖ = 1 := fun a => by
    have h1 : ‖jj (algebraMap T'.V T'.Fr (u2 a : T'.V))‖ ≤ 1 := (hR.int _).2 ⟨_, rfl⟩
    have h2 : ‖jj (algebraMap T'.V T'.Fr ((u2 a)⁻¹ : T'.Vˣ))‖ ≤ 1 := (hR.int _).2 ⟨_, rfl⟩
    have h3 : jj (algebraMap T'.V T'.Fr (u2 a : T'.V)) * jj (algebraMap T'.V T'.Fr ((u2 a)⁻¹ : T'.Vˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have h4 := congrArg norm h3
    rw [norm_mul, norm_one] at h4
    have h5 : ‖jj (algebraMap T'.V T'.Fr (u2 a : T'.V))‖ = 1 := by
      refine le_antisymm h1 (by_contra fun hlt => ?_)
      push_neg at hlt
      have : ‖jj (algebraMap T'.V T'.Fr (u2 a : T'.V))‖ * ‖jj (algebraMap T'.V T'.Fr ((u2 a)⁻¹ : T'.Vˣ))‖ < 1 :=
        (mul_le_of_le_one_right (norm_nonneg _) h2).trans_lt hlt
      exact this.ne h4
    exact h5
  have hnorm : ∀ a, ‖toCp (embC YS iC b) ((u * u2') a)‖ = 1 := fun a => by
    rw [Pi.mul_apply, Units.val_mul, map_mul, norm_mul, hu a, hunit a, one_mul]
  refine ⟨⟨z', T', i'.comp io, jj, hR, y', u * u2', hy', hnorm, w2, hRa ▸ hw2, hbor⟩, hz'⟩

end GlobalTheory.HeckeStableAt
