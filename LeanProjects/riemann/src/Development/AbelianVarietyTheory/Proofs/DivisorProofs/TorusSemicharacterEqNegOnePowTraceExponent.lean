import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfTrace
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem sig_eq_star (x : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := by
  have τ0 : D.what₂.Tau := D.eTau.symm 1
  apply (tauE D τ0).injective
  rw [GlobalTheory.FockCompare.tauE_star]
  exact D.sp.cm.cmUnram.2.1 (tauE D τ0) x

theorem cT_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A = Aᴴ := by
  refine Matrix.ext fun i j => ?_
  simp only [Formalism.UG.cT, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
  show (D.sp.cm.sig : D.host.E →+* D.host.E) (A j i) = star (A j i)
  exact sig_eq_star _

theorem hRat_eq (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T x y = Matrix.trace (S.gram⁻¹ * yᴴ * T.gram * x) := by
  simp only [GlobalTheory.LatVac.hRat, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext c; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem hRat_frames (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E)
    (hB : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1)
    (hB' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B'.1 * T.gram * B'.1 = 1)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)
      (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) = Matrix.trace (Mᴴ * M) := by
  rw [cT_eq] at hB hB'
  rw [hRat_eq]
  set Bi := (B⁻¹ : GL (Fin S.rank) D.host.E).1 with hBi_def
  have hBi : Bi * B.1 = 1 := by rw [hBi_def, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hSi : S.gram⁻¹ = B.1 * B.1ᴴ := by
    have h1 : B.1 * (B.1ᴴ * S.gram) = 1 := mul_eq_one_comm.1 hB
    have h2 : (B.1 * B.1ᴴ) * S.gram = 1 := by rw [Matrix.mul_assoc]; exact h1
    exact Matrix.inv_eq_left_inv h2
  have hBB : B.1ᴴ * Biᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hBi, Matrix.conjTranspose_one]
  calc Matrix.trace (S.gram⁻¹ * (B'.1 * M * Bi)ᴴ * T.gram * (B'.1 * M * Bi))
      = Matrix.trace (B.1 * ((B.1ᴴ * Biᴴ) * (Mᴴ * ((B'.1ᴴ * T.gram * B'.1) * (M * Bi))))) := by
        rw [hSi]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Matrix.trace (B.1 * (Mᴴ * (M * Bi))) := by rw [hBB, hB', Matrix.one_mul, Matrix.one_mul]
    _ = Matrix.trace ((Mᴴ * M * Bi) * B.1) := by
        rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Mᴴ * M) := by rw [Matrix.mul_assoc, hBi, Matrix.mul_one]

theorem embT_sqrt (τ : D.what₂.Tau) :
    embT D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) :=
  Formalism.L2.Theta.tauE_sqrtMinusD D τ

theorem embT_ne_conj (τ τ' : D.what₂.Tau) : embT D τ ≠ (starRingEnd ℂ).comp (embT D τ') := by
  intro h
  have h1 := congrArg Complex.im (DFunLike.congr_fun h D.host.sqrtMinusD)
  rw [RingHom.comp_apply, embT_sqrt, embT_sqrt] at h1
  have := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D
  simp at h1
  linarith

theorem trace_split (z : D.host.E) :
    ((Algebra.trace ℚ D.host.E z : ℚ) : ℂ) = ∑ τ : D.what₂.Tau, (embT D τ z + starRingEnd ℂ (embT D τ z)) := by
  have h := trace_eq_sum_embeddings ℂ (K := ℚ) (x := z)
  let e : D.what₂.Tau ⊕ D.what₂.Tau → (D.host.E →ₐ[ℚ] ℂ) := fun s =>
    RingHom.equivRatAlgHom _ _ (Sum.elim (embT D) (fun τ => (starRingEnd ℂ).comp (embT D τ)) s)
  have he : Function.Bijective e := by
    refine (RingHom.equivRatAlgHom _ _).bijective.comp ⟨?_, fun σ => ?_⟩
    · rintro (a | a) (b | b) hab
      · rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_inj D hab]
      · exact absurd hab (embT_ne_conj a b)
      · exact absurd hab.symm (embT_ne_conj b a)
      · have : embT D a = embT D b := RingHom.ext fun x =>
          (starRingEnd ℂ).injective (DFunLike.congr_fun hab x)
        rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_inj D this]
    · obtain ⟨τ, h | h⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.emb_cases D σ
      · exact ⟨Sum.inl τ, h.symm⟩
      · exact ⟨Sum.inr τ, h.symm⟩
  rw [← Fintype.sum_bijective e he (fun s => e s z) (fun σ => σ z) fun _ => rfl, Fintype.sum_sum_type] at h
  rw [show ((Algebra.trace ℚ D.host.E z : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ D.host.E z) from rfl, h,
    ← Finset.sum_add_distrib]
  rfl

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem embT_star (τ : D.what₂.Tau) (x : D.host.E) : embT D τ (star x) = starRingEnd ℂ (embT D τ x) :=
  GlobalTheory.FockCompare.tauE_star τ x

theorem absNorm_ne : ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) ≠ 0 := by
  have : Ideal.absNorm D.host.ccK ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  exact_mod_cast this

theorem embT_c_add_conj (τ : D.what₂.Tau) :
    embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2) +
      starRingEnd ℂ (embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2)) =
      -1 / ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) := by
  have hN := absNorm_ne (D := D)
  have hs : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D).ne'
  have e : embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2) =
      -1 / (((Ideal.absNorm D.host.ccK : ℕ) : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ))) *
        ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) ^ 2 := by
    unfold Formalism.BasicNotions.Host.xi0
    simp only [map_mul, map_div₀, map_neg, map_one, map_natCast, map_pow, map_add, map_ofNat, embT_sqrt]
  rw [e]
  simp only [map_mul, map_div₀, map_neg, map_one, map_pow, map_add, map_natCast, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  field_simp
  ring_nf

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem embT_trace (τ : D.what₂.Tau) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    embT D τ (Matrix.trace (Mᴴ * M)) =
      ((∑ i, ∑ j, Complex.normSq (embT D τ (M i j)) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul,
    embT_star, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  rw [Finset.sum_comm]

theorem k_eq {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (k : ℤ)
    (hk : (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
      Matrix.trace (Mᴴ * M))) :
    (k : ℝ) = -(∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) /
      (Ideal.absNorm D.host.ccK : ℝ) := by
  have h : ((k : ℚ) : ℂ) = ((Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
      Matrix.trace (Mᴴ * M)) : ℚ) : ℂ) := by rw [hk]
  rw [trace_split] at h
  have h2 : ∀ τ : D.what₂.Tau,
      embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * Matrix.trace (Mᴴ * M)) +
        starRingEnd ℂ (embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * Matrix.trace (Mᴴ * M))) =
      -1 / ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) *
        ((∑ i, ∑ j, Complex.normSq (embT D τ (M i j)) : ℝ) : ℂ) := by
    intro τ
    rw [show embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * Matrix.trace (Mᴴ * M)) =
        embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2) * embT D τ (Matrix.trace (Mᴴ * M)) from
        map_mul _ _ _, embT_trace, map_mul (starRingEnd ℂ), Complex.conj_ofReal, ← add_mul, embT_c_add_conj]
  rw [Finset.sum_congr rfl fun τ _ => h2 τ, ← Finset.mul_sum] at h
  have hN := absNorm_ne (D := D)
  have h3 : ((k : ℝ) : ℂ) = (((-(∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) /
      (Ideal.absNorm D.host.ccK : ℝ)) : ℝ) : ℂ) := by
    push_cast
    rw [show ((k : ℂ)) = ((k : ℚ) : ℂ) by push_cast; rfl, h]
    field_simp
    simp only [Complex.ofReal_sum]
  exact_mod_cast h3

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem qH_eq {m n : ℕ} (δ : ℂ) (hδ : δ ≠ 0) (M : Matrix (Fin m) (Fin n) D.host.E) :
    Real.sqrt D.host.d / 2 *
      (Hf D (tor0 D D.host.ccK δ) (δ • embV D (tor0 D D.host.ccK δ) M)
        (δ • embV D (tor0 D D.host.ccK δ) M)).re =
      (∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) / (Ideal.absNorm D.host.ccK : ℝ) := by
  have hA := GlobalTheory.MomDict.area_lamOf D D.host.ccK δ D.host.ccK_ne_bot
  have hH : Hf D (tor0 D D.host.ccK δ) (δ • embV D (tor0 D D.host.ccK δ) M)
        (δ • embV D (tor0 D D.host.ccK δ) M) =
      (((Complex.normSq δ * ∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) /
        area (lamOf D D.host.ccK δ) : ℝ) : ℂ) := by
    unfold Hf
    rw [Complex.ofReal_div]
    congr 1
    simp only [embV, tor0, Pi.smul_apply, smul_eq_mul, Complex.mul_conj, Complex.normSq_mul,
      Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  rw [hH, Complex.ofReal_re, hA]
  have hN : (0 : ℝ) < (Ideal.absNorm D.host.ccK : ℝ) := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  have hs := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D
  have hδ2 : 0 < Complex.normSq δ := Complex.normSq_pos.mpr hδ
  field_simp

theorem al_mul_neg_one_pow : ∀ {D : D7} (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B'.1 * T.gram * B'.1 = 1 → ∀ (δ : ℂ), δ ≠ 0 → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (k : ℤ), (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)) → Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M) * (-1 : ℂ) ^ k = 1 := by
  intro D S T B B' hB hB' δ hδ M k hk
  rw [hRat_frames S T B B' hB hB' M] at hk
  have hk' := k_eq M k hk
  have hq := qH_eq δ hδ M
  have hr : Real.sqrt D.host.d / 2 *
      (Hf D (tor0 D D.host.ccK δ) (δ • embV D (tor0 D D.host.ccK δ) M)
        (δ • embV D (tor0 D D.host.ccK δ) M)).re = ((-k : ℤ) : ℝ) := by
    rw [hq, Int.cast_neg, hk', neg_div, neg_neg]
  unfold al
  rw [hr, round_intCast, _root_.zpow_neg]
  exact inv_mul_cancel₀ (zpow_ne_zero _ (by norm_num))

end GlobalTheory.SemicharTrace
