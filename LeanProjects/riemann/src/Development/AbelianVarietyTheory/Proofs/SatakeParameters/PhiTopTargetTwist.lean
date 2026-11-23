import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistedStartColumnReading
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlkDetEqDB
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory.TopLaw

section Gen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {n r b : ℕ}

theorem parL_map_of_red (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : GLint E n P)
    (h : redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b) {v : Sp E n} (hv : v ∈ LocE.parL P (qOf P) r n 0) :
    j.1 v ∈ LocE.parL P (qOf P) r n 0 := by
  have hq0 := qOf_ne_zero (P := P)
  have hv' : ∀ l : Fin n, IntAt P (((qOf P : E) ^ (if r ≤ l.1 ∧ l.1 < n then (1 : ℤ) else 0))⁻¹ * v l) :=
    GlobalTheory.LastSteps.mem_sclLat.1 hv
  have hv0 : ∀ l : Fin n, IntAt P (v l) := fun l => by
    have h1 := hv' l
    split_ifs at h1
    · have h2 := (intAt_nat (P := P) (qOf P)).mul h1
      rwa [zpow_one, mul_inv_cancel_left₀ hq0] at h2
    · simpa using h1
  refine GlobalTheory.LastSteps.mem_sclLat.2 fun (l : Fin n) => ?_
  show IntAt P (((qOf P : E) ^ (if r ≤ l.1 ∧ l.1 < n then (1 : ℤ) else 0))⁻¹ * j.1 v l)
  split_ifs with hl
  · have e := apply_eq_sum (j.1 : Sp E n →ₗ[E] Sp E n) v l
    rw [LinearEquiv.coe_coe] at e
    rw [e, Finset.mul_sum, zpow_one]
    refine intAt_sum _ fun i _ => ?_
    by_cases hi : r ≤ i.1
    · have h1 := hv' i
      rw [if_pos ⟨hi, i.2⟩, zpow_one] at h1
      rw [← mul_assoc]
      exact h1.mul (glint_entry j l i)
    · have h0 : redP P (j.1 (Pi.single i 1) l) = 0 :=
        mem_btG.1 h l i (by rw [coarse_of_lt (Nat.not_le.1 hi), coarse_of_le hl.1]; omega)
      have h1 := (hv0 i).mul (intAt_div_of_redP hq (glint_entry j l i) h0)
      convert h1 using 1
      ring
  · rw [zpow_zero, inv_one, one_mul]
    exact mem_stdAt.1 (glint_mem j (mem_stdAt.2 hv0)) l

theorem mem_JQ_of_red (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : GLint E n P)
    (h : redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b) : j.1 ∈ LocE.JQ P (qOf P) r n 0 := by
  refine ⟨j.2, fun v => ⟨fun hv => ?_, parL_map_of_red hq j h⟩⟩
  have h1 := parL_map_of_red hq j⁻¹ (by rw [map_inv]; exact inv_mem h) hv
  have e : (j⁻¹).1 (j.1 v) = v := LinearEquiv.symm_apply_apply j.1 v
  exact e ▸ h1

theorem lamQB_eq_red (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (hn : n = r + b) (j : GLint E n P)
    (h : redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b) :
    LocE.lamQB ξ r n j.1.toLinearMap = (((lamQ ξ n r b ⟨_, h⟩)⁻¹ : Kˣ) : K) := by
  have hA : GlobalTheory.DatumLaw.IntM P n n fun p p' => Loc.atN (j.1.toLinearMap (Loc.eN E n p')) p := fun p p' hp hp' => by
    show IntAt P (Loc.atN _ _)
    rw [GlobalTheory.LastSteps.eN_eq hp', Loc.atN, dif_pos hp]
    exact glint_entry j _ _
  have h1 := blkDet_eq_dB (coarse r [b]) 1 r (n - r) (by omega) (fun i hi => by
    by_cases hr : i < r
    · rw [coarse_of_lt hr]; omega
    · rw [coarse_of_le (Nat.not_lt.1 hr), blkIdx, if_pos (by omega)]; omega) ⟨_, h⟩
    (GlobalTheory.DatumLaw.red P fun p p' => Loc.atN (j.1.toLinearMap (Loc.eN E n p')) p) (fun i l => by
      show redP P (Loc.atN _ _) = _
      rw [GlobalTheory.LastSteps.eN_eq l.2, Loc.atN, dif_pos i.2]
      rfl)
  rw [← GlobalTheory.DatumLaw.redP_dB hA (by omega) (by omega)] at h1
  rw [lamQ_apply, Units.val_inv_eq_inv_val]
  show (GlobalTheory.DatumLaw.ext0 ξ (redP P (GlobalTheory.DatumLaw.dB (fun p p' => Loc.atN (j.1.toLinearMap (Loc.eN E n p')) p) r (n - r))))⁻¹ = _
  rw [← h1, GlobalTheory.DatumLaw.ext0, dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]

end Gen

theorem phiTop_target_twist : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), R.m = m2 + 2 → ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → P ∉ Pr.vGs → ∀ (sharp : Bool) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (hQ : P ∈ Q) (j : GLint X.E (R.N R.m - 1) P) (h : redGL _ P j ∈ (rowTyQ R (mu : Chr X.F X.E X.K) Q ⟨P, hQ⟩).H) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) (R.N R.m - 1)), PhiTop Ch mu sharp m2 P (j.1.toLinearMap ∘ₗ x) * LocE.unitV (resChar (mu : Chr X.F X.E X.K) P)⁻¹ ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = (((rowTyQ R (mu : Chr X.F X.E X.K) Q ⟨P, hQ⟩).lam ⟨_, h⟩ : X.Kˣ) : X.K) * PhiTop Ch mu sharp m2 P x := by
  intro X Pr R Ch S mu m2 P hm hq hP sharp Q hQ j h x
  obtain ⟨a1, a2, a3, -⟩ := GlobalTheory.DatumLaw.ranks R (j := m2 + 1) (by omega)
  unfold PhiTop
  rw [if_neg hP]
  have h1 := GlobalTheory.DatumLaw.phiQ_target (resChar (mu : Chr X.F X.E X.K) P) (k₀ := R.k) (r := R.r) (c' := cOf R (m2 + 1))
    (n' := R.N (m2 + 1)) (c := 0) (n := R.N R.m - 1) (kj := R.r) (by omega) (r_le_X' R) rfl (by omega)
    (mem_JQ_of_red hq j h) x
  exact h1.trans (congrArg (· * _) (lamQB_eq_red _ (rank_X'_eq R) j h))

end GlobalTheory.TopLaw
