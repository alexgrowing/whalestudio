import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiscMaps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusRationalColumns
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusGaloisRelationFrameAinf
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.KappaFrob

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (g : ↥(GK K)) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → IsDiscMap WittVector.frobenius Φ → s.κ g * s.F.map (bk.iS.comp C) = s.F.map (bk.iS.comp C) * (s.κ g).map Φ := by
  intro l hl K bk τ hτ d ρ _ s g G Φ hG hΦ
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have h0 : 0 < bk.ρ₀ := NNReal.rpow_pos (zero_lt_one.trans hl1)
  have h1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg hl1
    (neg_lt_zero.2 (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  have hi : Function.Injective bk.iA := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk _ bk.ev ι TB bk.ρ₀ h0 h1).1
  obtain ⟨j, hj⟩ := exists_discMap_of_pow_dvd l _ _ bk.ev (X : bk.S) (bk.ev X) bk.ρ₀ bk.ρ₀ 1 h0
    (by rw [pow_one]) (by rw [pow_one])
  have hu : IsUnit (bk.iS (frobS l bk.a bk.E)) := by
    have h := (isUnit_toDisc_frobS_E l K bk).map j
    rwa [hj.ext] at h

  have hfτ : WittVector.frobenius τ ≠ 0 := by
    obtain ⟨-, ε, η, ⟨-, hδ1⟩, h⟩ := hτ
    rw [h]
    intro h'
    rw [Units.mul_right_eq_zero, sub_eq_zero] at h'
    have h1' : ε = 1 := by simpa using congrArg (fun w : Ainf l => w.coeff 0) h'
    exact hδ1 (by rw [h1', map_one, map_one])
  have hEτ : bk.ev bk.E * τ ≠ 0 := hτ.1 ▸ hfτ
  have hτ0 : τ ≠ 0 := right_ne_zero_of_mul hEτ
  have hE0 : bk.ev bk.E ≠ 0 := left_ne_zero_of_mul hEτ
  have hσinj : Function.Injective (Per.σA (g : GQ l)) := fun x y hxy => by
    have := congrArg (Per.σA ((g : GQ l)⁻¹)) hxy
    rwa [← GlobalTheory.RingBasics.σA_mul, ← GlobalTheory.RingBasics.σA_mul, inv_mul_cancel, GlobalTheory.RingBasics.σA_one, GlobalTheory.RingBasics.σA_one] at this
  have ha : bk.iA (bk.ev bk.E * τ) ≠ 0 := fun h => hEτ (hi (h.trans (map_zero _).symm))
  have hb : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) ≠ 0 := fun h =>
    hEτ (hσinj ((hi (h.trans (map_zero _).symm)).trans (map_zero _).symm))

  have hcomm : Φ.comp G = G.comp Φ := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp (Per.σA (g : GQ l)) =
        (Per.σA (g : GQ l)).comp WittVector.frobenius :=
      RingHom.ext fun x => (GlobalTheory.GalPhi.σA_frobenius _ x).symm
    have k1 : IsDiscMap ((WittVector.frobenius : Ainf l →+* Ainf l).comp (Per.σA (g : GQ l))) (Φ.comp G) :=
      ⟨fun x => by rw [RingHom.comp_apply, hG.ext, hΦ.ext, RingHom.comp_apply],
        fun x => (hΦ.norm_le _).trans (hG.norm_le _)⟩
    have k2 : IsDiscMap ((Per.σA (g : GQ l)).comp WittVector.frobenius) (G.comp Φ) :=
      ⟨fun x => by rw [RingHom.comp_apply, hΦ.ext, hG.ext, RingHom.comp_apply],
        fun x => (hG.norm_le _).trans (hΦ.norm_le _)⟩
    rw [e] at k1
    exact k1.unique k2
  have hΦa : Φ (bk.iA (bk.ev bk.E * τ)) = bk.iS (frobS l bk.a bk.E) * bk.iA (bk.ev bk.E * τ) := by
    rw [hΦ.ext, map_mul, hτ.1, ← bk.ev_frob, map_mul]; rfl
  have hΦb : Φ (bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ))) =
      G (bk.iS (frobS l bk.a bk.E)) * bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) := by
    rw [hΦ.ext, ← GlobalTheory.GalPhi.σA_frobenius, map_mul, hτ.1, ← bk.ev_frob, map_mul, map_mul]
    rw [show bk.iS (frobS l bk.a bk.E) = bk.iA (bk.ev (frobS l bk.a bk.E)) from rfl, hG.ext]

  have hφ : ((l : bk.DA bk.ρ₀) ^ s.c₁) • (s.W * s.X'.map bk.iS).map Φ =
      bk.iS (frobS l bk.a bk.E) ^ s.N • (s.W * s.X'.map bk.iS * s.F.map (bk.iS.comp C)) := s.φ Φ hΦ
  have hgal := s.gal g G hG
  set P := s.W * s.X'.map bk.iS with hP
  set FD := s.F.map (bk.iS.comp C) with hFD'
  set R := (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) with hR'
  set κ := s.κ g with hκ
  set a := bk.iA (bk.ev bk.E * τ) with ha'
  set b := bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) with hb'
  set u := bk.iS (frobS l bk.a bk.E) with hu'
  set L := (l : bk.DA bk.ρ₀) ^ s.c₁ with hL'
  have hMG : ∀ (H : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (c : bk.DA bk.ρ₀) (M : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)),
      (c • M).map H = H c • M.map H := fun H c M => Matrix.map_smul' _ _ _ (map_mul H)
  have hR : R.map Φ = R := Matrix.ext fun i j => by
    simp only [hR', Matrix.map_apply, RingHom.comp_apply]
    rw [hΦ.ext, GlobalTheory.GalPhi.frobenius_algebraMap]
  have hFD : FD.map G = FD := Matrix.ext fun i j => by
    simp only [hFD', Matrix.map_apply, RingHom.comp_apply]
    change G (bk.iA (bk.ev (C (s.F i j)))) = bk.iA (bk.ev (C (s.F i j)))
    rw [hG.ext, bk.ev_C, bk.gal_w]
  have hPG : (P.map G).map Φ = (P.map Φ).map G := Matrix.ext fun i j => by
    simp only [Matrix.map_apply]; exact RingHom.congr_fun hcomm _
  have hgalΦ : Φ a ^ s.N • (R * (P.map Φ).map G) = Φ b ^ s.N • (P.map Φ * κ.map Φ) := by
    have h := congrArg (fun M => M.map Φ) hgal
    have e1 : (R * P.map G).map Φ = R.map Φ * (P.map G).map Φ := Matrix.map_mul
    have e2 : (P * κ).map Φ = P.map Φ * κ.map Φ := Matrix.map_mul
    rwa [hMG, hMG, e1, e2, hR, hPG, map_pow, map_pow] at h
  have hL : G L = L := by simp [hL']
  have hA : L • (R * (P.map Φ).map G) = G (u ^ s.N) • (R * P.map G * FD) := by
    rw [← Matrix.mul_smul, ← hL, ← hMG, hφ, hMG, Matrix.map_mul, hFD, Matrix.mul_smul, Matrix.mul_assoc]
  have hB : L • (P.map Φ * κ.map Φ) = u ^ s.N • (P * FD * κ.map Φ) := by
    rw [← Matrix.smul_mul, hφ, Matrix.smul_mul]
  have step1 : (Φ a ^ s.N * G (u ^ s.N)) • (R * P.map G * FD) = (Φ b ^ s.N * u ^ s.N) • (P * FD * κ.map Φ) := by
    calc (Φ a ^ s.N * G (u ^ s.N)) • (R * P.map G * FD) = Φ a ^ s.N • (L • (R * (P.map Φ).map G)) := by
          rw [hA, smul_smul]
      _ = L • (Φ a ^ s.N • (R * (P.map Φ).map G)) := smul_comm _ _ _
      _ = L • (Φ b ^ s.N • (P.map Φ * κ.map Φ)) := by rw [hgalΦ]
      _ = Φ b ^ s.N • (L • (P.map Φ * κ.map Φ)) := smul_comm _ _ _
      _ = _ := by rw [hB, smul_smul]
  have hΦa' : Φ a ^ s.N = u ^ s.N * a ^ s.N := by rw [hΦa, mul_pow]
  have hΦb' : Φ b ^ s.N = G (u ^ s.N) * b ^ s.N := by rw [hΦb, mul_pow, map_pow]
  have key : (u ^ s.N * G (u ^ s.N) * a ^ s.N * b ^ s.N) • (P * κ * FD) =
      (u ^ s.N * G (u ^ s.N) * a ^ s.N * b ^ s.N) • (P * FD * κ.map Φ) := by
    calc (u ^ s.N * G (u ^ s.N) * a ^ s.N * b ^ s.N) • (P * κ * FD)
        = (Φ a ^ s.N * G (u ^ s.N)) • ((b ^ s.N • (P * κ)) * FD) := by
          rw [Matrix.smul_mul, smul_smul, hΦa']; congr 1; ring
      _ = (Φ a ^ s.N * G (u ^ s.N)) • ((a ^ s.N • (R * P.map G)) * FD) := by rw [hgal]
      _ = a ^ s.N • ((Φ a ^ s.N * G (u ^ s.N)) • (R * P.map G * FD)) := by
          rw [Matrix.smul_mul, smul_comm]
      _ = a ^ s.N • ((Φ b ^ s.N * u ^ s.N) • (P * FD * κ.map Φ)) := by rw [step1]
      _ = _ := by rw [smul_smul, hΦb']; congr 1; ring
  have hc : u ^ s.N * G (u ^ s.N) * a ^ s.N * b ^ s.N ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hu.pow _).ne_zero ((hu.pow _).map G).ne_zero) (pow_ne_zero _ ha))
      (pow_ne_zero _ hb)
  have h3 : P * κ * FD = P * FD * κ.map Φ := Matrix.ext fun i j => by
    have := congrFun (congrFun key i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hc this

  have hτi : bk.iA τ ≠ 0 := fun h => hτ0 (hi (h.trans (map_zero _).symm))
  have hdW : s.W.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det s.W_mul
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, h, zero_mul] at this
    exact pow_ne_zero _ (pow_ne_zero _ hτi) this.symm
  have hEi : bk.iS bk.E ≠ 0 := fun h => hE0 (hi (h.trans (map_zero _).symm))
  have hl0 : (l : bk.DA bk.ρ₀) ≠ 0 := (isUnit_l_disc l _ _).ne_zero
  have hdX : (s.X'.map bk.iS).det ≠ 0 := by
    intro h
    have := congrArg (fun M => (M.map bk.iS).det) s.X_mul
    rw [Matrix.map_mul, Matrix.det_mul, h, mul_zero, Matrix.map_smul' _ _ _ (map_mul bk.iS), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.det_smul, Matrix.det_one, mul_one, map_mul, map_pow, map_pow, map_natCast] at this
    exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ hEi)) this.symm
  have hdP : P.det ≠ 0 := by rw [hP, Matrix.det_mul]; exact mul_ne_zero hdW hdX
  have h4 : P.det • (κ * FD) = P.det • (FD * κ.map Φ) := by
    have e : ∀ M : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀), P.det • M = P.adjugate * (P * M) := fun M => by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [e, e, ← Matrix.mul_assoc P, ← Matrix.mul_assoc P, h3]
  exact Matrix.ext fun i j => by
    have := congrFun (congrFun h4 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hdP this

end GlobalTheory.BKLim.KappaFrob
