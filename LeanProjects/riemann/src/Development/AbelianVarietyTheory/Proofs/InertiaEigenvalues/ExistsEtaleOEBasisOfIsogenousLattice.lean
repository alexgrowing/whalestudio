import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfSaturated
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralWittLatticeBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.EtBasis

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_ne_zero (x : ℤ_[l]) (hx : x ≠ 0) : algebraMap ℤ_[l] (WCb l) x ≠ 0 := by
  rw [PadicInt.unitCoeff_spec hx, map_mul, map_pow, map_natCast]
  exact mul_ne_zero ((PadicInt.unitCoeff hx).isUnit.map _).ne_zero
    (pow_ne_zero _ (WittVector.irreducible l).ne_zero)

theorem algebraMap_mem_OE {K : FinExt l} (bk : BK K) (x : ℤ_[l]) : algebraMap ℤ_[l] (WCb l) x ∈ bk.OE := by
  intro n
  obtain ⟨y, hy⟩ := (Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x))
  refine ⟨0, (PadicInt.appr x n : bk.S), algebraMap ℤ_[l] (WCb l) y, ?_⟩
  have : x = (PadicInt.appr x n : ℤ_[l]) + (l : ℤ_[l]) ^ n * y := by rw [mul_comm, hy]; ring
  have h2 := congrArg (algebraMap ℤ_[l] (WCb l)) this
  rw [map_add, map_mul, map_pow, map_natCast, map_natCast] at h2
  rw [pow_zero, one_mul, h2, map_natCast]

theorem evW_mem_OE {K : FinExt l} (bk : BK K) (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem not_l_dvd_E {K : FinExt l} (bk : BK K) : ¬ (l : bk.S) ∣ bk.E := by
  rintro ⟨t, ht⟩
  have h := congrArg (coeff bk.Ep.natDegree) ht
  rw [← map_natCast (C (R := Wq l bk.a)) l, coeff_C_mul, Polynomial.coeff_coe, bk.monic.coeff_natDegree] at h
  have h2 := congrArg (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) h
  rw [map_mul, map_natCast, map_one, CharP.cast_eq_zero, zero_mul] at h2
  exact one_ne_zero h2

theorem adj_comm {d : ℕ} (f A B : Matrix (Fin d) (Fin d) ℤ_[l]) (hf : f.det ≠ 0) (h : f * B = A * f) :
    f.adjugate * A = B * f.adjugate := by
  have h1 : f.det • (f.adjugate * A) = f.det • (B * f.adjugate) := by
    calc f.det • (f.adjugate * A) = f.adjugate * A * (f * f.adjugate) := by
          rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
      _ = f.adjugate * (f * B) * f.adjugate := by rw [h]; simp only [Matrix.mul_assoc]
      _ = f.det • (B * f.adjugate) := by
          rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
  exact smul_right_injective _ hf h1

end GlobalTheory.EtBasis

namespace GlobalTheory.EtBasis

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ'' : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (F : Pre bk N d ρ) (f : Matrix (Fin d) (Fin d) (ℤ_[l])), f.det ≠ 0 → (∀ g, IsUnit (ρ'' g)) →
    (∀ g, f * ρ'' g = ρ g * f) → ∃ T'' P : Matrix (Fin d) (Fin d) (WCb l), IsUnit T'' ∧ (∀ i j, P i j ∈ bk.OE) ∧
      zW f * T'' = F.T * P := by
  intro l _ K bk τ _ N d ρ ρ'' F f hf hρ'' hfρ
  obtain ⟨hsat1, -, hinvS, -, -, hgalOE, hfrobOE⟩ := GlobalTheory.T.integral_elements_unit_factorization l K bk
  have hl0 : (l : WCb l) ≠ 0 := (WittVector.irreducible l).ne_zero
  have hzW : ∀ M : Matrix (Fin d) (Fin d) ℤ_[l], zW M = (algebraMap ℤ_[l] (WCb l)).mapMatrix M := fun _ => rfl
  have hzWmul : ∀ M M' : Matrix (Fin d) (Fin d) ℤ_[l], zW (M * M') = zW M * zW M' := fun M M' => by
    rw [hzW, hzW, hzW, map_mul]
  have hfadj : zW f * zW f.adjugate = algebraMap ℤ_[l] (WCb l) f.det • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← hzWmul, Matrix.mul_adjugate]
    ext i j
    by_cases h : i = j <;> simp [zW, h, Matrix.one_apply]
  have hTdet : F.T.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 F.unit).ne_zero
  have hdf : algebraMap ℤ_[l] (WCb l) f.det ≠ 0 := algebraMap_ne_zero _ hf
  set Y1 := zW f.adjugate * F.T with hY1
  have hY1det : Y1.det ≠ 0 := by
    rw [hY1, Matrix.det_mul, hzW, ← RingHom.map_det, Matrix.det_adjugate, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hdf) hTdet
  obtain ⟨m, P₀, Y', hP₀, hP₀det, hY', hlat, hsat⟩ := GlobalTheory.SatLattice.exists_lattice_basis l K bk d Y1 hY1det
  have hlm : (l : WCb l) ^ m ≠ 0 := pow_ne_zero _ hl0
  have hcancel : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (l : WCb l) ^ m • M = (l : WCb l) ^ m • M' → M = M' :=
    fun M M' h => Matrix.ext fun i j => mul_left_cancel₀ hlm (congrFun (congrFun h i) j)

  have hY'det : Y'.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hY'
    rw [Matrix.det_smul, h0, mul_zero, Matrix.det_mul] at this
    exact mul_ne_zero hY1det hP₀det this.symm

  obtain ⟨e, he, hEe⟩ := hinvS bk.E (not_l_dvd_E bk)
  have hφ : ∃ A'' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A'' i j ∈ bk.OE) ∧ Y'.map (frobW l) = Y' * A'' := by
    set B := e ^ N • F.A.map bk.evW with hB
    have hB_OE : ∀ i j, B i j ∈ bk.OE := fun i j => by
      simp only [hB, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      exact bk.OE.mul_mem (bk.OE.pow_mem he N) (evW_mem_OE bk _)
    have hTφ : F.T.map (frobW l) = F.T * B := by
      have h := congrArg (fun M => e ^ N • M) F.φ
      have h1 : e ^ N * bk.evW bk.E ^ N = 1 := by rw [← mul_pow, mul_comm, hEe, one_pow]
      simp only [smul_smul, h1, one_smul] at h
      rw [h, hB, Matrix.mul_smul]
    have hfrobzW : ∀ M : Matrix (Fin d) (Fin d) ℤ_[l], (zW M).map (frobW l) = zW M := fun M => by
      exact Matrix.ext fun i j => (frobW l).commutes _
    have hmapmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l),
        (M * M').map (frobW l) = M.map (frobW l) * M'.map (frobW l) :=
      fun M M' => Matrix.map_mul (f := (frobW l).toRingHom)
    have hY1φ : Y1.map (frobW l) = Y1 * B := by
      rw [hY1, hmapmul, hfrobzW, hTφ, Matrix.mul_assoc]
    set V := B * P₀.map (frobW l) with hV
    have hV_OE : ∀ i j, V i j ∈ bk.OE := fun i j => by
      simp only [hV, Matrix.mul_apply]
      exact bk.OE.sum_mem fun k _ => bk.OE.mul_mem (hB_OE i k) (hfrobOE _ (hP₀ k j))
    have hmain : (l : WCb l) ^ m • Y'.map (frobW l) = Y1 * V := by
      have h : ((l : WCb l) ^ m • Y').map (frobW l) = (Y1 * P₀).map (frobW l) := by rw [hY']
      rw [hmapmul, hY1φ] at h
      rw [hV, ← Matrix.mul_assoc, ← h]
      ext i j
      simp [map_mul, map_pow, map_natCast]
    have hcol : ∀ j, ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => V i j) = P₀ *ᵥ w := by
      intro j
      obtain ⟨w, hw, hvw⟩ := hlat (fun i => V i j) (fun i => hV_OE i j) m (fun i => by
        have : (Y1 *ᵥ fun i => V i j) i = (Y1 * V) i j := by
          simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
        rw [this, ← hmain, Matrix.smul_apply, smul_eq_mul]
        exact Dvd.intro _ rfl)
      exact ⟨w, hw, funext fun i => mul_left_cancel₀ hlm (congrFun hvw i)⟩
    choose w hw hvw using hcol
    refine ⟨Matrix.of fun i j => w j i, fun i j => hw j i, ?_⟩
    have hVP : V = P₀ * Matrix.of fun i j => w j i := by
      ext i j
      have := congrFun (hvw j) i
      simp only [Matrix.mulVec, dotProduct] at this
      simp [Matrix.mul_apply, this]
    apply hcancel
    rw [hmain, hVP, ← Matrix.mul_assoc, ← hY', Matrix.smul_mul]

  have hg : ∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (WCb l), IsUnit R ∧
      R * Y'.map (galW l (g : GQ l)) = Y' := by
    intro g hfix
    refine ⟨zW (ρ'' g), by rw [hzW]; exact (hρ'' g).map _, ?_⟩
    have hgmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (M * M').map (galW l (g : GQ l)) =
        M.map (galW l (g : GQ l)) * M'.map (galW l (g : GQ l)) :=
      fun M M' => Matrix.map_mul (f := (galW l (g : GQ l)).toRingEquiv.toRingHom)
    have hgzW : ∀ M : Matrix (Fin d) (Fin d) ℤ_[l], (zW M).map (galW l (g : GQ l)) = zW M := fun M => by
      exact Matrix.ext fun i j => (galW l (g : GQ l)).commutes _
    have hgP : P₀.map (galW l (g : GQ l)) = P₀ := by
      exact Matrix.ext fun i j => hgalOE g hfix _ (hP₀ i j)
    have hcomm : zW (ρ'' g) * zW f.adjugate = zW f.adjugate * zW (ρ g) := by
      rw [← hzWmul, ← hzWmul, adj_comm f (ρ g) (ρ'' g) hf (hfρ g)]
    have h : ((l : WCb l) ^ m • Y').map (galW l (g : GQ l)) = (Y1 * P₀).map (galW l (g : GQ l)) := by rw [hY']
    rw [hgmul, hY1, hgmul, hgzW, hgP] at h
    have hs : ((l : WCb l) ^ m • Y').map (galW l (g : GQ l)) = (l : WCb l) ^ m • Y'.map (galW l (g : GQ l)) := by
      ext i j; simp
    apply hcancel
    rw [← Matrix.mul_smul, ← hs, h, hY', hY1]
    calc zW (ρ'' g) * (zW f.adjugate * F.T.map (galW l (g : GQ l)) * P₀)
        = zW (ρ'' g) * zW f.adjugate * F.T.map (galW l (g : GQ l)) * P₀ := by simp only [Matrix.mul_assoc]
      _ = zW f.adjugate * (zW (ρ g) * F.T.map (galW l (g : GQ l))) * P₀ := by
          rw [hcomm]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [F.fix g hfix]
  obtain ⟨A'', hA'', hφ'⟩ := hφ
  have hunit : IsUnit Y' := GlobalTheory.SatInvUnit.isUnit_of_saturated l K bk d Y' A'' hY'det hA'' hφ' hg hsat
  set Ti := F.T⁻¹ with hTi'
  have hTi : Ti * F.T = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 F.unit)
  have hTTi : F.T * Ti = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 F.unit)
  refine ⟨Y', Ti * zW f * Y', hunit, fun i j => ?_, ?_⟩
  · have hP : (l : WCb l) ^ m • (Ti * zW f * Y') = algebraMap ℤ_[l] (WCb l) f.det • P₀ := by
      rw [← Matrix.mul_smul, hY', hY1]
      calc Ti * zW f * (zW f.adjugate * F.T * P₀) = Ti * (zW f * zW f.adjugate) * F.T * P₀ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [hfadj, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul, hTi, Matrix.one_mul]
    have := congrFun (congrFun hP i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    refine GlobalTheory.SatLattice.sat_pow bk.OE hl0 hsat1 m _ ?_
    rw [this]
    exact bk.OE.mul_mem (algebraMap_mem_OE bk _) (hP₀ i j)
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hTTi, Matrix.one_mul]

end GlobalTheory.EtBasis
