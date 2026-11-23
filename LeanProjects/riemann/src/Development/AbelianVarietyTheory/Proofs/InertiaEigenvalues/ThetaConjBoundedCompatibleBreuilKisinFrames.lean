import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitAndAinfSaturated
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaAinfPeriodPowNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeFrameCocyclesLinkedStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.HTBound

section mat
variable {𝕜 : Type*} [NormedField 𝕜] [IsUltrametricDist 𝕜] {m n k : Type*} [Fintype n]

theorem nsub_max (x y : 𝕜) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

theorem bnd_mul {A : Matrix m n 𝕜} {B : Matrix n k 𝕜} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hA : ∀ i j, ‖A i j‖ ≤ r) (hB : ∀ i j, ‖B i j‖ ≤ s) : ∀ i j, ‖(A * B) i j‖ ≤ r * s := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA _ _) (hB _ _) (norm_nonneg _) hr

theorem bnd_add {A B : Matrix m k 𝕜} {r : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ r) (hB : ∀ i j, ‖B i j‖ ≤ r) :
    ∀ i j, ‖(A + B) i j‖ ≤ r := fun i j =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA i j) (hB i j))

theorem bnd_sub {A B : Matrix m k 𝕜} {r : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ r) (hB : ∀ i j, ‖B i j‖ ≤ r) :
    ∀ i j, ‖(A - B) i j‖ ≤ r := fun i j =>
  (nsub_max _ _).trans (max_le (hA i j) (hB i j))

theorem bnd_smul {A : Matrix m k 𝕜} {r : ℝ} (a : 𝕜) (hA : ∀ i j, ‖A i j‖ ≤ r) :
    ∀ i j, ‖(a • A) i j‖ ≤ ‖a‖ * r := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hA i j) (norm_nonneg a)

end mat

variable {l : ℕ} [hl : Fact l.Prime]

theorem th_le (x : Ainf l) : ‖((Per.θD l).comp (aDp l)) x‖ ≤ 1 := by
  rw [RingHom.comp_apply, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
  exact (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l x).2

theorem norm_l : ‖((l : ℕ) : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]
  simp

theorem th_pow_dvd (n : ℕ) (x : Ainf l) (h : ((l : ℕ) : Ainf l) ^ n ∣ x) :
    ‖((Per.θD l).comp (aDp l)) x‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
  obtain ⟨w, rfl⟩ := h
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, norm_l, inv_pow]
  exact mul_le_of_le_one_right (by positivity) (th_le w)

theorem th_gal {K : FinExt l} (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    ((Per.θD l).comp (aDp l)) (Per.σA (g : GQ l) (bk.ev s)) = ((Per.θD l).comp (aDp l)) (bk.ev s) := by
  simp only [RingHom.comp_apply, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, GlobalTheory.RingBasics.θ_σA]
  obtain ⟨r, hr⟩ := bk.str.surjective (Ideal.Quotient.mk _ s)
  rw [bk.θ_ev r s hr.symm]
  refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (intToOC K r)).trans ?_
  rw [coe_intToOC, GlobalTheory.RingBasics.σC_coe]
  congr 1
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2

theorem zl_unique (f g : ℤ_[l] →+* ℂ_[l]) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1) (x : ℤ_[l]) :
    f x = g x := by
  have key : ∀ n : ℕ, ‖f x - g x‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ ^ n := by
    intro n
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x)
    have e : x = ((x.appr n : ℕ) : ℤ_[l]) + u * ((l : ℕ) : ℤ_[l]) ^ n := by rw [hu]; ring
    rw [e, map_add, map_add, map_natCast, map_natCast, add_sub_add_left_eq_sub, map_mul, map_mul, map_pow,
      map_pow, map_natCast, map_natCast, ← sub_mul, norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity)
      ((nsub_max _ _).trans (max_le (hf u) (hg u)))
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (GlobalTheory.RingBasics.norm_p_lt (p := l))
  have h0 := ge_of_tendsto' ht key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

theorem th_zl (z : ℤ_[l]) :
    ((Per.θD l).comp (aDp l)) (algebraMap ℤ_[l] (Ainf l) z) = algebraMap (Om l) ℂ_[l] (zOm l z) :=
  zl_unique (((Per.θD l).comp (aDp l)).comp (algebraMap ℤ_[l] (Ainf l)))
    ((algebraMap (Om l) ℂ_[l]).comp (zOm l)) (fun _ => th_le _) (fun x => by
      simp [zOm]
      exact PadicInt.norm_le_one x) z

theorem pow_dvd_of_inclW (k : ℕ) (a : Ainf l) (h : ((l : ℕ) : WCb l) ^ k ∣ inclW l a) :
    ((l : ℕ) : Ainf l) ^ k ∣ a := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    obtain ⟨c, hc⟩ := h
    have h0 : a.coeff 0 = 0 := by
      have h1 : (inclW l a).coeff 0 = 0 := by
        rw [hc, pow_succ', mul_assoc]; exact coeff_zero_l_mul _
      change algebraMap (OCb l) (Cb l) (a.coeff 0) = 0 at h1
      exact (map_eq_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).1 h1
    obtain ⟨b, rfl⟩ := ainf_exists_l_mul_of_coeff_zero a h0
    have hl0 : ((l : ℕ) : WCb l) ≠ 0 := fun h => by
      have h1 := congrArg (fun x : WCb l => x.coeff 1) h
      simp [WittVector.coeff_p] at h1
    have hb : ((l : ℕ) : WCb l) ^ k ∣ inclW l b := by
      refine ⟨c, mul_left_cancel₀ hl0 ?_⟩
      rw [← mul_assoc, ← pow_succ', ← hc, map_mul, map_natCast]
    exact pow_succ' ((l : ℕ) : Ainf l) k ▸ mul_dvd_mul_left _ (ih b hb)

theorem bounded_compat : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N : ℕ), ∃ Bd : ℝ, ∀ (N' d d' n : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Frame bk N' d ρ) (F' : Frame bk N d' ρ') (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Y' : Matrix (Fin d') (Fin d') (Ainf l)), N' = N → Y.map (inclW l) = inclW l τ ^ N • F.T → Y'.map (inclW l) = inclW l τ ^ N • F'.T → ∀ (g : ↥(GK K)) (U : Matrix (Fin d) (Fin d) (ℂ_[l])) (U' : Matrix (Fin d') (Fin d') (ℂ_[l])), U * Y.map ((Per.θD l).comp (aDp l)) = Y.map ((Per.θD l).comp (aDp l)) * (F.ε g).map ((Per.θD l).comp (aDp l)) → U' * Y'.map ((Per.θD l).comp (aDp l)) = Y'.map ((Per.θD l).comp (aDp l)) * (F'.ε g).map ((Per.θD l).comp (aDp l)) → (∀ i j, ‖U i j‖ ≤ Bd) ∧ (∀ i j, ‖U' i j‖ ≤ Bd) ∧ ∀ (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])) (R : Matrix (Fin d) (Fin d') (bk.S)), (∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j) → (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) → ∀ i j, ‖(U * Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) - Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) * U') i j‖ ≤ Bd * ((l : ℝ) ^ n)⁻¹ := by
  intro l _ K bk τ hτ N
  have hs0 := GlobalTheory.T.theta_ainf_period_pow_ne_zero l K bk τ hτ (2 * N)
  set s := ((Per.θD l).comp (aDp l)) (τ ^ (2 * N)) with hs
  have hc0 : 0 < ‖s‖ := norm_pos_iff.2 hs0
  have hc1 : ‖s‖ ≤ 1 := th_le _
  have hci : 1 ≤ ‖s‖⁻¹ := (one_le_inv₀ hc0).2 hc1
  refine ⟨‖s‖⁻¹ * ‖s‖⁻¹, ?_⟩
  intro N' d d' n ρ ρ' F F' Y Y' hN hY hY' g U U' hU hU'
  subst N'
  have hb1 : ∀ {m k : Type} (M : Matrix m k (Ainf l)), ∀ i j, ‖(M.map ((Per.θD l).comp (aDp l))) i j‖ ≤ 1 :=
    fun M i j => th_le _

  have inv : ∀ {e : ℕ} {σ : ↥(GK K) → Matrix (Fin e) (Fin e) ℤ_[l]} (G : Frame bk N e σ)
      (Z : Matrix (Fin e) (Fin e) (Ainf l)), Z.map (inclW l) = inclW l τ ^ N • G.T →
      ∃ Z₁ : Matrix (Fin e) (Fin e) (Ainf l),
        Z.map ((Per.θD l).comp (aDp l)) * Z₁.map ((Per.θD l).comp (aDp l)) = s • 1 := by
    intro e σ G Z hZ
    obtain ⟨Z₀, Z₁, h0, h1⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N e σ G.toPre
    have e0 : Z₀ = Z := by
      refine Matrix.ext fun i j => ?_
      apply inclW_injective
      have := congrFun (congrFun (h0.trans hZ.symm) i) j
      simpa using this
    subst e0
    refine ⟨Z₁, ?_⟩
    rw [← Matrix.map_mul, h1]
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j <;> simp [Matrix.smul_apply, Matrix.one_apply, hij, s]
  obtain ⟨Y₁, hY₁⟩ := inv F Y hY
  obtain ⟨Y₁', hY₁'⟩ := inv F' Y' hY'

  have solve : ∀ {e : ℕ} (y y₁ x V : Matrix (Fin e) (Fin e) ℂ_[l]), y * y₁ = s • 1 → V * y = y * x →
      V = s⁻¹ • (y * x * y₁) := by
    intro e y y₁ x V h1 h2
    rw [← h2, Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have bnd : ∀ {e : ℕ} {σ : ↥(GK K) → Matrix (Fin e) (Fin e) ℤ_[l]} (G : Frame bk N e σ)
      (Z Z₁ : Matrix (Fin e) (Fin e) (Ainf l)) (V : Matrix (Fin e) (Fin e) ℂ_[l]),
      Z.map ((Per.θD l).comp (aDp l)) * Z₁.map ((Per.θD l).comp (aDp l)) = s • 1 →
      V * Z.map ((Per.θD l).comp (aDp l)) = Z.map ((Per.θD l).comp (aDp l)) * (G.ε g).map ((Per.θD l).comp (aDp l)) →
      ∀ i j, ‖V i j‖ ≤ ‖s‖⁻¹ := by
    intro e σ G Z Z₁ V h1 h2
    rw [solve _ _ _ V h1 h2]
    have := bnd_smul s⁻¹ (bnd_mul (mul_nonneg zero_le_one zero_le_one) zero_le_one
      (bnd_mul zero_le_one zero_le_one (hb1 Z) (hb1 (G.ε g))) (hb1 Z₁))
    simpa [norm_inv] using this
  have hUb := bnd F Y Y₁ U hY₁ hU
  have hU'b := bnd F' Y' Y₁' U' hY₁' hU'
  have hle : ‖s‖⁻¹ ≤ ‖s‖⁻¹ * ‖s‖⁻¹ := le_mul_of_one_le_left (by positivity) hci
  refine ⟨fun i j => (hUb i j).trans hle, fun i j => (hU'b i j).trans hle, ?_⟩
  intro Pi R hequi hlink
  set θ' : Ainf l →+* ℂ_[l] := (Per.θD l).comp (aDp l) with hθ'
  have hD1 : ∀ i j, ((l : ℕ) : Ainf l) ^ n ∣ (Pi.map (algebraMap ℤ_[l] (Ainf l)) * Y' - Y * R.map bk.ev) i j := by
    intro i j
    apply pow_dvd_of_inclW
    have e1 : (Pi.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW Pi := by
      refine Matrix.ext fun a b => ?_
      exact (inclWA l).commutes _
    have e2 : (R.map bk.ev).map (inclW l) = R.map bk.evW := by
      rw [Matrix.map_map]; rfl
    have e : (Pi.map (algebraMap ℤ_[l] (Ainf l)) * Y' - Y * R.map bk.ev).map (inclW l) =
        inclW l τ ^ N • (zW Pi * F'.T - F.T * R.map bk.evW) := by
      rw [Matrix.map_sub _ (map_sub (inclW l)), Matrix.map_mul, Matrix.map_mul, hY, hY', e1, e2,
        Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    have := congrFun (congrFun e i) j
    rw [Matrix.map_apply] at this
    rw [this, Matrix.smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_left (hlink i j) _
  have hD2 := GlobalTheory.T.breuilKisinLatticeFrame_cocycles_linked l K bk N N d d' n ρ ρ' F F' Pi R hequi hlink g
  have hP : Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) = (Pi.map (algebraMap ℤ_[l] (Ainf l))).map θ' := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    exact (th_zl _).symm
  have hR : ((R.map bk.ev).map (Per.σA (g : GQ l))).map θ' = (R.map bk.ev).map θ' := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    exact th_gal bk g _
  rw [hP]
  set P := (Pi.map (algebraMap ℤ_[l] (Ainf l))).map θ' with hPdef
  set y := Y.map θ' with hy
  set y' := Y'.map θ' with hy'
  set Ry := (R.map bk.ev).map θ' with hRy
  set e := (F.ε g).map θ' with he
  set e' := (F'.ε g).map θ' with he'
  have eD1 : P * y' - y * Ry = (Pi.map (algebraMap ℤ_[l] (Ainf l)) * Y' - Y * R.map bk.ev).map θ' := by
    rw [Matrix.map_sub _ (map_sub θ'), Matrix.map_mul, Matrix.map_mul]
  have eD2 : e * Ry - Ry * e' = (F.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * F'.ε g).map θ' := by
    rw [Matrix.map_sub _ (map_sub θ'), Matrix.map_mul, Matrix.map_mul, hR]
  set q : ℝ := ((l : ℝ) ^ n)⁻¹ with hqdef
  have hq : 0 ≤ q := by positivity
  have bD1 : ∀ i j, ‖(P * y' - y * Ry) i j‖ ≤ q := by
    rw [eD1]; intro i j; exact th_pow_dvd n _ (hD1 i j)
  have bD2 : ∀ i j, ‖(e * Ry - Ry * e') i j‖ ≤ q := by
    rw [eD2]; intro i j; exact th_pow_dvd n _ (hD2 i j)
  have key : (U * P - P * U') * y' = U * (P * y' - y * Ry) + y * (e * Ry - Ry * e') - (P * y' - y * Ry) * e' := by
    rw [Matrix.sub_mul, Matrix.mul_assoc P U' y', hU', Matrix.mul_assoc U P y']
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hU]
    abel
  have hX : U * P - P * U' = s⁻¹ • ((U * P - P * U') * y' * Y₁'.map θ') := by
    rw [Matrix.mul_assoc (U * P - P * U') y', hY₁', Matrix.mul_smul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ hs0, one_smul]
  intro i j
  rw [hX, key]
  have hsq : q ≤ ‖s‖⁻¹ * q := le_mul_of_one_le_left hq hci
  have b1 : ∀ i j, ‖(U * (P * y' - y * Ry)) i j‖ ≤ ‖s‖⁻¹ * q := bnd_mul (by positivity) hq hUb bD1
  have b2 : ∀ i j, ‖(y * (e * Ry - Ry * e')) i j‖ ≤ ‖s‖⁻¹ * q := fun i j =>
    (bnd_mul zero_le_one hq (hb1 Y) bD2 i j).trans (by rw [one_mul]; exact hsq)
  have b3 : ∀ i j, ‖((P * y' - y * Ry) * e') i j‖ ≤ ‖s‖⁻¹ * q := fun i j =>
    (bnd_mul hq zero_le_one bD1 (hb1 _) i j).trans (by rw [mul_one]; exact hsq)
  have b4 := bnd_smul s⁻¹ (bnd_mul (by positivity) zero_le_one (bnd_sub (bnd_add b1 b2) b3) (hb1 Y₁'))
  calc _ ≤ _ := b4 i j
    _ = _ := by rw [norm_inv]; ring

end GlobalTheory.HTBound
