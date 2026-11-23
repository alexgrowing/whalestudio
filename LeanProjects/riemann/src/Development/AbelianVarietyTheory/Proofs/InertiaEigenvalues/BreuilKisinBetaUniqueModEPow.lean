import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisElemCyclotomicPeriodNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDivisibilityBreuilKisinFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaUniq

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem σO_intToOC (g : ↥(GK K)) (c : ↥(OL K)) : Per.σO (g : GQ l) (intToOC K c) = intToOC K c :=
  Subtype.ext ((GlobalTheory.RingIface.sigO_coe l (g : GQ l) (intToOC K c)).trans
    ((GlobalTheory.RingBasics.σC_coe (g : GQ l) _).trans (congrArg _
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (c : ↥K.1).2))))

theorem theta_gal_ev (g : ↥(GK K)) (s : bk.S) :
    Per.θ l (Per.σA (g : GQ l) (bk.ev s)) = Per.θ l (bk.ev s) := by
  rw [GlobalTheory.RingBasics.θ_σA, bk.θ_ev (bk.str.symm (Ideal.Quotient.mk _ s)) s (bk.str.apply_symm_apply _).symm,
    σO_intToOC]

theorem theta_eq_zero_iff (a : Ainf l) : Per.θ l a = 0 ↔ bk.ev bk.E ∣ a := by
  rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton]

theorem evE_ne_zero : bk.ev bk.E ≠ 0 := fun h =>
  GlobalTheory.BSP.AinfDiv.cc_E_ne bk (by rw [h, map_zero])

theorem l_ne_zero_OC : ((l : ℕ) : OC l) ≠ 0 := fun h =>
  GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h)

end GlobalTheory.BKLim.BetaUniq

noncomputable section

namespace GlobalTheory.BKLim.BetaUniq

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem step {d : ℕ} (g : ↥(GK K)) (w : Ainf l)
    (hw : Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w)
    (hwi : ∀ i : ℕ, 1 ≤ i → Per.θ l w ^ i ≠ 1)
    (P : Fin d → Fin d → Ainf l) (hP : ∀ a c, Per.θ l (P a c) = if a = c then 1 else 0)
    (m i : ℕ) (hi : 1 ≤ i) (him : i < m) (δ : Fin d → Fin d → bk.S)
    (hδ : ∀ a b, bk.ev bk.E ^ m ∣ ∑ c, P a c * Per.σA (g : GQ l) (bk.ev (δ c b)) - bk.ev (δ a b))
    (hdiv : ∀ a b, bk.E ^ i ∣ δ a b) : ∀ a b, bk.E ^ (i + 1) ∣ δ a b := by
  haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)
  choose δ' hδ' using hdiv
  intro a b
  have hX : ∑ c, P a c * Per.σA (g : GQ l) (bk.ev (δ c b)) - bk.ev (δ a b) =
      bk.ev bk.E ^ i * (w ^ i * ∑ c, P a c * Per.σA (g : GQ l) (bk.ev (δ' c b)) - bk.ev (δ' a b)) := by
    simp only [hδ', map_mul, map_pow, hw, mul_pow, Finset.mul_sum]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      ring
  have h1 : bk.ev bk.E ∣ w ^ i * ∑ c, P a c * Per.σA (g : GQ l) (bk.ev (δ' c b)) - bk.ev (δ' a b) := by
    have h2 := hδ a b
    rw [hX, show m = i + (m - i) by omega, pow_add] at h2
    have h3 := (mul_dvd_mul_iff_left (pow_ne_zero i (evE_ne_zero bk))).1 h2
    exact (dvd_pow_self (bk.ev bk.E) (by omega)).trans h3
  rw [← theta_eq_zero_iff] at h1
  simp only [map_sub, map_mul, map_pow, map_sum, theta_gal_ev, hP, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  have h4 : Per.θ l (bk.ev (δ' a b)) = 0 := by
    have h5 : (Per.θ l w ^ i - 1) * Per.θ l (bk.ev (δ' a b)) = 0 := by
      rw [sub_mul, one_mul]; exact h1
    exact (mul_eq_zero.1 h5).resolve_left (sub_ne_zero.2 (hwi i hi))
  rw [theta_eq_zero_iff] at h4
  have h6 := (GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk 1).2.1 (δ' a b) (by rwa [pow_one])
  rw [hδ' a b, pow_succ]
  exact mul_dvd_mul_left _ (by rwa [pow_one] at h6)

end GlobalTheory.BKLim.BetaUniq

theorem GlobalTheory.BKLim.beta_unique : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (k k' : ℕ) (β β' : Matrix (Fin d) (Fin d) (bk.S)), F.IsBeta m k β → F.IsBeta m k' β' → ∀ i j, bk.E ^ m ∣ ((l : bk.S) ^ k' • β - (l : bk.S) ^ k • β') i j := by
  intro l _ K bk m N d ρ F k k' β β' hβ hβ'
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · intro i j; simp
  obtain ⟨g, z, ⟨w, hw, hz⟩, hzi⟩ := GlobalTheory.T.exists_galois_elem_cyclotomic_period_not_root_of_unity l K bk
  have hwi : ∀ i : ℕ, 1 ≤ i → Per.θ l w ^ i ≠ 1 := by
    intro i hi h
    have h1 : Per.θD l (aDp l w) = (Per.θ l w : ℂ_[l]) := (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1 w
    apply hzi i hi
    have h2 : ((Per.θ l w : ℂ_[l])) ^ i = 1 := by exact_mod_cast congrArg Subtype.val h
    calc z ^ i = z ^ i * (Per.θ l w : ℂ_[l]) ^ i := by rw [h2, mul_one]
      _ = (z * Per.θD l (aDp l w)) ^ i := by rw [h1, mul_pow]
      _ = 1 := by rw [hz, one_pow]
  set P : Fin d → Fin d → Ainf l := fun a c => WittVector.frobenius (F.ε g a c) with hPdef
  have hent : ∀ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → ∀ a b,
      bk.ev bk.E ^ m ∣ ∑ c, P a c * Per.σA (g : GQ l) (bk.ev (β c b)) - bk.ev (β a b) := by
    intro k β h a b
    have := h.2 g a b
    simpa [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, hPdef] using this
  have hθβ : ∀ c b, Per.θ l (bk.ev (β c b)) = (l : OC l) ^ k * (if c = b then 1 else 0) := by
    intro c b
    have h2 : Per.θ l (bk.ev ((β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) c b)) = 0 :=
      (BetaUniq.theta_eq_zero_iff bk _).2 (map_dvd bk.ev (hβ.1 c b))
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_sub, map_mul, map_pow,
      map_natCast] at h2
    rw [sub_eq_zero] at h2
    rw [h2]; split_ifs <;> simp
  have hP : ∀ a c, Per.θ l (P a c) = if a = c then 1 else 0 := by
    intro a b
    have h := (BetaUniq.theta_eq_zero_iff bk _).2 ((dvd_pow_self _ hm.ne').trans (hent k β hβ a b))
    simp only [map_sub, map_sum, map_mul, BetaUniq.theta_gal_ev, hθβ, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [sub_eq_zero] at h
    have hl := pow_ne_zero k (BetaUniq.l_ne_zero_OC (l := l))
    apply mul_right_cancel₀ hl
    rw [h]; split_ifs <;> simp
  set δ : Fin d → Fin d → bk.S := fun a b => (l : bk.S) ^ k' * β a b - (l : bk.S) ^ k * β' a b with hδdef
  have hδ : ∀ a b, bk.ev bk.E ^ m ∣ ∑ c, P a c * Per.σA (g : GQ l) (bk.ev (δ c b)) - bk.ev (δ a b) := by
    intro a b
    have e1 : ∀ c, P a c * Per.σA (g : GQ l) (bk.ev (δ c b)) =
        (l : Ainf l) ^ k' * (P a c * Per.σA (g : GQ l) (bk.ev (β c b))) -
          (l : Ainf l) ^ k * (P a c * Per.σA (g : GQ l) (bk.ev (β' c b))) := by
      intro c; simp only [hδdef, map_sub, map_mul, map_pow, map_natCast]; ring
    have e : ∑ c, P a c * Per.σA (g : GQ l) (bk.ev (δ c b)) - bk.ev (δ a b) =
        (l : Ainf l) ^ k' * (∑ c, P a c * Per.σA (g : GQ l) (bk.ev (β c b)) - bk.ev (β a b)) -
          (l : Ainf l) ^ k * (∑ c, P a c * Per.σA (g : GQ l) (bk.ev (β' c b)) - bk.ev (β' a b)) := by
      rw [Finset.sum_congr rfl (fun c _ => e1 c), Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [hδdef, map_sub, map_mul, map_pow, map_natCast]; ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right (hent k β hβ a b) _) (dvd_mul_of_dvd_right (hent k' β' hβ' a b) _)
  have hbase : ∀ a b, bk.E ∣ δ a b := by
    intro a b
    have h1 := hβ.1 a b
    have h2 := hβ'.1 a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2
    have e : δ a b = (l : bk.S) ^ k' * (β a b - (l : bk.S) ^ k * (1 : Matrix (Fin d) (Fin d) bk.S) a b) -
        (l : bk.S) ^ k * (β' a b - (l : bk.S) ^ k' * (1 : Matrix (Fin d) (Fin d) bk.S) a b) := by
      simp only [hδdef]; ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)
  have hall : ∀ i, 1 ≤ i → i ≤ m → ∀ a b, bk.E ^ i ∣ δ a b := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => intro _ a b; rw [pow_one]; exact hbase a b
    | succ n hn ih =>
      intro hnm
      exact BetaUniq.step bk g w hw hwi P hP m n hn (by omega) δ hδ (ih (by omega))
  intro i j
  have := hall m hm le_rfl i j
  simpa [hδdef, Matrix.sub_apply, Matrix.smul_apply] using this
