import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeFrameCocyclesLinkedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionExtendsToAinfDiscRings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFacts
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.CrLimit

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem exists_smul_of_dvd {R : Type} [CommRing R] {m n : Type} (c : R) (M : Matrix m n R)
    (h : ∀ i j, c ∣ M i j) : ∃ M' : Matrix m n R, M = c • M' := by
  choose M' hM' using h
  exact ⟨Matrix.of M', by ext i j; simp [hM']⟩

theorem ev_X_dvd_gal (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    bk.ev X ∣ Per.σA (g : GQ l) (bk.ev s) - bk.ev s := by
  obtain ⟨c, hc⟩ := (GlobalTheory.BSP.galois_discMap l K bk).1 (g : GQ l)
  obtain ⟨t, w, e⟩ : ∃ (t : bk.S) (w : Wq l bk.a), s = X * t + C w := ⟨_, _, eq_X_mul_shift_add_const s⟩
  subst e
  rw [map_add, map_mul, map_add, map_mul, bk.ev_C, bk.gal_w, hc]
  exact ⟨c * Per.σA (g : GQ l) (bk.ev t) - bk.ev t, by ring⟩

theorem isUnit_inclW_ev_X (bk : BK K) : IsUnit (inclW l (bk.ev X)) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [bk.ev_X, inclW, WittVector.map_teichmuller, WittVector.teichmuller_coeff_zero]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 (GlobalTheory.BSP.FlatDisc.flat_ne_zero bk)

end GlobalTheory.BKLim.CrLimit

namespace GlobalTheory.BKLim.CrLimit

theorem isCr_of_link : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r) → (∀ n, (F n).IsCr) → F₀.IsCr := by
  intro l _ K bk d N ρ tw F F₀ r hlink hcr g i j
  suffices hx : ∀ n : ℕ, ∃ a : Ainf l, (l : WCb l) ^ n ∣ (l : WCb l) ^ r * inclW l ((F₀.ε g - 1) i j) -
      inclW l (bk.ev X * a) by
    obtain ⟨a, ha⟩ := GlobalTheory.T.ainf_principal_ideal_saturated_closed l (bk.ev X) (isUnit_inclW_ev_X bk) r (inclW l ((F₀.ε g - 1) i j)) hx
    exact ⟨a, inclW_injective ha⟩
  intro n
  obtain ⟨m, hnm, R, G, hT, hRG⟩ := hlink n
  have hk := GlobalTheory.T.breuilKisinLatticeFrame_cocycles_linked l K bk N N d (tw.d' m) n (fun g => (ρ g).val) (fun g => (tw.ρ' m g).val) F₀ (F m)
    (tw.Pi m) R (fun g i j => (pow_dvd_pow _ hnm).trans ((tw.onto m).equi g i j)) hT
  set σ := Per.σA (g : GQ l) with hσ
  set A := R.map bk.ev with hA
  set B := G.map bk.ev with hB
  set ε₀ := F₀.ε g with hε₀
  set ε' := (F m).ε g with hε'
  obtain ⟨D, hD⟩ := exists_smul_of_dvd ((l : Ainf l) ^ n) (ε₀ * A.map σ - A * ε') (hk g)
  obtain ⟨P, hP⟩ := exists_smul_of_dvd ((l : Ainf l) ^ n) (A * B - (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)))
    (fun i j => by
      have h := map_dvd bk.ev (hRG i j)
      have e : (A * B - (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j =
          bk.ev ((R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) := by
        rw [hA, hB, ← Matrix.map_mul]
        simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_sub,
          map_mul, map_pow, map_natCast]
        split_ifs <;> simp
      rw [e]
      simpa only [map_pow, map_natCast] using h)
  obtain ⟨Z1, hZ1⟩ := exists_smul_of_dvd (bk.ev X) (ε' - 1) (hcr m g)
  obtain ⟨Z2, hZ2⟩ := exists_smul_of_dvd (bk.ev X) (B.map σ - B) (fun i j => by
    simpa only [hB, Matrix.sub_apply, Matrix.map_apply] using ev_X_dvd_gal bk g (G i j))
  have h1 : ε₀ * A.map σ = A * ε' + (l : Ainf l) ^ n • D := (sub_eq_iff_eq_add').1 hD
  have h2 : A * B = (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)) + (l : Ainf l) ^ n • P :=
    (sub_eq_iff_eq_add').1 hP
  have h3 : A.map σ * B.map σ = (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)) + (l : Ainf l) ^ n • P.map σ := by
    rw [← Matrix.map_mul, h2]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_add, map_mul,
      map_pow, map_natCast]
    split_ifs <;> simp
  have h4 : ε' = 1 + bk.ev X • Z1 := (sub_eq_iff_eq_add').1 hZ1
  have h5 : B.map σ = B + bk.ev X • Z2 := (sub_eq_iff_eq_add').1 hZ2
  have e1 : ε₀ * (A.map σ * B.map σ) = (l : Ainf l) ^ r • ε₀ + (l : Ainf l) ^ n • (ε₀ * P.map σ) := by
    rw [h3, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
  have e2 : ε₀ * (A.map σ * B.map σ) = A * ε' * B.map σ + (l : Ainf l) ^ n • (D * B.map σ) := by
    rw [← Matrix.mul_assoc, h1, Matrix.add_mul, Matrix.smul_mul]
  have e3 : A * ε' * B.map σ = A * B.map σ + bk.ev X • (A * Z1 * B.map σ) := by
    rw [h4, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e4 : A * B.map σ = (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)) + (l : Ainf l) ^ n • P +
      bk.ev X • (A * Z2) := by
    rw [h5, Matrix.mul_add, h2, Matrix.mul_smul]
  have key : (l : Ainf l) ^ r • (ε₀ - 1) = (l : Ainf l) ^ n • (P + D * B.map σ - ε₀ * P.map σ) +
      bk.ev X • (A * Z1 * B.map σ + A * Z2) := by
    have h := e1.symm.trans e2
    rw [e3, e4] at h
    refine eq_of_sub_eq_zero ?_
    rw [← sub_eq_zero.2 h, smul_sub, smul_sub, smul_add, smul_add]
    abel
  have hij := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] at hij
  refine ⟨(A * Z1 * B.map σ + A * Z2) i j, ?_⟩
  have hd : (l : Ainf l) ^ n ∣ (l : Ainf l) ^ r * (ε₀ - 1) i j - bk.ev X * (A * Z1 * B.map σ + A * Z2) i j :=
    ⟨(P + D * B.map σ - ε₀ * P.map σ) i j, by
      simp only [Matrix.add_apply, Matrix.sub_apply] at hij ⊢
      linear_combination hij⟩
  simpa only [map_sub, map_mul, map_pow, map_natCast] using map_dvd (inclW l) hd

end GlobalTheory.BKLim.CrLimit

end
