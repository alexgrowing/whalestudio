import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDvdTiltUniformizerPowAcrisEventuallyStatement
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory.CrZero

theorem pow_cancel {A : Type*} [CommRing A] (p : A) (hp : ∀ x : A, p * x = 0 → x = 0)
    (k : ℕ) (a b : A) (h : p ^ k * a = p ^ k * b) : a = b := by
  induction k generalizing a b with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    have h' : p * (p ^ k * a - p ^ k * b) = 0 := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, ← pow_succ', h, sub_self]
    exact sub_eq_zero.mp (hp _ h')

theorem eq_zero_of_forall_dvd {A : Type*} [CommRing A] (p : A)
    (hH : IsHausdorff (Ideal.span {p}) A) (x : A) (h : ∀ M : ℕ, p ^ M ∣ x) : x = 0 := by
  refine hH.haus x fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton.mpr (h n)

end GlobalTheory.CrZero

open GlobalTheory.CrZero in

theorem GlobalTheory.BKLim.acris_frob_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d c : ℕ)
    (D₀ F F' : Matrix (Fin d) (Fin d) (Per.Acris l)),
    (∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ D₀ i j) →
    (l : Per.Acris l) ^ c • D₀ = F * D₀.map (phiA l) * F' → D₀ = 0 := by
  intro l _ K bk d c D₀ F F' hdiv hfr
  obtain ⟨htor, hcomp, -, hphi, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  set u := ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X with hu
  have hφu : phiA l u = u ^ l := by
    rw [hu, RingHom.comp_apply, hphi, ← bk.ev_frob]
    have : frobS l bk.a X = X ^ l := by simp [frobS]
    rw [this, map_pow, map_pow]
  have hφl : ∀ k : ℕ, phiA l ((l : Per.Acris l) ^ k) = (l : Per.Acris l) ^ k := by
    intro k; simp

  have key : ∀ n : ℕ, ∃ N : Matrix (Fin d) (Fin d) (Per.Acris l),
      (l : Per.Acris l) ^ (c * n) • D₀ = u ^ (l ^ n) • N := by
    intro n
    induction n with
    | zero =>
      refine ⟨Matrix.of fun i j => (hdiv i j).choose, ?_⟩
      ext i j
      simp only [mul_zero, pow_zero, pow_one, one_smul, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      rw [one_mul]; exact (hdiv i j).choose_spec
    | succ n ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨F * N.map (phiA l) * F', ?_⟩
      have hmap : ((l : Per.Acris l) ^ (c * n) • D₀).map (phiA l)
          = (l : Per.Acris l) ^ (c * n) • D₀.map (phiA l) := by
        ext i j; simp [hφl]
      have hmap2 : (u ^ (l ^ n) • N).map (phiA l) = u ^ (l ^ (n + 1)) • N.map (phiA l) := by
        ext i j; simp [hφu, ← pow_mul]; ring
      calc (l : Per.Acris l) ^ (c * (n + 1)) • D₀
          = (l : Per.Acris l) ^ (c * n) • ((l : Per.Acris l) ^ c • D₀) := by
            rw [smul_smul, ← pow_add, mul_add, mul_one]
        _ = F * (((l : Per.Acris l) ^ (c * n) • D₀).map (phiA l)) * F' := by
            rw [hfr, hmap, Matrix.mul_smul, Matrix.smul_mul]
        _ = u ^ (l ^ (n + 1)) • (F * N.map (phiA l) * F') := by
            rw [hN, hmap2, Matrix.mul_smul, Matrix.smul_mul]
  ext i j
  have hH : IsHausdorff (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) := hcomp.toIsHausdorff
  refine eq_zero_of_forall_dvd _ hH _ fun M => ?_
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.primePow_dvd_tiltUniformizer_pow_acris_eventually l K bk c M
  obtain ⟨N, hN⟩ := key n₀
  obtain ⟨y, hy⟩ := hn₀ n₀ le_rfl
  have hent : (l : Per.Acris l) ^ (c * n₀) * D₀ i j = u ^ (l ^ n₀) * N i j := by
    have := congrFun (congrFun hN i) j
    simpa using this
  have hpos : 1 ≤ l ^ n₀ := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  have hsplit : u ^ (l ^ n₀) = u * u ^ (l ^ n₀ - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  refine ⟨u * y * N i j, ?_⟩
  apply pow_cancel _ htor (c * n₀)
  rw [hent, hsplit, hy]
  ring
