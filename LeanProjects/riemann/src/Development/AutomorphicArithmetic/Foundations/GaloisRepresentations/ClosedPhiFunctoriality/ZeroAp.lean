import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFrobeniusMatrixEqZeroOfDvd
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.zeroAp_holds :
    ZeroAp := by
  intro l _ K bk c M
  obtain ⟨htor, -, -, hphi, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.primePow_dvd_tiltUniformizer_pow_acris_eventually l K bk c M
  refine ⟨c * n₀ + M, ?_⟩
  intro d d' D F F' hdiv hcong
  have hdiv' : ∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ D i j := hdiv
  set u := ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X with hu
  have hφu : phiA l u = u ^ l := by
    rw [hu, RingHom.comp_apply, hphi, ← bk.ev_frob]
    have : frobS l bk.a X = X ^ l := by simp [frobS]
    rw [this, map_pow, map_pow]
  have hφl : ∀ k : ℕ, phiA l ((l : Per.Acris l) ^ k) = (l : Per.Acris l) ^ k := by
    intro k; simp
  set P : Per.Acris l := (l : Per.Acris l) ^ (c * n₀ + M) with hP
  have hφP : phiA l P = P := hφl _
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin d) (Fin d') (Per.Acris l),
      (l : Per.Acris l) ^ c • D = F * D.map (phiA l) * F' + P • G := by
    refine ⟨Matrix.of fun i j => (hcong i j).choose, ?_⟩
    ext i j
    have h := (hcong i j).choose_spec
    rw [Matrix.add_apply, Matrix.smul_apply (P), Matrix.of_apply, smul_eq_mul, ← h,
      Matrix.sub_apply]
    ring
  have key : ∀ t : ℕ, ∃ N H : Matrix (Fin d) (Fin d') (Per.Acris l),
      (l : Per.Acris l) ^ (c * t) • D = u ^ (l ^ t) • N + P • H := by
    intro t
    induction t with
    | zero =>
      refine ⟨Matrix.of fun i j => (hdiv' i j).choose, 0, ?_⟩
      ext i j
      simp only [mul_zero, pow_zero, pow_one, one_smul, smul_zero, add_zero, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul]
      rw [one_mul]
      exact (hdiv' i j).choose_spec
    | succ t ih =>
      obtain ⟨N, H, hNH⟩ := ih
      refine ⟨F * N.map (phiA l) * F', F * H.map (phiA l) * F' + (l : Per.Acris l) ^ (c * t) • G, ?_⟩
      have hmap : ((l : Per.Acris l) ^ (c * t) • D).map (phiA l)
          = (l : Per.Acris l) ^ (c * t) • D.map (phiA l) := by
        ext i j; simp [hφl]
      have hmap2 : (u ^ (l ^ t) • N + P • H).map (phiA l)
          = u ^ (l ^ (t + 1)) • N.map (phiA l) + P • H.map (phiA l) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
          map_mul, map_pow, hφu, hφP]
        rw [← pow_mul, pow_succ' l t]
      calc (l : Per.Acris l) ^ (c * (t + 1)) • D
          = (l : Per.Acris l) ^ (c * t) • ((l : Per.Acris l) ^ c • D) := by
            rw [smul_smul, ← pow_add, mul_add, mul_one]
        _ = F * (((l : Per.Acris l) ^ (c * t) • D).map (phiA l)) * F'
              + P • ((l : Per.Acris l) ^ (c * t) • G) := by
            rw [hG, hmap, smul_add, Matrix.mul_smul, Matrix.smul_mul, smul_comm P]
        _ = u ^ (l ^ (t + 1)) • (F * N.map (phiA l) * F')
              + P • (F * H.map (phiA l) * F' + (l : Per.Acris l) ^ (c * t) • G) := by
            rw [hNH, hmap2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
              Matrix.mul_smul, Matrix.smul_mul, smul_add, add_assoc]
  intro i j
  obtain ⟨N, H, hNH⟩ := key n₀
  obtain ⟨y, hy⟩ := hn₀ n₀ le_rfl
  have hent : (l : Per.Acris l) ^ (c * n₀) * D i j = u ^ (l ^ n₀) * N i j + P * H i j := by
    have := congrFun (congrFun hNH i) j
    simpa using this
  have hpos : 1 ≤ l ^ n₀ := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  have hsplit : u ^ (l ^ n₀) = u * u ^ (l ^ n₀ - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  refine ⟨u * y * N i j + H i j, ?_⟩
  apply GlobalTheory.CrZero.pow_cancel _ htor (c * n₀)
  rw [hent, hsplit, hy, hP, pow_add]
  ring
