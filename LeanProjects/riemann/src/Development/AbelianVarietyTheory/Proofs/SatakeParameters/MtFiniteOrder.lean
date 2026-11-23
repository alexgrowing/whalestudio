import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharFiniteOrderUnitIdele

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.L2.Forms

noncomputable section

namespace GlobalTheory.TieFinOrd

set_option maxHeartbeats 4000000 in

theorem mt_finite_order : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m, ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E → ∃ n : ℕ, 0 < n ∧ (t.O u μ).mt (i + 1) (dtU y) ^ n = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H T i hi y hint
  classical
  letI := D.host.cmStar
  have hzU : Matrix.GeneralLinearGroup.det y.1 ∈ U1 (sigD D) := det_in_unitary_one D.host.F D.host.E (sigD D) 1 1 (by simp) y.1 y.2
  set z := Matrix.GeneralLinearGroup.det y.1 with hz
  have hconj : conjId (sigD D) z = z⁻¹ := by
    have h1 : z * conjId (sigD D) z = 1 := hzU
    exact eq_inv_of_mul_eq_one_right h1
  have hh90 : h90 (sigD D) z = Matrix.GeneralLinearGroup.det (y * y).1 := by
    show z / conjId (sigD D) z = _
    rw [hconj, div_inv_eq_mul]
    show _ = Matrix.GeneralLinearGroup.det (y.1 * y.1)
    rw [map_mul]
  set x : (AfE t.X.F t.X.E)ˣ := Units.map A.iA.symm.toRingHom.toMonoidHom z with hxdef
  have hxx : Units.map A.iA.toRingHom.toMonoidHom x = z := by
    ext
    simp [x]
  have hq : A.q x = dtU (y * y) := H.q_dt x (y * y) (by rw [hxx, hh90])
  have hcoe : ∀ w : AfE t.X.F t.X.E, A.iA w ∈ RInt D.host.F D.host.E ↔ w ∈ RInt t.X.F t.X.E := H.iA_int
  have hxint : x ∈ intU t.X.F t.X.E := by
    refine ⟨(hcoe _).1 ?_, (hcoe _).1 ?_⟩
    · simpa [x] using hint.1
    · simpa [x] using hint.2
  have hiso : IsAdIso (GlobalTheory.Mem.Col2.afIso t.X.F t.X.E) :=
    ⟨GlobalTheory.Mem.Col2.afIso_tmul_one _ _, GlobalTheory.Mem.Col2.mem_rInt_iff _ _⟩
  have hmu : ∃ n : ℕ, 0 < n ∧ D.muTil (i + 1) (A.q x) ^ n = 1 := by
    rw [H.muTil _ hiso ⟨i, hi⟩ (GlobalTheory.Mem.ReadEx.toIdl t.X.F t.X.E x) x (fun w => rfl) (GlobalTheory.Mem.ReadEx.toIdl_snd x).symm]
    exact GlobalTheory.HeckeFin.finite_order _ _ _ (fun w => rfl) ((GlobalTheory.Mem.ReadEx.mem_intU_iff x).1 hxint)
  obtain ⟨n, hn, hmun⟩ := hmu
  have hsq : (t.O u μ).mt (i + 1) (dtU y) ^ 2 = (t.O u μ).mt (i + 1) (A.q x) := by
    rw [hq, map_mul, map_mul, sq]
  by_cases hμ : μ = D.what₂.mu0
  · refine ⟨2 * n, by omega, ?_⟩
    rw [pow_mul, hsq, (H.ref hμ).2]
    exact hmun
  · obtain ⟨ξ, hξ, hmt⟩ := H.tw μ hμ rfl
    have htor := (t.tup μ).2
    simp only [tupGrp, finChar, Subgroup.mem_inf] at htor
    obtain ⟨k, hk, hkk⟩ := (isOfFinOrder_iff_pow_eq_one).1 htor.1.1.1.2
    refine ⟨2 * (n * k), by positivity, ?_⟩
    rw [pow_mul, hsq, hmt u, twMt, if_pos ⟨by omega, by omega⟩, MonoidHom.mul_apply, mul_pow, pow_mul, hmun, one_pow, one_mul,
      hξ x, ← map_pow, mul_comm, pow_mul]
    have : ((t.tup μ : Chr t.X.F t.X.E t.X.K) x) ^ k = 1 := by
      rw [← MonoidHom.pow_apply, hkk, MonoidHom.one_apply]
    rw [this, one_pow, map_one]

end GlobalTheory.TieFinOrd
