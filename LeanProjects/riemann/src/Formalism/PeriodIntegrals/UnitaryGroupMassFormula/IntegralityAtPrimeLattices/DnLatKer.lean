import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.StabiliserOfLocalTransport

noncomputable section

open NumberField Ideal IsDedekindDomain

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Matrix Formalism.UG

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem cls_tLd (K : ClsTied u i hi) (c : (D.mem u).C.cls i) (y : Fin (D.R.N i) → D.host.E) (hy : y ∈ Ld D u i hi c) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y ∈ clsCrd D u i hi c := by
  have hM : clsCrd D u i hi c = Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb :=
    Formalism.L2.GlobalTheoryTheory.Comp.eq_glob_of_hat (tld_isLat i hi c) (K.y c).1 (fun w => K.y_lat c w)
  rw [dual_class_lattice_eq_global K c] at hy
  rw [hM]
  have key : Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb ≤
      K.lev.Lb.comap ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • LinearMap.id) := by
    unfold Formalism.L2.GlobalTheoryTheory.Comp.dl
    refine Submodule.span_le.mpr ?_
    intro z hz
    have h2 := K.lev.Lb_dual z hz
    simpa [Nat.cast_smul_eq_nsmul] using h2
  have hG : ∀ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb,
      ((((D.mem u).A.T : ℕ) : D.host.E) • (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)) *ᵥ x ∈
        K.lev.Lb := by
    intro x hx
    have h2 := key hx
    simp only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] at h2
    have h3 : ((((D.mem u).A.T : ℕ) : D.host.E) • (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)) *ᵥ x =
        (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • x := by
      ext j
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    rw [h3]
    exact h2
  have hy' : ((((K.y c).1)⁻¹ : GL _ _) : Matrix _ _ _) *ᵥ Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.vi D.host.F y ∈
      Formalism.L2.GlobalTheoryTheory.Comp.hat D.host.F (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb) := hy
  have h1 := Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.hat_fwd _ hG _ hy'
  show ((((K.y c).1)⁻¹ : GL _ _) : Matrix _ _ _) *ᵥ
      Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.vi D.host.F ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y) ∈
    Formalism.L2.GlobalTheoryTheory.Comp.hat D.host.F K.lev.Lb
  convert h1 using 1
  have hv : Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.vi D.host.F ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y) =
      ((D.mem u).A.T) • Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.vi D.host.F y := by
    ext k
    simp [Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.vi, Nat.cast_smul_eq_nsmul]
  have hGm : ∀ w : Fin (D.R.N i) → TensorProduct D.host.F D.host.E (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      ((((D.mem u).A.T : ℕ) : D.host.E) • (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map
        (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) *ᵥ w = ((D.mem u).A.T) • w := by
    intro w
    ext k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, apply_ite, map_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, map_natCast, Pi.smul_apply, nsmul_eq_mul]
  rw [hv, hGm, Matrix.mulVec_smul]

set_option maxHeartbeats 1000000 in

theorem lk_locP (A : AtTTied u) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Lk A i hi v c) = Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (clsCrd D u i hi c) := by
  apply le_antisymm
  · obtain ⟨s, hs, h⟩ := unr_smul A v
    intro x hx
    obtain ⟨r, hr, hrx⟩ := (rlv_mem_locP _ _ _).1 hx
    obtain ⟨l, hl, m, hm, ex⟩ := Submodule.mem_sup.1 hrx
    obtain ⟨y, hy, ey⟩ := h (Ld D u i hi c) m hm
    refine (rlv_mem_locP _ _ _).2 ⟨s * r, fun h' => (Ideal.IsPrime.mem_or_mem inferInstance h').elim hs hr, ?_⟩
    rw [mul_smul, ← ex, smul_add, ey]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hl) (cls_tLd K c y hy)
  · intro x hx
    obtain ⟨r, hr, hrx⟩ := (rlv_mem_locP _ _ _).1 hx
    exact (rlv_mem_locP _ _ _).2 ⟨r, hr, Submodule.mem_sup_left hrx⟩

end PI.UnitaryGroupMassFormula.IAT

end
