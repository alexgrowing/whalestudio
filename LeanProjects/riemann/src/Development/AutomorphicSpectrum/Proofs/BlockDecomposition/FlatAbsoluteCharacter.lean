import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

open GlobalTheory.Mem.Chr.CharModel

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem logFin_eq_zero_of_integral (t : (Af E)ˣ)
    (h1 : (t : Af E) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E)
    (h2 : ((t⁻¹ : (Af E)ˣ) : Af E) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) : logFin E t = 0 := by
  have : GlobalTheory.Idele.idealOf t = 1 := by
    rw [← GlobalTheory.Idele.smul_one_eq, GlobalTheory.Idele.smul_eq_self_iff t one_ne_zero]
    intro v
    have e := congrArg Valued.v (GlobalTheory.Idele.idele_apply_mul_inv t v)
    rw [map_mul, map_one] at e
    have a1 : Valued.v ((t : Af E) v) ≤ 1 := GroundTheory.Global.mem_integralFiniteAdeles.1 h1 v
    have a2 : Valued.v (((t⁻¹ : (Af E)ˣ) : Af E) v) ≤ 1 := GroundTheory.Global.mem_integralFiniteAdeles.1 h2 v
    refine le_antisymm a1 ?_
    rw [← e]
    exact mul_le_of_le_one_right' a2
  simp [logFin, this]

theorem det_mem_of_entries {R : Type*} [CommRing R] (S : Subring R) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ a b, M a b ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

theorem logFin_det_of_mem {N : ℕ} {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    logFin E (GeneralLinearGroup.det c) = 0 := by
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E N).1 hc
  refine logFin_eq_zero_of_integral _ (det_mem_of_entries _ _ h1) ?_
  rw [← map_inv]
  exact det_mem_of_entries _ _ h2

theorem logNorm_finId (u : (Af E)ˣ) : logNorm E (finId E u) = - logFin E u := by
  have h1 : finPart E (finId E u) = u := Units.ext (by
    change (1 : Af E) - 1 + u = u
    simp)
  have h2 : infPart E (finId E u) = 1 := Units.ext (by
    change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp)
  rw [logNorm, h1, h2, logInf_one, zero_sub]

theorem norm_det_unitary_at {N : ℕ} (k : Kinf E N) (v : InfinitePlace E) :
    ‖((GeneralLinearGroup.det (Unitary.toUnits k) : (Cinf E)ˣ) : Cinf E) v‖ = 1 := by
  have hd : (k : Matrix (Fin N) (Fin N) (Cinf E)).det ∈ unitary (Cinf E) := Matrix.det_of_mem_unitary k.2
  have h : star ((k : Matrix (Fin N) (Fin N) (Cinf E)).det v) * (k : Matrix (Fin N) (Fin N) (Cinf E)).det v = 1 :=
    congrFun (Unitary.star_mul_self_of_mem hd) v
  have h2 := congrArg norm h
  rw [norm_mul, norm_star, norm_one] at h2
  exact (mul_self_eq_one_iff.1 h2).resolve_right (by linarith [norm_nonneg ((k : Matrix (Fin N) (Fin N) (Cinf E)).det v)])

theorem logNorm_det_cf (N : ℕ) (k : Kinf E N) {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    logNorm E (GeneralLinearGroup.det (cf N k c)) = 0 := by
  rw [cf, map_mul, logNorm_mul, det_infGL, det_finGL, Model.logNorm_infId, logNorm_finId, logFin_det_of_mem hc,
    Finset.sum_eq_zero fun v _ => by rw [norm_det_unitary_at, Real.log_one, mul_zero]]
  simp

theorem chiDet_absC_cf (N : ℕ) (w : ℂ) (k : Kinf E N) {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    chiDet N (GlobalTheory.CuspRep.Model.absC E w) (cf N k c) = 1 := by
  apply Units.ext
  change Complex.exp (w * (logNorm E (GeneralLinearGroup.det (cf N k c)) : ℂ)) = 1
  rw [logNorm_det_cf N k hc]
  simp

end

theorem absFn_flat : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (w : ℂ),
    FlatFn (absFn (E := E) N w) := by
  intro E _ _ _ N w
  refine ⟨fun x => Units.ne_zero _, fun x k c hc => ?_, ?_⟩
  · simp only [absFn, map_mul, chiDet_absC_cf N w k hc, mul_one]
  · have h : absFn (E := E) N w = (mulChi N (GlobalTheory.CuspRep.Model.absC E w) (oneFn E N)).1 := funext fun x => by
      rw [mulChi_apply]
      simp [absFn, oneFn]
    rw [h]
    exact (mulChi N (GlobalTheory.CuspRep.Model.absC E w) (oneFn E N)).2

end GlobalTheory.CompanionTheory.LimV

end
