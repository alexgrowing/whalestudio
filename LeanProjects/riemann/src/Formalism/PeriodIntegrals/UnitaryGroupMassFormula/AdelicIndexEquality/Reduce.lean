import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LiftMatMapSame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionB
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S

theorem glob_bound (I : AutInst) (x : I.Gf) :
    ∃ N : ℕ, 0 < N ∧ (∀ w ∈ I.Lf, N • (I.fmat x *ᵥ w) ∈ I.Lf) ∧
      (∀ w ∈ I.Lf, N • (I.fmat x⁻¹ *ᵥ w) ∈ I.Lf) := by
  obtain ⟨k, m, hm, hgen⟩ := PI.WAU.B.exists_gen I.L (Module.Finite.iff_fg.mpr I.L_fg)
  obtain ⟨N, hN⟩ := PI.WAU.B.exists_PN I m x
  refine ⟨N, hN.1, fun w hw => ?_, fun w hw => ?_⟩
  · have := PI.WAU.B.mulVec_lam hm hgen (N • I.fmat x)
      (fun j => by rw [Matrix.smul_mulVec]; exact (hN.2 j).1) hw
    rwa [Matrix.smul_mulVec] at this
  · have := PI.WAU.B.mulVec_lam hm hgen (N • I.fmat x⁻¹)
      (fun j => by rw [Matrix.smul_mulVec]; exact (hN.2 j).2) hw
    rwa [Matrix.smul_mulVec] at this

theorem cancel_nat {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (hN : Valued.v ((N : v.adicCompletion F)) = 1) {M : Type} [AddCommGroup M]
    [Module (v.adicCompletionIntegers F) M] (P : Submodule (v.adicCompletionIntegers F) M) {y : M}
    (h : N • y ∈ P) : y ∈ P := by
  have ha : (N : v.adicCompletion F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hN
    exact zero_ne_one hN
  let c : v.adicCompletionIntegers F :=
    ⟨(N : v.adicCompletion F)⁻¹, by rw [mem_adicCompletionIntegers, map_inv₀, hN, inv_one]⟩
  have hc : c * (N : v.adicCompletionIntegers F) = 1 := by
    apply Subtype.ext
    simp [c, ha]
  have h' : (N : v.adicCompletionIntegers F) • y ∈ P := by
    rwa [Nat.cast_smul_eq_nsmul]
  have := P.smul_mem c h'
  rwa [smul_smul, hc, one_smul] at this

theorem vecV_nsmul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (N : ℕ)
    (u : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (N • u) = N • PI.FinKW.vecV I v u := by
  funext i
  simp [PI.FinKW.vecV]

theorem loc_stab (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (Mx : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) {N : ℕ}
    (hv : Valued.v ((N : v.adicCompletion I.F)) = 1)
    (hM : ∀ w ∈ I.Lf, N • (Mx *ᵥ w) ∈ I.Lf) (z : Fin I.n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)
    (hz : z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    Mx.map (PI.FinKW.psiV I v).toRingHom *ᵥ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
  obtain ⟨w, hwv, hww⟩ := PI.FinKW.local_vector_lift I v z
  have hw : w ∈ I.Lf := PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective I w (fun u => by
    by_cases hu : u = v
    · subst hu
      rwa [hwv]
    · rw [hww u hu]
      exact zero_mem _)
  have h1 := PI.FinKW.LocTo.mem_local_lattice_iff I _ (hM w hw) v
  rw [vecV_nsmul, vecV_mulVec', hwv] at h1
  exact cancel_nat v hv _ h1

theorem finite_bad (I : AutInst) (x : I.Gf) :
    {v | matV I v (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∉ Kv I v}.Finite := by
  obtain ⟨N, hN0, h1, h2⟩ := glob_bound I x
  apply (Formalism.UG.P.levelaf_finite_places (F := I.F) (N : 𝓞 I.F) (by exact_mod_cast hN0.ne')).subset
  intro v hv
  by_contra hlt
  apply hv
  have hle := (mem_adicCompletionIntegers _ _ _).1 (Formalism.UG.P.levelaf_int_mem_v (F := I.F) v (N : 𝓞 I.F))
  rw [map_natCast] at hle
  have hval : Valued.v ((N : v.adicCompletion I.F)) = 1 := by
    refine le_antisymm hle (not_lt.mp ?_)
    simpa [map_natCast] using hlt
  have hinv : (I.fmat x⁻¹).map (PI.FinKW.psiV I v).toRingHom *
      (I.fmat x).map (PI.FinKW.psiV I v).toRingHom = 1 := by
    rw [← Matrix.map_mul, PI.WAU.B.fmat_inv_mul]
    simp
  intro z
  rw [matV_coe]
  constructor
  · exact loc_stab I v _ hval h1 z
  · intro hz
    have := loc_stab I v _ hval h2 _ hz
    rwa [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at this

theorem matV_inv_mul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (y x : I.Gf) :
    matV I v ((y⁻¹ * x : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) =
      (matV I v (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)))⁻¹ * matV I v (x : GL (Fin I.n) _) := by
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]

theorem reduce_aux (I : AutInst) (S : Finset (HeightOneSpectrum (𝓞 I.F))) :
    ∀ x : I.Gf, (∀ v, v ∉ S → matV I v (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Kv I v) →
      x ∈ Subgroup.closure ({y | ∃ v, SuppAt I v y} ∪ (PI.AdIndexEq.Ksub I : Set I.Gf)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro x hx
    apply Subgroup.subset_closure
    right
    exact (compact_local_global I x).2 (fun v => hx v (by simp))
  | insert a S ha ih =>
    intro x hx
    obtain ⟨y, hy, hsupp⟩ := lift_unitary' I a _ (matrix_v_unitary I a x)
    have hx' := ih (y⁻¹ * x) (fun v hv => by
      rw [matV_inv_mul]
      by_cases hva : v = a
      · subst hva
        rw [hy, inv_mul_cancel]
        exact one_mem _
      · rw [hsupp v hva, inv_one, one_mul]
        exact hx v (by simp [hva, hv]))
    have hyc : y ∈ Subgroup.closure ({y | ∃ v, SuppAt I v y} ∪ (PI.AdIndexEq.Ksub I : Set I.Gf)) :=
      Subgroup.subset_closure (Or.inl ⟨a, hsupp⟩)
    have := mul_mem hyc hx'
    rwa [mul_inv_cancel_left] at this

theorem reduce_local : ReduceLoc := by
  intro I x
  have hfin := finite_bad I x
  exact reduce_aux I hfin.toFinset x (fun v hv => by
    by_contra h
    exact hv (hfin.mem_toFinset.2 h))

end PI.UnitaryGroupMassFormula.AdIndexEq

end
