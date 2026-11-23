import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableAtDerivAtZero
import Formalism.GL3MeanSquares.HookFormulaTorsion.FourFoldOrthogonalSum
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.HalfPeriodValue

open Formalism.MainNotions.StandardLatticesGL3 (wpF cj FixK rhoBar StarPt w0 InRationalLattice)

theorem wpF_add_of_mem {Λ : AddSubgroup ℂ} (h : GlobalTheory.ThetaConj.IsLat Λ) {z ω : ℂ} (hz : z ∉ Λ)
    (hω : ω ∈ Λ) : wpF Λ (z + ω) = wpF Λ z := by
  obtain ⟨L, hL⟩ := h.exists_periodPair
  have hd := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  have hzω : z + ω ∉ Λ := fun hh => hz (by simpa using Λ.sub_mem hh hω)
  rw [(hd.2.2.2.2.1 _ hzω).1, (hd.2.2.2.2.1 _ hz).1]
  exact L.weierstrassP_add_coe z ⟨ω, (hL ω).1 hω⟩

theorem cmGenerator_mul_mem_curveLattice {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) :
    ∀ z ∈ lamOf D cc δ, w0 D * z ∈ lamOf D cc δ := by
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  rw [← ha]
  exact (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.2.2.2 a

theorem key_of_fix {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ)
    (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (hK : FixK D ⊤ ρ) {t t' : ℂ}
    (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t)
    (ht' : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ ρ (lamOf D cc δ)) t') :
    t' ∉ lamConj ⊤ ρ (lamOf D cc δ) ∧
      wpF (lamConj ⊤ ρ (lamOf D cc δ)) t' = cj ⊤ ρ (wpF (lamOf D cc δ) t) := by
  obtain ⟨hex, -, -, -, hmul, hord, -⟩ :=
    GlobalTheory.T.galStar_complexMultiplication_points D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨cc', δ', h', -, hL⟩ :=
    GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top 1 one_pos
  rw [GlobalTheory.ThetaConj.twoTorsionCMPoint_iff] at ht ht'
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have ha' : D.host.φ₀ ((((1 - a : 𝓞 D.host.K) : D.host.K) : D.host.E)) = 1 - w0 D := by
    rw [← ha]
    change D.host.φ₀ (algebraMap D.host.K D.host.E (algebraMap (𝓞 D.host.K) D.host.K (1 - a))) = _
    rw [map_sub, map_sub, map_sub, map_one, map_one, map_one]
    rfl
  have htn : t ∉ lamOf D cc δ := fun hh => ht.2.1 (cmGenerator_mul_mem_curveLattice h _ hh)
  obtain ⟨t'', ht''⟩ := hex t ⟨2, by norm_num, by exact_mod_cast ht.1⟩
    (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)
  have e2 := (hord 2 _ _ ht'').1 (by exact_mod_cast ht.1)
  have ea := (hord 1 _ _ (hmul a _ _ ht'')).2
  have eb := (hord 1 _ _ (hmul (1 - a) _ _ ht'')).2
  rw [ha] at ea
  rw [ha'] at eb
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at e2 ea eb
  obtain ⟨k, hk⟩ := GlobalTheory.ThetaConj.weylMatrix_mul_apply D
  have hlat : GlobalTheory.ThetaConj.IsLat (lamConj ⊤ ρ (lamOf D cc δ)) := hL ▸ GlobalTheory.ThetaConj.isLat_lamOf h'
  have hdiff : t' - t'' ∈ lamConj ⊤ ρ (lamOf D cc δ) :=
    GlobalTheory.ThetaConj.two_torsion_unique hlat (w0 D) k hk ht'.1 ht'.2.1 ht'.2.2 e2
      (fun hh => ht.2.1 (ea hh)) (fun hh => ht.2.2 (eb hh)) (by rw [hL]; exact cmGenerator_mul_mem_curveLattice h')
  rcases ht'' with ⟨hin, -⟩ | ⟨-, hn'', -, -, hwp, -⟩
  · exact absurd hin htn
  · refine ⟨fun hh => hn'' (by simpa using (lamConj ⊤ ρ (lamOf D cc δ)).sub_mem hh hdiff), ?_⟩
    rw [← hwp, ← wpF_add_of_mem hlat hn'' hdiff, add_sub_cancel]

theorem wpF_conj (Λ : AddSubgroup ℂ) (z : ℂ) :
    wpF (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ z) = starRingEnd ℂ (wpF Λ z) := by
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃
      {w : ℂ // w ∈ Λ.map (starRingEnd ℂ).toAddMonoidHom ∧ w ≠ 0} :=
    { toFun := fun w => ⟨starRingEnd ℂ w, by rw [GlobalTheory.ThetaConj.mem_conj, Complex.conj_conj]; exact w.2.1,
        by simpa using w.2.2⟩
      invFun := fun w => ⟨starRingEnd ℂ w, GlobalTheory.ThetaConj.mem_conj.1 w.2.1, by simpa using w.2.2⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  unfold wpF
  rw [map_add, Complex.conj_tsum, ← e.tsum_eq]
  simp [e, map_sub]
  rfl

theorem key_top {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ)
    (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) {t t' : ℂ}
    (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t)
    (ht' : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ ρ (lamOf D cc δ)) t') :
    t' ∉ lamConj ⊤ ρ (lamOf D cc δ) ∧
      wpF (lamConj ⊤ ρ (lamOf D cc δ)) t' = cj ⊤ ρ (wpF (lamOf D cc δ) t) := by
  obtain ⟨hK, hT, -⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ h ⊤ ρ
    ⟨fun _ _ => IntermediateField.mem_top, IntermediateField.mem_top, IntermediateField.mem_top⟩
  rcases hK with hK | hK
  · exact key_of_fix h ρ hK ht ht'
  · have hL : lamConj ⊤ (rhoBar ⊤ ρ) (lamOf D cc δ) =
        (lamConj ⊤ ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom := congrArg Tor.abelian₂ hT
    obtain ⟨hn, hw⟩ := key_of_fix h _ hK (t' := starRingEnd ℂ t') ht (hL ▸ GlobalTheory.ThetaConj.twoTorsionCMPoint_complexConj ht')
    rw [hL, wpF_conj, GlobalTheory.ThetaConj.cj_rhoBar] at hw
    rw [hL, GlobalTheory.ThetaConj.mem_conj, Complex.conj_conj] at hn
    exact ⟨hn, (starRingEnd ℂ).injective hw⟩

theorem halfPeriod_value : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t →
    ∃ e g : M, (g : ℂ) = g2 (lamOf D cc δ) ∧ lamConj M M.val (lamOf D cc δ) = lamOf D cc δ ∧
      ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧
        g2 (lamConj M ρ (lamOf D cc δ)) = ρ g ∧ t ρ ∉ lamConj M ρ (lamOf D cc δ) ∧
        Formalism.MainNotions.StandardLatticesGL3.wpF (lamConj M ρ (lamOf D cc δ)) (t ρ) = ρ e := by
  intro D cc δ M _ t hS
  obtain ⟨hcc, hδ, hdata, ht⟩ := hS
  have h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hg2 : g2 (lamOf D cc δ) ∈ M := hdata.2.1
  have hg3 : g3 (lamOf D cc δ) ∈ M := hdata.2.2
  have hlat := GlobalTheory.ThetaConj.isLat_lamOf h
  have hdisc : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 :=
    (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.2.1
  have hself : lamConj M M.val (lamOf D cc δ) = lamOf D cc δ :=
    GlobalTheory.ThetaConj.lamConj_eq_self hlat
      (by unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM; rw [dif_pos hg2]; rfl)
      (by unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM; rw [dif_pos hg3]; rfl)
  have ht0 : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) (t M.val) := by
    have := ht M.val
    rw [hself] at this
    exact this
  have he : wpF (lamOf D cc δ) (t M.val) ∈ M := by
    obtain ⟨y, hy⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := M)
      (wpF (lamOf D cc δ) (t M.val)) (fun σ => by
        have hσ : ∀ z ∈ M, cj ⊤ (GlobalTheory.ThetaConj.topHom (σ : ℂ →+* ℂ)) z = z := fun z hz => by
          rw [GlobalTheory.ThetaConj.cj_top]; exact σ.commutes ⟨z, hz⟩
        have hL := GlobalTheory.ThetaConj.lamConj_eq_self hlat (hσ _ hg2) (hσ _ hg3)
        have := (key_top h (GlobalTheory.ThetaConj.topHom (σ : ℂ →+* ℂ)) ht0 (by rw [hL]; exact ht0)).2
        rw [hL, GlobalTheory.ThetaConj.cj_top] at this
        exact this.symm)
    rw [← hy]
    exact y.2
  have hg2M : Formalism.MainNotions.TaylorLogMetric.liftM M (g2 (lamOf D cc δ)) = ⟨_, hg2⟩ := by simp [Formalism.MainNotions.TaylorLogMetric.liftM, hg2]
  have hg3M : Formalism.MainNotions.TaylorLogMetric.liftM M (g3 (lamOf D cc δ)) = ⟨_, hg3⟩ := by simp [Formalism.MainNotions.TaylorLogMetric.liftM, hg3]
  have hone : (⟨_, hg2⟩ : M) ^ 3 - 27 * (⟨_, hg3⟩ : M) ^ 2 = 1 :=
    by
    have := hdisc
    unfold Formalism.MainNotions.TaylorLogMetric.discr at this
    ext; push_cast; exact this
  refine ⟨⟨_, he⟩, ⟨_, hg2⟩, rfl, hself, fun ρ => ?_⟩
  have hρ1 : ρ ⟨_, hg2⟩ ^ 3 - 27 * ρ ⟨_, hg3⟩ ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hone, map_one]
  have hspec : g2 (lamConj M ρ (lamOf D cc δ)) = ρ ⟨_, hg2⟩ ∧
      g3 (lamConj M ρ (lamOf D cc δ)) = ρ ⟨_, hg3⟩ := by
    obtain ⟨L0, hL0⟩ := hlat.exists_periodPair
    obtain ⟨L', h2', h3'⟩ := (GlobalTheory.LatticeInvariants.invariants_dictionary L0 _ hL0).2.2.2.2.2.2 _ _
      (by rw [hρ1]; exact one_ne_zero)
    have hw := GlobalTheory.LatticeInvariants.invariants_dictionary L' L'.lattice.toAddSubgroup (fun _ => Iff.rfl)
    have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
      g2 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (g2 (lamOf D cc δ))) ∧
        g3 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (g3 (lamOf D cc δ))))
      ⟨L'.lattice.toAddSubgroup, by rw [hw.1, h2', hg2M], by rw [hw.2.1, h3', hg3M]⟩
    exact ⟨hs.1.trans (congrArg ρ hg2M), hs.2.trans (congrArg ρ hg3M)⟩
  have hcM : Set.Countable (M : Set ℂ) := (Algebraic.countable ℚ ℂ).mono fun x hx =>
    show IsAlgebraic ℚ x from
      (IntermediateField.isAlgebraic_iff (x := (⟨x, hx⟩ : M))).mp (Algebra.IsAlgebraic.isAlgebraic _)
  haveI : Countable M := hcM.to_subtype
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (K := M) M.val.toRingHom ρ.toRingHom
  have hcj : ∀ z (hz : z ∈ M), cj M ρ z = cj ⊤ (GlobalTheory.ThetaConj.topHom σ.toRingHom) z := fun z hz => by
    rw [GlobalTheory.ThetaConj.cj_of_mem _ _ hz, GlobalTheory.ThetaConj.cj_top]
    exact (hσ ⟨z, hz⟩).symm
  have hL : lamConj M ρ (lamOf D cc δ) = lamConj ⊤ (GlobalTheory.ThetaConj.topHom σ.toRingHom) (lamOf D cc δ) :=
    GlobalTheory.ThetaConj.lamConj_congr (hcj _ hg2) (hcj _ hg3)
  have ht' : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ (GlobalTheory.ThetaConj.topHom σ.toRingHom) (lamOf D cc δ)) (t ρ) := by
    have := ht ρ
    rw [hL] at this
    exact this
  obtain ⟨hn, hw⟩ := key_top h (GlobalTheory.ThetaConj.topHom σ.toRingHom) ht0 ht'
  refine ⟨?_, hspec.1, hL ▸ hn, ?_⟩
  · unfold Formalism.MainNotions.TaylorLogMetric.discr
    rw [hspec.1, hspec.2, hρ1]
  · rw [hL, hw, GlobalTheory.ThetaConj.cj_top]
    exact hσ ⟨_, he⟩

end GlobalTheory.HalfPeriodValue
