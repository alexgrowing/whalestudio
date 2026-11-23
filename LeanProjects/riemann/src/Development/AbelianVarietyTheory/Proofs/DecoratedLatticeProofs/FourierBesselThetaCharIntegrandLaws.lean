import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionHomMulEmbeddedAnisotropic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTermsMeanZeroUnipotentRadical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FB.ThLaws

variable {D : D7}

theorem heisO_zero_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (p : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T p f 0 = f p := by
  rw [heisO, GlobalTheory.MixModel.symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]

theorem jacS_zero_apply (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (x : Mx D T.rank ρ) (n : GA D S) (f : WO S₀ T → ℂ) :
    jacS ψ d T x n f 0 = ψ (cenS d T x n) * f (ptS d T x n) := by
  rw [jacS, Pi.smul_apply, smul_eq_mul, heisO_zero_apply]

theorem jacS_nC (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (x : Mx D T.rank ρ) (c : skewA D ρ) (f : WO S₀ T → ℂ) : jacS ψ d T x (d.nC c) f = ψ (d.qS T c x) • f := by
  have h := ptS_nB_mul_nC d T x 0 c
  rw [d.nB_zero, one_mul, Matrix.mul_zero] at h
  rw [jacS, h, cenS_nC, heisO_zero]

theorem continuous_psiE {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) : Continuous (psiE ψ) := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact hψ.comp ht

theorem continuous_upSum {X : Type} [TopologicalSpace X] {ρ : ℕ} {T : X → Mx D ρ ρ} (hT : Continuous T) :
    Continuous fun t => upSum (T t) := by
  unfold upSum
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  by_cases h : j.1 = i.1 + 1
  · simp only [h, if_true]; exact (continuous_apply j).comp ((continuous_apply i).comp hT)
  · simp only [h, if_false]; exact continuous_const

theorem continuous_psiFlag {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {S S₀ : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) : Continuous (psiFlag ψ d) := by
  unfold psiFlag blockX
  exact (continuous_psiE hψ).comp
    (continuous_upSum (continuous_const.matrix_mul ((GlobalTheory.MixModel.continuous_mt S).matrix_mul continuous_const)))

theorem continuous_ptS {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ) :
    Continuous (ptS d T x) := by
  unfold ptS
  exact (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt S)).matrix_mul continuous_const

theorem continuous_cenS {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ) :
    Continuous (cenS d T x) := by
  unfold cenS
  exact GlobalTheory.OrientedHeis.continuous_symplOH continuous_const
    (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt S))

theorem exists_bound_quasi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S L : HSp D}
    {y : WO S L → ℂ} (hy : Quasi ψ S L y) : ∃ M : ℝ, ∀ w, ‖y w‖ ≤ M := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D L.rank S.rank
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hy.2.continuousOn
  refine ⟨C, fun w => ?_⟩
  obtain ⟨γ, ⟨γ0, rfl⟩, hγ⟩ := hKc w
  have h2 : ‖y w‖ = ‖y (ratW L S γ0 + w)‖ := by rw [hy.1 γ0 w, norm_mul, hψ.2.1, one_mul]
  rw [h2]
  exact hC _ hγ

theorem zl_rat {σ : ℕ} (B : BesLev D σ) :
    ∃ z0 : Matrix (Fin B.L.rank) (Fin (σ + 1)) D.host.E, zl B = rat z0 := by
  refine ⟨Matrix.vecMulVec B.ζ (fun i : Fin (σ + 1) => if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0), ?_⟩
  funext i j
  simp only [zl, zEll, rat, Matrix.map_apply, Matrix.vecMulVec_apply, ell, map_mul, ratV]
  congr 1
  split_ifs <;> simp

theorem ptS_rat {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x0 : Matrix (Fin T.rank) (Fin ρ) D.host.E)
    {γ : GA D S} (hγ : γ ∈ GQ S) : ∃ g0, ptS d T (rat x0) γ = ratW T S₀ g0 := by
  obtain ⟨g, hg⟩ := (GlobalTheory.MixModel.mem_GQ_iff S γ).1 hγ
  refine ⟨x0 * d.qX * g * d.i₀, ?_⟩
  rw [ratW_eq, ptS, HypDec.extX_apply, ← hg]
  simp only [rat_mul]
  rfl

theorem psi_cenS_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S S₀ : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) (T : HSp D) (x0 : Matrix (Fin T.rank) (Fin ρ) D.host.E) {γ : GA D S} (hγ : γ ∈ GQ S) :
    ψ (cenS d T (rat x0) γ) = 1 := by
  obtain ⟨g, hg⟩ := (GlobalTheory.MixModel.mem_GQ_iff S γ).1 hγ
  have e : cenS d T (rat x0) γ = symplOH S T ((x0 * d.qX).map (incA D)) ((x0 * d.qX * g).map (incA D)) := by
    rw [cenS, HypDec.extX_apply, ← hg]
    change _ = symplOH S T (rat (x0 * d.qX)) (rat (x0 * d.qX * g))
    simp only [rat_mul]
    rfl
  rw [e]
  exact GlobalTheory.AnisoMean.psi_rat hψ S T _ _

theorem upSum_rat {ρ : ℕ} (M : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    upSum (rat M : Mx D ρ ρ) = incA D (∑ i, ∑ j, if j.1 = i.1 + 1 then M i j else 0) := by
  simp only [upSum, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [rat]

theorem psiE_incA {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (t : D.host.E) : psiE ψ (incA D t) = 1 := by
  rw [psiE, show Algebra.trace (AF D.host.F) (AE D) (incA D t) =
    algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E t) from GlobalTheory.AnisoMean.trace_one_tmul (AF D.host.F) t]
  exact hψ.2.2.1 _

theorem psiFlag_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S S₀ : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) {γ : GA D S} (hγ : γ ∈ GQ S) : psiFlag ψ d γ = 1 := by
  obtain ⟨g, hg⟩ := (GlobalTheory.MixModel.mem_GQ_iff S γ).1 hγ
  have e : blockX d γ = rat (d.qX * (g * d.e)) := by
    rw [blockX, ← hg]
    simp only [rat_mul]
    rfl
  rw [psiFlag, e, upSum_rat, psiE_incA hψ]

theorem psiFlag_nC (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c : skewA D ρ) :
    psiFlag ψ d (d.nC c) = 1 := by
  rw [psiFlag, blockX_of_fix d (d.nC_jX c), upSum_one, psiE_zero]

theorem psiFlag_nB (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (b : Mx D ρ S₀.rank) :
    psiFlag ψ d (d.nB b) = 1 := by
  rw [psiFlag, blockX_of_fix d (d.nB_jX b), upSum_one, psiE_zero]

theorem psiFlag_levi (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) :
    psiFlag ψ d (d.levi u) = psiUni ψ u := by
  rw [psiFlag_eq, psiBes_levi]

theorem th_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (y : WO J.W₀ B.L → ℂ), Quasi ψ J.W₀ B.L y → Continuous (th J ψ B y) ∧ (∃ M : ℝ, (∀ w, ‖y w‖ ≤ M) ∧ ∀ n, ‖th J ψ B y n‖ ≤ M) ∧ (∀ γ ∈ flagN J.d, γ ∈ GQ J.W → ∀ n ∈ flagN J.d, th J ψ B y (γ * n) = th J ψ B y n) ∧ (∀ c, ∀ n ∈ flagN J.d, th J ψ B y (J.d.nC c * n) = star (ψ (J.d.qS B.L c (zl B))) * th J ψ B y n) ∧ (∀ n ∈ flagN J.d, ∀ u ∈ UX D (σ + 1), th J ψ B y (n * J.d.levi u) = th J ψ B y n * star (psiUni ψ u)) ∧ ∀ b, ∀ u ∈ UX D (σ + 1), th J ψ B y (J.d.nB b * J.d.levi u) = star (psiUni ψ u) * star (y (zl B ⬝ b)) := by
  intro D ψ hψs σ J B y hy
  have hψ : IsCharAF D.host.F ψ := hψs.1
  have hx : ∀ u ∈ UX D (σ + 1), zl B ⬝ u.1 = zl B := fun u hu => zEll_mul B.L B.ζ hu
  obtain ⟨hcen, hmul, hlevi, -⟩ := GlobalTheory.JacHom.jacS_hom D ψ J.W J.W₀ B.L (σ + 1) J.d (zl B) hx
  obtain ⟨M, hM⟩ := exists_bound_quasi hψ hy
  have hval : ∀ n, th J ψ B y n =
      star (ψ (cenS J.d B.L (zl B) n) * y (ptS J.d B.L (zl B) n)) * star (psiFlag ψ J.d n) := fun n => by
    rw [th, jacS_zero_apply]
  have hnorm : ∀ a, ‖ψ a‖ = 1 := hψ.2.1
  have hflag1 : ∀ n, ‖psiFlag ψ J.d n‖ = 1 := fun n => hnorm _
  refine ⟨?_, ⟨M, hM, fun n => ?_⟩, ?_, ?_, ?_, ?_⟩
  · have e : th J ψ B y = fun n =>
        star (ψ (cenS J.d B.L (zl B) n) * y (ptS J.d B.L (zl B) n)) * star (psiFlag ψ J.d n) := funext hval
    rw [e]
    exact (((hψ.1.comp (continuous_cenS _ _ _)).mul (hy.2.comp (continuous_ptS _ _ _))).star).mul
      (continuous_psiFlag hψ.1 _).star
  · rw [hval, norm_mul, norm_star, norm_star, norm_mul, hnorm, hflag1, one_mul, mul_one]
    exact hM _
  · intro γ hγN hγQ n hn
    obtain ⟨z0, hz0⟩ := zl_rat B
    have hp := hmul γ hγN n hn
    obtain ⟨g0, hg0⟩ := ptS_rat J.d B.L z0 hγQ
    rw [← hz0] at hg0
    have hc : ψ (cenS J.d B.L (zl B) γ) = 1 := by rw [hz0]; exact psi_cenS_rat hψ J.d B.L z0 hγQ
    rw [hval, hval, hp.1, hp.2.1, psiFlag_mul J.d ψ hγN hn, psiFlag_rat hψ J.d hγQ, one_mul, hg0, hy.1 g0]
    congr 2
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel_right, AddChar.map_add_eq_mul, hc, one_mul]
  · intro c n hn
    have hc : J.d.nC c ∈ flagN J.d := J.d.nC_mem_NFlag c
    rw [th, (hmul _ hc n hn).2.2, th, psiFlag_mul J.d ψ hc hn, psiFlag_nC, jacS_nC]
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', one_mul, star_one]
    ring
  · intro n hn u hu
    have hl : J.d.levi u ∈ flagN J.d := J.d.levi_mem_NFlag hu
    rw [th, hlevi n hn u hu, psiFlag_mul J.d ψ hn hl, psiFlag_levi, th, star_mul', mul_assoc]
  · intro b u hu
    have hb : J.d.nB b ∈ flagN J.d := J.d.nB_mem_NFlag b
    have hl : J.d.levi u ∈ flagN J.d := J.d.levi_mem_NFlag hu
    have hp : ptS J.d B.L (zl B) (J.d.nB b) = zl B ⬝ b := by
      have := ptS_nB_mul_nC J.d B.L (zl B) b 0
      rwa [J.d.nC_zero, mul_one] at this
    have hc : cenS J.d B.L (zl B) (J.d.nB b) = 0 := by
      have := hcen b 0
      rw [J.d.nC_zero, mul_one] at this
      rw [this, HypDec.qS]
      simp [GlobalTheory.MixModel.symplOH_zero_right]
    rw [th, hlevi _ hb u hu, psiFlag_mul J.d ψ hb hl, jacS_zero_apply, hp, hc, AddChar.map_zero_eq_one, one_mul,
      psiFlag_nB, one_mul, psiFlag_levi]
    ring

end GlobalTheory.Unf.FB.ThLaws

end
