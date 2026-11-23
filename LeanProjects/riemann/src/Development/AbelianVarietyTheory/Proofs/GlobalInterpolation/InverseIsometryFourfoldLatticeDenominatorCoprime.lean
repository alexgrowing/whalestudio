import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.LatInvDenom

theorem lamMM_form (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    ∀ z ∈ lamMM D (lamOf D cc δ), ∃ e ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      z = fun τ => δ * embT D τ e := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, a, ha, rfl⟩ := hx
    obtain ⟨c, -, rfl⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ w hw
    refine ⟨((c : D.host.K) : D.host.E) * a, ?_, ?_⟩
    · exact Submodule.smul_mem (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)
        (⟨_, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.intK D c⟩ : 𝓞 D.host.E) ha
    · funext τ
      rw [map_mul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D τ _ (SetLike.coe_mem _)]
      ring
  | zero => exact ⟨0, Submodule.zero_mem _, by funext τ; simp⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨e1, he1, rfl⟩ := h1
    obtain ⟨e2, he2, rfl⟩ := h2
    exact ⟨e1 + e2, Submodule.add_mem _ he1 he2, by funext τ; simp only [Pi.add_apply, map_add]; ring⟩
  | neg x _ h1 =>
    obtain ⟨e1, he1, rfl⟩ := h1
    exact ⟨-e1, Submodule.neg_mem _ he1, by funext τ; simp only [Pi.neg_apply, map_neg]; ring⟩

theorem inverseIsometry_fourfoldLattice_denominator_coprime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, (∀ w, v w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ a, (s : D.host.E) * B.γ₀.g.symm (G.symm v) a ∈ D.host.AA0 := by
  intro D cc δ B hcc hδ12 q _ hNq u hu hidx hq hidx' G hG v hv
  have hqp : q.Prime := Fact.out
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B
  set S := Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau) with hS
  set M := Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
    (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
      (Formalism.L2.Th1.H.pow4 B.lamM)) with hM

  have hSd : Formalism.L2.Th1.H.IsSelfDual (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) S :=
    Formalism.L2.Th1.H.stdSelfDual B.L _
  have hMd : Formalism.L2.Th1.H.IsSelfDual (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) M :=
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.selfDual_img _ _ u hu _ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.selfDual B hcc hδ12)
  have heq : Formalism.L2.Th1.H.relIdx S M = Formalism.L2.Th1.H.relIdx M S :=
    Formalism.L2.Th1.H.indexEq _ _ (Formalism.L2.Th1.H.stdHBasic B.L _).2.1 S M hSd hMd hidx hidx'
  set n := Formalism.L2.Th1.H.relIdx M S with hn
  have hnq : Nat.Coprime n q := by
    rw [← heq]; exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hqp).2 hq)
  have h1 : ∀ x ∈ S, n • x ∈ M := by
    intro x hx
    have := AddSubgroup.nsmul_index_mem (M.addSubgroupOf S) (⟨x, hx⟩ : S)
    rw [AddSubgroup.mem_addSubgroupOf, AddSubmonoidClass.coe_nsmul] at this
    exact this

  set N := Ideal.absNorm cc with hNdef
  have hNc : ((N : 𝓞 D.host.K)) ∈ cc := Ideal.absNorm_mem cc
  have hN0 : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact hcc.1
  choose o ho using hv
  set V : Fin 4 × D.what₂.Tau → ℂ := fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E) with hV
  have hz : (δ * (N : ℂ)) • V ∈ S := by
    rw [hS, Formalism.L2.Th1.H.mem_stdLat]
    intro w
    rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B]
    refine AddSubgroup.subset_closure ⟨(N : 𝓞 D.host.K) * o w, cc.mul_mem_right _ hNc, ?_⟩
    simp only [hV, Pi.smul_apply, smul_eq_mul, ← ho w]
    push_cast
    rw [map_mul, map_natCast]
    ring
  set y := B.γ₀.g.symm (G.symm v) with hy
  have hgy : u (B.gC (emb4 D y)) = V := by
    rw [show B.gC (emb4 D y) = _ from B.gC_spec y, hy, LinearEquiv.apply_symm_apply, hG (G.symm v),
      LinearEquiv.apply_symm_apply]
  obtain ⟨m', ⟨m₀, hm₀, rfl⟩, hm'⟩ := h1 _ hz
  have hm0eq : m₀ = ((n : ℂ) * δ * (N : ℂ)) • emb4 D y := by
    apply B.gC.injective
    apply u.injective
    have e1 : u (B.gC m₀) = n • ((δ * (N : ℂ)) • V) := hm'
    rw [e1, map_smul, map_smul, hgy, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_assoc]

  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.mp (by
    rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.card_tau]; positivity)
  refine ⟨n * N, Nat.Coprime.mul hnq hNq, fun a => ?_⟩
  obtain ⟨e, he, hee⟩ := lamMM_form D cc δ _ (hm₀ a)
  have h2 := congrFun hee τ
  rw [hm0eq] at h2
  simp only [Formalism.L2.Th1.H.slice, Pi.smul_apply, smul_eq_mul, emb4] at h2
  have h3 : embT D τ (((n * N : ℕ) : D.host.E) * y a) = embT D τ e := by
    apply mul_left_cancel₀ hδ
    rw [map_mul, map_natCast]
    push_cast
    linear_combination h2
  rw [(embT D τ).injective h3]
  exact he

end GlobalTheory.LatInvDenom

end
