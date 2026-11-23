import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaKernelInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaUnipotentConjugationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Per.FJConv

theorem iterated_integrableOn {G N : Type} [TopologicalSpace G] [FirstCountableTopology G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [TopologicalSpace N] [MeasurableSpace N] [OpensMeasurableSpace N]
    {μ : Measure G} {𝓕 : Set G} {ν : Measure N} {𝓝 : Set N} (hμ : μ 𝓕 ≠ ⊤) (hν : ν 𝓝 ≠ ⊤) {P : G → N → ℂ}
    (hP : Continuous fun q : G × N => P q.1 q.2) {M : ℝ} (hM : ∀ g n, ‖P g n‖ ≤ M) :
    (∀ g, IntegrableOn (P g) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, P g n ∂ν) 𝓕 μ := by
  have h1 : ∀ g, Continuous (P g) := fun g => hP.comp (Continuous.prodMk_right g)
  have h2 : ∀ n, Continuous fun g => P g n := fun n => hP.comp (Continuous.prodMk_left n)
  have : IsFiniteMeasure (ν.restrict 𝓝) := isFiniteMeasure_restrict.2 hν
  refine ⟨fun g => Measure.integrableOn_of_bounded (M := M) hν (h1 g).measurable.aestronglyMeasurable
    (.of_forall (hM g)), ?_⟩
  have hc : Continuous fun g => ∫ n in 𝓝, P g n ∂ν :=
    continuous_of_dominated (bound := fun _ => M) (fun g => (h1 g).measurable.aestronglyMeasurable)
      (fun g => .of_forall (hM g)) (integrable_const M) (.of_forall h2)
  exact Measure.integrableOn_of_bounded (M := M * ν.real 𝓝) hμ hc.measurable.aestronglyMeasurable
    (.of_forall fun g => norm_setIntegral_le_of_norm_le_const hν.lt_top fun n _ => hM g n)

theorem continuous_theta {D : D7} {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) {L A B : HSp D}
    {ι : A.V →ₗ[D.host.E] B.V} (d : FJDat L A B ι) (hr : 1 < A.rank) (hψ : Continuous Wl.ψ) (Φ : X.Sch L A) :
    Continuous fun q : GA D A × GA D B => d.theta Wl.ψ (omZ Wl L A Φ) q.2 q.1 := by
  have i0 : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  have i1 : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  obtain ⟨-, ha, htc, -⟩ := GlobalTheory.T.theta_unipotent_conjugation D L A B ι d
  have hL := d.line.rank_one
  have hθ := GlobalTheory.T.weil_representation_continuous D X T Wl L A X.etaT⁻¹ (X.etaT ^ A.rank) (by omega) (resEta_line T hL) (resEta_pow T _) Φ
  have hcen : Continuous (cenCo L d.c) := continuous_const.mul (ht.comp (continuous_const.mul continuous_id))
  have htp : Continuous (tPt L A d.c) :=
    continuous_pi fun _ => continuous_pi fun k => (continuous_const.mul (continuous_apply k)).neg
  simp only [FJDat.theta_eq]
  exact (hψ.comp (hcen.comp (htc.comp continuous_snd))).mul
    (hθ.comp ((continuous_const.prodMk continuous_fst).prodMk (htp.comp (ha.comp continuous_snd))))

theorem conv_of_isAniso : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), 1 < A.rank → IsAniso A → ∀ μ 𝓕, μ.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕 μ → ∀ ν 𝓝, IsUnitN B d.eM ν 𝓝 → ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) → ∀ (Φ : X.Sch L A) φ F, IsAutFun A φ → IsAutFun B F → d.Conv Wl.ψ (omZ Wl L A Φ) μ 𝓕 ν 𝓝 s φ F := by
  intro D X T Wl L A B ι d hr hA μ 𝓕 hμ h𝓕 ν 𝓝 hν s hs Φ φ F hφ hF
  have hψ : IsCharAF D.host.F Wl.ψ := Wl.ψ_std.1
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D A hA
  obtain ⟨K', hK', hcov'⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B _ _ d.isIsoSub).1
  obtain ⟨s₀, hcont, hrel, hQ⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι d.isom
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs h)
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ A) hK hcov μ h𝓕
  obtain ⟨hchr, -, -, hconj⟩ := GlobalTheory.T.theta_unipotent_conjugation D L A B ι d
  have haut := GlobalTheory.T.theta_kernel_invariance D X T Wl L A B ι d hr Φ
  have hv : Continuous fun q : GA D A × d.N => (q.2 : GA D B) := continuous_subtype_val.comp continuous_snd
  have hP : Continuous fun q : GA D A × d.N => d.perFun Wl.ψ (omZ Wl L A Φ) s₀ φ F q.1 q.2 :=
    (((hφ.cont.comp continuous_fst).star.mul (hF.cont.comp (hv.mul (hcont.comp continuous_fst)))).mul
      ((continuous_theta Wl d hr hψ.1 Φ).comp (continuous_fst.prodMk hv))).mul ((hchr _ hψ).2.comp hv).star
  obtain ⟨M, hM⟩ := (hK.prod hK').exists_bound_of_continuousOn hP.continuousOn
  refine iterated_integrableOn hfin.ne (by rw [hν.2.2]; exact ENNReal.one_ne_top) hP (M := M) fun g n => ?_
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov g
  have hn : s₀ γ⁻¹ * n * (s₀ γ⁻¹)⁻¹ ∈ d.N := (hconj _ _ ((hrel _ _).2 rfl) n n.2).1
  obtain ⟨γ', hγ', k', hk', e⟩ := hcov' ⟨_, hn⟩
  have e' : s₀ γ⁻¹ * n * (s₀ γ⁻¹)⁻¹ = (γ' : GA D B) * k' := congrArg Subtype.val e
  have e1 : (n : GA D B) = s₀ γ * (γ' * k') * (s₀ γ)⁻¹ := by
    rw [← e']; simp only [map_inv, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  have e2 : (n : GA D B) * s₀ (γ * k) = s₀ γ * (γ' * (k' * s₀ k)) := by
    rw [e1]; simp only [map_mul, mul_assoc, inv_mul_cancel_left]
  have e3 : d.theta Wl.ψ (omZ Wl L A Φ) n (γ * k) = d.theta Wl.ψ (omZ Wl L A Φ) k' k := by
    rw [e1, (haut k _ (mul_mem γ'.2 k'.2)).2 γ hγ _ ((hrel _ _).2 rfl), (haut k _ k'.2).1 _ γ'.2 hγ']
  have hc : ∀ x, ‖d.chr Wl.ψ x‖ = 1 := fun x => hψ.2.1 _
  refine le_trans (le_of_eq ?_) (hM (k, k') ⟨hk, hk'⟩)
  simp only [FJDat.perFun, norm_mul, norm_star, hc]
  rw [e2, e3, hφ.left γ hγ, hF.left _ (hQ γ hγ), hF.left (γ' : GA D B) hγ']

end GlobalTheory.Per.FJConv
