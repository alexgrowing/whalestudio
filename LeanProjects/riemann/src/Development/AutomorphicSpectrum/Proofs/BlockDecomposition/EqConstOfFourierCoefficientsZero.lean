import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

section Abstract
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

open scoped Pointwise in

theorem mean_add_left (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] {s : Set G}
    (hs : IsAddFundamentalDomain Γ s μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) (t : G) :
    ∫ y in s, f (t + y) ∂μ = ∫ y in s, f y ∂μ := by
  have hFD : IsAddFundamentalDomain Γ (t +ᵥ s) μ := hs.vadd_of_comm t
  have h1 : ∫ y in (t +ᵥ s), f y ∂μ = ∫ y in s, f (t + y) ∂μ := by
    have hemb : MeasurableEmbedding (fun y : G => t + y) := (Homeomorph.addLeft t).measurableEmbedding
    exact (measurePreserving_add_left μ t).setIntegral_image_emb hemb f s
  rw [← h1]
  exact hFD.setIntegral_eq hs (fun g x => hf g.1 g.2 x)

theorem exists_bound_of_periodic (Γ : AddSubgroup G) {K : Set G} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
    (f : G → ℂ) (hc : Continuous f) (hf : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) : ∃ C, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hcov x
  rw [← hf γ hγ x]
  exact hC _ hk

theorem const_of_coefficients (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G) (hK : IsCompact K)
    (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K) (A : Type) [AddCommGroup A] (χ : A → G → ℂ) (hc : ∀ a, Continuous (χ a))
    (hx : ∀ a x y, χ a (x + y) = χ a x * χ a y) (ha : ∀ a b x, χ (a + b) x = χ a x * χ b x) (h0 : ∀ x, χ 0 x = 1)
    (hn : ∀ a x, ‖χ a x‖ = 1) (hker : ∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) (μ : Measure G) (𝓕 : Set G) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 ≠ ∞) (φ : G → ℂ) (hφ : Continuous φ)
    (hper : ∀ γ ∈ Γ, ∀ x, φ (γ + x) = φ x) (hco : ∀ a, a ≠ 0 → ∫ x in 𝓕, χ a x * φ x ∂μ = 0) (y : G) : φ y = φ 0 := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨C, hC⟩ := exists_bound_of_periodic Γ hK hcov φ hφ hper
  have hint : ∀ (a : A) (f : G → ℂ), Continuous f → (∀ x, ‖f x‖ ≤ C) → IntegrableOn (fun x => χ a x * f x) 𝓕 μ := by
    intro a f hf hb
    refine Measure.integrableOn_of_bounded (M := C) hfin ((hc a).mul hf).aestronglyMeasurable (.of_forall fun x => ?_)
    rw [norm_mul, hn, one_mul]
    exact hb x
  have hshift : ∀ a, ∫ x in 𝓕, χ a x * φ (y + x) ∂μ = ∫ x in 𝓕, χ a x * φ x ∂μ := by
    intro a
    by_cases h : a = 0
    · subst h
      simp only [h0, one_mul]
      exact mean_add_left Γ μ h𝓕 φ hper y
    · have hp : ∀ γ ∈ Γ, ∀ x, χ a (γ + x) * φ (γ + x) = χ a x * φ x := fun γ hγ x => by
        rw [hper γ hγ, hx, (hker γ).2 hγ a, one_mul]
      have h1 := mean_add_left Γ μ h𝓕 (fun x => χ a x * φ x) hp y
      rw [hco a h] at h1 ⊢
      have h2 : ∫ x in 𝓕, χ a (y + x) * φ (y + x) ∂μ = χ a y * ∫ x in 𝓕, χ a x * φ (y + x) ∂μ := by
        rw [← integral_const_mul]
        exact integral_congr_ae (.of_forall fun x => by simp only [hx, mul_assoc])
      rw [h2] at h1
      have hne : χ a y ≠ 0 := fun e => by simpa [e] using hn a y
      exact (mul_eq_zero.1 h1).resolve_left hne
  have hφy : Continuous fun x => φ (y + x) := hφ.comp (continuous_const.add continuous_id)
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero G Γ K hK hcov A χ hc hx ha h0 hn hker μ 𝓕 hμ h𝓕
    (fun x => φ (y + x) - φ x) (hφy.sub hφ)
    (fun γ hγ x => by
      show φ (y + (γ + x)) - φ (γ + x) = φ (y + x) - φ x
      rw [add_left_comm, hper γ hγ, hper γ hγ])
    (fun a => by
      have e : ∀ x, χ a x * (φ (y + x) - φ x) = χ a x * φ (y + x) - χ a x * φ x := fun x => mul_sub _ _ _
      simp only [e]
      rw [integral_sub (hint a _ hφy fun x => hC _) (hint a _ hφ hC), hshift a, sub_self])
  have h := congrFun key 0
  simp only [add_zero, Pi.zero_apply] at h
  exact sub_eq_zero.1 h

end Abstract

set_option synthInstance.maxHeartbeats 400000 in

theorem const_of_coeff : ∀ {D : D7} {p : ℕ} {lp : Measure (hermA D p)} {𝓖p : Set (hermA D p)}, IsCovolOneH lp 𝓖p →
    ∀ {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ φ : hermA D p → ℂ, Continuous φ → IsPer φ →
    (∀ a : HermE D p, a.1 ≠ 0 → ∫ y in 𝓖p, φ y * chn ψ a y ∂lp = 0) → ∀ y, φ y = φ 0 := by
  intro D p lp 𝓖p hC ψ hψ φ hφ hper hco y
  obtain ⟨hlam, hFD, h1⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D p p
  haveI : BorelSpace (Mx D p p) := ⟨rfl⟩
  haveI : BorelSpace (hermA D p) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (hermA D p) := GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : DiscreteTopology (ratHerm D p) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := p)
  refine const_of_coefficients (ratHerm D p) K hK hcov (GlobalTheory.CompanionTheory.FourierN.hermSub D p) (fun a x => ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 x.1))
    (fun a => hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr a.1).neg.comp continuous_subtype_val))
    (fun a x y => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 (x.1 + y.1)) = _
      rw [GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul])
    (fun a b x => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr (a.1 + b.1) x.1) = _
      rw [GlobalTheory.CompanionTheory.FourierN.pr_add_left, neg_add, AddChar.map_add_eq_mul])
    (fun x => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr 0 x.1) = 1
      rw [GlobalTheory.CompanionTheory.FourierN.pr_zero_left, neg_zero, AddChar.map_zero_eq_one])
    (fun a x => hψ.2.1 _)
    (fun x => ⟨fun h => GlobalTheory.CompanionTheory.FourierN.rat_ker hψ x (fun a ha => h ⟨a, ha⟩), fun hx a => GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ x hx a.1⟩)
    lp 𝓖p hlam hFD (by rw [h1]; exact ENNReal.one_ne_top) φ hφ hper
    (fun a ha => (integral_congr_ae (.of_forall fun x => mul_comm _ _)).trans
      (hco ⟨a.1, a.2⟩ (fun e => ha (Subtype.ext e)))) y

end GlobalTheory.CompanionTheory.PcFc
