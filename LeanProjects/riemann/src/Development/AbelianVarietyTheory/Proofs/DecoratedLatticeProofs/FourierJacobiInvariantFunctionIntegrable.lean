import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

open scoped Pointwise

namespace GlobalTheory.Unf

theorem vol_fund_lt_top {D : D7} {V : HSp D} (hc : CoCpt V) (v : Vol V) : v.μ v.𝓕 < ⊤ := by
  obtain ⟨_, _, _, _, _, _, hΓc⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := v.haar
  obtain ⟨K, hKc, hKcov⟩ := hc
  have hcover : v.𝓕 ⊆ ⋃ g : GQ V, (g • K) := by
    intro h _
    obtain ⟨γ, hγ, hk⟩ := hKcov h
    refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, ?_⟩
    refine Set.mem_smul_set.2 ⟨γ * h, hk, ?_⟩
    simp [Subgroup.smul_def]
  have hle : v.μ v.𝓕 ≤ v.μ K := by
    calc v.μ v.𝓕 = v.μ ((⋃ g : GQ V, (g • K)) ∩ v.𝓕) := by rw [Set.inter_eq_right.2 hcover]
      _ = v.μ (⋃ g : GQ V, (g • K ∩ v.𝓕)) := by rw [Set.iUnion_inter]
      _ ≤ ∑' g : GQ V, v.μ (g • K ∩ v.𝓕) := measure_iUnion_le _
      _ = v.μ K := (v.fund.measure_eq_tsum K).symm
  exact hle.trans_lt hKc.measure_lt_top

theorem jac_bound (D : D7) (ρ : ℕ) (J : JacLev D ρ) (K : GA D J.W → ℂ) (hK : Continuous K)
    (hinv : ∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, K (γ * h) = K h) (h : GA D J.W) :
    ∃ C, ∀ (n : flagN J.d) (h' : GA D J.W₀), ‖K (n.1 * J.d.emb0 h' * h)‖ ≤ C := by
  have hcont := J.d.continuous_embed
  obtain ⟨-, -, -, -, hnorm, -, -⟩ := GlobalTheory.MixPer.flag_jacobi_structure D J.W J.W₀ ρ J.d
  obtain ⟨⟨Kn, hKn, hcov⟩, -⟩ := GlobalTheory.Mem.UnipCocompact.radicals_cocompact D J.W ρ J.d.e (isIsoSub_e J.d)
  obtain ⟨K₀, hK₀, hcov₀⟩ := J.cpt
  obtain ⟨-, -, -, -, htop, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  let f : flagN J.d × GA D J.W₀ → GA D J.W := fun p => p.1.1 * J.d.emb0 p.2 * h
  have hf : Continuous f :=
    ((continuous_subtype_val.comp continuous_fst).mul (hcont.comp continuous_snd)).mul continuous_const
  have hS : IsCompact (f '' (Kn ×ˢ K₀)) := (hKn.prod hK₀).image hf
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hK.continuousOn
  refine ⟨C, fun n h' => ?_⟩
  obtain ⟨γ₀, hγ₀, hk₀⟩ := hcov₀ h'
  have hemb : J.d.emb0 γ₀ ∈ GQ J.W := J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hγ₀
  let n' : flagN J.d := ⟨J.d.emb0 γ₀ * n.1 * (J.d.emb0 γ₀)⁻¹, hnorm n.1 n.2 γ₀⟩
  obtain ⟨γ, hγ, k, hk, hn'⟩ := hcov n'
  have hδ : (J.d.emb0 γ₀)⁻¹ * γ.1 ∈ GQ J.W ⊓ jacGrp J.d :=
    Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hemb) (Subgroup.mem_subgroupOf.1 hγ),
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right (MonoidHom.mem_range.2 ⟨γ₀, rfl⟩)))
        (Subgroup.mem_sup_left γ.2)⟩
  have h1 : γ.1 * k.1 = J.d.emb0 γ₀ * n.1 * (J.d.emb0 γ₀)⁻¹ := (congrArg Subtype.val hn').symm
  have heq : n.1 * J.d.emb0 h' * h = ((J.d.emb0 γ₀)⁻¹ * γ.1) * (k.1 * J.d.emb0 (γ₀ * h') * h) := by
    rw [map_mul, show ((J.d.emb0 γ₀)⁻¹ * γ.1) * (k.1 * (J.d.emb0 γ₀ * J.d.emb0 h') * h) =
      (J.d.emb0 γ₀)⁻¹ * (γ.1 * k.1) * J.d.emb0 γ₀ * J.d.emb0 h' * h by simp only [mul_assoc], h1]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rw [heq, hinv _ hδ]
  exact hC _ ⟨(k, γ₀ * h'), ⟨hk, hk₀⟩, rfl⟩

theorem jac_absConv : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (K : GA D J.W → ℂ), Continuous K →
    (∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, K (γ * h) = K h) → ∀ h,
      AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 fun h' n => K (n.1 * J.d.emb0 h' * h) := by
  intro D ρ J K hK hinv h
  obtain ⟨C, hC⟩ := jac_bound D ρ J K hK hinv h
  have hcont := J.d.continuous_embed
  obtain ⟨-, h2W, -, hbW, htW, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  obtain ⟨-, h20, -, hb0, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  have hμ : J.v0.μ J.v0.𝓕 < ⊤ := vol_fund_lt_top J.cpt J.v0
  have hν : J.vN.ν J.vN.𝓝 < ⊤ := by rw [J.vN.unit.2.2]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2 hμ.ne
  haveI : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) := isFiniteMeasure_restrict.2 hν.ne
  unfold AbsConv
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun p => hC p.2 p.1)
  exact (hK.comp (((continuous_subtype_val.comp continuous_snd).mul (hcont.comp continuous_fst)).mul
    continuous_const)).aestronglyMeasurable

end GlobalTheory.Unf

end
