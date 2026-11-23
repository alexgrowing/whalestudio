import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompactStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PetIntOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLawsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.BesselIntegrable

theorem measure_le_of_cover {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] {𝓕 K : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hK : ∀ n, ∃ γ ∈ Γ, ∃ k ∈ K, n = γ * k) : μ 𝓕 ≤ μ K := by
  rw [h.measure_eq_tsum K]
  refine (measure_mono fun n hn => ?_).trans (measure_iUnion_le _)
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hK n
  exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hn⟩

theorem norm_besChar {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) {A B : HSp D}
    {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (n : GA D B) : ‖besChar ψ d n‖ = 1 := by
  unfold besChar
  split_ifs with h
  · obtain ⟨a, b, -, -, e⟩ := h.choose_spec
    rw [e]
    exact hψ _
  · exact norm_one

theorem besInt : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, BesInt D := by
  intro hP D θ hθ ψ hψ A B ι hι d μ 𝓕 hq μN 𝓕N hμN h𝓕N s hs φ F hφ hF hA
  obtain ⟨-, a2, a3, a4, a5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨-, b2, b3, b4, b5, -, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have : Countable (NFlagQ B d.e) :=
    Function.Injective.countable (f := fun x : NFlagQ B d.e => (⟨x.1.1, x.2⟩ : GQ B))
      fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ B => z.1) h))
  have : SecondCountableTopology (NFlag B d.e) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨⟨K, hK, hcov⟩, -⟩ := GlobalTheory.T.isotropic_unipotentRadicals_rational_cocompact D B d.ρ d.e d.e_iso
  have hfin : μN 𝓕N < ⊤ := (measure_le_of_cover _ μN h𝓕N hcov).trans_lt hK.measure_lt_top
  obtain ⟨C, hC⟩ := GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ hF.1 hF.2
  obtain ⟨s', hs', hs'', -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  have hsc : Continuous s := by
    rw [show s = s' from funext fun h => (hs'' h _).1 (hs h)]
    exact hs'
  have hχ := (GlobalTheory.T.besselCharacter_generic_character_laws D ψ hψ A B ι hι d).2.2.1
  have hb : ∀ (h : GA D A) (n : NFlag B d.e), ‖star (φ h) * F ((n : GA D B) * s h * (d.y : GA D B)) *
      star (besChar ψ d (n : GA D B))‖ ≤ ‖φ h‖ * C := fun h n => by
    rw [norm_mul, norm_mul, norm_star, norm_star, norm_besChar hψ.1.2.1, mul_one]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have hc : Continuous fun p : GA D A × NFlag B d.e => star (φ p.1) * F ((p.2 : GA D B) * s p.1 * (d.y : GA D B)) *
      star (besChar ψ d (p.2 : GA D B)) :=
    ((hφ.cont.comp continuous_fst).star.mul (hF.1.cont.comp
      (((continuous_subtype_val.comp continuous_snd).mul (hsc.comp continuous_fst)).mul continuous_const))).mul
      (hχ.comp continuous_snd).star
  refine ⟨fun h => Measure.integrableOn_of_bounded (M := ‖φ h‖ * C) hfin.ne
    (hc.comp (Continuous.prodMk_right h)).measurable.aestronglyMeasurable (.of_forall (hb h)), ?_⟩
  have hcusp : IsCuspForm θ A φ := ⟨hφ, hA.elim (fun h r C hC => absurd hC (h r C)) id⟩
  have hint := GlobalTheory.Mem.Th.petInt_of_cuspRapidDecay hP D θ hθ A μ 𝓕 hq (fun _ => 1) φ (isAutFunSm_const θ A 1) hcusp
  simp only [star_one, one_mul] at hint
  have : IsFiniteMeasure (μN.restrict 𝓕N) := isFiniteMeasure_restrict.2 hfin.ne
  refine Integrable.mono' ((hint.norm.mul_const C).mul_const (μN.real 𝓕N))
    (hc.stronglyMeasurable.integral_prod_right' (ν := μN.restrict 𝓕N)).aestronglyMeasurable (.of_forall fun h => ?_)
  exact norm_setIntegral_le_of_norm_le_const hfin fun n _ => hb h n

end GlobalTheory.Mem.BesselIntegrable
