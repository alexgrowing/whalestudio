import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumTransportSchwartzBruhatStandard
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsHeckeCharRestrictionEtaInv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerSiegelUnipotentAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatum
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisPoleLEZeroOfLt
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealParOfIsCharAF
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsClopenCompactNbhdZero

noncomputable section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn.Inhab

theorem weil_exists : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ lam : D.host.F, lam ≠ 0 → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∃ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch (shift ψ lam) χ θ V μ ω := by
  intro D n V ψ hψ lam hlam χ hχ hr θ hθ μ 𝓕 hμ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  have hlamE : algebraMap D.host.F D.host.E lam ≠ 0 := (map_ne_zero _).2 hlam
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  set μ' : D.host.E := -D.host.xi0 / algebraMap D.host.F D.host.E lam with hμ'
  have hsk : IsSkew μ' := by
    refine ⟨div_ne_zero (neg_ne_zero.2 hxi) hlamE, ?_⟩
    rw [hμ', star_div₀, star_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, Formalism.IndefR.Eqv.star_algebraMapF]
    ring
  have hl : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ' := by
    rw [hμ']; field_simp
  obtain ⟨κ, hκ⟩ := GlobalTheory.StdUnn.chart_exists D A μ' hsk
  obtain ⟨hχi, hri⟩ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χ V.rank hχ hr
  have hr1 : ResEta D 1 (dblSp A).rank := by
    have := GlobalTheory.Eis.SimplePoleModel.resEta_one_two_mul D A.rank
    convert this using 2
    simp [GlobalTheory.Doubling.dblSp]
    omega
  obtain ⟨omh, homh⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ (dblSp A) V 1 χ⁻¹ hψ
    ⟨continuous_const, fun _ => rfl⟩ hχi hr1 hri
  obtain ⟨omS, hS⟩ := GlobalTheory.StdUnn.exists_transport_std D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ κ
  refine ⟨omS, ⟨?_, ?_, ?_⟩⟩
  · intro g a hg Φ x
    have := GlobalTheory.StdUnn.transport_levi D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ μ' hsk κ hκ omS hS lam hl g a hg Φ x
    rw [inv_inv] at this
    exact this
  · intro g b hg Φ x
    exact GlobalTheory.StdUnn.Unip.transport_unip D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ μ' hsk κ hκ omS hS lam hl g b hg Φ x
  · intro g hg Φ x
    exact GlobalTheory.StdUnn.WeylStd.main D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ μ' hsk κ hκ omS hS lam hl g hg Φ x

theorem fock_gauss (hg : ∀ (D : D7) (n : ℕ) (V : HSp D) (l : D.what₂.Tau → ℝ), (∀ τ, l τ ≠ 0) → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∃ f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ, ∀ z, f z = gauss V l s (fun τ => Matrix.of (z τ))) : ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ), (∀ τ, l τ ≠ 0) → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ U : Set (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U → IsCompact U → (0 : Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∈ U → ∃ Φ : schwartzA θ V.rank n, Φ.1 = (fun x => gauss V l s (fun τ => compAt θ τ x) * U.indicator 1 (fun i j => finPart D (x i j))) ∧ Φ.1 ∈ fockA θ V n l s ∧ Φ.1 0 ≠ 0 := by
  intro D n V θ l hl s hs U hUo hUc h0
  obtain ⟨f, hf⟩ := hg D n V l hl s hs
  set g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := U.indicator 1 with hgdef
  have hgSB : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
    refine ⟨?_, ?_⟩
    · exact (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hUo).isLocallyConstant
    · exact HasCompactSupport.intro' hUc hUo.isClosed (fun x hx => Set.indicator_of_notMem hx _)
  have hmem : (fun x : Mx D V.rank n => gauss V l s (fun τ => compAt θ τ x) * g (fun i j => finPart D (x i j))) ∈ schwartzA θ V.rank n := by
    refine Submodule.subset_span ⟨f, g, hgSB, ?_⟩
    funext x
    rw [hf]
    rfl
  refine ⟨⟨_, hmem⟩, rfl, ?_, ?_⟩
  · refine Submodule.subset_span ⟨1, g, hgSB, ?_⟩
    funext x
    simp [evalPoly]
  · show gauss V l s (fun τ => compAt θ τ 0) * g (fun i j => finPart D ((0 : Mx D V.rank n) i j)) ≠ 0
    have h1 : (fun τ => compAt θ τ (0 : Mx D V.rank n)) = fun _ => 0 := by
      funext τ; ext i j; simp [compAt]
    have h2 : (fun i j => finPart D ((0 : Mx D V.rank n) i j)) = 0 := by
      funext i j; simp
    rw [h1, h2, hgdef, Set.indicator_of_mem h0]
    simp [gauss]

theorem hyps_satisfiable :
    (∀ (D : D7) (n : ℕ), ∃ H : G D n → ℝ≥0, IsHeight H) ∧ (∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ → ∃ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l) ∧ (∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ lam : D.host.F, lam ≠ 0 → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∃ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch (shift ψ lam) χ θ V μ ω) ∧ (∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ), (∀ τ, l τ ≠ 0) → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ U : Set (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U → IsCompact U → (0 : Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∈ U → ∃ Φ : schwartzA θ V.rank n, Φ.1 = (fun x => gauss V l s (fun τ => compAt θ τ x) * U.indicator 1 (fun i j => finPart D (x i j))) ∧ Φ.1 ∈ fockA θ V n l s ∧ Φ.1 0 ≠ 0) ∧ (∀ (D : D7) (m n : ℕ), ∃ U : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U ∧ IsCompact U ∧ (0 : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∈ U) :=
  ⟨GlobalTheory.StdUnn.exists_height, GlobalTheory.StdUnn.exists_realPar_of_isCharAF, weil_exists, fock_gauss GlobalTheory.GaussSchwartz.exists_schwartz_gauss, GlobalTheory.AfTensNbhd.exists_clopen_compact_nbhd_zero⟩

end GlobalTheory.StdUnn.Inhab
