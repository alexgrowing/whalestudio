import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero GlobalTheory.ThetaMean

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaMean.Model

variable {D : D7}

theorem isAniso_posSpace (m : ℕ) : IsAniso (D := D) (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral m) :=
  GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite _ (Examples₂.posSpace_sigOK _ _) fun _ => .inl rfl

theorem zero_vec (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (K : Subgroup (GA D S)) : IsThetaFunO ψ S T 0 ∧ IsKFinVec ω K 0 := by
  refine ⟨⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun u _ _ => funext fun w => by simp [heisO]⟩, continuous_const,
    fun _ _ _ _ _ => contDiff_const⟩, ?_⟩
  have : Submodule.span ℂ {f : WO S T → ℂ | ∃ k ∈ K, f = ω (k, 1) 0} = ⊥ :=
    Submodule.span_eq_bot.2 (by rintro _ ⟨k, -, rfl⟩; exact map_zero _)
  rw [IsKFinVec, this]
  infer_instance

theorem hypotheses_inhabited (H : GlobalTheory.Published.WeilRepresentationUnitaryPair) (D : D7) (n m : ℕ) :
    ∃ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle)
      (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (a : GL (Fin A.rank) (AE D))
      (μ : Measure (WO A B)) (𝓨 : Set (WO A B)) (ν : Measure (GA D B)),
      A.rank = n ∧ B.rank = m ∧ IsAniso B ∧ IsWeilDatumO ψ (dblSp A) B 1 χB ω ∧ IsMaj A a ∧
        IsCovolOne (ratL B A) μ 𝓨 ∧ ν.IsHaarMeasure := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  let A : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n
  let B : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral m
  have h1 : IsHeckeChar D (η ^ m) := ⟨by
    have : ((η ^ m : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ m := by funext x; simp
    rw [this]; exact hη.1.1.pow m, fun x => by rw [MonoidHom.pow_apply, hη.1.2 x, one_pow]⟩
  have hr := hη.2.2.1
  have h2 : ResEta D (η ^ m) B.rank := ⟨hr.1, fun e he a => by rw [MonoidHom.pow_apply, hr.2 e he a, pow_one]; rfl⟩
  have h3 : ResEta D 1 (dblSp A).rank := ⟨hr.1, fun e he a => by
    have h4 := he.2.2.1 (idF D a)
    have h5 : Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := Units.ext (by
      change Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) a.1) = _
      have := t2Space_adeleRing' (F := D.host.F)
      have : Nontrivial (AF D.host.F) :=
        (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers D.host.F) D.host.F).nontrivial
      rw [Algebra.norm_algebraMap, Module.finrank_baseChange, D.sp.cm.deg2, Units.val_pow_eq_pow_val])
    rw [h5, map_pow] at h4
    change (1 : Circle) = e a ^ (n + n)
    rw [← two_mul, pow_mul, h4, one_pow]⟩
  obtain ⟨ω, hω⟩ := H D ψ (dblSp A) B 1 (η ^ m) hψ ⟨continuous_const, fun _ => rfl⟩ h1 h3 h2
  obtain ⟨a, ha⟩ := exists_isMaj A
  obtain ⟨μ, 𝓨, hμ⟩ := exists_isCovolOne D B.rank A.rank
  exact ⟨ψ, A, B, _, ω, a, μ, 𝓨, Measure.haar, rfl, rfl, isAniso_posSpace m, hω, ha, hμ, inferInstance⟩

theorem integrable_of_isAniso {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χ χ' ω) (hT : IsAniso T)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (ν : Measure (GA D T)) [ν.IsHaarMeasure] (g : GA D S) :
    Integrable (AutomorphicL2Unitary.descend (GQ T) fun h => thetaKO ω g h f) (autMeasure T ν) :=
  integrable_theta hω hf (GlobalTheory.Mem.AnisoQuotient.exists_compact D T hT) g

theorem average_const_aut (T : HSp D) (ν : Measure (GA D T)) [ν.IsHaarMeasure] (c : ℂ) :
    ⨍ _, c ∂autMeasure T ν = c := average_const _ c

theorem conclusion_zero (A B : HSp D) (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ))
    (a : GL (Fin A.rank) (AE D)) (μ : Measure (WO A B)) (𝓨 : Set (WO A B)) (ν : Measure (GA D B)) :
    Eis.EisValueAt A (flat A a (swSec A B ω μ 𝓨 0) (sZero A B)) (sZero A B)
      ((if A.rank < B.rank then 1 else 2 : ℂ) • thetaMean ω ν 0) := by
  have h1 : flat A a (swSec A B ω μ 𝓨 0) (sZero A B) = fun _ _ => 0 := by
    funext s g
    refine (flatH_apply _ _ _ _).trans ?_
    simp [swSec, evZero]
  have h2 : thetaMean ω ν 0 = 0 := by
    funext g
    simp [thetaMean, thetaKO, AutomorphicL2Unitary.descend]
  rw [h1, h2, smul_zero]
  refine ⟨fun s _ => ⟨fun _ _ _ => rfl, fun g => ?_⟩, fun g => ?_⟩
  · simp [Eis.EisConv, Eis.CosetConv, Eis.term, summable_zero]
  · have : Eis.eisSer A (fun _ _ => (0 : ℂ)) g = fun _ => 0 := by
      funext s
      simp [Eis.eisSer, Eis.eis, Eis.cosetSum, Eis.term]
    rw [this]
    exact GlobalTheory.Cont.holValueAt_const 0 _

end GlobalTheory.ThetaMean.Model

end
