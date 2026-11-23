import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFundamentalDomainEqSumDoubleCosetAvg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralRealUnitaryHaarEqProdUpqHaar
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqBase
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem isCompact_ginfC_of_ontoUni (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hθ : IsInfFam θ) (hr : OntoUni (fun k : GinfC V => inB θ V B k.1)) : IsCompact (GinfC V : Set (GA D V)) := by
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hB : ∀ τ, IsUnit (B τ).det := by
    intro τ
    by_contra hn
    have h0 := hr.uni 1 τ
    have e : inB (Formalism.IndefR.Eqv.thetaC D) V B (1 : GinfC V).1 τ = 0 := by
      simp only [inB, Matrix.nonsing_inv_apply_not_isUnit _ hn, Matrix.zero_mul]
    rw [e] at h0
    have h1 : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 0 := by
      have := Matrix.mem_unitaryGroup_iff.mp h0
      simpa using this.symm
    have hB1 : B τ = 1 := by
      calc B τ = B τ * 1 := (Matrix.mul_one _).symm
        _ = 0 := by rw [h1, Matrix.mul_zero]
        _ = 1 := h1.symm
    exact hn (by rw [hB1, Matrix.det_one]; exact isUnit_one)
  have hconj : ∀ τ (M : Matrix (Fin V.rank) (Fin V.rank) ℂ), B τ * ((B τ)⁻¹ * M * B τ) * (B τ)⁻¹ = M := by
    intro τ M
    calc B τ * ((B τ)⁻¹ * M * B τ) * (B τ)⁻¹ = (B τ * (B τ)⁻¹) * M * (B τ * (B τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = M := by rw [Matrix.mul_nonsing_inv _ (hB τ), Matrix.one_mul, Matrix.mul_one]
  have hU : ∀ u : D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ,
      Formalism.IndefR.Eqv.IsUnitFam D V (fun τ => B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹) := by
    intro u
    obtain ⟨k, hk⟩ := hr.onto (fun τ => (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)) (fun τ => (u τ).2)
    have e : (fun τ => B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹) =
        fun τ => infMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.thetaC D τ) (k : GA D V) := by
      funext τ
      have := congrFun hk τ
      rw [← this]
      exact hconj τ _
    rw [e]
    exact Formalism.IndefR.Eqv.infMat_unitary' D V _
  have : CompactSpace (unitaryGroup (Fin V.rank) ℂ) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.isCompact_unitaryGroup _ _)
  let Ψ : (D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ) → GA D V := fun u => Formalism.IndefR.Eqv.famH D V _ (hU u)
  have hg : Continuous fun u : (D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ) =>
      fun τ => B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹ :=
    continuous_pi fun τ => (continuous_const.matrix_mul (continuous_subtype_val.comp (continuous_apply τ))).matrix_mul
      continuous_const
  have hΨ : Continuous Ψ := by
    refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
    · exact GlobalTheory.HaarReal.continuous_famM.comp hg
    · have hi : Continuous fun u : (D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ) =>
          fun τ => Formalism.IndefR.Eqv.ginv D V τ (B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹) :=
        continuous_pi fun τ => (continuous_const.matrix_mul ((continuous_apply τ).comp hg).matrix_conjTranspose).matrix_mul
          continuous_const
      exact GlobalTheory.HaarReal.continuous_famM.comp hi
  have hsub : (GinfC V : Set (GA D V)) ⊆ Set.range Ψ := by
    intro g hg
    refine ⟨fun τ => ⟨inB (Formalism.IndefR.Eqv.thetaC D) V B g τ, hr.uni ⟨g, hg⟩ τ⟩, ?_⟩
    refine (Formalism.IndefR.Eqv.famH_unique D V _ (hU _) g hg fun τ => ?_).symm
    exact (hconj τ _).symm
  exact (isCompact_range hΨ).of_isClosed_subset (GlobalTheory.Ker.CongTop.isClosed_GinfC V) hsub

end GlobalTheory.SeeSaw

namespace GlobalTheory.SeeSaw

theorem integral_eq_classSum : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ → OntoUni (fun k : GinfC V => inB θ V B k.1) → BorelSpace (GinfC V) ∧ CompactSpace (GinfC V) ∧ (∀ g ∈ GfC V, ∀ k ∈ GinfC V, g * k = k * g) ∧ ∃ ν : Measure (GinfC V), IsProbabilityMeasure ν ∧ ν.IsMulLeftInvariant ∧ ∀ (v : Vol V) (U : Subgroup (GA D V)) (cl : Type) [Fintype cl] (h : cl → GA D V), IsReps V U h → 0 < volLev v U ∧ (∀ a, 0 < stabOrd U (h a)) ∧ ∀ Φ : GA D V → ℂ, Continuous Φ → (∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) → (∀ κ ∈ U, ∀ g, Φ (g * κ) = Φ g) → ∫ g in v.𝓕, Φ g ∂v.μ = (volLev v U : ℂ) * ∑ a, ((stabOrd U (h a) : ℕ) : ℂ)⁻¹ * ∫ k, Φ (h a * k.1) ∂ν := by
  intro D θ V B hθ hr
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  have hK : IsCompact (GinfC V : Set (GA D V)) := isCompact_ginfC_of_ontoUni D θ V B hθ hr
  haveI : CompactSpace (GinfC V) := isCompact_iff_compactSpace.mp hK
  haveI : BorelSpace (GinfC V) := Subtype.borelSpace _
  have hcf : ∀ {a b : GA D V}, a ∈ GinfC V → b ∈ GfC V → a * b = b * a := fun ha hb =>
    Formalism.IndefR.Eqv.Act.comm_inf_fin ha hb
  refine ⟨inferInstance, inferInstance, fun g hg k hk => (hcf hk hg).symm, ?_⟩
  let ν : Measure (GinfC V) := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure ν :=
    ⟨by simpa using (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC V))))⟩
  refine ⟨ν, inferInstance, inferInstance, ?_⟩
  intro v U cl _ h hU
  haveI := v.haar
  haveI : v.μ.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V v.μ v.haar
  haveI : (GinfC V).Normal := inferInstanceAs ((finHom V).ker.Normal)
  let K : Subgroup (GA D V) := GinfC V ⊔ U
  have hKset : (K : Set (GA D V)) = {g | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ} := by
    show ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V)) = _
    rw [Subgroup.normal_mul]
    ext g
    simp only [Set.mem_mul, SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
  have hmemK : ∀ g, g ∈ K ↔ ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ := fun g => by
    rw [← SetLike.mem_coe, hKset]; rfl
  have hvol : volLev v U = (v.μ K).toReal := by
    simp only [volLev]
    rw [← hKset]
  have hKc : IsCompact (K : Set (GA D V)) := by
    show IsCompact ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V))
    rw [Subgroup.normal_mul]
    exact hK.mul hU.cpt
  have hKo : IsOpen (K : Set (GA D V)) := by
    have ho : IsOpen (((U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) : Subgroup (GA D V)) : Set (GA D V)) :=
      hU.opn.preimage (GlobalTheory.AutMult.continuous_toFin V)
    refine Subgroup.isOpen_mono (fun g hg => ?_) ho
    rw [hmemK]
    exact ⟨GlobalTheory.AutMult.toInf V g, (GlobalTheory.AutMult.toInf V g).2, GlobalTheory.AutMult.toFin V g,
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hg), (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  have hKfin : v.μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKpos : 0 < v.μ K := hKo.measure_pos v.μ ⟨1, K.one_mem⟩
  have huniq : ∀ x : GA D V, ∃! i, ∃ γ ∈ GQ V, ∃ k ∈ K, x = γ * h i * k := by
    intro x
    obtain ⟨γ, hγ, c, k, hk, κ, hκ, e⟩ := hU.dec x
    refine ⟨c, ⟨γ, hγ, k * κ, (hmemK _).2 ⟨k, hk, κ, hκ, rfl⟩, by rw [e]; group⟩, ?_⟩
    rintro c' ⟨γ', hγ', k', hk', e'⟩
    obtain ⟨k₁, hk₁, κ₁, hκ₁, rfl⟩ := (hmemK _).1 hk'
    refine (hU.uniq c c' (γ'⁻¹ * γ) (mul_mem (inv_mem hγ') hγ) (k * k₁⁻¹) (mul_mem hk (inv_mem hk₁)) (κ * κ₁⁻¹)
      (mul_mem hκ (inv_mem hκ₁)) ?_).symm
    have hc1 : k₁⁻¹ * (κ * κ₁⁻¹) = (κ * κ₁⁻¹) * k₁⁻¹ := hcf (inv_mem hk₁) (hU.le (mul_mem hκ (inv_mem hκ₁)))
    have e2 : h c' = γ'⁻¹ * x * (k₁ * κ₁)⁻¹ := by rw [e']; group
    rw [e2, e, _root_.mul_inv_rev]
    calc γ'⁻¹ * (γ * (h c * k) * κ) * (κ₁⁻¹ * k₁⁻¹) = γ'⁻¹ * γ * (h c * k) * ((κ * κ₁⁻¹) * k₁⁻¹) := by group
      _ = γ'⁻¹ * γ * (h c * k) * (k₁⁻¹ * (κ * κ₁⁻¹)) := by rw [hc1]
      _ = γ'⁻¹ * γ * (h c * (k * k₁⁻¹)) * (κ * κ₁⁻¹) := by group
  have hfin : ∀ i, {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ K}.Finite := by
    intro i
    have hC : IsCompact ((fun y => h i * y * (h i)⁻¹) '' (K : Set (GA D V))) :=
      hKc.image ((continuous_const.mul continuous_id).mul continuous_const)
    have hcl : IsClosed (GQ V : Set (GA D V)) := Subgroup.isClosed_of_discrete
    have hTc : IsCompact (((↑) : GQ V → GA D V) ⁻¹' ((fun y => h i * y * (h i)⁻¹) '' (K : Set (GA D V)))) :=
      hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hC
    refine (hTc.finite_of_discrete.image Subtype.val).subset ?_
    rintro γ ⟨hγ, hk⟩
    exact ⟨⟨γ, hγ⟩, ⟨_, hk, by group⟩, rfl⟩
  have hst : ∀ i, {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard = stabOrd U (h i) := by
    intro i
    have hs : {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ K} =
        Subtype.val '' {γ : GQ V | ∃ k ∈ GinfC V, ∃ κ ∈ U, γ.1 * h i = h i * k * κ} := by
      ext γ
      constructor
      · rintro ⟨hγ, hk⟩
        obtain ⟨k, hk, κ, hκ, e⟩ := (hmemK _).1 hk
        refine ⟨⟨γ, hγ⟩, ⟨k, hk, κ, hκ, ?_⟩, rfl⟩
        calc γ * h i = h i * ((h i)⁻¹ * γ * h i) := by group
          _ = h i * k * κ := by rw [e, mul_assoc]
      · rintro ⟨γ, ⟨k, hk, κ, hκ, e⟩, rfl⟩
        refine ⟨γ.2, (hmemK _).2 ⟨k, hk, κ, hκ, ?_⟩⟩
        calc (h i)⁻¹ * γ.1 * h i = (h i)⁻¹ * (γ.1 * h i) := by group
          _ = k * κ := by rw [e]; group
    rw [hs, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
    rfl
  refine ⟨by rw [hvol]; exact ENNReal.toReal_pos hKpos.ne' hKfin, fun a => ?_, ?_⟩
  · rw [← hst]
    exact (Set.ncard_pos (hfin a)).mpr ⟨1, (GQ V).one_mem, by simpa using K.one_mem⟩
  intro Φ hΦc hΦl hΦr
  obtain ⟨-, he⟩ := GlobalTheory.integral_fundamentalDomain_eq_sum_doubleCoset_avg (GA D V) v.μ (GQ V) K U v.𝓕 v.fund hKo hKfin
    (GinfC V) ν (GinfC V).subtype continuous_subtype_val
    (fun k hk => by
      obtain ⟨a, ha, κ, hκ, rfl⟩ := (hmemK _).1 hk
      exact ⟨κ, hκ, ⟨a, ha⟩, hcf ha (hU.le hκ)⟩)
    (fun k hk w => (hcf w.2 (hU.le hk)).symm) cl h huniq hfin Φ hΦc hΦl hΦr
  rw [he, hvol]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hst i]
  rfl

end GlobalTheory.SeeSaw
