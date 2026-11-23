import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingRuleTranslateStable
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryFramesOrthonormalUnit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFiniteAdelicElementMarkingComponent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemLevelKOfSameMarkAndFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlagDomainModelsExponentsLevelM
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArithmeticGroupCuspCentreLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDictionaryByMarkingRule
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryAdelicCharOfHeckeChar
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.ExistsCtxOkOfPins

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.MemberModel

theorem dict_invariant : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → (∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧ (∀ k ∈ Kf, ∀ g, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (g * k) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧ (∀ g, (dict g).2 ∈ (C.M.X (dict g).1).dom) ∧ (∀ g τ i, ‖dmin (C.M.X (dict g).1).Gm (dict g).2 τ i‖ = 1) ∧ ∀ g k γ, C.Mark g k γ → ∃ δ ∈ (C.M.X k).Γ, dict g = ⟨k, lact δ (C.fr (γ * g) k)⟩ := by
  intro D H Dw l Xo c σ V r C hC dict hd Kf hK
  have last : ∀ g k γ, C.Mark g k γ → ∃ δ ∈ (C.M.X k).Γ, dict g = ⟨k, lact δ (C.fr (γ * g) k)⟩ := by
    intro g k γ hm
    obtain ⟨γ₀, hm₀, hf⟩ := hd.1 g
    have hu := GlobalTheory.MarkUniq.mark_unique D H Dw l Xo c σ V r C hC g
    have hk : (dict g).1 = k := hu.1 _ _ _ _ hm₀ hm
    subst hk
    obtain ⟨δ, hδ, he⟩ := hu.2 _ γ γ₀ hm hm₀
    refine ⟨δ, hδ, ?_⟩
    rw [← he, ← hf]
  refine ⟨?_, ?_, ?_, ?_, last⟩
  · intro γ hγ g
    obtain ⟨γ₀, hm₀, hf⟩ := hd.1 g
    have hm := (GlobalTheory.Member.mark_move D H Dw l Xo c σ V r C hC g _ γ₀ hm₀).1 γ hγ
    obtain ⟨δ, hδ, he⟩ := last _ _ _ hm
    refine ⟨δ, hδ, ?_⟩
    rw [he, hf, mul_assoc, inv_mul_cancel_left]
  · intro k hk g
    obtain ⟨γ₀, hm₀, hf⟩ := hd.1 g
    have hk' := (hK k).1 hk
    have hm := (GlobalTheory.Member.mark_move D H Dw l Xo c σ V r C hC g _ γ₀ hm₀).2.1 k hk'.2
    obtain ⟨δ, hδ, he⟩ := last _ _ _ hm
    refine ⟨δ, hδ, ?_⟩
    rw [he, hf, ← mul_assoc,
      (GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC (γ₀ * g) (dict g).1).2.2.2.2.1 k hk'.1]
  · intro g
    obtain ⟨γ₀, -, hf⟩ := hd.1 g
    rw [hf]
    exact (GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC (γ₀ * g) (dict g).1).2.1
  · intro g τ i
    obtain ⟨γ₀, -, hf⟩ := hd.1 g
    rw [hf]
    exact (GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC (γ₀ * g) (dict g).1).2.2.1 τ i

theorem frame_rmul_lact {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (γ : GL (Fin r) E) (x b : Frame Ψ r) : rmul (lact γ x) b = lact γ (rmul x b) := by
  funext τ
  exact Matrix.mul_assoc (α := ℂ) _ (mat x τ) (mat b τ)

theorem dict_eq_of_mark (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r) (hC : C.OK)
    (dict : GA D V → Σ k, Frame (C.M.X k).Ψ r) (hd : C.IsDict dict) (g : GA D V) (k : Fin C.F.n)
    (γ : GA D V) (hm : C.Mark g k γ) :
    ∃ δ ∈ (C.M.X k).Γ, dict g = ⟨k, lact δ (C.fr (γ * g) k)⟩ := by
  obtain ⟨γ', hm', he⟩ := hd.1 g
  have hu := GlobalTheory.MarkUniq.mark_unique D H Dw l Xo c σ V r C hC g
  have hk : k = (dict g).1 := hu.1 _ _ _ _ hm hm'
  subst hk
  obtain ⟨δ, hδ, e⟩ := hu.2 _ _ _ hm hm'
  refine ⟨δ, hδ, ?_⟩
  rw [← e, ← he]

theorem dict_real_equivariant_onto : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → (∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V C.th C.hr (fun k => C.fr 1 k) h (dict g).1))⟩) ∧ ∀ k, ∀ x ∈ (C.M.X k).dom, ∃ g, ∃ γ ∈ (C.M.X k).Γ, ∃ b ∈ Bor (C.M.X k).Ψ r, dict g = ⟨k, rmul (lact γ x) b⟩ := by
  intro D H Dw l Xo c σ V r C hC dict hd
  refine ⟨fun g h hh => ?_, fun k x hx => ?_⟩
  · obtain ⟨γ, hm, he⟩ := hd.1 g
    have hm2 := (GlobalTheory.Member.mark_move D H Dw l Xo c σ V r C hC g _ γ hm).2.2.1 h hh
    obtain ⟨δ, hδ, e⟩ := dict_eq_of_mark D H Dw l Xo c σ V r C hC dict hd (g * h) _ γ hm2
    refine ⟨δ, hδ, ?_⟩
    rw [e, ← mul_assoc, (GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC (γ * g) _).2.2.2.2.2.1 h, ← he]
  · obtain ⟨x₀, b, hb, ho, hx₀⟩ := (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E r
      (C.M.X k).p0 (C.M.X k).Ψ (C.M.X k).Gm (C.M.X k).Gm_herm).1 x hx
    obtain ⟨u, hu, hux⟩ := (GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC 1 k).2.2.2.2.2.2 x₀ ho
    obtain ⟨f, hf, hm⟩ := GlobalTheory.Member.exists_finite_mark D H Dw l Xo c σ V r C hC k
    have hm2 := (GlobalTheory.Member.mark_move D H Dw l Xo c σ V r C hC f k 1 hm).2.2.1 u hu
    obtain ⟨δ, hδ, e⟩ := dict_eq_of_mark D H Dw l Xo c σ V r C hC dict hd (f * u) k 1 hm2
    refine ⟨f * u, δ, hδ, b, hb, ?_⟩
    rw [e, one_mul, ← (GlobalTheory.UnitarySplit.real_finite_split D V).2.1 u hu f hf,
      (GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC u k).2.2.2.2.1 f hf, hux, hx₀, frame_rmul_lact]

theorem dictIsUnif_of_isDict : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → DictIsUnif V dict Kf C.th C.hr := by
  intro D H Dw l Xo c σ V r C hC dict hd Kf hK
  obtain ⟨h1, h2, h3, -, -⟩ := dict_invariant D H Dw l Xo c σ V r C hC dict hd Kf hK
  obtain ⟨h4, h5⟩ := dict_real_equivariant_onto D H Dw l Xo c σ V r C hC dict hd
  refine ⟨h1, h2, ⟨fun k => C.fr 1 k, fun k => ⟨(GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC 1 k).2.1, hd.2 k⟩, h4⟩,
    h3, h5, ?_⟩
  rintro g g' ⟨δ, hδ, he⟩
  obtain ⟨γ, hγ, hf⟩ := hd.1 g
  obtain ⟨γ', hγ', hf'⟩ := hd.1 g'
  rw [he] at hγ' hf'
  dsimp only at hγ' hf'
  obtain ⟨γ₁, hγ₁, hm, hfr⟩ := (GlobalTheory.Member.mark_move D H Dw l Xo c σ V r C hC g _ γ hγ).2.2.2 δ hδ
  have hk := GlobalTheory.Member.mem_level_of_mark_of_frame_eq D H Dw l Xo c σ V r C hC Kf hK g g' _ _ _ hm hγ' (by rw [hfr, ← hf, hf'])
  refine ⟨γ'⁻¹ * (γ₁ * γ), mul_mem (inv_mem hγ'.1) hm.1, _, hk, ?_⟩
  group

theorem adel_leftInv_and_continuous : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ mu : GA D V → ℂ, (∀ g g', mu (g * g') = mu g * mu g') → (∀ γ ∈ GQ V, mu γ = 1) → Continuous mu → ∀ (la : ∀ k, Wt (C.M.X k).Ψ r) (P : FDSec C.M.X), IsHolCusp C.M.X la P → (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P) := by
  intro D H Dw l Xo c σ V r C hC dict hd mu hmul hrat hm la P hP
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨⟨Kf, hKf⟩, hnb⟩ := GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds D V l.M
  obtain ⟨h1, -, h3, -, h5⟩ := dict_invariant D H Dw l Xo c σ V r C hC dict hd Kf hKf
  have hχ := hC.base.chi
  have hsec : ∀ k, (C.M.X k).IsSec (la k) (P k) := fun k => (hP k).1.1
  constructor
  · intro γ hγ g
    obtain ⟨γ', hγ', he⟩ := h1 γ hγ g
    show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
    rw [he, hmul, hrat γ hγ, one_mul]
    show mu g * P (dict g).1 (lact γ' (dict g).2) = _
    rw [(hsec _).2.2 γ' hγ' _ (h3 g), hχ, one_mul]
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨γ, hmk, -⟩ := hd.1 g₀
    generalize (dict g₀).1 = k at hmk
    have hfr := fun h => GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC h k
    have hPc : ContinuousOn (P k) (C.M.X k).dom := (hsec k).1.continuousOn
    have hx : Continuous (fun g : GA D V => C.fr (γ * g) k) :=
      (hfr 1).2.2.2.1.comp (continuous_const.mul continuous_id)
    have hc : Continuous (fun g => mu g * P k (C.fr (γ * g) k)) :=
      hm.mul (hPc.comp_continuous hx fun g => (hfr _).2.1)
    have hN : {g : GA D V | FinCong V l.M (g₀⁻¹ * g)} ∈ 𝓝 g₀ := by
      have hcont : ContinuousAt (fun g : GA D V => g₀⁻¹ * g) g₀ :=
        (continuous_const.mul continuous_id).continuousAt
      have h0 := hnb hM
      rw [← inv_mul_cancel g₀] at h0
      exact hcont h0
    have heq : (fun g => mu g * P k (C.fr (γ * g) k)) =ᶠ[𝓝 g₀] adel V dict mu P := by
      filter_upwards [hN] with g hg
      have hmk' := (GlobalTheory.Member.mark_move D H Dw l Xo c σ V r C hC g₀ k γ hmk).2.1 _ hg
      rw [mul_inv_cancel_left] at hmk'
      obtain ⟨δ, hδ, he⟩ := h5 g k γ hmk'
      show mu g * P k (C.fr (γ * g) k) = mu g * P (dict g).1 (dict g).2
      rw [he]
      show _ = mu g * P k (lact δ (C.fr (γ * g) k))
      rw [(hsec k).2.2 δ hδ _ (hfr _).2.1, hχ, one_mul]
    exact hc.continuousAt.congr heq

theorem exists_pkgLaws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a, χ (idF D a) = 1) → ∃ un dict mu, C.IsDict dict ∧ GlobalTheory.FrameUnif.FramesOK C.e C.F C.M un ∧ PkgLaws V C.hr C.ι Kf χ (C.unf un) dict mu C.x₀ := by
  intro D H Dw l Xo c σ V r C hC Kf hK χ hχ hχF
  have hS := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hT := GlobalTheory.firstFiveLaws.2.1.secTwist
  have hneg : GlobalTheory.FrameUnif.NegXi C.M :=
    (GlobalTheory.Member.exists_ctx D H Dw l Xo c σ V r C.hr C.ι hC.iota hC.pos hC.lA hC.good).2.1 C hC
  obtain ⟨un, hun⟩ := GlobalTheory.FrameUnif.exists_framesOK hS hT _ H Dw l Xo c σ C.g C.e C.F r C.M hC.good hC.base hneg
  obtain ⟨dict, hd⟩ := GlobalTheory.Member.Ctx.exists_isDict D H Dw l Xo c σ V r C hC
  obtain ⟨mu, hval, hmul, hnorm, hrat, hcont⟩ := GlobalTheory.Member.exists_muVal D V χ hχ hχF
  have hU := GlobalTheory.FrameUnif.isUnf_built hS _ H Dw l Xo c σ C.g C.e C.F r C.M un hC.good hC.base hneg hun
  have : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  refine ⟨un, dict, mu, hd, hun, ?_⟩
  refine
    { unf := (Formalism.L2.PjFree.isUnf_ofPj (C.unf un)).1 hU
      unTest := fun k x => GlobalTheory.Frames.allTest_of_secBaseChange hS _ H Dw l Xo c (CAt σ) (un k x)
      chi1 := hC.base.chi
      modelW := hC.modelW
      familyUniformisationBasePointOrthogonal := hC.orth
      muUnit := ⟨hmul, hnorm, hrat, (dict_invariant D H Dw l Xo c σ V r C hC dict hd Kf hK).2.2.2.1⟩
      muCont := hcont
      muVal := hval
      adelAut := adel_leftInv_and_continuous D H Dw l Xo c σ V r C hC dict hd mu hmul hrat hcont
      expo := fun ρ => ⟨GlobalTheory.CuspCentre.latZ _ r ρ _ C.M.X,
        GlobalTheory.ExpoModels.expoMatch_models _ H Dw l Xo _ C.g _ C.F r C.M ρ hC.base hC.lA⟩
      dictLaws := ⟨C.g, C.e, C.F, id, C.M.φ, C.th, fun _ τ => hC.inf τ.1,
        dictIsUnif_of_isDict D H Dw l Xo c σ V r C hC dict hd Kf hK, ⟨hC.base.ef, fun k x => ?_⟩, fun h => ?_⟩ }
  · obtain ⟨Pm, h1, h2, h3, h4, -⟩ := hun.1 k x
    exact ⟨Pm, h1, h2, h3, h4⟩
  · obtain ⟨γ, ⟨h1, h2, h3⟩, h4⟩ := hd.1 h
    refine ⟨γ, h1, h2, h3, fun τ => ?_⟩
    exact congrFun h4 τ

theorem not_iotaOK_zero {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) (V : HSp D)
    (hV : 0 < V.rank) : ¬ IotaOK Dw V 0 := by
  intro h
  have h1 := GlobalTheory.Member.Inhab.latG_one_span V
  rw [← h.emb.2, LinearMap.range_zero] at h1
  have h2 : (Pi.single ⟨0, hV⟩ 1 : Fin V.rank → D.host.E) ∈
      Submodule.span D.host.E ((⊥ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set _) := by
    rw [h1]; trivial
  rw [Submodule.bot_coe, Submodule.span_zero_singleton, Submodule.mem_bot] at h2
  simpa using congrFun h2 ⟨0, hV⟩

theorem isRat_mul {D : D7} (V : HSp D) {a b : GA D V} {a' b' : GL (Fin V.rank) D.host.E}
    (ha : IsRat V a a') (hb : IsRat V b b') : IsRat V (a * b) (a' * b') := by
  unfold IsRat at *
  rw [map_mul, map_mul, ha, hb]

theorem exists_ctx_dict_pkg (D : D7) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) :
    ∃ (l : Level (hostOfRecord D)) (Xo : Moduli (datumW D j hj) l) (c : Coeff l) (σ : c.F →+* ℂ)
      (C : Ctx Xo c σ (D.sp.W j) (D.sp.W j).rank) (Kf : Subgroup (GA D (D.sp.W j))),
      C.OK ∧ 3 ≤ (D.sp.W j).rank ∧ 0 < C.F.n ∧ IsLevelK (D.sp.W j) l.M Kf ∧
      ∃ un dict mu, C.IsDict dict ∧ PkgLaws (D.sp.W j) C.hr C.ι Kf 1 (C.unf un) dict mu C.x₀ := by
  obtain ⟨l, Xo, c, σ, C, hC, h3, hn, -⟩ := GlobalTheory.Member.Inhab.exists_ctx_ok_at_lift D j hj
  obtain ⟨⟨Kf, hK⟩, -⟩ := GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds D (D.sp.W j) l.M
  obtain ⟨un, dict, mu, h1, -, h2⟩ := exists_pkgLaws D _ _ l Xo c σ _ _ C hC Kf hK 1
    ⟨continuous_const, fun _ => rfl⟩ (fun _ => rfl)
  exact ⟨l, Xo, c, σ, C, Kf, hC, h3, hn, hK, un, dict, mu, h1, h2⟩

end GlobalTheory.MemberModel
