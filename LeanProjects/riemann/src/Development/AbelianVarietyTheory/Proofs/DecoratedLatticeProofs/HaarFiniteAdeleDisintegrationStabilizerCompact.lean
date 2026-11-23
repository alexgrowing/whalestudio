import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.SfinHaar

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH Topology

theorem exists_idem_of_subspace {E : Type} [Field E] {n : ℕ} (W : Submodule E (Fin n → E)) :
    ∃ e : Matrix (Fin n) (Fin n) E, e * e = e ∧ ∀ x, x ∈ W ↔ e *ᵥ x = x := by
  obtain ⟨W', hc⟩ := W.exists_isCompl
  obtain ⟨p, hp⟩ : ∃ p : Matrix (Fin n) (Fin n) E, ∀ x, p *ᵥ x = Submodule.projection W W' hc x :=
    ⟨LinearMap.toMatrix' _, fun x => LinearMap.toMatrix'_mulVec _ x⟩
  have h1 : ∀ x, p *ᵥ x ∈ W := fun x => hp x ▸ Submodule.projection_apply_mem hc x
  have h2 : ∀ x ∈ W, p *ᵥ x = x := fun x hx => (hp x).trans (Submodule.projection_apply_of_mem_left hc hx)
  refine ⟨p, Matrix.ext_iff_mulVec.2 fun y => by rw [← Matrix.mulVec_mulVec, h2 _ (h1 y)], fun x =>
    ⟨fun hx => h2 x hx, fun hx => hx ▸ h1 x⟩⟩

theorem span_incl_eq (I : AutInst) (T : Set (Fin I.n → I.E)) :
    Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (incl I '' T) =
      Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
        ((fun w i => GlobalTheory.UnipApprox.inc I (w i)) '' (Submodule.span I.E T : Set (Fin I.n → I.E))) := by
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    induction hw using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have : (fun i => GlobalTheory.UnipApprox.inc I ((0 : Fin I.n → I.E) i)) = 0 := by ext; simp
      beta_reduce; rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : (fun i => GlobalTheory.UnipApprox.inc I ((x + y) i)) =
          (fun i => GlobalTheory.UnipApprox.inc I (x i)) + fun i => GlobalTheory.UnipApprox.inc I (y i) := by ext; simp
      rw [SetLike.mem_coe] at hx hy; beta_reduce at hx hy ⊢; rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : (fun i => GlobalTheory.UnipApprox.inc I ((a • x) i)) =
          GlobalTheory.UnipApprox.inc I a • fun i => GlobalTheory.UnipApprox.inc I (x i) := by ext; simp
      rw [SetLike.mem_coe] at hx; beta_reduce at hx ⊢; rw [this]; exact Submodule.smul_mem _ _ hx

theorem isClosed_cond (I : AutInst) (v : Fin I.n → I.E) (T : Set (Fin I.n → I.E)) :
    IsClosed {x : I.Gf | (I.fmat x - 1) *ᵥ incl I v ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (incl I '' T)} := by
  obtain ⟨t, hr, h2, -, -, -, hind⟩ := GlobalTheory.UnipApprox.exists_top I
  obtain ⟨e, he, hW⟩ := exists_idem_of_subspace (Submodule.span I.E T)
  have hset : {x : I.Gf | (I.fmat x - 1) *ᵥ incl I v ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (incl I '' T)} =
      {x | e.map (GlobalTheory.UnipApprox.inc I) *ᵥ ((I.fmat x - 1) *ᵥ incl I v) = (I.fmat x - 1) *ᵥ incl I v} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [span_incl_eq]
    exact GlobalTheory.UnipApprox.mem_span_iff (GlobalTheory.UnipApprox.inc I) he _ hW _
  rw [hset]
  have hc : Continuous fun x : I.Gf => I.fmat x := Units.continuous_val.comp hind.continuous
  have hc2 : Continuous fun x : I.Gf => (I.fmat x - 1) *ᵥ incl I v :=
    (hc.sub continuous_const).matrix_mulVec continuous_const
  exact isClosed_eq (continuous_const.matrix_mulVec hc2) hc2

theorem isClosed_sfin (I : AutInst) {r : ℕ} (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) :
    IsClosed (Sfin I e z) := by
  have h1 : ∀ a : Fin r, IsClosed {x : I.Gf | (I.fmat x - 1) *ᵥ incl I (e a) ∈
      Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((fun b => incl I (e b)) '' {b | b.1 < a.1})} := by
    intro a
    have := isClosed_cond I (e a) (e '' {b : Fin r | b.1 < a.1})
    rwa [Set.image_image] at this
  have h2 : IsClosed {x : I.Gf | (I.fmat x - 1) *ᵥ incl I z ∈
      Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => incl I (e b))} := by
    have := isClosed_cond I z (Set.range e)
    rwa [← Set.range_comp] at this
  unfold Sfin
  rw [Set.setOf_and, Set.setOf_forall]
  exact (isClosed_iInter h1).inter h2

end GlobalTheory.SfinHaar

namespace GlobalTheory.SfinHaar

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH Topology MeasureTheory

theorem disint_finPart : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    ∃ μSf : Measure (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)), μSf.IsHaarMeasure ∧ SigmaFinite μSf ∧
      ∃ c : ℝ, 0 < c ∧ ∀ φ : X.B.I.Gf → ENNReal, Measurable φ →
        (∀ x, φ x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x = s * X.xu u * k) →
        ∫⁻ x, φ x ∂X.B.μf = ENNReal.ofReal c * ∫⁻ t, ∫⁻ k in X.K2, φ (t.1 * X.xu u * k) ∂X.B.μf ∂μSf := by
  intro D X u
  set G := X.B.I.Gf
  set S := Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u) with hSdef
  set K := X.K2 with hKdef
  set x := X.xu u with hxdef
  haveI : SecondCountableTopology G := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI : X.B.μf.IsHaarMeasure := X.B.haar
  have hKg := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hKt := Formalism.L2.SG.Pf.level_subgroup_compact_open X
  have hK1 : (1 : G) ∈ K := hKg.1
  have hKmul : ∀ a ∈ K, ∀ b ∈ K, a * b ∈ K := hKg.2.1
  have hKinv : ∀ a ∈ K, a⁻¹ ∈ K := hKg.2.2.1
  have hKo : IsOpen K := hKt.1
  have hKc : IsCompact K := hKt.2
  haveI : LocallyCompactSpace G := hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds hK1)
  have hSc : IsClosed (S : Set G) := isClosed_sfin X.B.I X.eR (X.zR u)

  set C : Set G := {g | x⁻¹ * g * x ∈ K} with hCdef
  have hCeq : C = (fun k => x * k * x⁻¹) '' K := by
    ext g
    constructor
    · intro hg; exact ⟨x⁻¹ * g * x, hg, by group⟩
    · rintro ⟨k, hk, rfl⟩
      show x⁻¹ * (x * k * x⁻¹) * x ∈ K
      simpa [mul_assoc] using hk
  have hCc : IsCompact C := hCeq ▸ hKc.image ((continuous_const_mul _).mul continuous_const)
  have hCo : IsOpen C := hKo.preimage ((continuous_const_mul _).mul continuous_const)
  set H : Set S := Subtype.val ⁻¹' C with hHdef
  have hHc : IsCompact H := hSc.isClosedEmbedding_subtypeVal.isCompact_preimage hCc
  have hHo : IsOpen H := hCo.preimage continuous_subtype_val
  have hH1 : (1 : S) ∈ H := by
    show x⁻¹ * ((1 : S) : G) * x ∈ K
    simpa using hK1
  haveI : LocallyCompactSpace S := hHc.locallyCompactSpace_of_mem_nhds_of_group (hHo.mem_nhds hH1)
  let K₀ : TopologicalSpace.PositiveCompacts S := ⟨⟨H, hHc⟩, ⟨1, hHo.subset_interior_iff.2 le_rfl hH1⟩⟩
  set ν : Measure S := Measure.haarMeasure K₀ with hνdef
  haveI : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure K₀
  have hνH : ν H = 1 := Measure.haarMeasure_self
  refine ⟨ν, inferInstance, inferInstance, 1, one_pos, fun φ hφ hsupp => ?_⟩
  rw [ENNReal.ofReal_one, one_mul]

  set Z : Set (S × G) := {p | x⁻¹ * ((p.1 : G)⁻¹ * p.2) ∈ K} with hZdef
  have hZo : IsOpen Z := hKo.preimage
    (continuous_const.mul ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd))
  have hZm : MeasurableSet Z := hZo.measurableSet
  have hKm : MeasurableSet K := hKo.measurableSet
  let F : S → G → ENNReal := fun t g => φ g * Z.indicator 1 (t, g)
  have hF : Measurable (Function.uncurry F) :=
    (hφ.comp measurable_snd).mul (measurable_one.indicator hZm)

  have hA : ∀ t : S, ∫⁻ g, F t g ∂X.B.μf = ∫⁻ k in K, φ ((t : G) * x * k) ∂X.B.μf := by
    intro t
    rw [← lintegral_mul_left_eq_self _ ((t : G) * x), ← lintegral_indicator hKm]
    refine lintegral_congr fun k => ?_
    have e : x⁻¹ * ((t : G)⁻¹ * ((t : G) * x * k)) = k := by group
    by_cases hk : k ∈ K
    · have : ((t, (t : G) * x * k) : S × G) ∈ Z := by show x⁻¹ * ((t : G)⁻¹ * ((t : G) * x * k)) ∈ K; rw [e]; exact hk
      simp only [F]
      rw [Set.indicator_of_mem this, Set.indicator_of_mem hk, Pi.one_apply, mul_one]
    · have : ((t, (t : G) * x * k) : S × G) ∉ Z := by show ¬ x⁻¹ * ((t : G)⁻¹ * ((t : G) * x * k)) ∈ K; rw [e]; exact hk
      simp only [F]
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hk, mul_zero]

  have hC' : ∀ g, ∫⁻ t, F t g ∂ν = φ g := by
    intro g
    by_cases h0 : φ g = 0
    · simp [F, h0]
    obtain ⟨s, hs, k, hk, rfl⟩ := hsupp g h0
    have hset : {t : S | (t, s * x * k) ∈ Z} = (fun t => (⟨s, hs⟩ : S)⁻¹ * t) ⁻¹' H := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      show x⁻¹ * ((t : G)⁻¹ * (s * x * k)) ∈ K ↔ x⁻¹ * (s⁻¹ * (t : G)) * x ∈ K
      have e : x⁻¹ * ((t : G)⁻¹ * (s * x * k)) = (x⁻¹ * (s⁻¹ * (t : G)) * x)⁻¹ * k := by group
      rw [e]
      constructor
      · intro h
        have := hKinv _ (hKmul _ h _ (hKinv _ hk))
        simpa using this
      · intro h
        exact hKmul _ (hKinv _ h) _ hk
    have hmeas : MeasurableSet {t : S | (t, s * x * k) ∈ Z} :=
      hZm.preimage (measurable_id.prodMk measurable_const)
    calc ∫⁻ t, F t (s * x * k) ∂ν = ∫⁻ t, φ (s * x * k) * {t : S | (t, s * x * k) ∈ Z}.indicator 1 t ∂ν := by
          refine lintegral_congr fun t => ?_
          simp only [F]
          congr 1
      _ = φ (s * x * k) * ν {t : S | (t, s * x * k) ∈ Z} := by
          rw [lintegral_const_mul _ (measurable_one.indicator hmeas), lintegral_indicator_one hmeas]
      _ = φ (s * x * k) := by
          rw [hset, measure_preimage_mul, hνH, mul_one]
  calc ∫⁻ g, φ g ∂X.B.μf = ∫⁻ g, ∫⁻ t, F t g ∂ν ∂X.B.μf := lintegral_congr fun g => (hC' g).symm
    _ = ∫⁻ t, ∫⁻ g, F t g ∂X.B.μf ∂ν := (lintegral_lintegral_swap hF.aemeasurable).symm
    _ = ∫⁻ t, ∫⁻ k in K, φ ((t : G) * x * k) ∂X.B.μf ∂ν := lintegral_congr fun t => hA t

end GlobalTheory.SfinHaar
