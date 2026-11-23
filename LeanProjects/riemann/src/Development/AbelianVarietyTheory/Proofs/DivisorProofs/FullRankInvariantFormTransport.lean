import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankZetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenUnitMinorSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGroupOfUnitMinorStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitMinorStableIntegralGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMinorTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenCoverFiniteTranslatesSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenIntegrabilityFullRankOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOrbitalIntegralStableStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

open GlobalTheory.SplitFlip

theorem GlobalTheory.FullRankCoinv.form_vanish_of_smallF_vanish : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Bf : GlobalTheory.FullRankCoinv.fullRk k n d →ₗ[ℂ] GlobalTheory.FullRankCoinv.fullRk k n d →ₗ⋆[ℂ] ℂ,
      (∀ (g : GL (Fin n) k) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d), Ψ₁'.1 = GlobalTheory.FullRankCoinv.lact ν g Ψ₁.1 →
        Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) →
      (∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d,
        (∀ (Y₁ Y₂ : Matrix (Fin n) (Fin d) k), Ψ₁.1 Y₁ ≠ 0 → Ψ₂.1 Y₂ ≠ 0 → ∀ a : GL (Fin n) k, Y₁ ≠ a.1 * Y₂) →
        Bf Ψ₁ Ψ₂ = 0) →
      ∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d,
        (∀ Y, Ψ₂.1 Y ≠ 0 → GlobalTheory.SplitFlip.smallF (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₁.1 Y = 0) →
        Bf Ψ₁ Ψ₂ = 0 := by
  intro k _ _ _ _ _ _ n d ν hnd hν Bf hA hS Ψ₁ Ψ₂ hF0
  classical

  have hle : GlobalTheory.FullRankCoinv.augRk n d ν ≤ GlobalTheory.FullRankCoinv.fullRk k n d := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, Ψ, hΨ, rfl⟩
    exact sub_mem (GlobalTheory.FullRankCoinv.Reduce.lact_mem ν g hΨ) hΨ
  have hkill : ∀ x (hx : x ∈ GlobalTheory.FullRankCoinv.augRk n d ν),
      Bf ⟨x, hle hx⟩ Ψ₂ = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, Ψ, hΨ, rfl⟩ := hz
      have e : (⟨GlobalTheory.FullRankCoinv.lact ν g Ψ - Ψ, hle (Submodule.subset_span ⟨g, Ψ, hΨ, rfl⟩)⟩ :
          GlobalTheory.FullRankCoinv.fullRk k n d) =
          ⟨GlobalTheory.FullRankCoinv.lact ν g Ψ, GlobalTheory.FullRankCoinv.Reduce.lact_mem ν g hΨ⟩ - ⟨Ψ, hΨ⟩ := rfl
      rw [e, map_sub, LinearMap.sub_apply, hA g ⟨Ψ, hΨ⟩ _ Ψ₂ rfl, sub_self]
    | zero =>
      have e : (⟨0, hle (Submodule.zero_mem _)⟩ : GlobalTheory.FullRankCoinv.fullRk k n d) = 0 := rfl
      rw [e, map_zero, LinearMap.zero_apply]
    | add x y hx hy ihx ihy =>
      have e : (⟨x + y, hle (Submodule.add_mem _ hx hy)⟩ : GlobalTheory.FullRankCoinv.fullRk k n d) =
          ⟨x, hle hx⟩ + ⟨y, hle hy⟩ := rfl
      rw [e, map_add, LinearMap.add_apply, ihx, ihy, add_zero]
    | smul c x hx ihx =>
      have e : (⟨c • x, hle (Submodule.smul_mem _ c hx)⟩ : GlobalTheory.FullRankCoinv.fullRk k n d) = c • ⟨x, hle hx⟩ := rfl
      rw [e, map_smul, LinearMap.smul_apply, ihx, smul_zero]
  set S := GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d with hSdef
  have hSc : IsClopen S := GlobalTheory.T.isClopen_unit_minor_set k n d

  obtain ⟨s, hs⟩ := GlobalTheory.T.open_cover_finite_translates_support k n d S hSc.isOpen (GlobalTheory.T.exists_unit_minor_translate k n d) Ψ₁.1 Ψ₁.2
  obtain ⟨Φ, hΦ, hΦS, hdiff, hFΦ⟩ := GlobalTheory.T.clopen_integrability_full_rank_orbit k n d ν S hSc
    (fun Φ hΦ Y => GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Φ hΦ Y) s Ψ₁.1 Ψ₁.2 hs
  have e1 : Ψ₁ = ⟨Ψ₁.1 - Φ, hle hdiff⟩ + ⟨Φ, hΦ⟩ := Subtype.ext (by simp)
  rw [e1, map_add, LinearMap.add_apply, hkill _ hdiff, zero_add]

  obtain ⟨⟨hlc₂, hcs₂⟩, _⟩ := Ψ₂.2
  set V := Function.support Ψ₂.1 with hVdef
  have hVo : IsOpen V := hlc₂ {0}ᶜ
  have hVc : IsCompact V := by
    have hcl : IsClosed V := by
      have h := (hlc₂.isOpen_fiber 0).isClosed_compl
      convert h using 1
      ext Y; simp [V, Function.mem_support]
    exact IsCompact.of_isClosed_subset hcs₂ hcl (subset_tsupport _)
  obtain ⟨s₂, hs₂⟩ := GlobalTheory.T.open_cover_finite_translates_support k n d S hSc.isOpen (GlobalTheory.T.exists_unit_minor_translate k n d) Ψ₂.1 Ψ₂.2

  set C : Set (Matrix (Fin n) (Fin d) k) := {Y | Y ∈ S ∧ ∃ a : GL (Fin n) k, Ψ₂.1 (a.val * Y) ≠ 0} with hCdef
  have hCo : IsOpen C := by
    have : C = S ∩ ⋃ a : GL (Fin n) k, (fun Y => a.val * Y) ⁻¹' V := by
      ext Y; simp [C, V, Function.mem_support]
    rw [this]
    exact hSc.isOpen.inter (isOpen_iUnion fun a => hVo.preimage (continuous_const.matrix_mul continuous_id))
  set T : Set (Matrix (Fin n) (Fin d) k) := (⋃ E ∈ s₂, (fun Y => E.val * Y) '' V) ∩ S with hTdef
  have hTc : IsCompact T :=
    (s₂.isCompact_biUnion fun E _ => hVc.image (continuous_const.matrix_mul continuous_id)).inter_right hSc.isClosed
  have hCimg : C = (fun p : GL (Fin n) k × Matrix (Fin n) (Fin d) k => p.1.val * p.2) ''
      ((GlobalTheory.SplitWeil.KO k (Fin n) : Set (GL (Fin n) k)) ×ˢ T) := by
    ext Y
    constructor
    · rintro ⟨hYS, a, ha⟩
      obtain ⟨E, hE, hES⟩ := hs₂ _ ha
      have hκ : E * a ∈ GlobalTheory.SplitWeil.KO k (Fin n) :=
        GlobalTheory.T.integral_group_of_unit_minor_stable k n d (E * a) Y hYS (by rwa [Units.val_mul, Matrix.mul_assoc])
      refine ⟨((E * a)⁻¹, (E * a).val * Y), ⟨inv_mem hκ, ?_, ?_⟩, ?_⟩
      · refine Set.mem_biUnion hE ⟨a.val * Y, ha, ?_⟩
        simp only [Units.val_mul, Matrix.mul_assoc]
      · rw [Units.val_mul, Matrix.mul_assoc]; exact hES
      · simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    · rintro ⟨⟨κ, Z⟩, ⟨hκ, hZ, hZS⟩, rfl⟩
      obtain ⟨E, hE, v, hv, rfl⟩ := Set.mem_iUnion₂.1 hZ
      refine ⟨GlobalTheory.T.unit_minor_stable_integral_group k n d κ _ hκ hZS, E⁻¹ * κ⁻¹, ?_⟩
      have : (E⁻¹ * κ⁻¹).val * (κ.val * (E.val * v)) = v := by
        simp only [Units.val_mul, ← Matrix.mul_assoc]
        rw [Matrix.mul_assoc (E⁻¹).val, Units.inv_mul, Matrix.mul_one, Units.inv_mul, Matrix.one_mul]
      show Ψ₂.1 ((E⁻¹ * κ⁻¹).val * (κ.val * (E.val * v))) ≠ 0
      rw [this]; exact hv
  have hCc : IsClosed C := by
    rw [hCimg]
    exact ((GlobalTheory.SplitFlip.isCompact_KO).prod hTc).image
      ((Units.continuous_val.comp continuous_fst).matrix_mul continuous_snd) |>.isClosed
  have hC : IsClopen C := ⟨hCc, hCo⟩

  have h1 := GlobalTheory.FullRankCoinv.Reduce.indicator_mem hC hΦ
  have h2 := GlobalTheory.FullRankCoinv.Reduce.indicator_mem hC.compl hΦ
  have e2 : (⟨Φ, hΦ⟩ : GlobalTheory.FullRankCoinv.fullRk k n d) = ⟨C.indicator Φ, h1⟩ + ⟨Cᶜ.indicator Φ, h2⟩ :=
    Subtype.ext (Set.indicator_self_add_compl C Φ).symm
  rw [e2, map_add, LinearMap.add_apply]

  have hCorb : ∀ (g : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k), Y ∈ C → g.val * Y ∈ S → g.val * Y ∈ C := by
    rintro g Y ⟨_, a, ha⟩ hgY
    refine ⟨hgY, a * g⁻¹, ?_⟩
    rwa [Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (g⁻¹).val, Units.inv_mul, Matrix.one_mul]
  have hA1 : C.indicator Φ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
    refine GlobalTheory.T.smooth_character_orbital_integral_stable k n d ν hν C (fun E Y hY hEY => GlobalTheory.T.integral_group_of_unit_minor_stable k n d E Y hY.1 hEY.1)
      (fun E hE Y hY => hCorb E Y hY (GlobalTheory.T.unit_minor_stable_integral_group k n d E Y hE hY.1)) _ h1
      (fun Y hY => Set.indicator_of_notMem hY _) (fun Y hY => ?_)
    have hint : smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν (C.indicator Φ) Y =
        smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y := by
      unfold smallF
      congr 1; funext g
      by_cases hg : g.val * Y ∈ C
      · rw [Set.indicator_of_mem hg]
      · have : Φ (g.val * Y) = 0 := by
          by_contra h0
          exact hg (hCorb g Y hY (by by_contra hn; exact h0 (hΦS _ hn)))
        rw [Set.indicator_of_notMem hg, this]
    rw [hint, hFΦ]
    obtain ⟨_, a, ha⟩ := hY
    have hz := hF0 (a.val * Y) ha
    rw [← smallF_mul_left (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₁.1 a Y, hz, mul_zero]
  have e3 := hkill _ hA1
  rw [e3, zero_add]
  refine hS _ _ fun Y₁ Y₂ hY₁ hY₂ a heq => ?_
  have hn : Y₁ ∉ C := fun hm => hY₁ (Set.indicator_of_notMem (Set.notMem_compl_iff.2 hm) _)
  have hΦ1 : Φ Y₁ ≠ 0 := by
    intro h0; apply hY₁
    show Cᶜ.indicator Φ Y₁ = 0
    by_cases hm : Y₁ ∈ Cᶜ
    · rw [Set.indicator_of_mem hm, h0]
    · exact Set.indicator_of_notMem hm _
  have hY₁S : Y₁ ∈ S := by by_contra hn'; exact hΦ1 (hΦS _ hn')
  refine hn ⟨hY₁S, a⁻¹, ?_⟩
  rw [heq, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]; exact hY₂
