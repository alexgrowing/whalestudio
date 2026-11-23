import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix

noncomputable section

namespace GlobalTheory.FullRankCoinv

theorem continuous_of_mul_right_inv {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) (f : G → ℂ) (hf : ∀ g, ∀ h ∈ H, f (g * h) = f g) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have ho : IsOpen ((g⁻¹ * ·) ⁻¹' (H : Set G)) := hH.preimage (continuous_const.mul continuous_id)
  have hev : ∀ᶠ x in nhds g, f g = f x := by
    filter_upwards [ho.mem_nhds (by simpa using H.one_mem)] with x hx
    have := hf g (g⁻¹ * x) hx
    simpa using this.symm
  exact tendsto_const_nhds.congr' hev

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_gdet (n : ℕ) : Continuous (gdet : GL (Fin n) k → kˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · convert (Units.continuous_val (M := Matrix (Fin n) (Fin n) k)).matrix_det using 1
    funext g; exact Matrix.GeneralLinearGroup.val_det_apply g
  · convert (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) k)).matrix_det using 1
    funext g
    show (((gdet g)⁻¹ : kˣ) : k) = _
    rw [← map_inv]; exact Matrix.GeneralLinearGroup.val_det_apply _

theorem continuous_char_apow (n : ℕ) (ν : kˣ →* ℂˣ) (hν : GlobalTheory.SmGL.IsSmoothChar ν) (z : ℂ) :
    Continuous fun g : GL (Fin n) k => (ν (gdet g) : ℂ) * apow (gdet g) z := by
  let H : Subgroup (GL (Fin n) k) := GlobalTheory.SplitWeil.KO k (Fin n) ⊓ ν.ker.comap Matrix.GeneralLinearGroup.det
  have hH : IsOpen (H : Set (GL (Fin n) k)) :=
    isOpen_KO.inter (hν.preimage (continuous_gdet (k := k) n))
  refine continuous_of_mul_right_inv H hH _ fun g h hh => ?_
  have h1 : ν (gdet h) = 1 := hh.2
  have h2 : apow (gdet h) z = 1 := apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hh.1) z
  simp only [gdet_mul, map_mul, Units.val_mul, apow_mul, h1, h2, Units.val_one, mul_one]

theorem integrable_fibre (n d : ℕ) (ν : kˣ →* ℂˣ) (hν : GlobalTheory.SmGL.IsSmoothChar ν)
    [MeasurableSpace k] [BorelSpace k] (Ψ : Matrix (Fin n) (Fin d) k → ℂ) (hΨ : Ψ ∈ fullRk k n d)
    (Y : Matrix (Fin n) (Fin d) k) :
    Integrable (fun g : GL (Fin n) k =>
      Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))
      (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) := by
  obtain ⟨⟨hlc, hcs⟩, hrk⟩ := hΨ
  by_cases hY : Y.rank = n
  swap
  · have h0 : (fun g : GL (Fin n) k =>
        Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) = 0 := by
      funext g
      have : (g.val * Y).rank = Y.rank :=
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
      rw [hrk _ (by rw [this]; exact hY)]; simp
    rw [h0]; exact integrable_zero _ _ _

  obtain ⟨R, hR⟩ : ∃ R : Matrix (Fin d) (Fin n) k, Y * R = 1 := by
    have hsurj : LinearMap.range Y.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]; exact hY
    obtain ⟨f, hf⟩ := LinearMap.exists_rightInverse_of_surjective _ hsurj
    refine ⟨LinearMap.toMatrix' f, ?_⟩
    have := congrArg LinearMap.toMatrix' hf
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id,
      show LinearMap.toMatrix' Y.mulVecLin = Y from LinearMap.toMatrix'_toLin' Y] at this

  have hsupp : tsupport Ψ = Function.support Ψ := by
    refine (IsClosed.closure_eq ?_)
    convert (hlc.isOpen_fiber 0).isClosed_compl using 1
    ext x; simp [Function.support]
  have hrkS : ∀ X ∈ tsupport Ψ, X.rank = n := fun X hX => by
    by_contra h; rw [hsupp] at hX; exact hX (hrk X h)
  set K' : Set (Matrix (Fin n) (Fin d) k) := tsupport Ψ ∩ {X | X * R * Y = X}
  have hK' : IsCompact K' := hcs.inter_right
    (isClosed_eq ((continuous_id.matrix_mul continuous_const).matrix_mul continuous_const) continuous_id)
  have hunit : ∀ X ∈ K', IsUnit (X * R) := fun X hX => by
    have h1 : n ≤ (X * R).rank := by
      calc n = X.rank := (hrkS X hX.1).symm
        _ = (X * R * Y).rank := by rw [hX.2]
        _ ≤ (X * R).rank := Matrix.rank_mul_le_left _ _
    have h2 : (X * R).rank = Fintype.card (Fin n) := le_antisymm
      ((Matrix.rank_le_card_width _).trans (by simp)) (by simpa using h1)
    have hli : LinearIndependent k (X * R).row := by
      rw [linearIndependent_iff_card_eq_finrank_span]
      exact h2.symm.trans (Matrix.rank_eq_finrank_span_row _)
    exact Matrix.linearIndependent_rows_iff_isUnit.1 hli
  classical
  let φ : Matrix (Fin n) (Fin d) k → GL (Fin n) k := fun X =>
    if h : IsUnit (X * R) then h.unit else 1
  have hφ : ∀ X ∈ K', (φ X).val = X * R := fun X hX => by simp [φ, hunit X hX]
  have hφc : ContinuousOn φ K' := by
    rw [(isEmbedding_val_GL (k := k) (n := Fin n)).isInducing.continuousOn_iff]
    exact (continuous_id.matrix_mul continuous_const).continuousOn.congr fun X hX => hφ X hX
  set S : Set (GL (Fin n) k) := {g | g.val * Y ∈ tsupport Ψ}
  have hSsub : S ⊆ φ '' K' := fun g hg => by
    have hX : g.val * Y ∈ K' := ⟨hg, show g.val * Y * R * Y = g.val * Y by rw [Matrix.mul_assoc g.val Y R, hR, Matrix.mul_one]⟩
    refine ⟨_, hX, Units.ext ?_⟩
    rw [hφ _ hX, Matrix.mul_assoc, hR, Matrix.mul_one]
  have hSc : IsClosed S := (isClosed_tsupport Ψ).preimage (Units.continuous_val.matrix_mul continuous_const)
  have hS : IsCompact S := (hK'.image_of_continuousOn hφc).of_isClosed_subset hSc hSsub
  have hcont : Continuous (fun g : GL (Fin n) k =>
      Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) := by
    have h1 : Continuous fun g : GL (Fin n) k => Ψ (g.val * Y) :=
      hlc.continuous.comp (Units.continuous_val.matrix_mul continuous_const)
    refine (h1.mul (continuous_char_apow n ν hν ((Fintype.card (Fin d) : ℂ) / 2))).congr fun g => ?_
    simp only [Pi.mul_apply]; ring
  letI : MeasurableSpace (GL (Fin n) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin n) k) := borel_GL
  refine hcont.integrable_of_hasCompactSupport (μ := haarVol (GlobalTheory.SplitWeil.KO k (Fin n)))
    (HasCompactSupport.intro hS fun g hg => ?_)
  rw [image_eq_zero_of_notMem_tsupport hg]; simp

end GlobalTheory.FullRankCoinv

theorem GlobalTheory.FullRankCoinv.integrable_fibre_target : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    ∀ Y : Matrix (Fin n) (Fin d) k, Integrable (fun g : GL (Fin n) k =>
      Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) :=
  fun _ _ _ _ _ _ _ n d ν hν Ψ hΨ Y => GlobalTheory.FullRankCoinv.integrable_fibre n d ν hν Ψ hΨ Y
