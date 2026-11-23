import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepRows

namespace WeakSepPf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

variable (G) in

theorem nonempty_coreVol : Nonempty (CoreVol G) := ⟨fun i => (GlobalTheory.Unf.Inhab.nonempty_vol (G.V (.core i))).some⟩

theorem rapidDec_of_rapidRow {M : Vol G} {u : GA D (Yc D 0) → ℂ} (h : RapidRow W M u) : RapidDec (Yc D 0) u :=
  h (fun _ => 0) (fun _ => default) 0 (Nat.zero_le _)

theorem rapidDec_of_reach {v : CoreVol G} {F : Fn G (.core 0)} (h : F ∈ Reach W v) : RapidDec (G.V (.core 0)) F := by
  obtain ⟨Ψ, hΨ, rfl, -⟩ := h
  exact hΨ.1 0 (Nat.zero_le _)

theorem integrableOn_corePeriod_rapidlyDecreasing {M : Vol G} (hM : M.IsRow) {F : Fn G (.core 0)}
    (hF : RapidDec (G.V (.core 0)) F) {u : GA D (Yc D 0) → ℂ} (hu : RapidDec (Yc D 0) u) :
    IntegrableOn (fun h => F (stabilizerEmbedding G.sp.dec0 h) * u h) (M.fd (.grid 0 0)) (M.ν (.grid 0 0)) := by
  obtain ⟨h1, h2⟩ := (hM.row 0 (Nat.zero_le _)).haar_fund
  obtain ⟨C, hC⟩ := hF.2.2 0
  exact RapidDec.integrableOn_mul_of_le (V := Yc D 0) (f := fun h => F (stabilizerEmbedding G.sp.dec0 h)) hu h1 h2
    ((hF.2.1.comp (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding G.sp.dec0)).aestronglyMeasurable) (C := C) (A := 0)
    fun g => by simpa using hC _

theorem exists_reach_of_span {M : Vol G} (hM : M.IsRow) {v : CoreVol G}
    {u : GA D (Yc D 0) → ℂ} (hu : RapidDec (Yc D 0) u) {F : Fn G (.core 0)} (hF : F ∈ Submodule.span ℂ (Reach W v))
    (h0 : per0 G M F u ≠ 0) : ∃ F' ∈ Reach W v, per0 G M F' u ≠ 0 := by
  by_contra hn
  push_neg at hn
  have key : IntegrableOn (fun h => F (stabilizerEmbedding G.sp.dec0 h) * u h) (M.fd (.grid 0 0)) (M.ν (.grid 0 0)) ∧
      per0 G M F u = 0 := by
    clear h0
    induction hF using Submodule.span_induction with
    | mem x hx => exact ⟨integrableOn_corePeriod_rapidlyDecreasing hM (rapidDec_of_reach W hx) hu, hn x hx⟩
    | zero => exact ⟨by simp only [Pi.zero_apply, zero_mul]; exact integrableOn_zero, by simp [per0]⟩
    | add x y _ _ hx hy =>
      have e : (fun h => (x + y) (stabilizerEmbedding G.sp.dec0 h) * u h) =
          fun h => x (stabilizerEmbedding G.sp.dec0 h) * u h + y (stabilizerEmbedding G.sp.dec0 h) * u h := by
        funext h; simp [add_mul]
      refine ⟨e ▸ hx.1.add hy.1, ?_⟩
      have a := hx.2
      have b := hy.2
      unfold per0 at a b ⊢
      erw [e, integral_add hx.1 hy.1, a, b, add_zero]
    | smul c x _ hx =>
      have e : (fun h => (c • x) (stabilizerEmbedding G.sp.dec0 h) * u h) = fun h => c * (x (stabilizerEmbedding G.sp.dec0 h) * u h) := by
        funext h; simp [mul_assoc]
      refine ⟨e ▸ hx.1.const_mul c, ?_⟩
      have a := hx.2
      unfold per0 at a ⊢
      erw [e, integral_const_mul, a, mul_zero]
  exact h0 key.2

end WeakSepPf

theorem weakSep_of_steps : SizeGap → CoreModels → RowRapid → PeriodNe → CoreOnto → Ascent → WeakSep := by
  intro hs h1 h2 h3 h4 h5 ε CF hCF
  obtain ⟨x, hx⟩ := h3 ε CF hCF
  obtain ⟨x', hx'⟩ := hs ε
  refine ⟨max x x', fun D large₂ e a b T L μ0 hL G W M hM M₀ hc0 t ht t0 w w0 => ?_⟩
  have q := offQ_of_sizeRows b
  have s := hx' D large₂ e (le_trans (le_max_right _ _) a) b
  obtain ⟨MP, hMP⟩ := h1 D q T L μ0 hL _ G W M hM 0 (Nat.zero_le _)
  obtain ⟨y, hy, v, hv, hp⟩ := hx D large₂ e (le_trans (le_max_left _ _) a) b T L μ0 hL G W M hM M₀ MP t ht t0 w w0
  obtain ⟨vol⟩ := WeakSepPf.nonempty_coreVol G
  have hr := (h2 D q s T L μ0 hL _ rfl G W M hM M₀ hc0 t ht w).1
  obtain ⟨F, ⟨Ψ, hΨ, rfl, c, hcol, ξ, hξ⟩, hF⟩ := WeakSepPf.exists_reach_of_span W hM (WeakSepPf.rapidDec_of_rapidRow W hr)
    (h4 D q s T L μ0 hL _ rfl G W M hM vol MP hMP y hy v hv) hp
  obtain ⟨ρ, Φ, hB⟩ := h5 D q T L μ0 hL _ G W M hM vol Ψ hΨ _ hr hF
  exact ⟨ρ, ξ, c, hcol, Φ, by rw [fPsiPhi, ← hξ]; exact hB⟩

end GlobalTheory.SepRows

end
