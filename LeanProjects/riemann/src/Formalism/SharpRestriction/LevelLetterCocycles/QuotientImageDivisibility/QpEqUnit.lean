import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.GammaLevelsExpansion
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsInIInPNPowSmulSubMap

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Trans

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem qp_eq_unit (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    ∃ U : (LetA O n)ˣ, Formalism.MainNotions.LiftingTheory.qp W = (U : LetA O n) * W.Q := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  have hE : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))
      W.π₀ = Formalism.MainNotions.LiftingTheory.qp W := by
    funext i
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀]
  rw [hE] at hw
  refine ⟨w⁻¹, ?_⟩
  rw [Q_eq_q W hs, hw, ← mul_assoc, Units.inv_mul, one_mul]

theorem trans_d [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (c : ZMod n)
    (δ : W.Gam) (hδ : δ ∈ W.DelF) (ζ ζ' : LL) (χ : LL) (hχ0 : χ ≠ 0)
    (hΔN : ∀ (x : ↥(W.N T)) (hx : W.γD T δ x ∈ W.N T) (k : ℤ),
      W.levN T c ζ ⟨W.γD T δ x, hx⟩ k = χ ^ k • W.levN T c ζ' x k)
    (hΔA : ∀ f : LetA O n, W.lev c ζ (W.γA δ f) = PowerSeries.rescale χ (W.lev c ζ' f))
    {w : W.DD T} (hwΔ : W.γD T δ w = w) {K : ℕ} (hK : W.Q ^ K • w ∈ W.N T)
    (u u' : PowerSeries LL) (hu : W.lev c ζ W.q = X * u) (hu' : W.lev c ζ' W.q = X * u')
    (hu0 : constantCoeff u ≠ 0)
    {dz dz' : ℤ → T.V ⊗[Qp] BdR} (hdz : ∃ m, LB m dz) (hdz' : ∃ m, LB m dz')
    (ez : W.levN T c ζ ⟨W.Q ^ K • w, hK⟩ = smulS ((X * u) ^ K) dz)
    (ez' : W.levN T c ζ' ⟨W.Q ^ K • w, hK⟩ = smulS ((X * u') ^ K) dz') :
    dz = resc χ dz' := by
  obtain ⟨m, hm⟩ := hdz
  obtain ⟨m', hm'⟩ := hdz'
  have hQ : W.Q = W.q := Q_eq_q W hs
  obtain ⟨U, hU⟩ := qp_eq_unit W hs hR
  have hxeq : Formalism.MainNotions.LiftingTheory.qp W ^ K • w = (U : LetA O n) ^ K • (W.Q ^ K • w) := by
    rw [hU, mul_pow, mul_smul]
  have hxN : Formalism.MainNotions.LiftingTheory.qp W ^ K • w ∈ W.N T := by
    rw [hxeq]; exact (W.N T).smul_mem _ hK
  have hxΔ : W.γD T δ (Formalism.MainNotions.LiftingTheory.qp W ^ K • w) = Formalism.MainNotions.LiftingTheory.qp W ^ K • w := by
    rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', map_pow, (qp_mem_AΔ W hR) δ hδ, hwΔ]
  set x : ↥(W.N T) := ⟨Formalism.MainNotions.LiftingTheory.qp W ^ K • w, hxN⟩ with hxdef
  have hγx : W.γD T δ (x : W.DD T) ∈ W.N T := by rw [hxdef]; simp only; rw [hxΔ]; exact hxN
  have h1 : W.levN T c ζ x = resc χ (W.levN T c ζ' x) := by
    funext k
    simp only [resc]
    have hxx : (⟨W.γD T δ (x : W.DD T), hγx⟩ : ↥(W.N T)) = x := Subtype.ext hxΔ
    rw [← hΔN x hγx k, hxx]
  have hsplit : x = (U : LetA O n) ^ K • (⟨W.Q ^ K • w, hK⟩ : ↥(W.N T)) := Subtype.ext hxeq
  have h2 : ∀ (z : LL) (uz : PowerSeries LL) (dd : ℤ → T.V ⊗[Qp] BdR) (mm : ℤ), LB mm dd →
      W.levN T c z ⟨W.Q ^ K • w, hK⟩ = smulS ((X * uz) ^ K) dd →
      W.levN T c z x = smulS ((W.lev c z (U : LetA O n) * (X * uz)) ^ K) dd := by
    intro z uz dd mm hdd e
    rw [hsplit]
    have this : W.levN T c z ((U : LetA O n) ^ K • (⟨W.Q ^ K • w, hK⟩ : ↥(W.N T))) =
        smulS (W.lev c z ((U : LetA O n) ^ K)) (W.levN T c z ⟨W.Q ^ K • w, hK⟩) :=
      funext fun k => W.levN_smul T c z ((U : LetA O n) ^ K) ⟨W.Q ^ K • w, hK⟩ k
    rw [this, e, ← smulS_mul hdd, map_pow, ← mul_pow]
  have hz := h2 ζ u dz m hm ez
  have hz' := h2 ζ' u' dz' m' hm' ez'
  have hresc : PowerSeries.rescale χ (W.lev c ζ' (U : LetA O n) * (X * u')) =
      W.lev c ζ (U : LetA O n) * (X * u) := by
    have e1 : W.lev c ζ' (U : LetA O n) * (X * u') = W.lev c ζ' (Formalism.MainNotions.LiftingTheory.qp W) := by
      rw [hU, map_mul, hQ, hu']
    have e2 : W.lev c ζ (U : LetA O n) * (X * u) = W.lev c ζ (Formalism.MainNotions.LiftingTheory.qp W) := by
      rw [hU, map_mul, hQ, hu]
    rw [e1, e2, ← hΔA, (qp_mem_AΔ W hR) δ hδ]
  rw [h1, hz', ← smulS_rescale hm' χ hχ0, map_pow, hresc] at hz
  have hUc : constantCoeff (W.lev c ζ (U : LetA O n) * u) ≠ 0 := by
    rw [map_mul]
    refine mul_ne_zero ?_ hu0
    have hu1 : IsUnit (W.lev c ζ (U : LetA O n)) := (Units.isUnit U).map _
    exact (PowerSeries.isUnit_iff_constantCoeff.1 hu1).ne_zero
  have e3 : W.lev c ζ (U : LetA O n) * (X * u) = X * (W.lev c ζ (U : LetA O n) * u) := by ring
  rw [e3] at hz
  exact div_unique (m := min m m') (LB_mono hm (min_le_left _ _))
    (LB_mono (LB_resc hm' χ) (min_le_right _ _)) _ hUc K hz.symm

end Trans

end Formalism.MainNotions.N.Pv.LocalLengthBound
