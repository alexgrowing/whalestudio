import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

open TypesA

variable (W : LocWach PD LL O v n)

section Smul

variable {T : LocLat G Qp LL O}

theorem algebraMap_mem_invariants (t : O) : algebraMap O (LetA O n) t ∈ W.AΔ := W.AΔ.algebraMap_mem t

theorem algebraMap_smul_eq_smul (t : O) (x : W.DD T) : algebraMap O (LetA O n) t • x = t • x :=
  algebraMap_smul (LetA O n) t x

theorem inI_algebraMap_smul {c : ZMod n} (t : O) {w : W.DD T} (h : InI W T c w) :
    InI W T c (algebraMap O (LetA O n) t • w) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • (algebraMap O (LetA O n) t • w) = algebraMap O (LetA O n) t • w
    rw [smul_comm]
    exact congrArg _ h1
  · intro δ hδ
    rw [algebraMap_smul_eq_smul, map_smul, h2 δ hδ]
  · have : W.γ T (algebraMap O (LetA O n) t • w) - algebraMap O (LetA O n) t • w =
        algebraMap O (LetA O n) t • (W.γ T w - w) := by
      rw [algebraMap_smul_eq_smul, algebraMap_smul_eq_smul, map_smul, smul_sub]
    rw [this]
    exact InFNc_smul W (algebraMap_mem_invariants W t) h3

theorem repVV_smul_invariant {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ} {b : Fin d → W.DD T}
    {sol : Fin d → ℕ → Fin d → LL} (a : LetA O n) (ha : a ∈ W.AΔ) {x : W.DD T} {f : Fin d → W.EE}
    (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (a • x) (fun k => algebraMap (LetA O n) W.EE a * f k) := by
  obtain ⟨κ, κ', H, a', hH, ha', hP⟩ := h
  refine ⟨κ, κ', H, fun k => a * a' k, hH,
    fun k => ⟨W.AΔ.mul_mem ha (ha' k).1, ?_⟩, ?_⟩
  · rw [map_mul, ← (ha' k).2]
    ring
  · have hs : ∑ k, (a * a' k) • ((W.φD T) ^ e) (H k) = a • ∑ k, a' k • ((W.φD T) ^ e) (H k) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => mul_smul _ _ _
    rw [hs]
    have key : lA W ^ κ' • (lA W ^ κ • Λ • (a • x) - a • ∑ k, a' k • ((W.φD T) ^ e) (H k)) =
        a • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a' k • ((W.φD T) ^ e) (H k))) := by
      simp only [smul_sub]
      rw [smul_comm Λ a x, smul_comm (lA W ^ κ) a, smul_comm (lA W ^ κ') a, smul_comm (lA W ^ κ') a]
    rw [key]
    exact inMultiple_smul W ha hP

end Smul

theorem liftsAt_algebraMap_mul (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d) {g : W.EE}
    {e : ℕ} (t : O) (h : LiftsAt W A F c bb sol k₀ g e) :
    LiftsAt W A F c bb sol k₀ (algebraMap O W.EE t * g) e := by
  obtain ⟨w₁, z, h1, ⟨Λ', hΛ', h2⟩, h3, h4, h5⟩ := h
  set a := algebraMap O (LetA O n) t with ha_def
  have ha : a ∈ W.AΔ := algebraMap_mem_invariants W t
  refine ⟨a • w₁, a • z, inI_algebraMap_smul W t h1, ⟨Λ', hΛ', ?_⟩, ?_, InFNc_smul W ha h4, ?_⟩
  · rw [smul_comm]
    exact InFNc_smul W ha h2
  · rw [map_smulA, smul_comm]
    exact inMultiple_smul W ha h3
  · have h6 := repVV_smul_invariant W a ha h5
    rw [map_smulA, ← smul_sub]
    refine RepVV_congr W h6 rfl fun k => ?_
    have hat : algebraMap (LetA O n) W.EE a = algebraMap O W.EE t := by
      rw [ha_def, ← IsScalarTower.algebraMap_apply]
    split_ifs
    · rw [hat]; ring
    · rw [mul_zero]

end Formalism.MainNotions.N.FrobeniusPowerSeries
