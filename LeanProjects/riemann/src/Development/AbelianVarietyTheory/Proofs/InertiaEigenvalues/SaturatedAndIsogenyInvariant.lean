import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulIntegralBis

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.Isog

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem pow_smul_eq (T : LocLat G Qp LL O) (k : ℕ) (x : W.DD T) :
    ((PD.p : ℕ) : LetA O n) ^ k • x = ((PD.p : ℕ) : O) ^ k • x := by
  rw [← map_natCast (algebraMap O (LetA O n)), ← map_pow, algebraMap_smul]

theorem sat_of (T : LocLat G Qp LL O)
    (hs : ∀ (m : ℕ) (x : W.DD T), ((PD.p : O) ^ m) • x ∈ W.N T → x ∈ W.N T) : wachSaturated W T := by
  rintro x ⟨k, hk⟩
  rw [pow_smul_eq] at hk
  exact hs k x hk

theorem isog_of {T' T : LocLat G Qp LL O} (f : LatHom T'.L T.L)
    (hi : Function.Bijective f.f → Function.Injective (W.map f) ∧
      (∃ c : ℕ, ∀ y : W.DD T, ∃ x : W.DD T', W.map f x = ((PD.p : O) ^ c) • y ∧
        (y ∈ W.N T → x ∈ W.N T')) ∧
      ∀ x : W.DD T', W.map f x ∈ W.N T ↔ x ∈ W.N T') : p6V W f := by
  intro hf
  obtain ⟨hinj, ⟨c, hc⟩, -⟩ := hi hf
  refine ⟨fun x _ hx => hinj (hx.trans (map_zero _).symm), fun y hy => ?_⟩
  obtain ⟨x, hx, hxN⟩ := hc y
  exact ⟨c, x, hxN hy, hx.trans (pow_smul_eq W T c y).symm⟩

end Generic

set_option linter.unusedVariables false in

theorem saturated_and_isogeny_invariant : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; (∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → wachSaturated W T) ∧ ∀ (T' T : Lt K LL) (f : LatHom T'.L T.L), IsCrys ((D.loc l).PD K) T'.ρ → IsCrys ((D.loc l).PD K) T.ρ → p6V W f := by
  intro D HW F l _ K s LL h W E
  refine ⟨fun T hT => sat_of W T fun m x hx => sat_loc (HW l) K s LL h T hT m x hx,
    fun T' T f hT' hT => isog_of W f fun hf => isog_loc (HW l) K s LL h T' T f hT' hT hf⟩

end GlobalTheory.NL.Isog
