import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianOrbitUniqueLatticeIntegralFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameWitnessIntegralChangeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermLatticeOverInnerDatumFgSpanStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermNoDefectPrimeToInvariantsStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass.Fibre

theorem rank_eq (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  obtain ⟨a, ha⟩ := D.R.m_even
  have := D.R.two_le_m
  unfold Formalism.BasicNotions.Ranks.r Formalism.BasicNotions.Ranks.rS
  omega

theorem finrank_eq {D : D7} (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp, rank_eq]

theorem theta_eq_one {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {p : PlF D}
    (h : (FP p).PrimeTo) : LocNG.theta (Z.M p) = 1 := by
  unfold LocNG.theta
  rw [h.1]

theorem isLat : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D) (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → t.abelian₂.FG ∧ Submodule.span (D.s.atP p).Ep (t.abelian₂ : Set (Vp D p)) = ⊤ := GlobalTheory.T.localTermLattice_over_innerDatum_fg_span

theorem noDefect : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), (FP p).RelG (LocNG.theta (Z.M p)) → (FP p).PrimeTo → ∀ (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → ¬ LocNG.BBne (H := locH Z p) t := GlobalTheory.T.localTerm_noDefect_primeTo_invariants

theorem fibre : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → ∀ y : Dat Z FP, (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) → {p | y p ≠ d0 p}.Finite → ((globSet G G' y).encard : ℝ≥0∞) = ∏ p ∈ P, ((locSet G G' p (y p)).encard : ℝ≥0∞) := by
  intro D Z FP u u' F G F' G' P d0 hk hB hS y hrel hfin
  obtain ⟨hBased, hRelG, hPrime, hTerm0, Λ₀, hΛ₀, hΛ₀t⟩ := hB
  obtain ⟨-, -, -, -, hloc⟩ := hS
  have hLG := LatLoc.lattices_local_global D Z

  have single : ∀ p, p ∉ P → ∃! L, L ∈ locSet G G' p (y p) := by
    intro p hp
    obtain ⟨A, A', hA, hA', hint, hc, hc'⟩ := hloc p hp
    have key := GlobalTheory.T.hermitian_orbit_unique_lattice_integral_frames (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) hk (finrank_eq p)
      (hRelG p) (hPrime p hp) A A' (fun a b h => ⟨hA.1 a b h, hA'.1 a b h⟩) (fun a => ⟨hA.2 a, hA'.2 a⟩) hint
      (scaled Z p (frame G)) (scaled Z p (frame G'))
      (fun j => by rw [hc j, (hBased p).1]; rfl) (fun j => by rw [hc' j, (hBased p).2.1]; rfl)
      (d0 p) (hTerm0 p) (y p)
    exact key.1 (hrel p hp)

  have std : ∀ p, p ∉ P → y p = d0 p → lattice₂ D Z.M p Λ₀ ∈ locSet G G' p (y p) := by
    intro p hp hy
    rw [hy]
    obtain ⟨A, A', hA, hA', hint, hc, hc'⟩ := hloc p hp
    have hT : LocNG.IsTermOver (FP p) (d0 p) (tm FP G G' p (lattice₂ D Z.M p Λ₀)) :=
      GlobalTheory.T.hermitian_frame_witness_integral_change (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (finrank_eq p) (hRelG p) (d0 p)
        (tm FP F F' p (lattice₂ D Z.M p Λ₀)) (hΛ₀t p hp) A A' (scaled Z p (frame G)) (scaled Z p (frame G')) hA hA'
        (fun a b => ⟨(hint a b).1, (hint a b).2, by
          rw [theta_eq_one (hPrime p hp), map_one]
          refine Submodule.mem_span_singleton.2 ⟨⟨A a b - A' a b, (Z.M p).L.O.sub_mem (hint a b).1 (hint a b).2⟩, ?_⟩
          first
            | (rw [Algebra.smul_def, mul_one]; rfl)
            | (rw [Submodule.smul_def]; simp)
            | (simp [Algebra.smul_def])
            | (erw [smul_eq_mul, mul_one])
            | (change (A a b - A' a b) * 1 = _; rw [mul_one])⟩) hc hc'
    exact ⟨hT, noDefect D Z FP p (hRelG p) (hPrime p hp) (d0 p) _ hT⟩

  let Φ : LV D → ∀ q : P, Submodule (Z.M q).L.O (Vp D q) := fun Λ q => lattice₂ D Z.M q Λ
  have hinj : Set.InjOn Φ (globSet G G' y) := by
    intro Λ₁ h₁ Λ₂ h₂ e
    refine (hLG.1 Λ₁ Λ₂ h₁.1 h₂.1).2 fun p => ?_
    by_cases hp : p ∈ P
    · exact congrFun e ⟨p, hp⟩
    · exact (single p hp).unique (h₁.2 p) (h₂.2 p)
  have himg : Φ '' globSet G G' y = Set.univ.pi (fun q : P => locSet G G' q (y q)) := by
    ext g
    constructor
    · rintro ⟨Λ, hΛ, rfl⟩ q -
      exact hΛ.2 q
    · intro hg
      let Lp : ∀ p : PlF D, Submodule (Z.M p).L.O (Vp D p) := fun p =>
        if h : p ∈ P then g ⟨p, h⟩ else (single p h).exists.choose
      have hLp : ∀ p, Lp p ∈ locSet G G' p (y p) := by
        intro p
        by_cases h : p ∈ P
        · simp only [Lp, dif_pos h]; exact hg ⟨p, h⟩ (Set.mem_univ _)
        · simp only [Lp, dif_neg h]; exact (single p h).exists.choose_spec
      have hlat : ∀ p, (Lp p).FG ∧ Submodule.span (D.s.atP p).Ep (Lp p : Set (Vp D p)) = ⊤ :=
        fun p => isLat D Z FP p (y p) (tm FP G G' p (Lp p)) (hLp p).1
      have hfin' : {p | Lp p ≠ lattice₂ D Z.M p Λ₀}.Finite := by
        refine ((P.finite_toSet).union hfin).subset fun p hp => ?_
        by_contra hn
        simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hn
        exact hp ((single p hn.1).unique (hLp p) (std p hn.1 hn.2))
      obtain ⟨Λ, hΛ, hΛp⟩ := hLG.2 Λ₀ hΛ₀ Lp hlat hfin'
      refine ⟨Λ, ⟨hΛ, fun p => by rw [hΛp p]; exact hLp p⟩, ?_⟩
      funext q
      show lattice₂ D Z.M q Λ = g q
      rw [hΛp q]
      show (if h : (q : PlF D) ∈ P then g ⟨q, h⟩ else (single q h).exists.choose) = g q
      rw [dif_pos q.2]
  have e1 := hinj.encard_image
  rw [himg, Set.encard_pi_eq_prod_encard] at e1
  rw [← e1]
  exact (map_prod ENat.toENNRealRingHom (fun i : P => (locSet G G' i (y i)).encard) Finset.univ).trans
    (Finset.prod_coe_sort P (fun p => ((locSet G G' p (y p)).encard : ℝ≥0∞)))

end GlobalTheory.GenMass.Fibre
