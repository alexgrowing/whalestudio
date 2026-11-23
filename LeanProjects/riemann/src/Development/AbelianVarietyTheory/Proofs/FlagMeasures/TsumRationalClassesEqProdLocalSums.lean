import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitRepsOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumPiProdEnnreal
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass

theorem datum_wt_nonneg {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} (p : PlF D)
    (a b : LocNG.Datum (FP p)) : 0 ≤ LocNG.Datum.wt a b := by
  unfold LocNG.Datum.wt LocNG.volRel
  exact div_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem tsum_classes_eq_prod_locSums : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP) (R : ∀ p, LocNG.Reps (FP p)) (V : ℝ), 0 ≤ V → BaseOK (Tu D u) (Tu D u') F F' P d0 → MassLaw F F' P d0 V → ∀ φ : ∀ p, LocNG.Datum (FP p) → ℝ≥0∞, (∀ p d d', LocNG.Datum.Rel d d' → φ p d = φ p d') → (∀ p d, (¬ ∃ τ, LocNG.IsTermOver (FP p) d τ) → φ p d = 0) → (∑' o : Quot (GRel (Z := Z) (FP := FP) F F'), if (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (o.out p)) ∧ {p | o.out p ≠ d0 p}.Finite then (((stabY F F' o.out).encard : ℝ≥0∞))⁻¹ * ∏ p ∈ P, φ p (o.out p) else 0) = ENNReal.ofReal V * ∏ p ∈ P, ∑' d : (R p).RD, ENNReal.ofReal (LocNG.Datum.wt (d0 p) d.1) * φ p d.1 := by
  intro D Z FP u u' F F' P d0 R V hV hB hM φ hφ hφ0
  have hEq : ∀ p, Equivalence (LocNG.Datum.Rel (P := FP p)) := fun p => GlobalTheory.NonGenericLocalCheck.rel_equiv (FP p)
  let rep : ∀ p, LocNG.Datum (FP p) → (R p).RD := fun p y =>
    ⟨Classical.choose ((R p).hRD.2.1 y (Set.mem_univ y)), (Classical.choose_spec ((R p).hRD.2.1 y (Set.mem_univ y))).1⟩
  have hrep : ∀ p y, LocNG.Datum.Rel (rep p y).1 y := fun p y =>
    (Classical.choose_spec ((R p).hRD.2.1 y (Set.mem_univ y))).2
  have huniq : ∀ p y (a : (R p).RD), LocNG.Datum.Rel a.1 y → a = rep p y := fun p y a ha =>
    Subtype.ext ((R p).hRD.2.2 _ a.2 _ (rep p y).2 ((hEq p).trans ha ((hEq p).symm (hrep p y))))
  let ext : (∀ p : P, (R p.1).RD) → Dat Z FP := fun x p => if h : p ∈ P then (x ⟨p, h⟩).1 else d0 p
  have ext_in : ∀ x (p : P), ext x p.1 = (x p).1 := fun x p => by simp [ext, p.2]
  have ext_out : ∀ x p, p ∉ P → ext x p = d0 p := fun x p hp => by simp [ext, hp]
  let g : ∀ p : P, (R p.1).RD → ℝ≥0∞ := fun p d => ENNReal.ofReal (LocNG.Datum.wt (d0 p.1) d.1) * φ p.1 d.1

  have hR : ENNReal.ofReal V * ∏ p ∈ P, ∑' d : (R p).RD, ENNReal.ofReal (LocNG.Datum.wt (d0 p) d.1) * φ p d.1
      = ∑' x : (∀ p : P, (R p.1).RD), ENNReal.ofReal V * ∏ p : P, g p (x p) := by
    rw [ENNReal.tsum_mul_left, GlobalTheory.HL.tsum_pi_prod_ennreal g, ← Finset.prod_coe_sort P]

  rw [hR]
  let c : Quot (GRel (Z := Z) (FP := FP) F F') → ℝ≥0∞ := fun o =>
    (((stabY F F' o.out).encard : ℝ≥0∞))⁻¹ * ∏ p ∈ P, φ p (o.out p)

  have hx : ∀ x : (∀ p : P, (R p.1).RD), ENNReal.ofReal V * ∏ p : P, g p (x p)
      = ∑' o : Quot (GRel (Z := Z) (FP := FP) F F'), if InGen (ext x) o.out then c o else 0 := by
    intro x
    have h1 : ENNReal.ofReal V * ∏ p : P, g p (x p) = massA F F' (ext x) * ∏ p : P, φ p.1 (x p).1 := by
      by_cases hT : ∀ p : P, ∃ τ, LocNG.IsTermOver (FP p.1) (x p).1 τ
      · have hTall : ∀ p, ∃ τ, LocNG.IsTermOver (FP p) (ext x p) τ := by
          intro p
          by_cases hp : p ∈ P
          · rw [ext_in x ⟨p, hp⟩]; exact hT ⟨p, hp⟩
          · rw [ext_out x p hp]; exact hB.2.2.2.1 p
        rw [hM (ext x) (ext_out x) hTall, ENNReal.ofReal_mul hV,
          ENNReal.ofReal_prod_of_nonneg (fun p _ => datum_wt_nonneg p _ _), ← Finset.prod_coe_sort P, mul_assoc,
          ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl (fun p _ => ?_)
        simp only [g, ext_in x p]
      · push_neg at hT
        obtain ⟨p, hp⟩ := hT
        have h0 : φ p.1 (x p).1 = 0 := hφ0 p.1 _ (by push_neg; exact hp)
        rw [Finset.prod_eq_zero (Finset.mem_univ p) (by simp [g, h0]),
          Finset.prod_eq_zero (Finset.mem_univ p) h0, mul_zero, mul_zero]
    rw [h1, massA, ← ENNReal.tsum_mul_right]
    refine tsum_congr (fun o => ?_)
    split_ifs with hI
    · simp only [c]
      rw [← Finset.prod_coe_sort P (fun p => φ p (o.out p))]
      congr 1
      refine Finset.prod_congr rfl (fun p _ => ?_)
      have := hI.1 p.1
      rw [ext_in x p] at this
      exact hφ p.1 _ _ this
    · exact zero_mul _
  rw [tsum_congr hx, ENNReal.tsum_comm]
  refine tsum_congr (fun o => ?_)
  let x0 : ∀ p : P, (R p.1).RD := fun p => rep p.1 (o.out p.1)
  have hfin : ∀ x, {p | o.out p ≠ ext x p} ⊆ {p | o.out p ≠ d0 p} ∪ (P : Set (PlF D)) ∧
      {p | o.out p ≠ d0 p} ⊆ {p | o.out p ≠ ext x p} ∪ (P : Set (PlF D)) := by
    intro x
    constructor
    · intro p hp
      by_cases hpP : p ∈ P
      · exact Or.inr hpP
      · left; simpa [Set.mem_setOf_eq, ext_out x p hpP] using hp
    · intro p hp
      by_cases hpP : p ∈ P
      · exact Or.inr hpP
      · left; simpa [Set.mem_setOf_eq, ext_out x p hpP] using hp
  rw [tsum_eq_single x0]
  · have hiff : InGen (ext x0) o.out ↔ ((∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (o.out p)) ∧ {p | o.out p ≠ d0 p}.Finite) := by
      constructor
      · rintro ⟨hr, hf⟩
        refine ⟨fun p hp => ?_, ((hf.union P.finite_toSet).subset (hfin x0).2)⟩
        have := hr p; rwa [ext_out x0 p hp] at this
      · rintro ⟨hr, hf⟩
        refine ⟨fun p => ?_, ((hf.union P.finite_toSet).subset (hfin x0).1)⟩
        by_cases hp : p ∈ P
        · rw [ext_in x0 ⟨p, hp⟩]; exact hrep p _
        · rw [ext_out x0 p hp]; exact hr p hp
    simp only [hiff, c]
  · intro x hx
    rw [if_neg]
    rintro ⟨hr, _⟩
    apply hx
    funext p
    have := hr p.1
    rw [ext_in x p] at this
    exact huniq p.1 _ (x p) this

end GlobalTheory.GenMass
