import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ProdFormulaE
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.L2.SG.NGCut
  Formalism.L2.SG.NGData

namespace Formalism.L2.SG.NGHTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def nDelta {E : Type} [Field E] (r : ℕ) (γ : PN.Pts E r) : ℕ :=
  r * (r + 1) + ∑ a : Fin γ.1.length, endIdx γ a * (2 * r + 1 - endIdx γ a)

def HTPlace : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ {Cl' Nu : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl') (nml : TauC Y u u' → Nu)
        (γ : PN.Pts D.host.E D.R.rS) (Fm : LocFam (zOf Y) Cl' Nu), FamTie TS cls nml γ Fm →
        (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ≠ 0 ∧ ∀ a, endMin γ a ≠ 0) ∧ ∀ p : PlF D,
        ((Fm.FP p).PrimeTo → (Fm.FP p).Hp = 1) ∧
        (Fm.FP p).Hp =
          ((zOf Y).M p).modK (algebraMap _ _ (LocNG.theta ((zOf Y).M p))) ^ ((2 * D.R.rS + 1 : ℝ) / 2) *
          ((zOf Y).M p).modK (algebraMap _ _ ((zOf Y).δ p)) ^ (nDelta D.R.rS γ : ℝ) *
          ((zOf Y).M p).modK ((D.s.atP p).ιE (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ)) ^ (-(1 / 2 : ℝ)) *
          ∏ a : Fin γ.1.length, (((zOf Y).M p).modK ((D.s.atP p).ιE (endMin γ a)))⁻¹

def HTDelta : Prop :=
  ∀ (D : D7) (Z : LocDat D),
    (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (Z.δ p))).Finite ∧
    ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (Z.δ p)) =
      (D.host.rdE ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹

def HTTheta : Prop :=
  ∀ (D : D7) (Z : LocDat D),
    (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p)))).Finite ∧
    ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) =
      (((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹

section Asm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem prod_inf_sq (x : E) : ∏ w : InfinitePlace E, w x ^ 2 = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [(IsTotallyComplex.isComplex w).mult_eq_two]

theorem prod_inf (x : E) : ∏ w : InfinitePlace E, w x = Real.sqrt |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  rw [← prod_inf_sq, Finset.prod_pow, Real.sqrt_sq (Finset.prod_nonneg fun w _ => (w.1.nonneg x))]

theorem g_pow (g : ℝ) (hg : 0 < g) (f r : ℕ) :
    ((g ^ (2 * f))⁻¹) ^ ((2 * r + 1 : ℝ) / 2) = (g ^ ((2 * r + 1) * f))⁻¹ := by
  rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast g (2 * f), ← Real.rpow_mul hg.le, ← Real.rpow_natCast g]
  congr 2
  push_cast
  ring

theorem inv_rpow_half (x : ℝ) (hx : 0 ≤ x) : (x⁻¹) ^ (-(1 / 2 : ℝ)) = Real.sqrt x := by
  rw [Real.inv_rpow hx, Real.rpow_neg hx, inv_inv, Real.sqrt_eq_rpow]

theorem hpt_eq [StarRing E] (r : ℕ) (γ : PN.Pts E r) (rd g : ℝ) (hg : 0 < g) (TT : ℕ) :
    HPt rd g TT γ =
      ((g ^ (2 * Fintype.card (InfinitePlace E)))⁻¹) ^ ((2 * r + 1 : ℝ) / 2) *
      ((rd ^ (2 * Fintype.card (InfinitePlace E)))⁻¹) ^ (nDelta r γ : ℝ) *
      (|((Algebra.norm ℚ (GPt TT γ) : ℚ) : ℝ)|⁻¹) ^ (-(1 / 2 : ℝ)) *
      ∏ a : Fin γ.1.length, (|((Algebra.norm ℚ (endMin γ a) : ℚ) : ℝ)|⁻¹)⁻¹ := by
  set f := Fintype.card (InfinitePlace E) with hf
  rw [g_pow g hg f r, inv_rpow_half _ (abs_nonneg _), Real.rpow_natCast]
  simp only [inv_inv]
  unfold HPt NGPt NDPt
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hf, prod_inf]
  have hD : ∀ a : Fin γ.1.length, ∏ w : InfinitePlace E,
      (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * w (endMin γ a) ^ 2 =
      ((rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹) ^ f * |((Algebra.norm ℚ (endMin γ a) : ℚ) : ℝ)| := by
    intro a
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hf, prod_inf_sq]
  simp_rw [hD]
  rw [Finset.prod_mul_distrib]
  have hrd : ((rd ^ (2 * r * (r + 1)))⁻¹) ^ f *
      ∏ a : Fin γ.1.length, ((rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹) ^ f =
      ((rd ^ (2 * f))⁻¹) ^ nDelta r γ := by
    simp only [← inv_pow, ← pow_mul, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, ← mul_inv, ← pow_add]
    congr 2
    unfold nDelta
    have e : ∀ i : Fin γ.1.length, 2 * (endIdx γ i * (2 * r + 1 - endIdx γ i)) * f =
        2 * f * (endIdx γ i * (2 * r + 1 - endIdx γ i)) := fun i => by ring
    simp only [e, ← Finset.mul_sum]
    ring
  rw [← hrd]
  ring

end Asm

section Main

open Formalism.MainNotions.S.LocNG

theorem hTie_of (hP : HTPlace) (hD : HTDelta) (hT : HTTheta) : Formalism.L2.SG.FamDefs.HTie := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a0, b0, hP2⟩ := hP Cg cb Cw cT CT C0
  refine ⟨a0, b0, ?_⟩
  intro C' Cl e1 e2 D large₂ X Y u u' hc Cl' Nu TS cls nml γ Fm hFT
  obtain ⟨⟨hG0, hD0⟩, hloc⟩ := hP2 C' Cl e1 e2 D large₂ X Y u u' hc TS cls nml γ Fm hFT
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨w, F00, F'0, F'1, hw, -, -, -, -, -, -, hgood, -⟩ := hFT
  have hOK : ∀ p, ((zOf Y).M p).OK := fun p => ((zOf Y).agree p).1
  have hPF := (product_formula_e D.host.F D.host.E _ (Formalism.MainNotions.BridgeLemma.szf_finrankFE D) D.s.atP).1 (zOf Y).M hOK
  obtain ⟨hAf, hAv⟩ := hT D (zOf Y)
  obtain ⟨hBf, hBv⟩ := hD D (zOf Y)
  obtain ⟨hCf, hCv⟩ := hPF _ hG0
  have hDf := fun a => hPF _ (hD0 a)
  classical
  set S : Finset (PlF D) := Fm.P ∪ hAf.toFinset ∪ hBf.toFinset ∪ hCf.toFinset ∪
    Finset.univ.biUnion (fun a => (hDf a).1.toFinset) with hS
  have hPS : Fm.P ⊆ S := fun p hp => by simp [hS, hp]
  have hsA : (Function.mulSupport fun p : PlF D =>
      ((zOf Y).M p).modK (algebraMap _ _ (LocNG.theta ((zOf Y).M p)))) ⊆ ↑S := fun p hp => by
    simp [hS, Set.Finite.mem_toFinset, hp]
  have hsB : (Function.mulSupport fun p : PlF D => ((zOf Y).M p).modK (algebraMap _ _ ((zOf Y).δ p))) ⊆ ↑S :=
    fun p hp => by simp [hS, Set.Finite.mem_toFinset, hp]
  have hsC : (Function.mulSupport fun p : PlF D =>
      ((zOf Y).M p).modK ((D.s.atP p).ιE (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ))) ⊆ ↑S :=
    fun p hp => by simp [hS, Set.Finite.mem_toFinset, hp]
  have hsD : ∀ a, (Function.mulSupport fun p : PlF D => ((zOf Y).M p).modK ((D.s.atP p).ιE (endMin γ a))) ⊆ ↑S :=
    fun a p hp => by
      simp only [hS, Finset.coe_union, Finset.coe_biUnion, Finset.coe_univ, Set.mem_union, Set.mem_iUnion,
        Set.Finite.coe_toFinset, Set.mem_univ, true_and]
      exact Or.inr ⟨a, trivial, hp⟩
  have hnn : ∀ p (x : (D.s.atP p).Ep), 0 ≤ ((zOf Y).M p).modK x := fun p x => ENNReal.toReal_nonneg

  have h1 : Fm.toL.Htot = ∏ p ∈ S, (Fm.FP p).Hp := by
    show ∏ p : {p // p ∈ Fm.P}, (Fm.FP p.1).Hp = _
    rw [Finset.prod_coe_sort Fm.P (fun p => (Fm.FP p).Hp)]
    exact Finset.prod_subset hPS fun p _ hp => (hloc p).1 (hgood p hp)
  rw [h1, Finset.prod_congr rfl fun p _ => (hloc p).2, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_comm (s := S) (t := Finset.univ),
    Real.finsetProd_rpow S (fun p => ((zOf Y).M p).modK (algebraMap _ _ (LocNG.theta ((zOf Y).M p))))
      (fun p _ => hnn p _),
    Real.finsetProd_rpow S (fun p => ((zOf Y).M p).modK (algebraMap _ _ ((zOf Y).δ p))) (fun p _ => hnn p _),
    Real.finsetProd_rpow S (fun p => ((zOf Y).M p).modK ((D.s.atP p).ιE (GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ)))
      (fun p _ => hnn p _)]
  simp_rw [Finset.prod_inv_distrib]
  rw [← finprod_eq_prod_of_mulSupport_subset _ hsA, ← finprod_eq_prod_of_mulSupport_subset _ hsB,
    ← finprod_eq_prod_of_mulSupport_subset _ hsC, hAv, hBv, hCv]
  have hDv : ∀ a, ∏ p ∈ S, ((zOf Y).M p).modK ((D.s.atP p).ιE (endMin γ a)) =
      |((Algebra.norm ℚ (endMin γ a) : ℚ) : ℝ)|⁻¹ := fun a => by
    rw [← finprod_eq_prod_of_mulSupport_subset _ (hsD a), (hDf a).2]
  simp_rw [hDv]
  have hg : (0 : ℝ) < ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by
    have h0 := (D.host.g_prime 0).pos
    have h1 := (D.host.g_prime 1).pos
    exact_mod_cast Nat.mul_pos h0 h1
  have hXg : (X.B.g : ℝ) = ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by rw [X.g_eq]
  rw [hXg, ← Finset.prod_inv_distrib]
  exact hpt_eq D.R.rS γ D.host.rdE _ hg _

end Main

end Formalism.L2.SG.NGHTie
