import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumHeckeEigenvalueGeneratingSeriesGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaHalfMulUnrTorus
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.GLTwist

open Formalism.UG (Tj Ov)

section Twist

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ordV_mul {x y : w.adicCompletion E} (hx : x ≠ 0) (hy : y ≠ 0) :
    Formalism.UG.ordV E w (x * y) = Formalism.UG.ordV E w x + Formalism.UG.ordV E w y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, GlobalTheory.LGrp.BorelCompletion.ordV_eq, GlobalTheory.LGrp.BorelCompletion.ordV_eq, map_mul,
    WithZero.log_mul hx' hy']
  ring

theorem ordV_zpow {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (k : ℤ) : Formalism.UG.ordV E w (ϖ ^ k) = k := by
  rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, map_zpow₀, show Valued.v ϖ = _ from hϖ, WithZero.log_zpow,
    show WithZero.log (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ)) : WithZero (Multiplicative ℤ)) = -1 from rfl]
  simp

def ordDet (g : GL (Fin r) (w.adicCompletion E)) : ℤ := Formalism.UG.ordV E w g.val.det

theorem det_ne_zero (g : GL (Fin r) (w.adicCompletion E)) : g.val.det ≠ 0 :=
  (Matrix.GeneralLinearGroup.det g).ne_zero

theorem ordDet_mul (g h : GL (Fin r) (w.adicCompletion E)) : ordDet (g * h) = ordDet g + ordDet h := by
  rw [ordDet, Units.val_mul, Matrix.det_mul, ordV_mul (det_ne_zero g) (det_ne_zero h)]
  rfl

theorem ordDet_of_mem {k : GL (Fin r) (w.adicCompletion E)} (hk : k ∈ KGL w r) : ordDet k = 0 := by
  have h : Valued.v k.val.det = 1 := GlobalTheory.SphGal.isUnitAt_det_of_mem hk
  rw [ordDet, GlobalTheory.LGrp.BorelCompletion.ordV_eq, h]
  simp

theorem ordDet_one : ordDet (1 : GL (Fin r) (w.adicCompletion E)) = 0 := ordDet_of_mem (one_mem _)

theorem prod_zpow_eq {ι : Type} {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (d : ι → ℤ) (s : Finset ι) :
    ∏ i ∈ s, ϖ ^ d i = ϖ ^ ∑ i ∈ s, d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ h0]

theorem ordDet_of_diagonal {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {t : GL (Fin r) (w.adicCompletion E)}
    {d : Fin r → ℤ} (ht : t.1 = Matrix.diagonal fun i => ϖ ^ d i) : ordDet t = ∑ i, d i := by
  have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  rw [ordDet, ht, Matrix.det_diagonal, prod_zpow_eq h0, ordV_zpow hϖ]

def twistRep (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (z : ℂˣ) :
    Representation ℂ (GL (Fin r) (w.adicCompletion E)) V where
  toFun g := ((z : ℂ) ^ ordDet g) • ρ g
  map_one' := by simp [ordDet_one]
  map_mul' g h := by
    rw [ordDet_mul, zpow_add₀ z.ne_zero, map_mul]
    refine LinearMap.ext fun y => ?_
    simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul, mul_smul]
    exact smul_comm _ _ _

theorem twistRep_apply (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (z : ℂˣ)
    (g : GL (Fin r) (w.adicCompletion E)) (y : V) : twistRep ρ z g y = ((z : ℂ) ^ ordDet g) • ρ g y := rfl

theorem heckeVec_twistRep (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (z : ℂˣ)
    (t : GL (Fin r) (w.adicCompletion E)) (x : V) :
    heckeVec (twistRep ρ z) (KGL w r) (dosetInd ℂ (KGL w r) t) x =
      ((z : ℂ) ^ ordDet t) • heckeVec ρ (KGL w r) (dosetInd ℂ (KGL w r) t) x := by
  rw [heckeVec, heckeVec, smul_finsum]
  refine finsum_congr fun c => ?_
  by_cases hc : ∃ a ∈ KGL w r, ∃ b ∈ KGL w r, c.out = a * t * b
  · obtain ⟨a, ha, b, hb, e⟩ := id hc
    have h : ordDet c.out = ordDet t := by
      rw [e, ordDet_mul, ordDet_mul, ordDet_of_mem ha, ordDet_of_mem hb]
      simp
    rw [twistRep_apply, h, smul_comm]
  · rw [GlobalTheory.WeylGL.dosetInd_of_not hc]
    simp

theorem isSatVecGL_twistRep {ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V} {x : V} {B : Multiset ℂˣ}
    (hx : IsSatVecGL w ρ x B) (z : ℂˣ) : IsSatVecGL w (twistRep ρ z) x (B.map (z * ·)) := by
  refine ⟨hx.1, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by rw [Multiset.card_map, hx.2.2.1], fun ϖ hϖ j hj => ?_⟩
  · rw [twistRep_apply, ordDet_of_mem hk, zpow_zero, one_smul]
    exact GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk
  · have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
    have em : B.map (z * ·) = B.map (· * z) := Multiset.map_congr rfl fun b _ => mul_comm _ _
    have ho : ordDet (GlobalTheory.WeylGL.tor h0 fun i : Fin r => if (i : ℕ) < j then 1 else 0) = j := by
      rw [ordDet_of_diagonal hϖ (GlobalTheory.WeylGL.tor_val h0 _)]
      simp [Finset.sum_boole, Fin.card_filter_val_lt, min_eq_right hj]
    rw [GlobalTheory.WeylGL.Tj_eq h0, heckeVec_twistRep, ← GlobalTheory.WeylGL.Tj_eq h0, hx.2.2.2 ϖ hϖ j hj, em,
      GlobalTheory.SphGal.satEig_map_mul, ho, zpow_natCast, smul_smul]

end Twist

theorem hasSum_twisted_hecke_eigenvalues : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → ∀ (z : ℂˣ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∀ c : (Fin r → ℤ) → ℂ, (∀ d, heckeVec ρ (KGL w r) (dosetInd ℂ (KGL w r) (T d)) x = c d • x) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac (B.map (z * ·)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B.map fun β => (z * β)⁻¹) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  intro hP E _ _ w r V _ _ ρ x B hx z ϖ hϖ T hT c hc
  have hc' : ∀ d, heckeVec (twistRep ρ z) (KGL w r) (dosetInd ℂ (KGL w r) (T d)) x =
      ((z : ℂ) ^ (∑ i, d i) * c d) • x := fun d => by
    rw [heckeVec_twistRep, hc d, ordDet_of_diagonal hϖ (hT d), smul_smul]
  obtain ⟨δ, h0, h⟩ := GlobalTheory.T.hasSum_heckeEigenvalue_generatingSeries_GL hP E w r V (twistRep ρ z) x _ (isSatVecGL_twistRep hx z) ϖ hϖ T hT _ hc'
  refine ⟨δ, h0, fun X h1 h2 => ?_⟩
  have := h X h1 h2
  rw [Multiset.map_map] at this
  exact this

end GlobalTheory.FinZeta.GLTwist

end
