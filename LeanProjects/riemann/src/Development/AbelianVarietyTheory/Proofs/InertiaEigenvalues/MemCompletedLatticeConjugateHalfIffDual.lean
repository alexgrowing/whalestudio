import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVecExistsUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.ConjHalfDual

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat

variable {D : D7}

theorem cA_cA_self (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x =>
    show a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig x) = a ⊗ₜ[D.host.F] x
    congr 1
    exact star_star x
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem infPart_cA_of_zero {z : AE D} (h : infPart D z = 0) : infPart D (cA D z) = 0 := by
  have key : ∀ w : AE D, infPart D (cA D w) =
      Algebra.TensorProduct.map (AlgHom.id D.host.F (Ainf D.host.F)) D.sp.cm.sig (infPart D w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  rw [key, h, map_zero]

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO; rw [hO_add_right, mul_add, map_add]

theorem hO_eq_zero_of {f g : AE D} (hfg : cA D g * f = 0) {S T : HSp D} {x y' : WO S T} (hx : IsHalf f x) :
    hO S T x (g • y') = 0 := by
  unfold hO
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, ← hx d a, map_mul]
  calc incA D (S.gram⁻¹ a b) * (cA D g * cA D (y' c b)) * incA D (T.gram c d) * (f * x d a)
      = (cA D g * f) * (incA D (S.gram⁻¹ a b) * cA D (y' c b) * incA D (T.gram c d) * x d a) := by ring
    _ = 0 := by rw [hfg, zero_mul]

theorem symplO_eq_zero_of {f g : AE D} (hfg : cA D g * f = 0) {S T : HSp D} {x y' : WO S T} (hx : IsHalf f x) :
    symplO S T x (g • y') = 0 := by
  unfold symplO; rw [hO_eq_zero_of hfg hx, mul_zero, map_zero]

theorem mem_latO_iff_of_conjHalf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e : AE D, e * e = e → e * cA D e = 0 → infPart D e = 0 → finPart D e ∈ intAE D → ∀ u : WO S T, IsHalf (cA D e) u → (u ∈ latO S T ΛS ΛT (fun _ => True) ↔ ∀ l ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e l → ψ (symplO S T l u) = 1) := by
  intro D ψ S T ΛS ΛT hψ hS hT e he hec hinf hfin u hu
  have key := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  have hcc : cA D (cA D e) = e := cA_cA_self e
  have hcidem : cA D e * cA D e = cA D e := by rw [← map_mul, he]
  have hcinf : infPart D (cA D e) = 0 := infPart_cA_of_zero hinf
  constructor
  · intro hmem l hl _
    have hl0 : l.map (infPart D) = 0 := by
      ext i j; exact latAll_infPart hl i j
    exact (key l hl0).1 hl u hmem
  · intro h
    have hu0 : u.map (infPart D) = 0 := by
      ext i j
      rw [Matrix.map_apply, Matrix.zero_apply, ← hu i j, map_mul, hcinf, zero_mul]
    refine (key u hu0).2 fun u' hu' => ?_
    have hdec : u' = e • u' + (cA D e • u' + (1 - e - cA D e) • u') := by
      ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    have m1 : e • u' ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
      smul_mem_latAll hfin hu'
    have hh1 : IsHalf e (e • u') := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]
    have t1 : ψ (symplO S T u (e • u')) = 1 := by
      rw [GlobalTheory.SplitScalar.symplO_skew, AddChar.map_neg_eq_inv, h _ m1 hh1, inv_one]
    have t2 : symplO S T u (cA D e • u') = 0 :=
      symplO_eq_zero_of (f := cA D e) (by rw [hcc]; exact hec) hu
    have t3 : symplO S T u ((1 - e - cA D e) • u') = 0 :=
      symplO_eq_zero_of (f := cA D e) (by
        rw [map_sub, map_sub, map_one, hcc]
        linear_combination (-1 : AE D) * hcidem - hec) hu
    rw [hdec, symplO_add_right', symplO_add_right', t2, t3, add_zero, add_zero, t1]

end GlobalTheory.ConjHalfDual

end
