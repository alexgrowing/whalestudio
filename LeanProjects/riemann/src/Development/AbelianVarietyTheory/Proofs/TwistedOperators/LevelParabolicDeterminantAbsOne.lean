import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsAUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicDeterminantMultiplicativeStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift

noncomputable section

open scoped TensorProduct NNReal

namespace GlobalTheory.LeviShift.CptTriv

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : HSpace E} (Φ : WittFrame V) (hc : CMData F E) (R : Type) [CommRing R] [Algebra F R]

theorem hLin_coordR (x y : V.V) :
    hLin hc.sig V.gram R (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R x) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R y) = inclR R (V.hD x y) := by
  change hR R hc.sig V.gram _ _ = inclR R (V.hT _ _)
  rw [IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp [hR, Formalism.UG.hform, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR, JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, CMData.sig, TensorProduct.tmul_sum,
    starRingEnd_apply]

theorem hD_f_e (i j : Fin (wittIndex V)) : V.hD (Φ.f i) (Φ.e j) = if i = j then 1 else 0 := by
  have h := V.herm.eq (Φ.f i) (Φ.e j)
  simp only [HSpace.hD] at *
  have e2 := Φ.ef j i
  simp only [HSpace.hD] at e2
  rw [← h, e2]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]

theorem hD_bas_dbas (u : SV (wittIndex V)) (i j : Supp u) :
    V.hD (bas Φ u j) (dbas Φ u i) = if i = j then 1 else 0 := by
  have hij : (i = j) ↔ (j.1 = i.1) := by rw [Subtype.ext_iff, eq_comm]
  simp only [bas, dbas]
  by_cases hj : u j.1 = -1 <;> by_cases hi : u i.1 = -1
  · rw [if_pos hj, if_pos hi, hD_f_e]; exact if_congr hij.symm rfl rfl
  · rw [if_pos hj, if_neg hi, Φ.ff, if_neg]; intro h; rw [h] at hi; exact hi hj
  · rw [if_neg hj, if_pos hi, Φ.ee, if_neg]; intro h; rw [h] at hi; exact hj hi
  · rw [if_neg hj, if_neg hi, Φ.ef]; exact if_congr hij.symm rfl rfl

theorem detMat_one (u : SV (wittIndex V)) : detMat Φ hc R u 1 = 1 := by
  ext i j
  simp only [detMat, Matrix.of_apply, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_one, hLin_coordR, hD_bas_dbas, Matrix.one_apply]
  split_ifs <;> simp [inclR, Algebra.TensorProduct.one_def]

theorem detU_one (u : SV (wittIndex V)) : detU Φ hc R u 1 = 1 := by
  rw [detU, detMat_one, Matrix.det_one]

end General

end GlobalTheory.LeviShift.CptTriv

namespace GlobalTheory.LeviShift.CptTriv

variable {D : D7} {V : HSp D} (Φ : WittFrame V) (u : SV (wittIndex V))

local notation "PU" => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub u)

theorem detU_mul_inv (p : PU) :
    detU Φ D.sp.cm (AF D.host.F) u (p : GA D V) * detU Φ D.sp.cm (AF D.host.F) u ((p⁻¹ : PU) : GA D V) = 1 := by
  rw [← GlobalTheory.T.parabolic_determinant_multiplicative Φ D.sp.cm (AF D.host.F) u _ _ p.2 (p⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel,
    Subgroup.coe_one, detU_one]

def detUnit (p : PU) : (AF D.host.F ⊗[D.host.F] D.host.E)ˣ where
  val := detU Φ D.sp.cm (AF D.host.F) u (p : GA D V)
  inv := detU Φ D.sp.cm (AF D.host.F) u ((p⁻¹ : PU) : GA D V)
  val_inv := detU_mul_inv Φ u p
  inv_val := by rw [mul_comm]; exact detU_mul_inv Φ u p

def delta : PU →* ℝ≥0 where
  toFun p := absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) u (p : GA D V))
  map_one' := by
    rw [Subgroup.coe_one, detU_one]
    have := absA_unit (F := D.host.F) (E := D.host.E) 1
    rwa [Units.val_one, map_one] at this
  map_mul' p q := by
    rw [Subgroup.coe_mul, GlobalTheory.T.parabolic_determinant_multiplicative Φ D.sp.cm (AF D.host.F) u _ _ p.2 q.2, absA_mul]

theorem delta_eq (p : PU) : delta Φ u p = Doubling.absE D.host.F D.host.E (detUnit Φ u p) := by
  rw [← absA_unit]; rfl

theorem continuous_detU : Continuous fun g : GA D V => detU Φ D.sp.cm (AF D.host.F) u g := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have hm : Continuous fun g : GA D V => (HA.mat _ D.sp.cm.sig V.gram g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [detMat, Matrix.of_apply, hLin, hR_eq, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act]
  exact continuous_const.dotProduct (continuous_const.matrix_mulVec (hm.matrix_mulVec continuous_const))

theorem continuous_delta : Continuous (delta Φ u) := by
  have h : Continuous fun p : PU => detU Φ D.sp.cm (AF D.host.F) u (p : GA D V) :=
    (continuous_detU Φ u).comp continuous_subtype_val
  have hu : Continuous (detUnit Φ u) := Units.continuous_iff.2 ⟨h, h.comp continuous_inv⟩
  have : (delta Φ u : PU → ℝ≥0) = fun p => Doubling.absE D.host.F D.host.E (detUnit Φ u p) :=
    funext (delta_eq Φ u)
  rw [this]
  exact Doubling.continuous_absE.comp hu

end GlobalTheory.LeviShift.CptTriv

theorem GlobalTheory.LeviShift.CptTriv.absA_detU_eq_one : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ (u : SV (wittIndex V)) (k : GA D V), k ∈ levelAll D.sp.cm.sig V.gram L a → k ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub u) → absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) u k) = 1 := by
  intro D V Φ L a hG u k hk hp
  have := Doubling.t2Space_adeleRing' (F := D.host.F)
  exact Doubling.triv_of_isCompact (δ := GlobalTheory.LeviShift.CptTriv.delta Φ u)
    (GlobalTheory.Cusp.isClosed_parab (hc := D.sp.cm) (V := V) (R := AF D.host.F) (Φ.sub u)) (GlobalTheory.LeviShift.CptTriv.continuous_delta Φ u)
    hG.isCompact ⟨k, hp⟩ hk
