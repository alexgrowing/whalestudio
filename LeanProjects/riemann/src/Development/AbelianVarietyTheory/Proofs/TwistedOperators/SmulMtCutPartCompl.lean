import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdPartialEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompMemGinfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

open GlobalTheory.IdemSupport

variable {D : D7}

open Classical in

def cutPart (a : AE D) (V : HSp D) (g : GA D V) : GA D V :=
  if h : a * a = a ∧ cA D a = a then ⟨piece h.1 g.1, piece_mem _ _ h.1 h.2 g.2⟩ else g

theorem mt_cutPart {a : AE D} (h : a * a = a) (hc : cA D a = a) (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V (cutPart a V g) = a • Formalism.L2.Theta.mt V g + (1 - a) • (1 : Matrix _ _ (AE D)) := by
  have e : cutPart a V g = ⟨piece h g.1, piece_mem _ _ h hc g.2⟩ := dif_pos ⟨h, hc⟩
  rw [e]
  rfl

end GlobalTheory.ExpansionInvariance

namespace GlobalTheory.ExpansionInvariance

open GlobalTheory.IdemSupport

variable {D : D7}

theorem idem_conj_sum {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) :
    (e + cA D e) * (e + cA D e) = e + cA D e ∧ cA D (e + cA D e) = e + cA D e := by
  have h1 : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  refine ⟨by linear_combination he + h1 + 2 * hc, ?_⟩
  rw [RingHom.map_add, GlobalTheory.SplitOnto.cA_cA, add_comm]

theorem idem_compl {f : AE D} (hf : f * f = f ∧ cA D f = f) : (1 - f) * (1 - f) = 1 - f ∧ cA D (1 - f) = 1 - f := by
  refine ⟨by linear_combination hf.1, ?_⟩
  rw [RingHom.map_sub, RingHom.map_one, hf.2]

theorem cutPart_mul {f : AE D} (hf : f * f = f ∧ cA D f = f) (V : HSp D) (g : GA D V) :
    g = cutPart f V g * cutPart (1 - f) V g := by
  have h2 := idem_compl hf
  refine GlobalTheory.IdemSupport.mt_inj V ?_
  rw [GlobalTheory.IdemSupport.mt_mul, mt_cutPart hf.1 hf.2, mt_cutPart h2.1 h2.2, sub_sub_cancel]
  exact (mix_split hf.1 rfl rfl).symm

theorem suppAt_cutPart {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (V : HSp D) (g : GA D V) :
    SuppAt e V (cutPart (e + cA D e) V g) := by
  have hf := idem_conj_sum he hc
  exact (supp_iff _ _).2 (smul_mix hf.1 (mt_cutPart hf.1 hf.2 V g))

theorem smul_mt_cutPart_compl {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (V : HSp D) (g : GA D V) :
    e • Formalism.L2.Theta.mt V (cutPart (1 - (e + cA D e)) V g) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have hf := idem_conj_sum he hc
  have h2 := idem_compl hf
  rw [mt_cutPart h2.1 h2.2, sub_sub_cancel, smul_add, smul_smul, smul_smul]
  have k1 : e * (1 - (e + cA D e)) = 0 := by linear_combination -he - hc
  have k2 : e * (e + cA D e) = e := by linear_combination he + hc
  rw [k1, k2, zero_smul, zero_add]

end GlobalTheory.ExpansionInvariance

namespace GlobalTheory.ExpansionInvariance

variable {D : D7}

theorem actO_cutPart_compl {S T : HSp D} {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (g : GA D S) {z : WO S T}
    (hz : IsHalf e z) : actO S T (cutPart (1 - (e + cA D e)) S g)⁻¹ 1⁻¹ z = z := by
  have hz' : e • z = z := Matrix.ext fun i j => hz i j
  unfold actO
  rw [inv_inv, inv_one, GlobalTheory.IdemSupport.mt_one, Matrix.one_mul]
  conv_lhs => rw [← hz']
  rw [Matrix.smul_mul, ← Matrix.mul_smul, smul_mt_cutPart_compl he hc, Matrix.mul_smul, Matrix.mul_one, hz']

theorem halfInd_cutPart {S T : HSp D} {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (Λ : AddSubgroup (WO S T))
    (g : GA D S) (x : WO S T) :
    halfInd e Λ (actO S T (cutPart (e + cA D e) S g)⁻¹ 1⁻¹ x) = halfInd e Λ (actO S T g⁻¹ 1⁻¹ x) := by
  have hf := idem_conj_sum he hc
  have hg : g = cutPart (e + cA D e) S g * cutPart (1 - (e + cA D e)) S g := cutPart_mul hf S g
  have key : actO S T g⁻¹ 1⁻¹ x = actO S T (cutPart (1 - (e + cA D e)) S g)⁻¹ 1⁻¹
      (actO S T (cutPart (e + cA D e) S g)⁻¹ 1⁻¹ x) := by
    rw [← GlobalTheory.SplitLinear.actO_mul, ← mul_inv_rev, ← hg, inv_one, mul_one]
  rw [key]
  by_cases hy : IsHalf e (actO S T (cutPart (e + cA D e) S g)⁻¹ 1⁻¹ x)
  · rw [actO_cutPart_compl he hc g hy]
  · unfold halfInd
    rw [if_neg fun h => hy h.2, if_neg fun h => hy (GlobalTheory.ThetaMove.isHalf_of_act _ _ h.2)]

end GlobalTheory.ExpansionInvariance

end
