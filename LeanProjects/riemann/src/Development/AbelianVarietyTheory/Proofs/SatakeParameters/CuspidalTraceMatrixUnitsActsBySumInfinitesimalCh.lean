import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterCentralExponentProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterRealExponentEqZeroIffIsUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
noncomputable section

namespace GlobalTheory

open Polynomial in

theorem trace_Eop_of_hasInfChar (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (π : GlobalTheory.CuspRep.CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ) (h : π.HasInfChar τ m) :
    ∀ φ ∈ π.V, (∑ i : Fin a, GlobalTheory.CuspRep.Eop τ i i) φ = m.sum • φ := by
  intro φ hφ
  obtain ⟨hcard, hcap⟩ := h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Multiset.card_eq_zero.1 hcard]; simp
  set c : ℂ := ((a : ℂ) - 1) / 2 with hc
  set P := GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (GlobalTheory.CuspRep.Eop (a := a) τ) with hPdef
  have hP : P.coeff (a - 1) = ∑ i, GlobalTheory.CuspRep.Eop τ i i -
      algebraMap ℂ (Module.End ℂ (GlobalTheory.CuspRep.Sm E a)) (((a : ℂ) * ((a : ℂ) - 1)) / 2) := by
    obtain ⟨-, -, hsub⟩ := GroundTheory.BlockD.FourierDecayAlt.GaugeExists.prod_linear a fun k =>
      GlobalTheory.CuspRep.Eop (a := a) τ k k - algebraMap ℂ (Module.End ℂ (GlobalTheory.CuspRep.Sm E a)) ((k : ℕ) : ℂ)
    rw [hPdef, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.coeff_qdetPoly_top _ (a - 1) (by omega), hsub (a - 1) (by omega),
      Finset.sum_sub_distrib, ← map_sum, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.sum_fin_cast]
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
  let Q : ℂ[X] := ∑ j ∈ Finset.range (a + 1), C (ℓ (P.coeff j φ)) * X ^ j
  let R : ℂ[X] := C (ℓ φ) * (m.map fun z => X + C (z - c)).prod
  have hdeg : P.natDegree < a + 1 :=
    Nat.lt_succ_of_le (GroundTheory.BlockD.FourierDecayAlt.GaugeExists.natDegree_qdetPoly_le _)
  have hQ : ∀ v : ℂ, Q.eval v = ℓ ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU v P) φ) := by
    intro v
    rw [GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_apply, eval₂_eq_sum_range' _ hdeg, LinearMap.sum_apply, map_sum,
      eval_finset_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, RingHom.id_apply, Module.End.mul_apply, ← map_pow,
      Module.algebraMap_end_apply, map_smul, map_smul, smul_eq_mul, mul_comm]
  have hQR : Q = R := by
    refine Polynomial.funext fun v => ?_
    rw [hQ, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_qdetPoly]
    have e := hcap (v - c) φ hφ
    rw [GlobalTheory.CuspRep.cap, show v - c + ((a : ℂ) - 1) / 2 = v by rw [hc]; ring] at e
    rw [e, map_smul, smul_eq_mul]
    simp only [R, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_add, eval_X]
    rw [mul_comm]
    congr 2
    refine Multiset.map_congr rfl fun z _ => ?_
    ring
  have hco := congrArg (fun p : ℂ[X] => p.coeff (a - 1)) hQR
  have hlt : a - 1 ∈ Finset.range (a + 1) := Finset.mem_range.2 (by omega)
  simp only [Q, R, finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', if_pos hlt] at hco
  have hm : (m.map fun z => X + C (z - c)).prod =
      ((m.map fun z => z - c).map fun r => X + C r).prod := by rw [Multiset.map_map]; rfl
  rw [hm, Multiset.prod_X_add_C_coeff _ (by simp [hcard]), Multiset.card_map, hcard,
    show a - (a - 1) = 1 by omega, Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map] at hco
  simp only [Function.comp_def, Multiset.prod_singleton, Multiset.map_id', Multiset.sum_map_sub,
    Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul] at hco
  rw [hP] at hco
  simp only [LinearMap.sub_apply, map_sub, Module.algebraMap_end_apply, map_smul, smul_eq_mul] at hco ⊢
  rw [hc] at hco
  linear_combination hco

end GlobalTheory
