import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtPosDef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFinitePartMemHomLatticeCompletionIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualImageOrthonormalFrameLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedTransLat

open Matrix

variable {D : D7}

theorem AA_le_Iid (a : D.host.E) (ha : a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)) :
    a ∈ GlobalTheory.InertSign.Iid D D.host.ccK := by
  have ha' : a ∈ D.host.ccE * D.host.AA0 := by rw [← Host.AA]; exact ha
  refine FractionalIdeal.mul_induction_on ha' (fun x hx y hy => ?_) (fun x y hx hy => add_mem hx hy)
  rw [Host.ccE] at hx
  obtain ⟨x', hx', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    exact Submodule.subset_span ⟨c, hc, y, hy, rfl⟩
  | zero => simp
  | add u w _ _ hu hw => rw [map_add, add_mul]; exact add_mem hu hw
  | smul o u _ hu =>
    rw [smul_eq_mul, map_mul, mul_assoc]
    exact Submodule.smul_mem _ o hu

theorem coord_genMap {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (a : D.host.E) (s' : Fin S.rank → D.host.E) (t' : Fin T.rank → D.host.E) :
    (frT⁻¹).1 * GlobalTheory.LatVac.genMap S T a (frS.1 *ᵥ s') (frT.1 *ᵥ t') * frS.1 = a • Matrix.vecMulVec t' (star s') := by
  have hS' : frS.1ᴴ * S.gram * frS.1 = 1 := hS
  have e : ∀ (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E),
      GlobalTheory.LatVac.genMap S T a s t = a • Matrix.vecMulVec t (star s ᵥ* S.gram) := by
    intro s t
    ext i j
    simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.vecMul,
      dotProduct, smul_eq_mul, Pi.star_apply, mul_assoc]
  rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_mulVec,
    Units.inv_mul, Matrix.one_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hS',
    Matrix.vecMul_one]

theorem vecMulVec_mem_homL {N N' : ℕ} {Ls : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {Lt : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hLs : SD D Ls) {s' : Fin N → D.host.E} (hs' : s' ∈ Ls)
    {t' : Fin N' → D.host.E} (ht' : t' ∈ Lt) : Matrix.vecMulVec t' (star s') ∈ homL D Ls Lt := by
  refine GlobalTheory.ThetaLatImage.mem_homL.2 fun x hx => ?_
  obtain ⟨o, ho⟩ := (((GlobalTheory.InertSign.sd_iff D Ls).1 hLs).2.2 x).1 hx s' hs'
  have e : Matrix.vecMulVec t' (star s') *ᵥ x = o • t' := by
    funext i
    rw [Pi.smul_apply, ← algebraMap_smul D.host.E o (t' i), ho, smul_eq_mul]
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, GlobalTheory.InertSign.hE, Pi.star_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [bridge_star_holds D.R D.host]; ring
  rw [e]
  exact Lt.smul_mem o ht'

theorem coord_mem_RL {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    {Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hLs : SD D Ls) {w : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hw : w ∈ GlobalTheory.LatVac.latRat S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt)) :
    (frT⁻¹).1 * w * frS.1 ∈ GlobalTheory.InertSign.RL D D.host.ccK Ls Lt := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, s, ⟨s', hs', rfl⟩, t, ⟨t', ht', rfl⟩, rfl⟩ := hw
    rw [coord_genMap frS frT hS]
    exact Submodule.subset_span ⟨a, AA_le_Iid a ha, _, vecMulVec_mem_homL hLs hs' ht', rfl⟩
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem hx

theorem mem_La_of_finRat : ∀ {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), SD D Ls → SD D Lt → ∀ (δ : ℂ) (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E), GlobalTheory.VacUnique.finRat S T v ∈ latO S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True) → δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b) ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt := by
  intro D S T frS frT hS hT Ls Lt hLs hLt δ v hv
  obtain ⟨ΛS, hΛS, hSD⟩ := GlobalTheory.T.isSelfDual_image_orthonormalFrame_lattice S frS hS Ls hLs
  obtain ⟨ΛT, hΛT, hTD⟩ := GlobalTheory.T.isSelfDual_image_orthonormalFrame_lattice T frT hT Lt hLt
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  rw [← hΛS, ← hΛT] at hv
  have hrat := (GlobalTheory.AdForm.RatLat.finTens_mem_iff hψ hSD hTD v).1 hv
  rw [hΛS, hΛT] at hrat
  have hpt := GlobalTheory.ThetaLatImage.pt_mem_La (δ := δ) (coord_mem_RL frS frT hS hLs hrat) 1
  rw [one_smul] at hpt
  convert hpt using 1
  funext τ a b
  rw [GlobalTheory.ThetaLatImage.pt_apply]
  have hi : (GlobalTheory.FockPos.frAt frT τ)⁻¹ = (frT⁻¹).1.map (tauE D τ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [GlobalTheory.FockPos.frAt, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hv' : Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) = v.map (tauE D τ) := rfl
  show δ * ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b = _
  rw [hi, hv', GlobalTheory.FockPos.frAt, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

end GlobalTheory.MovedTransLat
