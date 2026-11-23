import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseMulIntersectionNumberLeSectionDimStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

namespace GlobalTheory.HSCore.RankBound

theorem topologicalKrullDim_le_of_smooth {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp k) (D : ℕ)
    (h : SmoothOfRelativeDimension D p) : topologicalKrullDim Y ≤ D := by
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top x)
  replace hU : IsAffineOpen (X := Y) U := hU
  refine ⟨U, U.isOpen, hx, le_of_eq ?_⟩
  rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, U))).trans
    (SmoothDim.ringKrullDim_affineOpen k _ p _ h U hU ⟨x, hx⟩)

theorem rankLow : Quoted → RankLow := by
  intro Q F _ _ G hnef hbig T
  have hV := G.geom.alg.variety
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · rw [Nat.zero_sub, Nat.choose_eq_zero_of_lt hV.one_le, Nat.cast_zero, zero_mul]
    exact Int.natCast_nonneg _
  have hstr : strHom F G.Y = G.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom F G.Y) := hstr ▸ hV.proj
  have hdim := topologicalKrullDim_le_of_smooth G.str G.D hV.smooth
  have hM : (tens G.K.bundle G.LA).IsLB := isLB_tens G.K.isLB G.isLBA
  let e : twist (GlobalTheory.structureModule G.Y) (tens G.K.bundle G.LA) ≅ LB.toMod (tens G.K.bundle G.LA) :=
    Twist.unitTwistIso _
  have hq := Twist.isFiniteQC_twist (F := GlobalTheory.structureModule G.Y) hM
  have hvan : VanishFrom G.L (twist (GlobalTheory.structureModule G.Y) (tens G.K.bundle G.LA)) 1 := fun j hj q hq =>
    (cohOn.mapIso Γ(G.Y, ⊤) ⊤ q ((twistFunctor (lbZPow G.L j)).mapIso e)).toEquiv.subsingleton_congr.2
      (GlobalTheory.T.kawamataViehweg_vanishing_numberField_twist Q F G hnef hbig j (by omega) q hq)
  have key := GlobalTheory.T.choose_mul_intersectionNumber_le_sectionDim F G.Y hproj G.L G.isLB G.N G.b
    (fun y => TopologicalSpace.Opens.mem_iSup.1 (G.geom.alg.bpf.ge (Set.mem_univ y))) G.D _
    ((suppDim_le _).trans hdim) 1 hvan (T - 1)
  rw [(diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom F G.Y) (GlobalTheory.structureModule G.Y) hproj
    ((suppDim_le _).trans hdim)).interNum_twist (by simp) (fun _ => G.isLB) hM] at key
  have hT' : (1 : ℤ) + ((T - 1 : ℕ) : ℤ) = T := by omega
  rw [hT'] at key
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (GlobalTheory.structureModule G.Y) hM (Twist.isLB_lbZPow G.isLB T)
    (G.isLB_adj T) rfl
  rw [G.finrank_global, lbH0, ← hdim_congr F 0 i]
  exact key

end GlobalTheory.HSCore.RankBound
