import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeisLinear
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonomialMatricesProjectiveRep
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinearIndependentThetaBasisGeometricFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExist
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadic
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelLabelledTorsionPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfUniformisationOverDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaSectionGeneratorPower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HypSEisensteinCurve
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaValueTorsionFrame
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalisedMulPullIsoOrigin
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvrStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsOfGeometric
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.RealCompare
open GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds hiding fn PsiNorm
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

instance noeth [ArithBase o Ω] (S : ThetaSys o Ω) : IsNoetherianRing S.R := by
  have := ArithBase.ded (o := o) (Ω := Ω)
  exact isNoetherianRing_of_fg S.fg

theorem unit_rN (S : ThetaSys o Ω) : IsUnit ((S.r * S.N : ℕ) : Γ(Sp S.R, ⊤)) := by
  have := S.unit.map (cst S)
  rwa [map_natCast] at this

theorem unit_N (S : ThetaSys o Ω) : IsUnit ((S.N : ℕ) : Γ(Sp S.R, ⊤)) := by
  have := unit_rN S
  rw [Nat.cast_mul] at this
  exact isUnit_of_mul_isUnit_right this

theorem one_le_rN (S : ThetaSys o Ω) : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)

theorem odd_N {S : ThetaSys o Ω} (Z : Realisation S) : Odd S.N := Z.N_eq ▸ Z.odd.pow.pow

def newBasis {S : ThetaSys o Ω} (Z : Realisation S) (c : Change S) (j : c.J) : SecM Z.P.A Z.P.L S.N (Base S) :=
  ∑ i, cst S (c.M i j) • SecM.ofSec Z.P.A (Z.b i)

theorem comb_single (S : ThetaSys o Ω) {M : Type} [AddCommGroup M] [Module Γ((Base S).left, ⊤) M] {I : Type}
    [Fintype I] (b : I → M) (i : I) (d : o) : ∑ l, cst S (if l = i then d else 0) • b l = cst S d • b i := by
  rw [Finset.sum_eq_single i (fun l _ hl => by rw [if_neg hl, map_zero, zero_smul])
    (fun h => (h (Finset.mem_univ i)).elim), if_pos rfl]

theorem map_comb (S : ThetaSys o Ω) {M : Type} [AddCommGroup M] [Module Γ((Base S).left, ⊤) M] {I J : Type}
    [Fintype I] [Fintype J] (u : M →ₗ[Γ((Base S).left, ⊤)] M) (b : I → M) (b' : J → M) (A : Matrix J I o)
    (h : ∀ i, u (b i) = ∑ j, cst S (A j i) • b' j) (c : I → o) :
    u (∑ i, cst S (c i) • b i) = ∑ j, cst S (∑ i, A j i * c i) • b' j := by
  simp only [map_sum u, map_smul, h]
  exact comb_comb S b' A c

theorem old_eq {S : ThetaSys o Ω} (Z : Realisation S) (c : Change S) (i : S.J) :
    SecM.ofSec Z.P.A (Z.b i) = ∑ j, cst S (c.M' j i) • newBasis Z c j := by
  refine Eq.trans ?_ (comb_comb S _ c.M fun j => c.M' j i).symm
  refine Eq.trans ?_ (Finset.sum_congr rfl fun l _ => congrArg (fun q => cst S q • _) (c.sum_mul l i)).symm
  refine Eq.symm ((comb_single S (fun i => SecM.ofSec Z.P.A (Z.b i)) i 1).trans ?_)
  rw [(cst S).map_one, one_smul]

theorem newBasis_indep {S : ThetaSys o Ω} (Z : Realisation S) (c : Change S) (d : c.J → o)
    (h : ∑ j, cst S (d j) • newBasis Z c j = 0) : d = 0 := by
  simp only [newBasis] at h
  rw [comb_comb] at h
  have e : c.M.mulVec d = 0 := Z.b_indep _ h
  rw [← Matrix.one_mulVec d, ← c.inv_mul, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_zero]

theorem newBasis_span {S : ThetaSys o Ω} (Z : Realisation S) (c : Change S) :
    cstSpan S (Set.range (newBasis Z c)) = cstSpan S (Set.range fun i => SecM.ofSec Z.P.A (Z.b i)) :=
  le_antisymm (cstSpan_le S fun _ ⟨j, e⟩ => (mem_cstSpan_range S _ _).2 ⟨fun i => c.M i j, e.symm⟩)
    (cstSpan_le S fun _ ⟨i, e⟩ => (mem_cstSpan_range S _ _).2 ⟨fun j => c.M' j i, e.symm.trans (old_eq Z c i)⟩)

theorem newBasis_act [ArithBase o Ω] {S : ThetaSys o Ω} (Z : Realisation S) (c : Change S) (a : S.Gam) (j : c.J) :
    ∃ s, IsHeis Z.P S.N (Z.tor a ^ S.r) (SecM.toSec Z.P.A (newBasis Z c j)) s ∧
      SecM.ofSec Z.P.A s = ∑ l, cst S ((c.M' * S.ρ a * c.M) l j) • newBasis Z c l := by
  obtain ⟨_, ⟨hx, -⟩, -⟩ := Z.ρ_eq a (Classical.arbitrary _)
  obtain ⟨u, hu⟩ := exists_heis_linear abelianSchemeLaws_all.1 Z.P (odd_N Z) (unit_N S) hx
  have hb : ∀ i, u (SecM.ofSec Z.P.A (Z.b i)) = ∑ i', cst S (S.ρ a i' i) • SecM.ofSec Z.P.A (Z.b i') := fun i => by
    obtain ⟨s, h₁, h₂⟩ := Z.ρ_eq a i
    exact ((hu _ _).1 h₁).trans h₂
  refine ⟨SecM.toSec Z.P.A (u (newBasis Z c j)), (hu _ _).2 rfl, ?_⟩
  refine (map_comb S u _ _ (S.ρ a) hb fun i => c.M i j).trans
    (Eq.trans ?_ (comb_comb S _ c.M fun l => (c.M' * S.ρ a * c.M) l j).symm)
  have e : c.M * (c.M' * S.ρ a * c.M) = S.ρ a * c.M := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, c.mul_inv, Matrix.one_mul]
  exact Finset.sum_congr rfl fun i _ => congrArg (fun q => cst S q • _) (congrFun (congrFun e i) j).symm

theorem fn_ev (S : ThetaSys o Ω) (c : Change S) (a : S.Gam) (j : c.J) :
    IndefiniteRowSideFullHecke.UniformityLowerBounds.fn S ⟨(change S c).ev a j, (change S c).ev_mem a j⟩ =
      ∑ i, cst S (c.M i j) * IndefiniteRowSideFullHecke.UniformityLowerBounds.fn S ⟨S.ev a i, S.ev_mem a i⟩ := by
  have : (⟨(change S c).ev a j, (change S c).ev_mem a j⟩ : S.R) =
      ∑ i, algebraMap o S.R (c.M i j) * ⟨S.ev a i, S.ev_mem a i⟩ := Subtype.ext (by
    rw [AddSubmonoidClass.coe_finset_sum]; rfl)
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun i _ => map_mul _ _ _

theorem fn_th (S : ThetaSys o Ω) (c : Change S) (a : S.Gam) :
    IndefiniteRowSideFullHecke.UniformityLowerBounds.fn S ⟨(change S c).th a, (change S c).th_mem a⟩ =
      cst S S.ζ ^ c.e a * IndefiniteRowSideFullHecke.UniformityLowerBounds.fn S ⟨S.th a, S.th_mem a⟩ := by
  rw [← map_pow]
  exact map_mul (IndefiniteRowSideFullHecke.UniformityLowerBounds.fn S) (algebraMap o S.R (S.ζ ^ c.e a)) ⟨S.th a, S.th_mem a⟩

def changeReal [ArithBase o Ω] {S : ThetaSys o Ω} (Z : Realisation S) (c : Change S) : Realisation (change S c) where
  n := Z.n
  k := Z.k
  j := Z.j
  prime := Z.prime
  odd := Z.odd
  two_le := Z.two_le
  N_eq := Z.N_eq
  r_eq := Z.r_eq
  bounds := Z.bounds
  P := Z.P
  dim := Z.dim
  rig := Z.rig
  rig_gen := Z.rig_gen
  w := Z.w
  w_hom := Z.w_hom
  selfPaired := Z.selfPaired
  lev := Z.lev
  θ := Z.θ
  θ_gen := Z.θ_gen
  th_eq := fun a => by
    obtain ⟨x', v, e, h₁, h₂, h₃⟩ := Z.th_eq a
    refine ⟨x', v, c.e a + e, h₁, h₂, (fn_th S c a).trans ?_⟩
    rw [h₃, ← _root_.mul_assoc, ← pow_add]
    rfl
  s₁ := Z.s₁
  s₁_eq := Z.s₁_eq
  b := fun j => SecM.toSec Z.P.A (newBasis Z c j)
  b_indep := newBasis_indep Z c
  b_span := (newBasis_span Z c).trans Z.b_span
  ρ_eq := newBasis_act Z c
  ev_eq := fun a => (Z.ev_eq a).imp fun e he => ⟨he.1, fun j =>
    (congrArg (IsValueAt _ _ _ _ _ _) (fn_ev S c a j)).mpr
      (isValueAt_sum Z.P.isLB (fun i => cst S (c.M i j)) _ Z.b he.2 rfl)⟩

structure Agree {S : ThetaSys o Ω} (ρ : S.Real) (Z : Realisation S) : Prop where
  P : ρ.P = Z.P
  n : ρ.n = Z.n
  k : ρ.k = Z.k
  pt : ∀ a, HEq (ρ.pt a) (Z.tor a)
  rig : HEq ρ.rig Z.rig
  θ : HEq ρ.th₁ Z.θ
  s₁ : HEq (ρ.s ρ.i₀) Z.s₁
  b : ∀ i, HEq (ρ.s i) (Z.b i)

def Refines {S : ThetaSys o Ω} (ρ : S.Real) (lev : Out.Level ρ.P ((S.r * S.N) ^ 2) (zetaUnit S)) : Prop :=
  ∀ a, torPt S ρ.g_eq lev a = ρ.pt a

end GlobalTheory.RealCompare
end
