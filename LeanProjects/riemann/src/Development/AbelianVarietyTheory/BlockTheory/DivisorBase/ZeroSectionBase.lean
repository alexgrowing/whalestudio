import Mathlib
import Formalism.LocalRingCardinality.DataDIV
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffineOpenAndIsPushout
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibres
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic GlobalTheory.VB

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase

section Surface

variable (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)]

def IsProjSurface : Prop :=
  IsIntegral T ∧ topologicalKrullDim T = 2 ∧ IsProjOver (strHom k T)

variable {T}

def degCh2 (E : T.Modules) (r : ℕ) : ℚ :=
  ((chi k E + chi k (VB.dual E) - 2 * r * chi k (structureModule T) : ℤ) : ℚ) / 2

variable {k}

theorem IsProjSurface.finiteCoh (h : IsProjSurface k T) {E : T.Modules} {r : ℕ} (hE : IsVB E r) :
    FiniteCoh k E ∧ FiniteCoh k (VB.dual E) ∧ FiniteCoh k (structureModule T) :=
  have := hE.isFiniteQC
  have := hE.dual.isFiniteQC
  have := (isVB_structureModule T).isFiniteQC
  ⟨finiteCoh_of_isProjOver (algebraMap_eq_strHom k T) _ h.2.2,
    finiteCoh_of_isProjOver (algebraMap_eq_strHom k T) _ h.2.2,
    finiteCoh_of_isProjOver (algebraMap_eq_strHom k T) _ h.2.2⟩

theorem degCh2_congr {E E' : T.Modules} (φ : E ≅ E') (r : ℕ) : degCh2 k E r = degCh2 k E' r := by
  rw [degCh2, degCh2, chi_congr k φ, chi_congr k (dualIso φ)]

theorem IsProjSurface.degCh2_rank_one (h : IsProjSurface k T) {E : T.Modules} (hE : IsVB E 1) :
    degCh2 k E 1 = (topSelfIntersection k (det E 1) 2 : ℚ) / 2 := by
  have := (isVB_structureModule T).isFiniteQC
  have hL := hE.isLB_det
  have e₁ : chi k E = chiPic k (structureModule T) (cls _ hL) :=
    (chi_congr k hE.isoDet).trans (chi_congr k (Twist.unitTwistIso _)).symm
  have e₂ : chi k (VB.dual E) = chiPic k (structureModule T) (-cls _ hL) := by
    rw [← cls_dual hL (isLB_dual hL),
      (cls_eq_iff (isLB_dual hL) hE.dual.isLB_det).2 hE.lbIso_det_dual]
    exact (chi_congr k hE.dual.isoDet).trans (chi_congr k (Twist.unitTwistIso _)).symm
  have hv : DiffVanish (2 + 1) (chiPic k (structureModule T)) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k T) _ h.2.2
      ((QCoh.suppDim_le _).trans h.2.1.le)
  have e₃ := congrFun (hv fun _ => cls _ hL) (cls _ hL)
  rw [degCh2, e₁, e₂, ← chiPic_zero, topSelf_def, interNum_eq_multiDiff k _ fun _ => hL]
  generalize cls _ hL = c at e₃ ⊢
  generalize chiPic k (structureModule T) = φ at e₃ ⊢
  rw [multiDiff_const] at e₃ ⊢
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, bwdDiff_apply,
    sub_self, zero_sub, Pi.zero_apply] at e₃ ⊢
  congr 2
  push_cast
  omega

theorem isProjSurface_plane (k : Type) [Field k] :
    letI : Algebra k Γ(PSpace k 2, ⊤) :=
      ((PSpace.str k 2).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
    IsProjSurface k (PSpace k 2) := by
  letI : Algebra k Γ(PSpace k 2, ⊤) :=
    ((PSpace.str k 2).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  refine ⟨GlobalTheory.ProjSpace.isIntegral_of_isDomain _ _, ProjSpace.topologicalKrullDim_eq k 2, 2, 𝟙 _, inferInstance, ?_⟩
  rw [Category.id_comp]
  exact (strHom_eq (f := PSpace.str k 2) fun _ => rfl).symm

end Surface

section Abelian

variable {S S' : Scheme.{0}} (A : Over S)

def toBase (s : S' ⟶ S) {Y : Over S'} (x : Y ⟶ (Over.pullback s).obj A) :
    Over.mk (Y.hom ≫ s) ⟶ A :=
  Over.homMk (x.left ≫ pullback.fst A.hom s) (by
    have := Over.w x
    simp only [Over.mk_hom, Category.assoc, pullback.condition]
    rw [← this]; simp)

def sqToBase (s : S' ⟶ S) :
    ((Over.pullback s).obj A ⊗ (Over.pullback s).obj A).left ⟶ (A ⊗ A).left :=
  (lift (toBase A s (fst _ _)) (toBase A s (snd _ _))).left

variable [GrpObj A]

def IsPrincipalPol (c : Pic (A ⊗ A).left) : Prop :=
  pull (lift (1 : A ⟶ A) (𝟙 A)).left c = 0 ∧ pull (lift (𝟙 A) (1 : A ⟶ A)).left c = 0 ∧
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S),
      ∃ (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB),
        Out.RelAmple ((Over.pullback s).obj A) L ∧ Out.KTriv ((Over.pullback s).obj A) L ∧
          pull (sqToBase A s) c = lam (cls L hL) (fst _ _) (snd _ _)

def zeroSec : S ⟶ A.left := η[A].left

theorem zeroSec_comp : zeroSec A ≫ A.hom = 𝟙 S := Over.w η[A]

def hodge : S.Modules := Conormal.conormal (zeroSec A)

theorem isVB_hodge (hA : IsAbelianScheme A) (g : ℕ) [SmoothOfRelativeDimension g A.hom] :
    IsVB (hodge A) g := by
  have := hA.proper
  have : IsClosedImmersion (zeroSec A ≫ A.hom) := by rw [zeroSec_comp]; infer_instance
  have : IsClosedImmersion (zeroSec A) := IsClosedImmersion.of_comp (zeroSec A) A.hom
  exact Conormal.isVB_conormal (zeroSec_comp A) g

theorem isPrincipalPol_of_polAV (P : Out.PolAV S) :
    IsPrincipalPol P.A (lam (cls P.L P.isLB) (fst P.A P.A) (snd P.A P.A)) := by
  have := P.isAb.comm
  refine ⟨?_, ?_, fun Ω _ _ s => ?_⟩
  · rw [pull_lam, lift_fst, lam_one_left]
  · rw [pull_lam, lift_snd, lam_one_right]
  · have h := isGrpPullback_pullback P.A s
    have hL := pull_isLB P.isLB (pullback.fst P.A.hom s)
    obtain ⟨w, hw⟩ := (cls_eq_iff hL hL).1 rfl
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := S)
      (x := s (IsLocalRing.closedPoint Ω)) (U := ⊤) trivial
    refine ⟨_, hL, relAmple_pull h.1 P.isLB hL ((isGen_iff w).1 hw) U hU
      (fun y => by rwa [Subsingleton.elim y (IsLocalRing.closedPoint Ω)]) P.ample,
      kTriv_pull h P.isLB hL ((isGen_iff w).1 hw) P.ktriv, ?_⟩
    rw [sqToBase, pull_lam, lift_fst, lift_snd, cls_pull P.isLB, lam_pull_of_isGrpPullback h]
    rfl

end Abelian

def Ch2HodgeVanishes : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (T : Scheme.{0}) [Algebra (ZMod p) Γ(T, ⊤)],
    IsProjSurface (ZMod p) T →
      ∀ (A : Over T) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
        (∃ c, IsPrincipalPol A c) → degCh2 (ZMod p) (hodge A) g = 0

open Formalism.BasicNotions

def RecordVanishes (D : D7) (X : DivX D) : Prop := ∀ s : X.SurfFp, X.surfFpCh2 s = 0

def RecordIsGeometric (D : D7) (X : DivX D) : Prop :=
  ∀ s : X.SurfFp, ∃ (p : ℕ) (_ : Fact p.Prime) (T : Scheme.{0}) (_ : Algebra (ZMod p) Γ(T, ⊤))
    (A : Over T) (_ : GrpObj A) (g : ℕ), IsProjSurface (ZMod p) T ∧ IsAbelianScheme A ∧
      SmoothOfRelativeDimension g A.hom ∧ (∃ c, IsPrincipalPol A c) ∧
        X.surfFpCh2 s = (degCh2 (ZMod p) (hodge A) g : ℝ)

theorem recordVanishes_of (h : Ch2HodgeVanishes) {D : D7} {X : DivX D}
    (hX : RecordIsGeometric D X) : RecordVanishes D X := fun s => by
  obtain ⟨p, _, T, _, A, _, g, hT, hA, hg, hc, e⟩ := hX s
  rw [e, h p T hT A g hA hg hc, Rat.cast_zero]

end GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase
