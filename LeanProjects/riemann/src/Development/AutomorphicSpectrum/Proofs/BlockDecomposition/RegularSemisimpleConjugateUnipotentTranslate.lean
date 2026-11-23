import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLocallyFiniteContinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIsoFrameFirstCols
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSemisimpleFlagStabilizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitInclMemExtSubIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommuteOfWittFrameWeights
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WittIndexAddOfIsWittLower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt
namespace GlobalTheory.CompanionTheory.ParabConj

open Polynomial

section Filt

variable {E M : Type} [Field E] [AddCommGroup M] [Module E M]

def strictUp (A B : Submodule E M) : Submodule E (Module.End E M) where
  carrier := {T | (∀ x ∈ A, T x = 0) ∧ (∀ x ∈ B, T x ∈ A) ∧ ∀ x, T x ∈ B}
  add_mem' := by
    rintro S T ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x => ?_⟩
    · simp [h1 x hx, k1 x hx]
    · exact add_mem (h2 x hx) (k2 x hx)
    · exact add_mem (h3 x) (k3 x)
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => zero_mem _, fun _ => zero_mem _⟩
  smul_mem' := by
    rintro c T ⟨h1, h2, h3⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x => ?_⟩
    · simp [h1 x hx]
    · exact Submodule.smul_mem _ _ (h2 x hx)
    · exact Submodule.smul_mem _ _ (h3 x)

variable {A B : Submodule E M}

def Stabs (A B : Submodule E M) (f : Module.End E M) : Prop := (∀ x ∈ A, f x ∈ A) ∧ ∀ x ∈ B, f x ∈ B

theorem mul_mem_strictUp (hAB : A ≤ B) {S T : Module.End E M} (hS : S ∈ strictUp A B) (hT : T ∈ strictUp A B) :
    S * T ∈ strictUp A B := by
  obtain ⟨h1, h2, h3⟩ := hS
  obtain ⟨k1, k2, k3⟩ := hT
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x => ?_⟩
  · rw [Module.End.mul_apply, k1 x hx, map_zero]
  · rw [Module.End.mul_apply, h1 _ (k2 x hx)]; exact zero_mem _
  · exact hAB (h2 _ (k3 x))

theorem Stabs.mul_left {f T : Module.End E M} (hf : Stabs A B f) (hT : T ∈ strictUp A B) :
    f * T ∈ strictUp A B := by
  obtain ⟨k1, k2, k3⟩ := hT
  refine ⟨fun x hx => ?_, fun x hx => hf.1 _ (k2 x hx), fun x => hf.2 _ (k3 x)⟩
  rw [Module.End.mul_apply, k1 x hx, map_zero]

theorem Stabs.mul_right {f T : Module.End E M} (hf : Stabs A B f) (hT : T ∈ strictUp A B) :
    T * f ∈ strictUp A B := by
  obtain ⟨k1, k2, k3⟩ := hT
  exact ⟨fun x hx => k1 _ (hf.1 x hx), fun x hx => k2 _ (hf.2 x hx), fun x => k3 _⟩

theorem Stabs.add_strictUp (hAB : A ≤ B) {f d : Module.End E M} (hf : Stabs A B f) (hd : d ∈ strictUp A B) :
    Stabs A B (f + d) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [LinearMap.add_apply, hd.1 x hx, add_zero]; exact hf.1 x hx
  · rw [LinearMap.add_apply]; exact add_mem (hf.2 x hx) (hAB (hd.2.1 x hx))

theorem Stabs.aeval {f f' : Module.End E M} (hAB : A ≤ B) (hf : Stabs A B f) (hd : f' - f ∈ strictUp A B) (r : E[X]) :
    Stabs A B (Polynomial.aeval f r) ∧ Polynomial.aeval f' r - Polynomial.aeval f r ∈ strictUp A B := by
  have hf' : Stabs A B f' := by simpa using hf.add_strictUp hAB hd
  induction r using Polynomial.induction_on with
  | C a =>
    refine ⟨⟨fun x hx => ?_, fun x hx => ?_⟩, ?_⟩
    · rw [aeval_C, Module.algebraMap_end_apply]; exact Submodule.smul_mem _ _ hx
    · rw [aeval_C, Module.algebraMap_end_apply]; exact Submodule.smul_mem _ _ hx
    · simp [zero_mem]
  | add p q hp hq =>
    refine ⟨⟨fun x hx => ?_, fun x hx => ?_⟩, ?_⟩
    · rw [map_add, LinearMap.add_apply]; exact add_mem (hp.1.1 x hx) (hq.1.1 x hx)
    · rw [map_add, LinearMap.add_apply]; exact add_mem (hp.1.2 x hx) (hq.1.2 x hx)
    · have := add_mem hp.2 hq.2
      rw [map_add, map_add]
      convert this using 1
      abel
  | monomial k a ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e : ∀ g : Module.End E M, Polynomial.aeval g (C a * X ^ (k + 1)) = Polynomial.aeval g (C a * X ^ k) * g := fun g => by
      rw [pow_succ, ← mul_assoc, map_mul _ (C a * X ^ k) X, aeval_X]
    rw [e, e]
    refine ⟨⟨fun x hx => ih1.1 _ (hf.1 x hx), fun x hx => ih1.2 _ (hf.2 x hx)⟩, ?_⟩
    have h1 := hf'.mul_right ih2
    have h2 := ih1.mul_left hd
    have := add_mem h1 h2
    convert this using 1
    noncomm_ring

theorem aeval_intertwine {f f' T : Module.End E M} (h : T * f = f' * T) (r : E[X]) :
    T * Polynomial.aeval f r = Polynomial.aeval f' r * T := by
  induction r using Polynomial.induction_on with
  | C a => rw [aeval_C, aeval_C]; exact (Algebra.commutes a T).symm
  | add p q hp hq => simp only [map_add, mul_add, add_mul, hp, hq]
  | monomial k a ih =>
    have e : ∀ g : Module.End E M, Polynomial.aeval g (C a * X ^ (k + 1)) = Polynomial.aeval g (C a * X ^ k) * g := fun g => by
      rw [pow_succ, ← mul_assoc, map_mul _ (C a * X ^ k) X, aeval_X]
    rw [e, e, ← mul_assoc, ih, mul_assoc, h, mul_assoc]

variable [FiniteDimensional E M]

theorem eq_zero_of_intertwine (hAB : A ≤ B) {f f' T : Module.End E M} (hs : (LinearMap.charpoly f).Separable)
    (hf : Stabs A B f) (hd : f' - f ∈ strictUp A B) (hT : T ∈ strictUp A B) (h : T * f = f' * T) : T = 0 := by
  obtain ⟨p, hp1, hp2⟩ := GlobalTheory.CompanionTheory.LeviConj.exists_poly_proj f hs A hf.1
  obtain ⟨q, hq1, hq2⟩ := GlobalTheory.CompanionTheory.LeviConj.exists_poly_proj f hs B hf.2
  have hpi := aeval_intertwine h p
  have hqi := aeval_intertwine h q

  have k1 : ∀ z, T z ∈ A → T z = 0 := fun z hz => by
    have e1 : (Polynomial.aeval f' p) (T z) = T z := by
      have := (Stabs.aeval hAB hf hd p).2.1 _ hz
      rw [LinearMap.sub_apply, hp2 _ hz, sub_eq_zero] at this
      exact this
    have e2 := congrArg (fun U : Module.End E M => U z) hpi
    simp only [Module.End.mul_apply] at e2
    rw [e1, hT.1 _ (hp1 z)] at e2
    exact e2.symm

  have k2 : ∀ z, T z ∈ A := fun z => by
    have hz := hT.2.2 z
    have e1 := (Stabs.aeval hAB hf hd q).2.2.1 _ hz
    rw [LinearMap.sub_apply, hq2 _ hz] at e1
    have e2 := congrArg (fun U : Module.End E M => U z) hqi
    simp only [Module.End.mul_apply] at e2
    rw [← e2] at e1
    have e3 := sub_mem (hT.2.1 _ (hq1 z)) e1
    simpa using e3
  ext z
  simpa using k1 z (k2 z)

theorem exists_intertwiner (hAB : A ≤ B) {f f' : Module.End E M} (hs : (LinearMap.charpoly f).Separable)
    (hf : Stabs A B f) (hd : f' - f ∈ strictUp A B) :
    ∃ T ∈ strictUp A B, (1 + T) * f = f' * (1 + T) := by
  have hf' : Stabs A B f' := by simpa using hf.add_strictUp hAB hd
  let Φ : strictUp A B →ₗ[E] strictUp A B :=
    { toFun := fun T => ⟨T.1 * f - f' * T.1, sub_mem (hf.mul_right T.2) (hf'.mul_left T.2)⟩
      map_add' := fun S T => Subtype.ext (by simp only [Submodule.coe_add, add_mul, mul_add]; abel)
      map_smul' := fun c T => Subtype.ext (by simp [smul_sub]) }
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro T hT
    have h1 : T.1 * f - f' * T.1 = 0 := congrArg Subtype.val hT
    exact Subtype.ext (eq_zero_of_intertwine hAB hs hf hd T.2 (sub_eq_zero.1 h1))
  obtain ⟨T, hT⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨_, hd⟩
  have h1 : T.1 * f - f' * T.1 = f' - f := congrArg Subtype.val hT
  refine ⟨T.1, T.2, ?_⟩
  rw [add_mul, mul_add, one_mul, mul_one]
  rw [sub_eq_iff_eq_add] at h1
  rw [h1]; abel

end Filt

section Unitary

open GlobalTheory.Cusp.WeightCommute

variable {D : D7} {V : HSp D}

theorem exists_adjoint (X : Module.End D.host.E V.V) :
    ∃ Y : Module.End D.host.E V.V, ∀ x y, V.hT (X x) y = V.hT x (Y y) := by
  set g := LinearMap.toMatrix V.frame V.frame X with hg
  have hu : IsUnit V.gram.det := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V
  refine ⟨Matrix.toLin V.frame V.frame (V.gram⁻¹ * gᴴ * V.gram), fun x y => ?_⟩
  have h1 : V.frame.equivFun (X x) = g *ᵥ V.frame.equivFun x := by
    simp only [Module.Basis.equivFun_apply]
    rw [hg, LinearMap.toMatrix_mulVec_repr]
  have h2 : V.frame.equivFun (Matrix.toLin V.frame V.frame (V.gram⁻¹ * gᴴ * V.gram) y) =
      (V.gram⁻¹ * gᴴ * V.gram) *ᵥ V.frame.equivFun y := by
    simp only [Module.Basis.equivFun_apply]
    rw [Matrix.repr_toLin]
  rw [GlobalTheory.ChiGrid.SumDual.hT_eq, GlobalTheory.ChiGrid.SumDual.hT_eq, h1, h2, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem ratAct_inv_right (γ : GF V) (x : V.V) :
    GlobalTheory.Cusp.ratAct D.sp.cm V γ (GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x) = x := by
  rw [← ratAct_mul', mul_inv_cancel, ratAct_one']

theorem conj_of_isotropic {W : Submodule D.host.E V.V} (hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W) (δ : GF V)
    (hreg : IsRegSS δ.1.1) (hδ : δ ∈ (IsoFlag.single hW).parRat D.sp.cm) (ν : GF V)
    (hν : ν ∈ (IsoFlag.single hW).unipRat D.sp.cm) : ∃ g : GF V, g * δ * g⁻¹ = δ * ν := by
  set A := W with hA
  set B := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W with hB
  have hAB : A ≤ B := hW.2
  have hBA : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V B = A := GlobalTheory.SplitFlag.perp_perp W
  have memB : ∀ {y}, y ∈ B ↔ ∀ x ∈ A, V.hT x y = 0 := GlobalTheory.Cusp.WittIdx.mem_perp'
  have memA : ∀ {y}, y ∈ A ↔ ∀ x ∈ B, V.hT x y = 0 := fun {y} => by
    rw [← GlobalTheory.Cusp.WittIdx.mem_perp', hBA]
  set u : Module.End D.host.E V.V := GlobalTheory.Cusp.ratAct D.sp.cm V δ with hu
  set n : Module.End D.host.E V.V := GlobalTheory.Cusp.ratAct D.sp.cm V ν with hn
  set u' : Module.End D.host.E V.V := GlobalTheory.Cusp.ratAct D.sp.cm V (δ * ν) with hu'
  have hu'n : u' = u * n := LinearMap.ext fun x => ratAct_mul' δ ν x
  have par : ∀ γ ∈ (IsoFlag.single hW).parRat D.sp.cm, ∀ x ∈ A, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ A :=
    fun γ hγ x hx => IsoFlag.mem_parRat.1 hγ 1 x hx
  have uA : ∀ x ∈ A, u x ∈ A := par δ hδ
  have uiA := par δ⁻¹ (inv_mem hδ)
  have uB : ∀ x ∈ B, u x ∈ B := fun x hx => memB.2 fun a ha => by
    rw [← ratAct_inv_right δ a, hu, hT_ratAct]
    exact memB.1 hx _ (uiA a ha)
  have hf : Stabs A B u := ⟨uA, uB⟩
  obtain ⟨ν1, ν2⟩ := IsoFlag.mem_unipRat.1 hν
  have nA : ∀ x ∈ A, n x = x := fun x hx => by
    have := ν1 (0 : Fin 1) x hx
    exact sub_eq_zero.1 ((Submodule.mem_bot _).1 this)
  have nB : ∀ x ∈ B, n x - x ∈ A := ν2
  have nV : ∀ x, n x - x ∈ B := fun x => memB.2 fun a ha => by
    rw [map_sub]
    have e : V.hT a (n x) = V.hT a x := by
      conv_lhs => rw [← nA a ha]
      exact hT_ratAct ν a x
    rw [e, sub_self]
  have hn1 : n - 1 ∈ strictUp A B := ⟨fun x hx => by simp [nA x hx], fun x hx => nB x hx, fun x => nV x⟩
  have hd : u' - u ∈ strictUp A B := by
    have := hf.mul_left hn1
    rwa [mul_sub, mul_one, ← hu'n] at this
  have hs : (LinearMap.charpoly u).Separable := by
    rw [← LinearMap.charpoly_toMatrix u V.frame, hu, GlobalTheory.Cusp.ratAct, LinearMap.toMatrix_toLin]
    exact hreg
  obtain ⟨T, hT, he⟩ := exists_intertwiner hAB hs hf hd
  obtain ⟨Y, hY⟩ := exists_adjoint (1 + T)
  have hTR : ∀ x y, V.hT (T x) y = V.hT x ((Y - 1) y) := fun x y => by
    have := hY x y
    simp only [LinearMap.add_apply, Module.End.one_apply, map_add, LinearMap.sub_apply, map_sub] at this ⊢
    rw [← this]; abel
  have hR : Y - 1 ∈ strictUp A B := by
    refine ⟨fun a ha => ?_, fun b hb => ?_, fun x => ?_⟩
    · refine V.nondeg.2 _ fun x => ?_
      rw [← hTR]
      exact memA.1 ha _ (hT.2.2 x)
    · exact memA.2 fun x hx => by
        rw [← hTR]
        exact memB.1 hb _ (hT.2.1 x hx)
    · exact memB.2 fun a ha => by
        rw [← hTR, hT.1 a ha]
        simp
  have hYu : Y * u' = u * Y := by
    ext1 y
    rw [← sub_eq_zero]
    refine V.nondeg.2 _ fun x => ?_
    rw [map_sub, sub_eq_zero, Module.End.mul_apply, Module.End.mul_apply, ← hY]
    have e1 : (1 + T) x = u' ((1 + T) (GlobalTheory.Cusp.ratAct D.sp.cm V δ⁻¹ x)) := by
      have := congrArg (fun U : Module.End D.host.E V.V => U (GlobalTheory.Cusp.ratAct D.sp.cm V δ⁻¹ x)) he
      simp only [Module.End.mul_apply] at this
      rw [← this, hu, ratAct_inv_right]
    rw [e1, hu', hT_ratAct]
    conv_rhs => rw [← ratAct_inv_right δ x]
    rw [hu, hT_ratAct, hY]
  have hZ : Y * (1 + T) - 1 = 0 := by
    have hmem : Y * (1 + T) - 1 ∈ strictUp A B := by
      have e : Y * (1 + T) - 1 = (Y - 1) + T + (Y - 1) * T := by noncomm_ring
      rw [e]
      exact add_mem (add_mem hR hT) (mul_mem_strictUp hAB hR hT)
    refine eq_zero_of_intertwine hAB hs hf (f' := u) (by simp [zero_mem]) hmem ?_
    rw [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, he, ← mul_assoc, hYu, mul_assoc]
  have hZ' : Y * (1 + T) = 1 := sub_eq_zero.1 hZ
  have hiso : ∀ x y, V.hT ((1 + T) x) ((1 + T) y) = V.hT x y := fun x y => by
    rw [hY, ← Module.End.mul_apply, hZ', Module.End.one_apply]
  set gm := LinearMap.toMatrix V.frame V.frame (1 + T) with hgm
  set gy := LinearMap.toMatrix V.frame V.frame Y with hgy
  have m1 : gy * gm = 1 := by
    rw [hgm, hgy, ← LinearMap.toMatrix_mul, hZ', LinearMap.toMatrix_one]
  have m2 : gm * gy = 1 := mul_eq_one_comm.mp m1
  have hU : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) gm * V.gram * gm = V.gram :=
    GlobalTheory.ChiGrid.SumDual.gram_isom V V (1 + T) hiso
  let g : GF V := ⟨⟨gm, gy, m2, m1⟩, hU⟩
  refine ⟨g, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  refine Subtype.ext (Units.ext ?_)
  show gm * δ.1.1 = (δ * ν).1.1 * gm
  apply (Matrix.toLin V.frame V.frame).injective
  rw [Matrix.toLin_mul V.frame V.frame V.frame, Matrix.toLin_mul V.frame V.frame V.frame, hgm, Matrix.toLin_toMatrix]
  exact he

end Unitary

theorem conj_translate : ∀ (D : D7) (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C)
    (δ : GF V), IsRegSS δ.1.1 → δ ∈ (frameFlag hC).parRat D.sp.cm → ∀ ν ∈ (frameFlag hC).unipRat D.sp.cm,
      ∃ g : GF V, g * δ * g⁻¹ = δ * ν :=
  fun _ _ _ _ hC δ hreg hδ ν hν => conj_of_isotropic _ δ hreg hδ ν hν

end GlobalTheory.CompanionTheory.ParabConj
