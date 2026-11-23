import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

open scoped TensorProduct

namespace GlobalTheory.IwasawaTri

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (coordR extSub act)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {V : HSpace E} {R : Type} [CommRing R] [Algebra F R]

theorem act_mem_of_mem_span {S : Set V.V} {A : Submodule E V.V} {g : HA R hc.sig V.gram}
    (h : ∀ x ∈ S, act hc V g (coordR V R x) ∈ extSub (F := F) V R A) {x : V.V}
    (hx : x ∈ Submodule.span E S) : act hc V g (coordR V R x) ∈ extSub (F := F) V R A := by
  let f : (Fin V.rank → R ⊗[F] E) →ₗ[R ⊗[F] E] Fin V.rank → R ⊗[F] E :=
    (HA.mat R hc.sig V.gram g).1.mulVecLin
  change f (coordR V R x) ∈ _
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [show coordR V R 0 = 0 from funext fun _ => by simp [coordR], map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 =>
    rw [show coordR V R (x + y) = coordR V R x + coordR V R y from funext fun _ => by simp [coordR], map_add]
    exact add_mem h1 h2
  | smul a x _ h1 =>
    rw [show coordR V R (a • x) = inclR (F := F) R a • coordR V R x from funext fun _ => by simp [coordR], map_smul]
    exact Submodule.smul_mem _ _ h1

end Gen

theorem mem_pLoc_flag0_of_mul_eq_upper : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (v : HeightOneSpectrum (𝓞 D.host.F)) (p : GLoc D.sp.cm.sig V.gram v) (b : Matrix (Fin (wittIndex V)) (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E)), b.BlockTriangular id → (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram p).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * b → p ∈ PLoc Φ.flag0 v := by
  intro D V Φ v p b hb h
  refine IsoFlag.mem_par.2 fun i => GlobalTheory.Cusp.mem_parab.2 fun x hx => ?_
  have hgen : ∀ j : Fin (wittIndex V), j.val < i.val →
      act D.sp.cm V p (coordR V (Fv D.host.F v) (Φ.e j)) ∈ extSub (F := D.host.F) V (Fv D.host.F v) (Φ.flag0.X i) := by
    intro j hj
    have hcol : act D.sp.cm V p (coordR V (Fv D.host.F v) (Φ.e j)) =
        ∑ k, b k j • coordR V (Fv D.host.F v) (Φ.e k) := by
      funext a
      have := congrFun (congrFun h a) j
      simp only [Matrix.mul_apply, Matrix.of_apply] at this
      simp only [act, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hcol]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : j < k
    · rw [hb hk, zero_smul]; exact zero_mem _
    · exact Submodule.smul_mem _ _ (GlobalTheory.Cusp.coordR_mem V _
        (Submodule.subset_span ⟨k, show k.val < i.val from Nat.lt_of_le_of_lt (Fin.le_def.1 (not_lt.1 hk)) hj, rfl⟩))
  exact act_mem_of_mem_span (S := Φ.e '' {j | j.val < i.val}) (fun _ ⟨j, hj, e⟩ => e ▸ hgen j hj) hx

end GlobalTheory.IwasawaTri
