import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

section Ev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def rulEv (U : Unf Xo c σ r)
    (hT : ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)) :
    Rul Xo c →+* ((Σ k : U.Comp, (U.X k).dom) → ℂ) where
  toFun f y := rdU U f y.1 y.2.1
  map_zero' := by funext y; rw [map_zero]; rfl
  map_add' f g := by funext y; rw [map_add]; rfl
  map_mul' f g := by funext y; rw [rdU_mul]; rfl
  map_one' := by
    funext y
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.rdU_apply_dom U 1 y.1 y.2]
    have e : evR Xo c 1 (U.un y.1 y.2) = 1 := evalAt_one _ _ _ (hT y.1 y.2)
    rw [e]
    rfl

end Ev

def sumParts (R M : Type) [CommRing R] [AddCommMonoid M] :
    AddMonoidAlgebra R M →+* R :=
  (AddMonoidAlgebra.lift R R M 1).toRingHom

theorem sumParts_single (R M : Type) [CommRing R] [AddCommMonoid M] (m : M) (f : R) :
    sumParts R M (AddMonoidAlgebra.single m f) = f := by
  simp [sumParts]

theorem sumParts_smul (K R M : Type) [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (a : K)
    (x : AddMonoidAlgebra R M) : sumParts R M (a • x) = a • sumParts R M x := by
  rw [← algebraMap_smul R a x, ← algebraMap_smul R a (sumParts R M x)]
  exact map_smul (AddMonoidAlgebra.lift R R M 1) _ _

set_option synthInstance.maxHeartbeats 200000 in

theorem exists_isRdgU : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)), ∃ (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e := by
  intro D T h j hj n
  have hT := h.unTest j hj T.σ₀ T.good_σ₀
  have hU : IsUnf (T.U j T.σ₀) := h.unf j hj T.σ₀ T.good_σ₀
  let ev : AddMonoidAlgebra (T.R j) (Deg D j) →+* (DomPt T j → ℂ) :=
    (rulEv (T.U j T.σ₀) hT).comp (sumParts (T.R j) (Deg D j))
  have hev : ∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (y : DomPt T j),
      ev (incG deg (cutR T.C j) u F) y = rdR h j F y.1 y.2.1 := by
    intro u F y
    show rulEv (T.U j T.σ₀) hT (sumParts (T.R j) (Deg D j) (AddMonoidAlgebra.single (deg u) F.1)) y = _
    rw [sumParts_single]
    rfl
  have hsm : ∀ (a : T.Q.c.F) (F : AddMonoidAlgebra (T.R j) (Deg D j)), ev (a • F) = T.σ₀ a • ev F := by
    intro a F
    funext y
    show rdU (T.U j T.σ₀) (sumParts (T.R j) (Deg D j) (a • F)) y.1 y.2.1 =
      T.σ₀ a • rdU (T.U j T.σ₀) (sumParts (T.R j) (Deg D j) F) y.1 y.2.1
    rw [sumParts_smul, map_smulₛₗ]
    rfl
  have hind : ∀ (u : WeightFamilies.Wt D j) (m : ℕ) (F : Fin m → cutR T.C j u),
      LinearIndependent T.Q.c.F F → LinearIndependent ℂ fun i => ev (incG deg (cutR T.C j) u (F i)) := by
    intro u m F hF
    have hb := hF.map' (cutR T.C j u).subtype (Submodule.ker_subtype _)
    have hs : ∀ i, (F i).1 ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n := fun i =>
      cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) (wtA u) u.n (cutR_le T.C j u (F i).2)
    have hli : LinearIndependent ℂ (fun i => rdU (T.U j T.σ₀) (F i).1) :=
      (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ _ _ _ _ _ T.σ₀ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀))
        ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU) (wtA u) u.n).1 m (fun i => (F i).1) hs hb
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro g hg
    refine hli g ?_
    funext k x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hx : x ∈ ((T.U j T.σ₀).X k).dom
    · have h1 := congrFun hg ⟨k, ⟨x, hx⟩⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => congrArg (fun z => g i * z) (hev u (F i) ⟨k, ⟨x, hx⟩⟩).symm
    · refine Finset.sum_eq_zero fun i _ => ?_
      have : rdU (T.U j T.σ₀) (F i).1 k x = 0 := dif_neg hx
      rw [this, mul_zero]
  exact ⟨⟨DomPt T j, T.σ₀, ev, hsm, hind⟩, Equiv.refl _, fun _ => rfl, hev⟩

end GlobalTheory.Shares
