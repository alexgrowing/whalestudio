import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsAUnit
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
open scoped TensorProduct

namespace GlobalTheory.LeviShift

section Mult

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : HSpace E} (Φ : WittFrame V) (hc : CMData F E) (R : Type) [CommRing R] [Algebra F R]

namespace DetUMul

theorem hLin_coordR (x y : V.V) :
    hLin hc.sig V.gram R (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R x) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R y) = inclR R (V.hD x y) := by
  change hR R hc.sig V.gram _ _ = inclR R (V.hT _ _)
  rw [IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp [hR, Formalism.UG.hform, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR, JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, CMData.sig,
    TensorProduct.tmul_sum, starRingEnd_apply]

theorem hD_bas_dbas (u : SV (wittIndex V)) (i k : Supp u) :
    V.hD (bas Φ u i.1) (dbas Φ u k.1) = if i = k then 1 else 0 := by
  have hi := i.2
  have hk := k.2
  simp only [bas, dbas]
  by_cases ei : u i.1 = -1 <;> by_cases ek : u k.1 = -1
  · rw [if_pos ei, if_pos ek]
    have h1 := V.herm.eq (Φ.f i.1) (Φ.e k.1)
    have h2 := Φ.ef k.1 i.1
    simp only [HSpace.hD] at h2 ⊢
    rw [← h1, h2]
    by_cases e : i = k
    · subst e; simp
    · rw [if_neg (fun h => e (Subtype.ext h.symm)), if_neg e]; simp
  · rw [if_pos ei, if_neg ek, Φ.ff, if_neg]
    rintro rfl; exact ek ei
  · rw [if_neg ei, if_pos ek, Φ.ee, if_neg]
    rintro rfl; exact ei ek
  · rw [if_neg ei, if_neg ek, Φ.ef]
    by_cases e : i = k
    · subst e; simp
    · rw [if_neg (fun h => e (Subtype.ext h)), if_neg e]

theorem coordR_zero : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R (0 : V.V) = (0 : Fin V.rank → R ⊗[F] E) := by
  funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR]

theorem coordR_add (x y : V.V) : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R (x + y) =
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R x + GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R y := by
  funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR]

theorem coordR_smul (c : E) (x : V.V) : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R (c • x) =
    inclR (F := F) R c • GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R x := by
  funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR]

def hLinL (x : Fin V.rank → R ⊗[F] E) : (Fin V.rank → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun y := hLin hc.sig V.gram R y x
  map_add' y y' := hLin_add_left _ _ _ y y' _
  map_smul' c y := hLin_smul_left _ _ _ c y _

def projU (u : SV (wittIndex V)) : (Fin V.rank → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin V.rank → R ⊗[F] E) :=
  ∑ k : Supp u, (hLinL hc R (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (dbas Φ u k.1))).smulRight
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (bas Φ u k.1))

theorem expand (u : SV (wittIndex V)) {y : Fin V.rank → R ⊗[F] E}
    (hy : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extSub (F := F) V R (Φ.sub u)) :
    y = ∑ k : Supp u, hLin hc.sig V.gram R y (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (dbas Φ u k.1)) •
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (bas Φ u k.1) := by
  suffices h : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extSub (F := F) V R (Φ.sub u) ≤ LinearMap.eqLocus LinearMap.id (projU Φ hc R u) by
    have := h hy
    simpa [projU, hLinL, LinearMap.sum_apply] using this
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have key : ∀ i : Supp u, x = bas Φ u i.1 →
        GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R x ∈ LinearMap.eqLocus LinearMap.id (projU Φ hc R u) := by
      rintro i rfl
      show _ = _
      simp only [LinearMap.id_apply, projU, LinearMap.sum_apply, LinearMap.smulRight_apply, hLinL,
        LinearMap.coe_mk, AddHom.coe_mk, hLin_coordR, hD_bas_dbas, apply_ite (inclR R), map_one, map_zero,
        ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rcases hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · refine key ⟨i, by rw [show u i = 1 from hi]; decide⟩ ?_
      simp only [bas]; rw [if_neg]; rw [show u i = 1 from hi]; decide
    · refine key ⟨i, by rw [show u i = -1 from hi]; decide⟩ ?_
      simp only [bas]; rw [if_pos (show u i = -1 from hi)]
  | zero => rw [coordR_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [coordR_add]; exact add_mem hx hy
  | smul c x _ hx => rw [coordR_smul]; exact Submodule.smul_mem _ _ hx

theorem detMat_mul (u : SV (wittIndex V)) (g g' : HA R hc.sig V.gram)
    (hg' : g' ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab hc V R (Φ.sub u)) :
    detMat Φ hc R u (g * g') = detMat Φ hc R u g * detMat Φ hc R u g' := by
  ext i j
  have hb : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R (bas Φ u j.1) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extSub (F := F) V R (Φ.sub u) := by
    refine GlobalTheory.Cusp.coordR_mem V R (Submodule.subset_span ?_)
    by_cases h : u j.1 = -1
    · right; exact ⟨j.1, h, by simp [bas, h]⟩
    · have h1 : u j.1 = 1 := by
        have := j.2
        revert h this; cases u j.1 <;> decide
      left; exact ⟨j.1, h1, by simp [bas, h]⟩
  have key : ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extSub (F := F) V R (Φ.sub u),
      hLin hc.sig V.gram R (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act hc V g y) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (dbas Φ u i.1)) =
      ∑ k : Supp u, hLin hc.sig V.gram R (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act hc V g (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (bas Φ u k.1)))
          (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (dbas Φ u i.1)) *
        hLin hc.sig V.gram R y (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (dbas Φ u k.1)) := by
    intro y hy
    conv_lhs => rw [expand Φ hc R u hy]
    have e1 : ∀ z : Fin V.rank → R ⊗[F] E, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act hc V g z =
        Matrix.mulVecLin ((HA.mat R hc.sig V.gram g : GL (Fin V.rank) (R ⊗[F] E)) : Matrix (Fin V.rank) (Fin V.rank) (R ⊗[F] E)) z :=
      fun _ => rfl
    have e2 : ∀ z x : Fin V.rank → R ⊗[F] E, hLin hc.sig V.gram R z x = hLinL hc R x z := fun _ _ => rfl
    simp only [e1, e2, map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  simp only [detMat, Matrix.of_apply, Matrix.mul_apply]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, key _ (GlobalTheory.Cusp.mem_parab_iff_maps.1 hg' _ hb)]

end DetUMul

open DetUMul in

theorem detU_mul (u : SV (wittIndex V)) (g g' : HA R hc.sig V.gram)
    (_hg : g ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab hc V R (Φ.sub u)) (hg' : g' ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab hc V R (Φ.sub u)) :
    detU Φ hc R u (g * g') = detU Φ hc R u g * detU Φ hc R u g' := by
  rw [detU, detMat_mul Φ hc R u g g' hg', Matrix.det_mul]; rfl

end Mult

end GlobalTheory.LeviShift
