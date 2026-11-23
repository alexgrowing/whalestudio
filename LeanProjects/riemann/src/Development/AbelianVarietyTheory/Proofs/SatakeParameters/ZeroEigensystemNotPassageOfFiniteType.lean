import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ZeroPassage

theorem dualPoly_coeff_zero {K : Type} [Field K] (s : K) (p : K[X]) (hp : p ≠ 0) : (dualPoly s p).coeff 0 = 1 := by
  unfold dualPoly
  rw [coeff_C_mul, coeff_zero_eq_eval_zero, eval_comp]
  simp [← coeff_zero_eq_eval_zero, hp]

theorem heckePoly_zero {L Pl : Type} [Field L] (n : ℕ) (q : Pl → ℕ) (P : Pl) :
    Formalism.L2.Col.heckePoly n q (fun _ => (0 : L)) P = 0 := by
  simp [Formalism.L2.Col.heckePoly, Formalism.L2.Col.heckePolyOf]

theorem mem_resSet_of_mem_ixFin3 {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 I0 Ty : Type} {B : BlockDat K G Pl0} (D : InertDat3 B I0 Ty) {X : Finset (G → K)}
    {p : Typ3 K Pl0 I0 Ty} (hp : p ∈ D.ixFin3 X) : p.1 ∈ B.resSet X := by
  unfold InertDat3.ixFin3 at hp
  split_ifs at hp with hfin
  · rw [Set.Finite.mem_toFinset] at hp
    refine ⟨hp.1, fun hb => hp.2.2 ?_⟩
    have hle : D.inertTypeEigenspaceSum p ≤ B.partF p.1 := by
      refine iSup₂_le fun x hx => ?_
      refine le_trans ?_ (Formalism.L2.Col.eigAt_le_eigSum (op := B.op) (C := B.HasRes p.1) (x := fun i => x (Sum.inl i)) hx.1)
      exact le_iInf fun i => iInf_le (fun k => (D.opAll k).maxGenEigenspace (x k)) (Sum.inl i)
    rw [eq_bot_iff] at hb ⊢
    exact le_trans (Submodule.comap_mono (Submodule.map_mono hle)) hb
  · simp at hp

theorem zero_not_passage : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ j (p : A3.fam3.base3.Ix), ¬ cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h j p
  rintro ⟨x, hx, hx0⟩
  obtain ⟨P, hP⟩ := (GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F h).2.2.2.2.2.2
  have hxz : (fun i => x (Sum.inl i)) = fun _ => (0 : D.what₂.LL) := by
    funext i
    have h1 := congrFun hx0 (Sum.inl i)
    exact (map_eq_zero_iff _ D.what₂.embLL.injective).1 h1.symm
  let P' : (A3.A.fam.L j A3.A.μ0).Pl := ⟨P, hP⟩
  have hres := hx.1 P'
  rw [hxz] at hres
  replace hres := (heckePoly_zero (L := D.what₂.LL) (Pl := (A3.A.fam.L j A3.A.μ0).Pl) _ _ _).symm.trans hres
  have hmem : p.1.1 ∈ (A3.A.fam.R A3.A.μ0).resSet A3.A.X := mem_resSet_of_mem_ixFin3 (A3.rowI A3.A.μ0) p.2
  have hc : (p.1.1 P).coeff 0 = 1 :=
    (A3.A.fam.R A3.A.μ0).lf_coeff_zero_of_mem_resSet (fun Q => (h.base.fam.degR A3.A.μ0 Q).1) hmem P
  have hne : p.1.1 P ≠ 0 := fun h0 => by rw [h0, coeff_zero] at hc; exact zero_ne_one hc
  have hb : ((A3.A.fam.L j A3.A.μ0).blockProd P').coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero]; exact (A3.A.fam.L j A3.A.μ0).lf_blockProd_eval_zero P'
  have ht : ((A3.fam3.tr3 j p.1).1 ((A3.A.fam.L j A3.A.μ0).pl P')).coeff 0 = 1 := dualPoly_coeff_zero _ _ hne
  have h2 := congrArg (fun f => Polynomial.coeff f 0) hres
  simp only [coeff_zero, mul_coeff_zero, hb, ht, mul_one] at h2
  exact zero_ne_one h2

end GlobalTheory.ZeroPassage
