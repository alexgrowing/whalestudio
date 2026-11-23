import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpConjOfOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseRatAtOfPhaseOne

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjExpandRational

theorem evaluates_of_unif' {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀) (hu : R.LUnif) : fw.Evaluates := by
  intro i σ hσ hV
  refine fw.ev i σ hσ hV ?_
  by_contra hne
  have h0 := fw.ev0 i σ hσ hV hne
  have hx : ∀ x : Fin (R.nW i) → D.what₂.LL, x = 0 := fun x => by
    by_contra hx
    have h1 : LinearIndependent D.what₂.LL (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 hx
    have h2 := ((hu i σ).1 1 _ h1).ne_zero 0
    rw [h0] at h2
    exact h2 rfl
  refine hne ⟨0, fun f => ?_⟩
  have hf : f = 0 := (fw.e i).injective (Subtype.ext ((hx _).trans (hx _).symm))
  subst hf
  refine Eq.trans ?_ (GlobalTheory.phiC_zero_rule T hV (wtA (κ i))).symm
  rw [LinearMap.zero_apply, map_zero]
  rfl

end GlobalTheory.ConjExpandRational

theorem GlobalTheory.ConjExpandRational.conj_expansion_rational : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → AtTw fun Fm x hx i p w j => ∀ τ : ℂ ≃+* ℂ,
  (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
  ∀ Φ Φ' : GA (Fm.D x i) (Wc (Fm.D x i) j) → ℂ, GlobalTheory.ConjTwist.ConjFun (p.O j) (p.κ j) τ 1 Φ Φ' →
    ∃ (n : ℕ) (b : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
      Φ = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧ ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val = Φ' := by
  intro _ _ _ _
  unfold AtTw AtPts
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j τ hτ Φ Φ' hC => ?_⟩⟩⟩
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hb := GlobalTheory.IndefiniteRowSideFullHecke.LatticePartsOverBalls.base_of_tie (i := j) p.fw
  have hso : (p.O j).s0 = res p.T (sg0 _ p.P.A3.A) := (sOv_eq p.T.toCore (p.O j).c' (p.O j).hle).trans hb.1.symm
  have hev := GlobalTheory.ConjExpandRational.evaluates_of_unif' p.fw hU j (sg0 _ p.P.A3.A) hb.2.1 hb.2.2

  let gf : p.T.cuspA ((j : ℕ) + 1) (wtA (p.κ j)) (p.κ j).n → NX.FmK p.Sx ((j : ℕ) + 1) := fun f =>
    ⟨(p.nexp.fi j).e.symm (p.fw.e j f), ((p.nexp.fi j).wk _).2 (by rw [LinearEquiv.apply_symm_apply]; exact (p.fw.e j f).2)⟩
  have hread : ∀ (f : p.T.cuspA ((j : ℕ) + 1) (wtA (p.κ j)) (p.κ j).n) h,
      (lieFac (p.T.Q.Dw ((j : ℕ) + 1)) (xiR (Fm.D x i)) (wtA (p.κ j)) : ℂ) *
      (p.O j).phi (p.T.cE ((j : ℕ) + 1) (p.O j).s0) (f : p.T.R ((j : ℕ) + 1)) h = evW p.nexp p.v₀ j (gf f).val h := by
    intro f h
    rw [phi_cE p.T p.R.toRealDat p.O j]
    refine Eq.trans ?_ ((congrFun (hev f) h).symm.trans ?_)
    · exact congrFun (GlobalTheory.LiftRatObj.phiC_congr p.T hso (p.O j).hV hb.2.2 _ _) h
    · show _ = ((p.R.HW j (sg0 _ p.P.A3.A)).e (((p.R.FW j).j (sg0 _ p.P.A3.A)) ((p.nexp.fi j).e
        ((p.nexp.fi j).e.symm (p.fw.e j f))))) (p.v₀ j (sg0 _ p.P.A3.A)) h
      rw [LinearEquiv.apply_symm_apply]
      rfl
  obtain ⟨⟨n, a, f, hf⟩, h2⟩ := hC
  have hf' := h2 n a f hf
  refine ⟨n, a, fun k => gf (f k), funext fun h => ?_, funext fun h => ?_⟩
  · rw [hf h, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hread]
  · rw [hf' h, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hread]
    simp only [one_mul]
