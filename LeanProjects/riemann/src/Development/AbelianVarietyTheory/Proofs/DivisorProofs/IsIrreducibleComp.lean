import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCosocleComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalInvTransposeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistInvTransposeDetCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContragredientEqInvTransposeClassStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.DualityMap

open GlobalTheory.TypeTame

section Comp

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def compEquiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) (s : H →* G) :
    Representation.Equiv (π.comp s : Representation ℂ H V) (σ.comp s : Representation ℂ H W) :=
  Representation.Equiv.mk φ.toLinearEquiv fun g => φ.toIntertwiningMap.isIntertwining' (s g)

end Comp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem isSmooth_comp {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} (h : IsSmooth π) :
    IsSmooth (π.comp (invTranspose n) : Representation ℂ (GL (Fin n) k) V) :=
  fun v => (h v).preimage (continuous_invTranspose n)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem isIrreducible_comp {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} (h : π.IsIrreducible) :
    Representation.IsIrreducible (π.comp (invTranspose n) : Representation ℂ (GL (Fin n) k) V) :=
  GlobalTheory.CosocleComp.isIrreducible_comp (fun g => ⟨_, invTranspose_invTranspose n g⟩) h

def dual (x : IrrGL k) : IrrGL k :=
  IrrGL.of (x.rep.comp (invTranspose x.1)) (isSmooth_comp x.2.rep.smooth) (isIrreducible_comp x.2.rep.irr)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem dual_of {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) :
    dual (IrrGL.of π hs hi) = IrrGL.of (π.comp (invTranspose n)) (isSmooth_comp hs) (isIrreducible_comp hi) :=
  IrrGL.of_eq_of.2 ⟨compEquiv (IrrGL.equivOf π hs hi).symm (invTranspose n)⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem dual_dual (x : IrrGL k) : dual (dual x) = x := by
  refine (dual_of _ _ _).trans (Eq.trans (IrrGL.of_eq_of.2 ⟨?_⟩) (IrrGL.of_rep x))
  refine Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun g => ?_
  ext v
  show x.rep (invTranspose x.1 (invTranspose x.1 g)) v = x.rep g v
  rw [invTranspose_invTranspose]

theorem dual_nu (x : IrrGL k) (s : ℂ) : dual (x.nu s) = (dual x).nu (-s) := by
  obtain ⟨e⟩ := GlobalTheory.T.twist_inv_transpose_det_char k x.1 _ x.rep s
  refine Eq.trans ?_ (IrrGL.tw_of _ _ _ _ _).symm
  exact IrrGL.of_eq_of.2 ⟨(compEquiv (IrrGL.twEquiv x _ (isSmoothChar_absPow s)).symm (invTranspose x.1)).trans e⟩

theorem isCusp_dual (x : IrrGL k) (h : x.IsCusp) : (dual x).IsCusp :=
  ⟨h.1, isCuspidal_of_equiv (IrrGL.equivOf _ _ _) (GlobalTheory.T.cuspidal_inv_transpose k x.1 _ x.rep h.2)⟩

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → ∃ D : IrrGL k → IrrGL k, (∀ x y, DualCl x y ↔ y = D x) ∧ (∀ x, D (D x) = x) ∧
      (∀ (x : IrrGL k) (s : ℂ), D (x.nu s) = (D x).nu (-s)) ∧ (∀ x, x.IsCusp → (D x).IsCusp) ∧
      (∀ x, (D x).1 = x.1) := by
  intro k _ _ _ _ hA
  refine ⟨dual, fun x y => (GlobalTheory.T.contragredient_eq_inv_transpose_class k hA x y).trans ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨_, _, h⟩⟩, dual_dual,
    dual_nu, isCusp_dual, fun _ => rfl⟩

end GlobalTheory.DualityMap
