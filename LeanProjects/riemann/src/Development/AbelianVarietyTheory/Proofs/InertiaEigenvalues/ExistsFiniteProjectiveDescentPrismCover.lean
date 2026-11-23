import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeIffIsBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleDescentFiniteLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteProjectiveLiftOfIsAdicCompleteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismPushoutModAdicPowUniversalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentSolutionLiftModPrismIdealStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeOfIsBaseChangeQuotientStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.CoverDesc

def solSub {l : ℕ} {R : Type} [CommRing R] {d : ℕ} {B C D : Obj l R} (h : Hom B C) (p q : Hom C D)
    (hpq : p.comp h = q.comp h) (E : Matrix (Fin d) (Fin d) D.A) :
    letI := h.f.toAlgebra; Submodule B.A (Fin d → C.A) :=
  letI := h.f.toAlgebra
  { carrier := {z | (fun i => p.f (z i)) = E.mulVec fun i => q.f (z i)}
    add_mem' := by
      intro a b ha hb
      change (fun i => p.f (a i + b i)) = E.mulVec fun i => q.f (a i + b i)
      have e1 : (fun i => p.f (a i + b i)) = (fun i => p.f (a i)) + fun i => p.f (b i) := by
        funext i; exact map_add _ _ _
      have e2 : (fun i => q.f (a i + b i)) = (fun i => q.f (a i)) + fun i => q.f (b i) := by
        funext i; exact map_add _ _ _
      rw [e1, e2, Matrix.mulVec_add]
      exact congrArg₂ (· + ·) ha hb
    zero_mem' := by
      change (fun i => p.f 0) = E.mulVec fun i => q.f 0
      simp only [map_zero]
      exact (Matrix.mulVec_zero _).symm
    smul_mem' := by
      intro b z hz
      change (fun i => p.f (h.f b * z i)) = E.mulVec fun i => q.f (h.f b * z i)
      have hc : p.f (h.f b) = q.f (h.f b) := congrArg (fun k : Hom B D => k.f b) hpq
      have e1 : (fun i => p.f (h.f b * z i)) = p.f (h.f b) • fun i => p.f (z i) := by
        funext i; exact map_mul _ _ _
      have e2 : (fun i => q.f (h.f b * z i)) = p.f (h.f b) • fun i => q.f (z i) := by
        funext i; rw [map_mul, ← hc]; rfl
      rw [e1, e2, Matrix.mulVec_smul]
      exact congrArg _ hz }

theorem lift_mod {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d) {B C D : Obj l ↥(OL K)}
    (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D) (hc : Cover h) (hpo : IsPO h h p q)
    (v : Fin d → C.A ⧸ adI C ^ 1)
    (hv : (fun i => qmap p 1 (v i)) =
      ((S.ε (p.comp f) (q.comp f)).map (Ideal.Quotient.mk (adI D ^ 1))).mulVec fun i => qmap q 1 (v i)) :
    ∃ z : Fin d → C.A, (fun i => p.f (z i)) = (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) ∧
      ∀ i, Ideal.Quotient.mk (adI C ^ 1) (z i) = v i := by
  choose z₀ hz₀ using fun i => Ideal.Quotient.mk_surjective (I := adI C ^ 1) (v i)
  obtain rfl : (fun i => Ideal.Quotient.mk (adI C ^ 1) (z₀ i)) = v := funext hz₀
  have hyp : ∀ i, p.f (z₀ i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z₀ j)) i ∈ adI D ^ 1 := by
    intro i
    rw [← Ideal.Quotient.eq]
    have e := congrFun hv i
    simp only [qmap_mk] at e
    exact e.trans (RingHom.map_mulVec _ _ _ i).symm
  have H := GlobalTheory.T.exists_descent_solution_lift_mod_prism_ideal l K bk d S B C D h f p q hc hpo z₀ hyp
  exact ⟨H.choose, H.choose_spec.2, fun i => Ideal.Quotient.eq.2 (H.choose_spec.1 i)⟩

set_option maxHeartbeats 1600000 in

theorem exists_descent : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C), Cover h → ∃ (P : Type) (_ : AddCommGroup P) (_ : Module B.A P) (_ : Module.Finite B.A P) (_ : Module.Projective B.A P) (u : P →ₛₗ[h.f] (Fin d → C.A)), SemiBC u ∧ ∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → ∀ x, (fun i => p.f (u x i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (u x i) := by
  intro l _ K bk d S B C h f hc
  obtain ⟨D, p₀, q₀, hpo⟩ := hc.stable.po C h
  have hcomm : ∀ b, p₀.f (h.f b) = q₀.f (h.f b) := fun b => congrArg (fun k : Hom B D => k.f b) hpo.comm
  letI : Algebra (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := (qmap h 1).toAlgebra
  obtain ⟨N₁, hN₁, hfin, hproj, hbc⟩ := GlobalTheory.T.stratifiedPhiModule_descent_finite_level l K bk d S B C D h f p₀ q₀ hc hpo 1
  haveI hcB : IsAdicComplete (adI B ^ 1) B.A := by rw [pow_one]; exact B.complete
  obtain ⟨P, _, _, _, _, u₁, hu₁⟩ := GlobalTheory.T.exists_finite_projective_lift_of_isAdicComplete B.A (adI B ^ 1) ↥N₁
  letI : Algebra B.A C.A := h.f.toAlgebra
  haveI : IsScalarTower B.A (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := IsScalarTower.of_algebraMap_eq (fun b => rfl)
  have hs : ∀ (b : B.A) (y : ↥N₁), (Ideal.Quotient.mk (adI B ^ 1) b) • y = b • y := fun b y => Subtype.ext rfl
  let u₁' : P →ₗ[B.A] ↥N₁ := { toFun := fun x => u₁ x, map_add' := fun x y => u₁.map_add x y, map_smul' := fun b x => (u₁.map_smulₛₗ b x).trans (hs b (u₁ x)) }
  have hb1 : IsBaseChange (B.A ⧸ adI B ^ 1) u₁' := (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange B.A (B.A ⧸ adI B ^ 1) P ↥N₁ u₁ u₁' (fun x => rfl)).1 hu₁
  have hb2 := hb1.comp hbc
  let M := solSub h p₀ q₀ hpo.comm (S.ε (p₀.comp f) (q₀.comp f))
  have memM : ∀ z, z ∈ M ↔ (fun i => p₀.f (z i)) = (S.ε (p₀.comp f) (q₀.comp f)).mulVec fun i => q₀.f (z i) := fun z => Iff.rfl
  have memN : ∀ z : Fin d → C.A, z ∈ M → (fun i => Ideal.Quotient.mk (adI C ^ 1) (z i)) ∈ N₁ := by
    intro z hz
    rw [hN₁]
    funext i
    simp only [qmap_mk]
    have e : p₀.f (z i) = (S.ε (p₀.comp f) (q₀.comp f)).mulVec (fun j => q₀.f (z j)) i := congrFun ((memM z).1 hz) i
    exact (congrArg (Ideal.Quotient.mk (adI D ^ 1)) e).trans (RingHom.map_mulVec _ _ _ i)
  let π : M →ₗ[B.A] ↥N₁ :=
    { toFun := fun z => ⟨fun i => Ideal.Quotient.mk (adI C ^ 1) (z.1 i), memN z.1 z.2⟩
      map_add' := fun a b => Subtype.ext (funext fun i => map_add _ _ _)
      map_smul' := fun b z => Subtype.ext (funext fun i => map_mul _ _ _) }
  have hπ : Function.Surjective π := by
    intro n
    have H := lift_mod S h f p₀ q₀ hc hpo n.1 ((hN₁ n.1).1 n.2)
    exact ⟨⟨H.choose, (memM _).2 H.choose_spec.1⟩, Subtype.ext (funext H.choose_spec.2)⟩
  have HG := Module.projective_lifting_property π u₁' hπ
  let g := HG.choose
  have hg : π ∘ₗ g = u₁' := HG.choose_spec
  let u' : P →ₗ[B.A] (Fin d → C.A) := M.subtype ∘ₗ g
  let u : P →ₛₗ[h.f] (Fin d → C.A) :=
    { toFun := fun x => u' x, map_add' := fun x y => u'.map_add x y, map_smul' := fun b x => u'.map_smul b x }
  have huM : ∀ x, u x ∈ M := fun x => (g x).2
  refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, u, ?_, ?_⟩
  · haveI := C.complete
    have hV : IsBaseChange C.A u' := by
      have hgq := (IsBaseChange.linearMap C.A (C.A ⧸ adI C ^ 1)).finitePow (Fin d)
      refine GlobalTheory.T.isBaseChange_of_isBaseChange_quotient_comp B.A C.A (adI C ^ 1) ?_ P (Fin d → C.A) _ u' _ hgq ?_
      · exact le_trans (Ideal.pow_le_self one_ne_zero) (IsAdicComplete.le_jacobson_bot _)
      · have heq : ((Algebra.linearMap C.A (C.A ⧸ adI C ^ 1)).compLeft (Fin d)).restrictScalars B.A ∘ₗ u' =
            (N₁.subtype.restrictScalars B.A).comp u₁' := by
          refine LinearMap.ext fun x => funext fun i => ?_
          exact congrArg (fun y : ↥N₁ => y.1 i) (LinearMap.congr_fun hg x)
        rw [heq]; exact hb2
    exact (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange B.A C.A P (Fin d → C.A) u u' (fun x => rfl)).2 hV
  · intro Q p q hpq x
    have HC := GlobalTheory.T.prismPushoutModAdicPow_universal l _ B C C D h h p₀ q₀ hpo Q p q hpq
    obtain ⟨c, ⟨hcp, hcq⟩, -⟩ := HC
    subst hcp hcq
    have hx := (memM _).1 (huM x)
    rw [show (c.comp p₀).comp f = c.comp (p₀.comp f) from rfl, show (c.comp q₀).comp f = c.comp (q₀.comp f) from rfl,
      ← S.ε_nat c]
    funext i
    change c.f (p₀.f (u x i)) = _
    have e : p₀.f (u x i) = (S.ε (p₀.comp f) (q₀.comp f)).mulVec (fun j => q₀.f (u x j)) i := congrFun hx i
    rw [e, RingHom.map_mulVec]
    rfl

end GlobalTheory.BSP.CoverDesc
