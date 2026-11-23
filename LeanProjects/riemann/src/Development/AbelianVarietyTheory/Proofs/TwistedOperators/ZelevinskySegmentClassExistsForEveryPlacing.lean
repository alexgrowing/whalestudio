import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
open scoped TensorProduct

namespace GlobalTheory.SegmentClass

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def rangeEquiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) : ρ.Equiv f.range.toRepresentation :=
  .mk (LinearEquiv.ofInjective f.toLinearMap hf) fun g =>
    LinearMap.ext fun v => Subtype.ext (by change f (ρ g v) = σ g (f v); rw [f.isIntertwining])

def subIncl {ρ : Representation ℂ G V} (S : Subrepresentation ρ) : S.toRepresentation.IntertwiningMap ρ :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem subIncl_injective {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    Function.Injective (subIncl S) := Subtype.val_injective

theorem nonempty_equiv_of_eq {ρ : Representation ℂ G V} {S T : Subrepresentation ρ} (h : S = T) :
    Nonempty (S.toRepresentation.Equiv T.toRepresentation) := by
  subst h; exact ⟨.refl _⟩

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cuspRep (Δ : Segment k) : IrrRep (GL (Fin Δ.d) k) := Δ.cusp.choose

theorem cuspRep_cl (Δ : Segment k) : (cuspRep Δ).cl = Δ.start := Δ.cusp.choose_spec.1

theorem cuspRep_isCuspidal (Δ : Segment k) : IsCuspidal (cuspRep Δ).ρ := Δ.cusp.choose_spec.2

theorem nonempty_prod_equiv (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start)
    (e : (Σ _ : Fin Δ.len, Fin Δ.d) ≃ Fin (Δ.len * Δ.d)) :
    Nonempty ((multiProd e (segTerm σ.ρ Δ.len)).Equiv
      (multiProd (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segTerm (cuspRep Δ).ρ Δ.len))) := by
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 (hσ.trans (cuspRep_cl Δ).symm)
  obtain ⟨ψ⟩ := (Placing.parInd_jac_placing k (Fin Δ.len) (Fin (Δ.len * Δ.d)) (fun _ => Fin Δ.d) e
    (GlobalTheory.Published.consecBlocks Δ.len Δ.d) _).1 (piTensor (segTerm (cuspRep Δ).ρ Δ.len))
  exact ⟨(GlobalTheory.LocGL.multiProdEquiv e (π := segTerm σ.ρ Δ.len) (σ := segTerm (cuspRep Δ).ρ Δ.len)
    fun a => GlobalTheory.LocGL.twistEquiv φ _).trans ψ⟩

theorem nonempty_piTensor_equiv (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start) :
    Nonempty ((piTensor (segTerm (cuspRep Δ).ρ Δ.len)).Equiv (piTensor (segTerm σ.ρ Δ.len))) := by
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 ((cuspRep_cl Δ).trans hσ.symm)
  exact ⟨GlobalTheory.LocGL.piTensorEquiv (ρ := segTerm (cuspRep Δ).ρ Δ.len) (σ := segTerm σ.ρ Δ.len)
    fun a => GlobalTheory.LocGL.twistEquiv φ _⟩

section Published

variable (h : GlobalTheory.Published.SegmentRepresentation)
include h

def segSub (Δ : Segment k) :
    Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segTerm (cuspRep Δ).ρ Δ.len)) :=
  (h k Δ.d Δ.len Δ.d_pos Δ.len_pos (cuspRep Δ) (cuspRep_isCuspidal Δ)).choose

theorem segSub_spec (Δ : Segment k) :
    (segSub h Δ).toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segTerm (cuspRep Δ).ρ Δ.len)),
        S'.toRepresentation.IsIrreducible → S' = segSub h Δ) ∧
      Nonempty ((jac (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segSub h Δ).toRepresentation).Equiv
        (piTensor (segTerm (cuspRep Δ).ρ Δ.len))) :=
  (h k Δ.d Δ.len Δ.d_pos Δ.len_pos (cuspRep Δ) (cuspRep_isCuspidal Δ)).choose_spec

def segIrr (Δ : Segment k) : IrrRep (GL (Fin (Δ.len * Δ.d)) k) where
  V := (segSub h Δ).toSubmodule
  ρ := (segSub h Δ).toRepresentation
  smooth := IsSubquotient.isSmooth ⟨segSub h Δ, .id _, Function.surjective_id⟩ (isSmooth_parInd _ _)
  irr := (segSub_spec h Δ).1

theorem embeds_iff (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start)
    (e : (Σ _ : Fin Δ.len, Fin Δ.d) ≃ Fin (Δ.len * Δ.d)) (π : IrrRep (GL (Fin (Δ.len * Δ.d)) k)) :
    (∃ φ : π.ρ.IntertwiningMap (multiProd e (segTerm σ.ρ Δ.len)), Function.Injective φ) ↔
      Nonempty (π.ρ.Equiv (segIrr h Δ).ρ) := by
  obtain ⟨Φ⟩ := nonempty_prod_equiv Δ σ hσ e
  constructor
  · rintro ⟨φ, hφ⟩
    let f := Φ.toIntertwiningMap.comp φ
    have hf : Function.Injective f := Φ.toLinearEquiv.injective.comp hφ
    have hR : f.range.toRepresentation.IsIrreducible :=
      GlobalTheory.Parabolic.isIrreducible_of_equiv (rangeEquiv f hf) π.irr
    obtain ⟨ψ⟩ := nonempty_equiv_of_eq ((segSub_spec h Δ).2.1 _ hR)
    exact ⟨(rangeEquiv f hf).trans ψ⟩
  · rintro ⟨ψ⟩
    exact ⟨Φ.symm.toIntertwiningMap.comp ((subIncl (segSub h Δ)).comp ψ.toIntertwiningMap),
      Φ.symm.toLinearEquiv.injective.comp ((subIncl_injective _).comp ψ.toLinearEquiv.injective)⟩

theorem jac_iff (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start)
    (e : (Σ _ : Fin Δ.len, Fin Δ.d) ≃ Fin (Δ.len * Δ.d)) (π : IrrRep (GL (Fin (Δ.len * Δ.d)) k)) :
    Nonempty ((jac e π.ρ).Equiv (piTensor (segTerm σ.ρ Δ.len))) ↔ Nonempty (π.ρ.Equiv (segIrr h Δ).ρ) := by
  constructor
  · rintro ⟨ψ⟩
    obtain ⟨f, hf⟩ := (Model.evalOne_bijective e π.smooth (piTensor (segTerm σ.ρ Δ.len))).2
      ψ.toIntertwiningMap
    refine (embeds_iff h Δ σ hσ e π).1 ⟨f, ?_⟩
    haveI := π.irr
    refine (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right fun h0 => ?_
    haveI : Nontrivial (⨂[ℂ] _ : Fin Δ.len, σ.V) :=
      GlobalTheory.ProdSupport.nontrivial_piTensor _ fun _ => Model.nontrivial_of_isIrreducible σ.irr
    obtain ⟨y, hy⟩ := exists_ne (0 : ⨂[ℂ] _ : Fin Δ.len, σ.V)
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (ψ.symm y)
    have h1 : ψ (Submodule.Quotient.mk v) = (f v).1.1 1 :=
      (congrArg (fun F => F (Submodule.Quotient.mk v)) hf).symm
    rw [h0, hv] at h1
    exact hy ((ψ.apply_symm_apply y).symm.trans h1)
  · rintro ⟨ψ⟩
    obtain ⟨A⟩ := (Placing.parInd_jac_placing k (Fin Δ.len) (Fin (Δ.len * Δ.d)) (fun _ => Fin Δ.d) e
      (GlobalTheory.Published.consecBlocks Δ.len Δ.d) _).2 (segSub h Δ).toRepresentation
    obtain ⟨B⟩ := (segSub_spec h Δ).2.2
    obtain ⟨C⟩ := nonempty_piTensor_equiv Δ σ hσ
    exact ⟨(Exponents.jacEquiv e ψ).trans (A.trans (B.trans C))⟩

theorem exists_isSegmentClass : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∃ Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k), IsSegmentClass k Z := by
  intro k _ _ _ _
  refine ⟨fun Δ => (segIrr h Δ).cl, fun Δ σ hσ e π => ⟨?_, ?_⟩⟩
  · rw [IrrRep.cl_eq_iff]; exact (embeds_iff h Δ σ hσ e π).symm
  · rw [IrrRep.cl_eq_iff]; exact (jac_iff h Δ σ hσ e π).symm

end Published

end GlobalTheory.SegmentClass

theorem GlobalTheory.segmentClass_exists : GlobalTheory.Published.SegmentRepresentation → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ∃ Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k), IsSegmentClass k Z :=
  fun h => GlobalTheory.SegmentClass.exists_isSegmentClass h

end
