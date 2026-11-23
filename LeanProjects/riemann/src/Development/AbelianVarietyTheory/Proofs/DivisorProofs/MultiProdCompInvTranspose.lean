import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedParabolicInductionReindexEquiv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductRepresentationReorderEquivStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.InvTransposeProd

open Matrix GlobalTheory.TypeTame
open scoped TensorProduct

variable {k : Type} [Field k] {h n : ℕ} {d : Fin h → ℕ}

def revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) : (Σ a : Fin h, Fin (d (Fin.rev a))) ≃ Fin n :=
  (Equiv.sigmaCongrLeft (β := fun b => Fin (d b)) Fin.revPerm).trans e

theorem revPlace_apply (e : (Σ a, Fin (d a)) ≃ Fin n) (a : Fin h) (i : Fin (d (Fin.rev a))) :
    revPlace e ⟨a, i⟩ = e ⟨Fin.rev a, i⟩ := rfl

theorem blk_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) (x : Fin n) :
    blk e x = Fin.rev (blk (revPlace e) x) := by
  obtain ⟨⟨a, i⟩, rfl⟩ := (revPlace e).surjective x
  rw [blk_apply, revPlace_apply, blk_apply]

theorem mem_parab_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) {q : GL (Fin n) k} (hq : q ∈ parab k e) :
    invTranspose n q ∈ parab k (revPlace e) := by
  refine mem_parab.2 fun i j hij => ?_
  rw [invTranspose_val, Matrix.transpose_apply]
  refine mem_parab.1 (inv_mem hq) j i ?_
  rw [blk_revPlace e i, blk_revPlace e j]
  exact Fin.rev_lt_rev.2 hij

theorem mem_parab_of_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) {p : GL (Fin n) k}
    (hp : p ∈ parab k (revPlace e)) : invTranspose n p ∈ parab k e := by
  refine mem_parab.2 fun i j hij => ?_
  rw [invTranspose_val, Matrix.transpose_apply]
  refine mem_parab.1 (inv_mem hp) j i ?_
  rw [blk_revPlace e i, blk_revPlace e j] at hij
  exact Fin.rev_lt_rev.1 hij

theorem leviProj_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) (q : parab k e)
    (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)) (b : Fin h) :
    leviProj k (revPlace e) ⟨invTranspose n q, hq⟩ b =
      invTranspose (d (Fin.rev b)) (leviProj k e q (Fin.rev b)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [invTranspose_val, Matrix.transpose_apply, ← Pi.inv_apply, ← map_inv, leviProj_apply, leviProj_apply]
  rfl

theorem det_invTranspose (m : ℕ) (g : GL (Fin m) k) :
    GeneralLinearGroup.det (invTranspose m g) = (GeneralLinearGroup.det g)⁻¹ := by
  ext
  rw [GeneralLinearGroup.val_det_apply, invTranspose_val, Matrix.det_transpose, ← GeneralLinearGroup.val_det_apply,
    map_inv]

omit [Field k] in
theorem modExp_rev (b : Fin h) :
    modExp (fun a => Fin (d (Fin.rev a))) b = -modExp (fun a => Fin (d a)) (Fin.rev b) := by
  unfold modExp
  simp only [Fintype.card_fin, Finset.sum_filter]
  have h1 : (∑ c : Fin h, if b < c then (d (Fin.rev c) : ℤ) else 0) =
      ∑ c : Fin h, if c < Fin.rev b then (d c : ℤ) else 0 :=
    Fintype.sum_equiv Fin.revPerm _ _ fun c => by simp [Fin.rev_lt_rev]
  have h2 : (∑ c : Fin h, if c < b then (d (Fin.rev c) : ℤ) else 0) =
      ∑ c : Fin h, if Fin.rev b < c then (d c : ℤ) else 0 :=
    Fintype.sum_equiv Fin.revPerm _ _ fun c => by simp [Fin.rev_lt_rev]
  rw [h1, h2]
  ring

section Local

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deltaHalf_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) (q : parab k e)
    (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)) :
    deltaHalf k (fun a => Fin (d (Fin.rev a))) (leviProj k (revPlace e) ⟨invTranspose n q, hq⟩) =
      deltaHalf k (fun a => Fin (d a)) (leviProj k e q) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Fintype.prod_equiv Fin.revPerm _ _ fun b => ?_
  rw [leviProj_revPlace e q hq b, det_invTranspose, modExp_rev]
  simp only [Int.cast_neg, neg_div, absPow_neg, MonoidHom.inv_apply, map_inv, inv_inv, Fin.revPerm_apply]
  rfl

variable (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

def revTensor : (⨂[ℂ] a, X a) ≃ₗ[ℂ] ⨂[ℂ] a, X (Fin.rev a) :=
  PiTensorProduct.reindex ℂ X Fin.revPerm

theorem revTensor_tprod (z : ∀ a, X a) :
    revTensor X (PiTensorProduct.tprod ℂ z) = PiTensorProduct.tprod ℂ fun a => z (Fin.rev a) :=
  PiTensorProduct.reindex_tprod _ _

variable {X}

def revRep (π' : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))) :
    Representation ℂ (Levi k fun a => Fin (d (Fin.rev a))) (⨂[ℂ] a, X a) where
  toFun g := (revTensor X).symm.toLinearMap ∘ₗ piTensor π' g ∘ₗ (revTensor X).toLinearMap
  map_one' := by ext; simp
  map_mul' g g' := by ext; simp

def revRepEquiv (π' : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))) :
    (revRep π').Equiv (piTensor π') :=
  Representation.Equiv.mk (revTensor X) fun g => LinearMap.ext fun v => by
    simp [revRep]

theorem revRep_leviProj (e : (Σ a, Fin (d a)) ≃ Fin n)
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (q : parab k e)
    (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)) :
    revRep (fun a => (π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))))
        (leviProj k (revPlace e) ⟨invTranspose n q, hq⟩) = piTensor π (leviProj k e q) := by
  have key : (piTensor fun a => (π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))))
        (leviProj k (revPlace e) ⟨invTranspose n q, hq⟩) ∘ₗ (revTensor X).toLinearMap =
      (revTensor X).toLinearMap ∘ₗ piTensor π (leviProj k e q) := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun z => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      revTensor_tprod, piTensor_tprod]
    congr 1
  refine LinearMap.ext fun v => ?_
  show (revTensor X).symm _ = _
  rw [(revTensor X).symm_apply_eq]
  exact LinearMap.congr_fun key v

end Local

theorem multiProd_comp_invTranspose : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h n : ℕ) (d : Fin h → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : (Σ a, Fin (d (Fin.rev a))) ≃ Fin n) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (π a)) → Nonempty (Representation.Equiv ((multiProd e π).comp (GlobalTheory.TypeTame.invTranspose n)) (multiProd e' fun a => ((π (Fin.rev a)).comp (GlobalTheory.TypeTame.invTranspose (d (Fin.rev a))) : Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))))) := by
  intro k _ _ _ _ h n d e e' X _ _ π _
  set π' : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a)) :=
    fun a => (π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))) with hπ'
  have key : ∀ (q : parab k e) (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)),
      ((twist (revRep π') (deltaHalf k _)).comp (leviProj k (revPlace e))) ⟨invTranspose n q, hq⟩ =
        ((twist (piTensor π) (deltaHalf k _)).comp (leviProj k e)) q := by
    intro q hq
    refine LinearMap.ext fun v => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, twist_apply, twist_apply, deltaHalf_revPlace e q hq,
      hπ', revRep_leviProj e π q hq]
  obtain ⟨A⟩ : Nonempty ((parInd (revPlace e) (revRep π')).Equiv
      ((multiProd e π).comp (invTranspose n))) := by
    refine Relabel.smInd_equiv_comp (P := parab k (revPlace e)) (Q := parab k e)
      (σ := (twist (revRep π') (deltaHalf k _)).comp (leviProj k (revPlace e)))
      (τ := (twist (piTensor π) (deltaHalf k _)).comp (leviProj k e))
      (invTranspose n) (invTranspose n) (continuous_invTranspose n) (continuous_invTranspose n)
      (invTranspose_invTranspose n) (invTranspose_invTranspose n)
      (fun q => ⟨⟨_, mem_parab_revPlace e q.2⟩, rfl, key q _⟩) (fun p => ?_)
    have hp : invTranspose n (invTranspose n (p : GL (Fin n) k)) ∈ parab k (revPlace e) := by
      rw [invTranspose_invTranspose]
      exact p.2
    refine ⟨⟨_, mem_parab_of_revPlace e p.2⟩, rfl, ?_⟩
    refine (key ⟨_, mem_parab_of_revPlace e p.2⟩ hp).symm.trans ?_
    exact congrArg _ (Subtype.ext (invTranspose_invTranspose n (p : GL (Fin n) k)))
  obtain ⟨B⟩ := GlobalTheory.T.product_representation_reorder_equiv k h n (fun a => d (Fin.rev a)) (revPlace e) e' (fun a => X (Fin.rev a)) π'
  exact ⟨A.symm.trans ((parIndEquiv (revPlace e) (revRepEquiv π')).trans B)⟩

end GlobalTheory.InvTransposeProd
