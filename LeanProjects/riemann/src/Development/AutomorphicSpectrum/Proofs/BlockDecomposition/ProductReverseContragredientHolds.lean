import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.ProdIotaRev
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductRepresentationReorderEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiProdCompInvTranspose
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import BuildAid.D3
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CompanionTheory.ProdIota

theorem typeTame_invTranspose (n : ℕ) (k : Type) [Field k] :
    GlobalTheory.TypeTame.invTranspose (R := k) n = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose n k :=
  MonoidHom.ext fun _ => Units.ext rfl

section Reverse

open GlobalTheory.TypeTame GlobalTheory.InvTransposeProd

theorem multiProd_comp_rev (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h n : ℕ) (d : Fin h → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : (Σ a, Fin (d (Fin.rev a))) ≃ Fin n) (X : Fin h → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) :
    Nonempty (Representation.Equiv ((multiProd e π).comp (invTranspose n))
      (multiProd e' fun a => ((π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))) :
        Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))))) := by
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
  obtain ⟨B⟩ := GlobalTheory.PlacingProd.multiProd_placing_equiv k h n (fun a => d (Fin.rev a)) (revPlace e) e'
    (fun a => X (Fin.rev a)) π'
  exact ⟨A.symm.trans ((parIndEquiv (revPlace e) (revRepEquiv π')).trans B)⟩

end Reverse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_gk (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (y : IrrGL k) :
    Nonempty (Representation.Equiv (y.rep.comp (GlobalTheory.TypeTame.invTranspose y.1)) (contra y.rep)) := by
  rw [typeTame_invTranspose]
  exact GlobalTheory.GelfandKazhdan.equiv_contra k _ _ _ (hA k _ _ _ y.2.rep.smooth y.2.rep.irr) y.2.rep.irr

theorem step_general {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hrev : ∑ a, d (Fin.rev a) = N)
    {X : Fin h → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    {Y : Fin h → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (σ : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (Y a))
    (φ : ∀ a, Nonempty (Representation.Equiv ((π (Fin.rev a)).comp (GlobalTheory.TypeTame.invTranspose (d (Fin.rev a)))) (σ a))) :
    Nonempty (Representation.Equiv ((multiProd (stdBlocks d hd) π).comp (GlobalTheory.TypeTame.invTranspose N))
      (multiProd (stdBlocks (fun a => d (Fin.rev a)) hrev) σ)) := by
  obtain ⟨A⟩ := multiProd_comp_rev k h N d (stdBlocks d hd)
    (stdBlocks (fun a => d (Fin.rev a)) hrev) X π
  exact ⟨A.trans (multiProdEquiv _ fun a => (φ a).some)⟩

theorem step_contra (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N)
    (hrev : ∑ a, (x (Fin.rev a)).1 = N) :
    Nonempty (Representation.Equiv ((prodIrr x hd).comp (GlobalTheory.TypeTame.invTranspose N))
      (multiProd (stdBlocks (fun a => (x (Fin.rev a)).1) hrev) fun a => contra (x (Fin.rev a)).rep)) :=
  step_general (fun a => (x a).1) hd hrev (fun a => (x a).rep)
    (fun a => contra (x (Fin.rev a)).rep) fun a => step_gk hA (x (Fin.rev a))

theorem step_class {N h : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin N) k) V}
    (d : Fin h → ℕ) (hd : ∑ a, d a = N) {Y : Fin h → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a)) (hs : ∀ a, IsSmooth (σ a)) (hi : ∀ a, (σ a).IsIrreducible)
    (A : Nonempty (ρ.Equiv (multiProd (stdBlocks d hd) σ))) :
    Nonempty (ρ.Equiv (prodIrr (fun a => IrrGL.of (σ a) (hs a) (hi a)) hd)) :=
  A.map fun A => A.trans (prodIrrEquiv hd σ hs hi)

theorem contragredient_product_reversed (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N)
    (hrev : ∑ a, (x (Fin.rev a)).1 = N) (hs : ∀ a, IsSmooth (contra (x (Fin.rev a)).rep))
    (hi : ∀ a, (contra (x (Fin.rev a)).rep).IsIrreducible) :
    Nonempty (Representation.Equiv ((prodIrr x hd).comp (GlobalTheory.TypeTame.invTranspose N))
      (prodIrr (fun a => IrrGL.of (contra (x (Fin.rev a)).rep) (hs a) (hi a)) hrev)) :=
  step_class (fun a => (x (Fin.rev a)).1) hrev (fun a => contra (x (Fin.rev a)).rep) hs hi (step_contra hA x hd hrev)

theorem comp_invTranspose_congr {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W}
    (A : Nonempty (Representation.Equiv (ρ.comp (GlobalTheory.TypeTame.invTranspose N)) τ)) :
    Nonempty (Representation.Equiv (ρ.comp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N k)) τ) := by
  rw [← typeTame_invTranspose]
  exact A

theorem exists_prodIrr_of_eq {h N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin N) k) V} (y z : Fin h → IrrGL k) (hzy : z = y) (hy : ∑ a, (y a).1 = N)
    (E : Nonempty (ρ.Equiv (prodIrr y hy))) : ∃ hz : ∑ a, (z a).1 = N, Nonempty (ρ.Equiv (prodIrr z hz)) := by
  subst hzy
  exact ⟨hy, E⟩

theorem prodIotaRev : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.ProdIotaRev k := by
  intro k _ _ _ _ hA h N x hd
  have hrev : ∑ a, (x (Fin.rev a)).1 = N := by
    rw [← hd]
    exact Equiv.sum_comp Fin.revPerm fun a => (x a).1
  have hi : ∀ a, (contra (x (Fin.rev a)).rep).IsIrreducible := fun a =>
    GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA _ (x (Fin.rev a)).2.rep.smooth (x (Fin.rev a)).2.rep.irr
  have hs : ∀ a, IsSmooth (contra (x (Fin.rev a)).rep) := fun a => isSmooth_contra _
  exact exists_prodIrr_of_eq (fun a => IrrGL.of (contra (x (Fin.rev a)).rep) (hs a) (hi a))
    (fun a => Zc.dualCl (x (Fin.rev a))) (funext fun a => GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA _) hrev
    (comp_invTranspose_congr (contragredient_product_reversed hA x hd hrev hs hi))

end GlobalTheory.CompanionTheory.ProdIota
end
