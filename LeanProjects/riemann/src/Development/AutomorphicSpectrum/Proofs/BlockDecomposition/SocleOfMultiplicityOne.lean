import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetWordMultiplicityAdditiveJordanHolder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodChevalley
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SocleJm

section General

variable {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem jhMult_le_of_injective {σ : Representation ℂ G U} {ρ₁ : Representation ℂ G V}
    {ρ : Representation ℂ G W} (hσ : σ.IsIrreducible) (ι : ρ₁.IntertwiningMap ρ)
    (hι : Function.Injective ι) : jhMult σ ρ₁ ≤ jhMult σ ρ := by
  let R : Subrepresentation ρ := ι.range
  let p : ρ.IntertwiningMap (subQuot ⊤ R) :=
    ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id
      (fun _ => trivial), fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v ∈ R.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  rw [jhMult_exact ι p hσ hι (fun x => ?_) (fun u => (hp _).2 ⟨u, rfl⟩) (fun v hv => (hp v).1 hv)]
  · exact le_self_add
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨v.1, rfl⟩

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V W U X : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]

theorem jhMult_jac_exact (e : (Σ a, m a) ≃ n) {σ : Representation ℂ (Levi k m) X}
    (hσ : σ.IsIrreducible) {π : Representation ℂ (GL n k) V} {π₁ : Representation ℂ (GL n k) W}
    {π₂ : Representation ℂ (GL n k) U} (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂)
    (hπ : IsSmooth π) (hι : Function.Injective ι) (hp : Function.Surjective p)
    (he : Function.Exact ι p) :
    jhMult σ (jac e π) = jhMult σ (jac e π₁) + jhMult σ (jac e π₂) := by
  refine jhMult_exact (jacMap e ι) (jacMap e p) hσ
    (GlobalTheory.JacInj.jacMap_injective k _ _ _ e W V π₁ π ι hπ hι) (fun x => ?_) (fun x => ?_)
    (fun x hx => ?_)
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨v, rfl⟩ := hp u
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (p (ι u)) = 0
    rw [he.apply_apply_eq_zero]
    rfl
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : p v ∈ twKer π₂ (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨v', hv', h2⟩ := GlobalTheory.SmGL.Exponents.Additive.exists_mem_twKer p hp _ h1
    obtain ⟨u, hu⟩ := (he (v - v')).1 (by rw [map_sub, h2, sub_self])
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v
    rw [hu]
    exact (Submodule.Quotient.eq _).2 (by simpa using hv')

theorem one_le_jhMult_jac (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) {τ : Representation ℂ (GL n k) V} (f : τ.IntertwiningMap (parInd e ρ))
    (hf : ∃ v, f v ≠ 0) : 1 ≤ jhMult ρ (jac e τ) := by
  obtain ⟨v, hv⟩ := hf
  obtain ⟨x, hx⟩ : ∃ x, (f v).1.1 x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (Subtype.ext (Subtype.ext (funext h)))
  let φ := GlobalTheory.SmGL.Model.evalOne e f
  have h1 : φ (Submodule.Quotient.mk (τ x v)) ≠ 0 := by
    have : φ (Submodule.Quotient.mk (τ x v)) = (f v).1.1 x := by
      show (f (τ x v)).1.1 1 = _
      rw [f.isIntertwining, parInd_apply, one_mul]
    rwa [this]
  have h2 : Function.Surjective φ := by
    intro w
    rcases eq_bot_or_eq_top φ.range with e' | e'
    · have h3 : φ (Submodule.Quotient.mk (τ x v)) ∈ φ.range :=
        (Representation.IntertwiningMap.mem_range _ _ _ _).2 ⟨_, rfl⟩
      rw [e'] at h3
      exact absurd h3 h1
    · have h3 : w ∈ φ.range := e' ▸ trivial
      exact (Representation.IntertwiningMap.mem_range _ _ _ _).1 h3
  exact ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 (.of_surjective φ h2))

theorem isIrreducible_piTensor (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL k) :
    (piTensor fun a => (x a).rep).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) fun a φ hφ =>
    GlobalTheory.SchurAdm.schur_admissible (GL (Fin (x a).1) k) (KO k (Fin (x a).1)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO _ (x a).rep (x a).2.rep.irr
      (hA k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

theorem exists_isSocle_of_forall_isAtom (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) {π : Representation ℂ (GL n k) V} (hs : IsSmooth π) [Nontrivial V]
    (hfl : HasFiniteLength π)
    (hone : ∀ T : Subrepresentation π, IsAtom T → 1 ≤ jhMult ρ (jac e T.toRepresentation))
    (hjm : jhMult ρ (jac e π) ≤ 1) : ∃ τ : IrrRep (GL n k), IsSocle τ.ρ π := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded _).1 hfl
  haveI : IsAtomic (Subrepresentation π) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  have hnt : (⊤ : Subrepresentation π) ≠ ⊥ := fun hb => by
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have h1 : u ∈ (⊥ : Subrepresentation π) := hb ▸ trivial
    exact hu h1
  obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation π)).resolve_left hnt
  let ι : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have huniq : ∀ T : Subrepresentation π, IsAtom T → T = S := by
    intro T hT
    by_contra hne
    have hdis : T ⊓ S = ⊥ := (hT.disjoint_of_ne hS hne).eq_bot
    let p : π.IntertwiningMap (subQuot ⊤ S) :=
      ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation π).toSubmodule
        LinearMap.id (fun _ => trivial), fun _ => rfl⟩
    have hp0 : ∀ v, p v = 0 ↔ v ∈ S.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have hps : Function.Surjective p := fun y => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨v.1, rfl⟩
    have hQ : IsSmooth (subQuot ⊤ S) := (IsSubquotient.of_surjective p hps).isSmooth hs
    have hex : Function.Exact ι p := fun v =>
      ⟨fun h0 => ⟨⟨v, (hp0 v).1 h0⟩, rfl⟩, fun ⟨u, hu⟩ => (hp0 v).2 (hu ▸ u.2)⟩
    have hadd := jhMult_jac_exact e hρ ι p hs Subtype.val_injective hps hex
    let ιT : T.toRepresentation.IntertwiningMap π := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
    have hinj : Function.Injective (p.comp ιT) := by
      refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
      have h1 : (u : V) ∈ S.toSubmodule := (hp0 _).1 hu
      have h2 : (u : V) ∈ (T ⊓ S) := ⟨u.2, h1⟩
      rw [hdis] at h2
      exact Subtype.ext h2
    have h1 : 1 ≤ jhMult ρ (jac e (subQuot ⊤ S)) :=
      (hone T hT).trans (jhMult_le_of_injective hρ (jacMap e (p.comp ιT))
        (GlobalTheory.JacInj.jacMap_injective k _ _ _ e _ _ _ _ _ hQ hinj))
    have h2 : (2 : ℕ∞) ≤ jhMult ρ (jac e π) := by
      rw [hadd]
      exact (by norm_num : (2 : ℕ∞) = 1 + 1).le.trans (add_le_add (hone S hS) h1)
    exact absurd (h2.trans hjm) (by norm_num)
  have hirr := GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS
  refine ⟨⟨S.toSubmodule, S.toRepresentation,
    (IsSubquotient.of_injective ι Subtype.val_injective).isSmooth hs, hirr⟩, hirr, ι,
    Subtype.val_injective, fun T hT => ?_⟩
  rw [huniq T hT]
  refine SetLike.ext fun v => ⟨fun hv => (Representation.IntertwiningMap.mem_range _ _ _ _).2
    ⟨⟨v, hv⟩, rfl⟩, fun hv => ?_⟩
  obtain ⟨u, rfl⟩ := (Representation.IntertwiningMap.mem_range _ _ _ _).1 hv
  exact u.2

theorem nontrivial_indSp (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) (hsρ : IsSmooth ρ) : Nontrivial (IndSp e ρ) := by
  haveI : Nontrivial X := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hρ
  obtain ⟨u, hu⟩ := exists_ne (0 : X)
  obtain ⟨f, hf, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one e ρ hsρ u
  exact ⟨f, 0, fun h => hu (by rw [← hf, h]; rfl)⟩

theorem one_le_jhMult_jac_atom (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) (T : Subrepresentation (parInd e ρ)) (hT : IsAtom T) :
    1 ≤ jhMult ρ (jac e T.toRepresentation) := by
  let ιT : T.toRepresentation.IntertwiningMap (parInd e ρ) := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
  refine one_le_jhMult_jac e hρ ιT ?_
  by_contra hc
  push_neg at hc
  exact hT.1 (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv =>
    (Submodule.mem_bot ℂ).2 (hc ⟨v, hv⟩)))

theorem exists_isSocle_of_jm_le_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), jm x hd (prodIrr x hd) ≤ 1 →
    ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr x hd) := by
  intro k _ _ _ _ hA h N x hd hjm
  have hρ := isIrreducible_piTensor hA x
  have hsρ : IsSmooth (piTensor fun a => (x a).rep) := isSmooth_piTensor fun a => (x a).2.rep.smooth
  haveI := nontrivial_indSp (stdBlocks (fun a => (x a).1) hd) hρ hsρ
  exact exists_isSocle_of_forall_isAtom (stdBlocks (fun a => (x a).1) hd) hρ
    (isSmooth_parInd _ _)
    (GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ))
    (one_le_jhMult_jac_atom _ hρ) hjm

end GlobalTheory.CompanionTheory.SocleJm

end
