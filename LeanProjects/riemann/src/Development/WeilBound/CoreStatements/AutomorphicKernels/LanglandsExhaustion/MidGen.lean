import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.MidExact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthExistsCoatomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContraMapInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskySegmentClassExistsForEveryPlacing
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
open GlobalTheory.LocGL.ProjLine (quot quotMk)
open GlobalTheory.SegmentClass (rangeEquiv subIncl subIncl_injective)

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section General

variable {m N : ℕ}
  (T : ∀ {V : Type} [AddCommGroup V] [Module ℂ V], Representation ℂ (GL (Fin m) k) V → GlobalTheory.ProdFlatten.BR k N)
  (Tm : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ (GL (Fin m) k) V}
    {τ' : Representation ℂ (GL (Fin m) k) W}, τ.IntertwiningMap τ' → (T τ).ρ.IntertwiningMap (T τ').ρ)
  (hT : ∀ {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    {τ₁ : Representation ℂ (GL (Fin m) k) V} {τ₂ : Representation ℂ (GL (Fin m) k) W} {τ₃ : Representation ℂ (GL (Fin m) k) U}
    (f : τ₁.IntertwiningMap τ₂) (g : τ₂.IntertwiningMap τ₃), Function.Injective f → Function.Exact f g →
      Function.Injective (Tm f) ∧ Function.Exact (Tm f) (Tm g))

def codSub {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ) (S : Subrepresentation σ)
    (h : ∀ v, f v ∈ S.toSubmodule) : ρ.IntertwiningMap S.toRepresentation :=
  ⟨f.toLinearMap.codRestrict S.toSubmodule h, fun g => LinearMap.ext fun v => Subtype.ext (by
    change f (ρ g v) = σ g (f v)
    rw [f.isIntertwining])⟩

theorem codSub_injective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ) (S : Subrepresentation σ)
    (h : ∀ v, f v ∈ S.toSubmodule) (hf : Function.Injective f) : Function.Injective (codSub f S h) :=
  fun a b hab => hf (congrArg Subtype.val hab)

include hT in

theorem mid_sub {V : Type} [AddCommGroup V] [Module ℂ V] {P : Representation ℂ (GL (Fin m) k) V}
    (hP : HasFiniteLength P) (hs : IsSmooth P) (x : IrrCl (GL (Fin N) k)) (S : Subrepresentation P)
    (hx : ∃ f : x.rep.ρ.IntertwiningMap (T S.toRepresentation).ρ, Function.Injective f) :
    ∃ c : IrrCl (GL (Fin m) k), IsSubquotient c.rep.ρ P ∧
      ∃ f : x.rep.ρ.IntertwiningMap (T c.rep.ρ).ρ, Function.Injective f := by
  have hInj : ∀ {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
      {σ₁ : Representation ℂ (GL (Fin m) k) A} {σ₂ : Representation ℂ (GL (Fin m) k) B}
      (f : σ₁.IntertwiningMap σ₂), Function.Injective f → Function.Injective (Tm f) := by
    intro A B _ _ _ _ σ₁ σ₂ f hf
    refine (hT f (quotMk (Representation.IntertwiningMap.range σ₁ σ₂ f)) hf ?_).1
    intro y
    show (Representation.IntertwiningMap.range σ₁ σ₂ f).toSubmodule.mkQ y = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Representation.IntertwiningMap.mem_range σ₁ σ₂ f y
  have hzero : ∀ {A : Type} [AddCommGroup A] [Module ℂ A] {σ : Representation ℂ (GL (Fin m) k) A},
      Subsingleton A → Subsingleton (T σ).V := by
    intro A _ _ σ hA
    have h0inj : Function.Injective (0 : σ.IntertwiningMap σ) := fun a b _ => Subsingleton.elim a b
    have h0ex : Function.Exact (0 : σ.IntertwiningMap σ) (0 : σ.IntertwiningMap σ) := by
      intro y
      exact ⟨fun _ => ⟨y, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
    obtain ⟨hI, hE⟩ := hT (0 : σ.IntertwiningMap σ) (0 : σ.IntertwiningMap σ) h0inj h0ex
    have hz : ∀ z, Tm (0 : σ.IntertwiningMap σ) z = 0 := by
      intro z
      have h1 : Tm (0 : σ.IntertwiningMap σ) (Tm (0 : σ.IntertwiningMap σ) z) = 0 := (hE _).2 ⟨z, rfl⟩
      apply hI
      rw [h1, map_zero]
    refine ⟨fun a b => hI ?_⟩
    rw [hz a, hz b]
  have hwf := (hasFiniteLength_iff_wellFounded P).1 hP
  obtain ⟨S₀, hS₀, hmin⟩ := (@wellFounded_lt _ _ hwf.2).has_min
    {W : Subrepresentation P | ∃ f : x.rep.ρ.IntertwiningMap (T W.toRepresentation).ρ, Function.Injective f}
    ⟨S, hx⟩
  have hmin' : ∀ W : Subrepresentation P,
      (∃ f : x.rep.ρ.IntertwiningMap (T W.toRepresentation).ρ, Function.Injective f) → ¬ W < S₀ :=
    fun W hW => hmin W hW
  have hS₀' : ∃ f : x.rep.ρ.IntertwiningMap (T S₀.toRepresentation).ρ, Function.Injective f := hS₀
  obtain ⟨f₀, hf₀⟩ := hS₀'
  have hne : S₀ ≠ ⊥ := by
    intro h0
    subst h0
    haveI : Subsingleton (↥(⊥ : Subrepresentation P).toSubmodule) := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have ha : (a : V) = 0 := (Submodule.mem_bot ℂ).1 a.2
      have hb : (b : V) = 0 := (Submodule.mem_bot ℂ).1 b.2
      rw [ha, hb]
    haveI := hzero (σ := (⊥ : Subrepresentation P).toRepresentation) inferInstance
    haveI : Subsingleton x.rep.V := ⟨fun a b => hf₀ (Subsingleton.elim _ _)⟩
    haveI := x.rep.irr
    refine not_subsingleton (Subrepresentation x.rep.ρ) ⟨fun a b => Subrepresentation.ext (Submodule.ext fun v => ?_)⟩
    rw [Subsingleton.elim v 0]
    exact iff_of_true a.toSubmodule.zero_mem b.toSubmodule.zero_mem
  have hbot : ⊥ < S₀ := bot_lt_iff_ne_bot.2 hne
  obtain ⟨U, hU, hmax⟩ := (@wellFounded_gt _ _ hwf.1).has_min {W : Subrepresentation P | W < S₀} ⟨⊥, hbot⟩
  have hU' : U < S₀ := hU
  have hcov : U ⋖ S₀ := ⟨hU', fun W hUW hWS => hmax W hWS hUW⟩
  have hle : U.toSubmodule ≤ S₀.toSubmodule := hU'.le
  let ι : U.toRepresentation.IntertwiningMap S₀.toRepresentation :=
    ⟨Submodule.inclusion hle, fun g => LinearMap.ext fun v => Subtype.ext rfl⟩
  let p : S₀.toRepresentation.IntertwiningMap (subQuot S₀ U) :=
    ⟨(Submodule.comap S₀.toSubmodule.subtype U.toSubmodule).mkQ, fun g => LinearMap.ext fun v => rfl⟩
  have hιinj : Function.Injective ι := by
    intro a b h
    have h2 := congrArg (fun z : S₀.toSubmodule => (z : V)) h
    exact Subtype.ext h2
  have hex : Function.Exact ι p := by
    intro y
    show Submodule.Quotient.mk y = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    constructor
    · intro h
      exact ⟨⟨y, h⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact u.2
  obtain ⟨hTι, hTex⟩ := hT ι p hιinj hex
  let g := (Tm p).comp f₀
  rcases x.rep.irr.eq_bot_or_eq_top (Representation.IntertwiningMap.ker _ _ g) with hk | hk
  · have hginj : Function.Injective g := by
      intro a b hab
      have hmem : a - b ∈ Representation.IntertwiningMap.ker _ _ g := by
        rw [Representation.IntertwiningMap.mem_ker, map_sub, hab, sub_self]
      rw [hk] at hmem
      exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hmem)
    have hirr : (subQuot S₀ U).IsIrreducible := isIrreducible_subQuot hcov
    have hsm : IsSmooth (subQuot S₀ U) := (GlobalTheory.ParIndExact.isSubquotient_subQuot S₀ U).isSmooth hs
    let σ : IrrRep (GL (Fin m) k) := ⟨_, subQuot S₀ U, hsm, hirr⟩
    obtain ⟨e⟩ := IrrRep.nonempty_equiv_rep σ
    refine ⟨σ.cl, ?_, (Tm e.symm.toIntertwiningMap).comp g, ?_⟩
    · exact (IsSubquotient.of_injective e.toIntertwiningMap e.left_inv.injective).trans
        (GlobalTheory.ParIndExact.isSubquotient_subQuot S₀ U)
    · exact fun a b hab => hginj (hInj e.symm.toIntertwiningMap e.symm.left_inv.injective hab)
  · exfalso
    have hall : ∀ v, f₀ v ∈ (Representation.IntertwiningMap.range _ _ (Tm ι)).toSubmodule := by
      intro v
      have hv : v ∈ Representation.IntertwiningMap.ker _ _ g := by
        rw [hk]
        exact Submodule.mem_top
      rw [Representation.IntertwiningMap.mem_ker, Representation.IntertwiningMap.comp_apply] at hv
      exact (Representation.IntertwiningMap.mem_range _ _ _ _).2 ((hTex (f₀ v)).1 hv)
    have h1inj : Function.Injective (codSub f₀ _ hall) := codSub_injective f₀ _ hall hf₀
    let e := rangeEquiv (Tm ι) hTι
    exact hmin' U ⟨e.symm.toIntertwiningMap.comp (codSub f₀ _ hall),
      fun a b hab => h1inj (e.symm.left_inv.injective hab)⟩ hU'

include hT in

theorem mid_gen {V : Type} [AddCommGroup V] [Module ℂ V] {P : Representation ℂ (GL (Fin m) k) V}
    (hP : HasFiniteLength P) (hs : IsSmooth P) (x : IrrCl (GL (Fin N) k))
    (f : x.rep.ρ.IntertwiningMap (T P).ρ) (hf : Function.Injective f) :
    ∃ c : IrrCl (GL (Fin m) k), IsSubquotient c.rep.ρ P ∧
      ∃ f : x.rep.ρ.IntertwiningMap (T c.rep.ρ).ρ, Function.Injective f := by
  have hInj : ∀ {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
      {σ₁ : Representation ℂ (GL (Fin m) k) A} {σ₂ : Representation ℂ (GL (Fin m) k) B}
      (f : σ₁.IntertwiningMap σ₂), Function.Injective f → Function.Injective (Tm f) := by
    intro A B _ _ _ _ σ₁ σ₂ f hf
    refine (hT f (quotMk (Representation.IntertwiningMap.range σ₁ σ₂ f)) hf ?_).1
    intro y
    show (Representation.IntertwiningMap.range σ₁ σ₂ f).toSubmodule.mkQ y = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Representation.IntertwiningMap.mem_range σ₁ σ₂ f y
  let j : P.IntertwiningMap (⊤ : Subrepresentation P).toRepresentation :=
    ⟨LinearMap.codRestrict (⊤ : Subrepresentation P).toSubmodule LinearMap.id (fun v => Submodule.mem_top),
      fun g => LinearMap.ext fun v => Subtype.ext rfl⟩
  have hj : Function.Injective j := fun a b h => congrArg Subtype.val h
  exact mid_sub T Tm hT hP hs x ⊤ ⟨(Tm j).comp f, fun a b h => hf (hInj j hj h)⟩

end General

end PositivityTheory.Exh

end
