import Mathlib
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.MidExact
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.ZelevinskyCosets.Imports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ContragredientProductIrreducibleImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.ParabolicInductionFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthExistsCoatomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContraMapInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskySegmentClassExistsForEveryPlacing

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
open GlobalTheory.LocGL.ProjLine (quot quotMk)
open GlobalTheory.SegmentClass (rangeEquiv subIncl subIncl_injective)

namespace CompanionTheory.Exh

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

include hT in

theorem Tm_equiv_injective {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ (GL (Fin m) k) V} {τ' : Representation ℂ (GL (Fin m) k) W} (e : τ.Equiv τ') :
    Function.Injective (Tm e.toIntertwiningMap) := by
  refine (hT e.toIntertwiningMap (quotMk (⊤ : Subrepresentation τ'))
    e.toLinearEquiv.injective fun y => ?_).1
  constructor
  · intro _
    obtain ⟨v, hv⟩ := e.toLinearEquiv.surjective y
    exact ⟨v, hv⟩
  · intro _
    exact (Submodule.Quotient.mk_eq_zero _).2 (show y ∈ (⊤ : Subrepresentation τ').toSubmodule from trivial)

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
  obtain ⟨-, hwf⟩ := (GlobalTheory.SmGL.hasFiniteLength_iff_wellFounded P).1 hP
  induction S using WellFoundedLT.induction with
  | _ S ih =>
  obtain ⟨f, hf⟩ := hx
  have hSsub : IsSubquotient S.toRepresentation P := IsSubquotient.of_injective (subIncl S) (subIncl_injective S)
  have hSs : IsSmooth S.toRepresentation := hSsub.isSmooth hs
  have hSf : HasFiniteLength S.toRepresentation :=
    GlobalTheory.ProdLength.hasFiniteLength_of_injective (subIncl S) (subIncl_injective S) hP
  haveI := x.rep.irr
  haveI : Nontrivial x.rep.V := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible x.rep.irr
  by_cases hnt : Nontrivial S.toSubmodule
  swap
  · exfalso
    rw [not_nontrivial_iff_subsingleton] at hnt
    let I := Representation.IntertwiningMap.id S.toRepresentation
    have hI : Function.Exact I I := fun y => ⟨fun _ => ⟨y, rfl⟩, fun _ => Subsingleton.elim _ _⟩
    obtain ⟨hinj, hex⟩ := hT I I (fun a b h => h) hI
    set F := Tm I
    have h0 : ∀ w : (T S.toRepresentation).V, w = 0 := fun w =>
      hinj (hinj (((hex (F w)).2 ⟨w, rfl⟩).trans ((congrArg F (map_zero F)).trans (map_zero F)).symm))
    obtain ⟨v, hv⟩ := exists_ne (0 : x.rep.V)
    exact hv (hf ((h0 (f v)).trans (h0 (f 0)).symm))
  obtain ⟨C, hC⟩ := GlobalTheory.T.finite_length_exists_coatom S.toRepresentation hSf hnt
  let q := Tm (quotMk C)
  by_cases h0 : ∀ v, q (f v) = 0
  ·
    have hexC : Function.Exact (subIncl C) (quotMk C) := fun y => by
      show C.toSubmodule.mkQ y = 0 ↔ _
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, by rintro ⟨z, rfl⟩; exact z.2⟩
    obtain ⟨hιinj, hexT⟩ := hT (subIncl C) (quotMk C) (subIncl_injective C) hexC
    set ι := Tm (subIncl C)
    have hmem : ∀ v, f v ∈ ι.range.toSubmodule := fun v => by
      obtain ⟨u, hu⟩ := (hexT (f v)).1 (h0 v)
      exact ⟨u, hu⟩
    let f1 := (rangeEquiv ι hιinj).symm.toIntertwiningMap.comp (codSub f ι.range hmem)
    have hf1 : Function.Injective f1 :=
      (rangeEquiv ι hιinj).symm.toLinearEquiv.injective.comp (codSub_injective f ι.range hmem hf)
    let j := (subIncl S).comp (subIncl C)
    have hj : Function.Injective j := (subIncl_injective S).comp (subIncl_injective C)
    let e' := rangeEquiv j hj
    have hlt : j.range < S := by
      refine lt_of_le_of_ne (fun v hv => ?_) fun e => hC.1 (eq_top_iff.2 fun y _ => ?_)
      · obtain ⟨c, rfl⟩ := hv
        exact (c : S.toSubmodule).2
      · have hy : (y : V) ∈ j.range := e.ge y.2
        obtain ⟨c, hc⟩ := hy
        have hcy : (c : S.toSubmodule) = y := Subtype.ext hc
        rw [← hcy]
        exact c.2
    exact ih _ hlt ⟨(Tm e'.toIntertwiningMap).comp f1,
      (Tm_equiv_injective T Tm hT e').comp hf1⟩
  ·
    let F := q.comp f
    have hker : F.ker = ⊥ := (eq_bot_or_eq_top F.ker).resolve_right fun e => h0 fun v => by
      have hv : v ∈ F.ker := e ▸ trivial
      exact hv
    have hFinj : Function.Injective F := fun a b hab => by
      have hm : a - b ∈ F.ker := by
        show F (a - b) = 0
        rw [map_sub, hab, sub_self]
      rw [hker] at hm
      exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hm)
    have hsq := GlobalTheory.CosocleOfContra.isSmooth_quot hSs C
    have hirr := GlobalTheory.CosocleOfContra.isIrreducible_quot hC
    let e := IrrGL.equivOf (quot C) hsq hirr
    refine ⟨(IrrGL.of (quot C) hsq hirr).2, ?_, (Tm e.toIntertwiningMap).comp F,
      (Tm_equiv_injective T Tm hT e).comp hFinj⟩
    exact (IsSubquotient.of_surjective e.toIntertwiningMap e.toLinearEquiv.surjective).trans
      ((IsSubquotient.of_surjective (quotMk C) C.toSubmodule.mkQ_surjective).trans hSsub)

include hT in

theorem mid_gen {V : Type} [AddCommGroup V] [Module ℂ V] {P : Representation ℂ (GL (Fin m) k) V}
    (hP : HasFiniteLength P) (hs : IsSmooth P) (x : IrrCl (GL (Fin N) k))
    (f : x.rep.ρ.IntertwiningMap (T P).ρ) (hf : Function.Injective f) :
    ∃ c : IrrCl (GL (Fin m) k), IsSubquotient c.rep.ρ P ∧
      ∃ f : x.rep.ρ.IntertwiningMap (T c.rep.ρ).ρ, Function.Injective f := by
  let I := Representation.IntertwiningMap.id P
  let e := rangeEquiv I (fun a b h => h)
  exact mid_sub T Tm hT hP hs x I.range ⟨(Tm e.toIntertwiningMap).comp f,
    (Tm_equiv_injective T Tm hT e).comp hf⟩

end General

end CompanionTheory.Exh

end
