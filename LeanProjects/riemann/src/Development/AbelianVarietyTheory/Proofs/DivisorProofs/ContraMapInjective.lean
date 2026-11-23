import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothDualNeZeroAtVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CosocleOfContra

open ProjLine

section General

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ G V}

theorem isIrreducible_quot {S : Subrepresentation π} (hS : IsCoatom S) : (quot S).IsIrreducible := by
  have h1 : S.toSubmodule ≠ ⊤ := fun e => hS.1 (Subrepresentation.toSubmodule_injective e)
  have := Submodule.Quotient.nontrivial_iff.2 h1
  have : Nontrivial (Subrepresentation (quot S)) := ⟨⊥, ⊤, fun e =>
    bot_ne_top (α := Submodule ℂ (V ⧸ S.toSubmodule)) (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun T => ?_⟩
  let T' : Subrepresentation π := ⟨T.toSubmodule.comap S.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
  have hle : S ≤ T' := fun v hv => by
    show S.toSubmodule.mkQ v ∈ T.toSubmodule
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hv]
    exact T.toSubmodule.zero_mem
  rcases hS.le_iff.1 hle with e | e
  · right
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    have : v ∈ T' := e ▸ trivial
    exact this
  · left
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    have : v ∈ T' := hy
    rw [e] at this
    exact (Submodule.Quotient.mk_eq_zero _).2 this

theorem ker_quotMk (S : Subrepresentation π) : (quotMk S).ker = S :=
  SetLike.ext fun _ => Submodule.Quotient.mk_eq_zero _

theorem contraMap_injective {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {σ : Representation ℂ G X} {τ : Representation ℂ G Y} (q : σ.IntertwiningMap τ) (hq : Function.Surjective q) :
    Function.Injective (GlobalTheory.ContraRefl.contraMap q) := by
  intro a b h
  refine Subtype.ext (LinearMap.ext fun y => ?_)
  obtain ⟨x, rfl⟩ := hq y
  have := congrArg (fun l : smoothPart σ.dual => (l : Module.Dual ℂ X) x) h
  simpa [GlobalTheory.ContraRefl.contraMap_apply] using this

end General

section GeneralLinearIntegers

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}

theorem isSmooth_quot (hπ : IsSmooth π) (S : Subrepresentation π) : IsSmooth (quot S) :=
  (IsSubquotient.of_surjective (quotMk S) S.toSubmodule.mkQ_surjective).isSmooth hπ

theorem le_of_range_eq (hπ : IsSmooth π) {S S' : Subrepresentation π}
    (h : (GlobalTheory.ContraRefl.contraMap (quotMk S)).range = (GlobalTheory.ContraRefl.contraMap (quotMk S')).range) : S ≤ S' := by
  intro v hv
  by_contra hv'
  have hy : S'.toSubmodule.mkQ v ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨l, hl, hlv⟩ := GlobalTheory.SmoothForm.exists_smooth_form_ne_zero _ _ (quot S') (GlobalTheory.SqIntUnit.compactOpen_basis k N)
    (isSmooth_quot hπ S') _ hy
  have hm : GlobalTheory.ContraRefl.contraMap (quotMk S') ⟨l, hl⟩ ∈ (GlobalTheory.ContraRefl.contraMap (quotMk S)).range :=
    h ▸ ⟨⟨l, hl⟩, rfl⟩
  obtain ⟨m, hm⟩ := hm
  have h1 : (m : Module.Dual ℂ (V ⧸ S.toSubmodule)) (quotMk S v) = l (quotMk S' v) :=
    congrArg (fun u : smoothPart π.dual => (u : Module.Dual ℂ V) v) hm
  have h2 : (quotMk S) v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
  rw [h2, map_zero] at h1
  exact hlv h1.symm

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (N : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth π → HasFiniteLength π → IsSocle σ (contra π) → ∃ τ : IrrRep (GL (Fin N) k), IsCosocle τ.ρ π := by
  intro k _ _ _ _ hAdm N V W _ _ _ _ π σ hπ hfl hsoc
  obtain ⟨hσ, f, hf, hat⟩ := hsoc
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k N
  have key : ∀ S : Subrepresentation π, IsCoatom S →
      (GlobalTheory.ContraRefl.contraMap (quotMk S)).range = f.range := by
    intro S hS
    have hirr := isIrreducible_quot hS
    have hc := GlobalTheory.ContraRefl.contra_isIrreducible hG (hAdm k N _ (quot S) (isSmooth_quot hπ S) hirr) hirr
    exact hat _ (isAtom_range hc _ (contraMap_injective _ S.toSubmodule.mkQ_surjective))
  have uniq : ∀ S S' : Subrepresentation π, IsCoatom S → IsCoatom S' → S = S' := by
    intro S S' hS hS'
    have hle := le_of_range_eq hπ ((key S hS).trans (key S' hS').symm)
    exact ((hS.le_iff.1 hle).resolve_left hS'.1).symm
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hσ
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    apply hw
    apply hf
    rw [map_zero]
    exact Subtype.ext (LinearMap.ext fun v => by simp [Subsingleton.elim v 0])
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := by
    intro e
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1 : v ∈ (⊥ : Subrepresentation π) := e ▸ trivial
    exact hv h1
  obtain ⟨hN, -⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hfl
  have hc : IsCoatomic (Subrepresentation π) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)).isCoatomic_iff.2 inferInstance
  obtain ⟨S₀, hS₀, -⟩ := (hc.eq_top_or_exists_le_coatom ⊥).resolve_left hbt
  refine ⟨⟨_, quot S₀, isSmooth_quot hπ S₀, isIrreducible_quot hS₀⟩, isIrreducible_quot hS₀, quotMk S₀,
    S₀.toSubmodule.mkQ_surjective, fun S hS => ?_⟩
  rw [ker_quotMk]
  exact uniq S S₀ hS hS₀

end GeneralLinearIntegers

end GlobalTheory.CosocleOfContra
