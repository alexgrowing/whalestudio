import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitImgMono
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfIrreducibleImageStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientOfExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSubquotientEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.BZNuPair.WhitSub

theorem exists_injective_of_subQuot_bot {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} (hσ : σ.IsIrreducible) {ρ : Representation ℂ G V}
    (A B : Subrepresentation ρ) (hB : B = ⊥) (f : σ.IntertwiningMap (subQuot A B))
    (hf : f.toLinearMap ≠ 0) : ∃ g : σ.IntertwiningMap ρ, Function.Injective g := by
  subst hB
  have hle : (⊥ : Subrepresentation ρ).toSubmodule.comap A.toSubmodule.subtype ≤
      LinearMap.ker A.toSubmodule.subtype := fun v hv => by
    have : (v : V) ∈ (⊥ : Subrepresentation ρ).toSubmodule := hv
    exact this
  let p : (subQuot A ⊥).IntertwiningMap ρ :=
    .mk (Submodule.liftQ _ A.toSubmodule.subtype hle) (fun g => by
      ext v
      rfl)
  have hp : Function.Injective p := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 hx
  have hi : Function.Injective (p.comp f) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    rcases eq_bot_or_eq_top (p.comp f).ker with h | h
    · have : x ∈ (p.comp f).ker := hx
      rw [h] at this
      exact this
    · exfalso
      refine hf (LinearMap.ext fun y => ?_)
      have hy : y ∈ (p.comp f).ker := by rw [h]; trivial
      exact hp (by simpa using hy)
  exact ⟨p.comp f, hi⟩

theorem exists_irr_sub : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → Nontrivial (X ⧸ whitKer ψ d J) →
    ∃ (S : IrrRep (GL (Fin (d 0)) k)) (f : S.ρ.IntertwiningMap (whit2 ψ d J)), Function.Injective f := by
  intro k _ _ _ _ ψ _ d X _ _ J hs hfl hnt
  obtain ⟨hgt, hlt⟩ := (hasFiniteLength_iff_wellFounded J).1 hfl
  have hbotImg : whitImg ψ d J ⊥ = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.map_bot _
  have htop : whitImg ψ d J ⊤ ≠ ⊥ := by
    intro h
    have h1 : (whitImg ψ d J ⊤).toSubmodule = ⊤ := by
      show (⊤ : Subrepresentation J).toSubmodule.map (whitKer ψ d J).mkQ = ⊤
      exact (Submodule.map_top _).trans (Submodule.range_mkQ _)
    rw [h] at h1
    obtain ⟨x, hx⟩ := exists_ne (0 : X ⧸ whitKer ψ d J)
    have : x ∈ (⊥ : Subrepresentation (whit2 ψ d J)).toSubmodule := by rw [h1]; trivial
    exact hx this
  obtain ⟨T, hT, hmin⟩ := (wellFounded_lt (α := Subrepresentation J)).has_min
    {T | whitImg ψ d J T ≠ ⊥} ⟨⊤, htop⟩
  have hbot : (⊥ : Subrepresentation J) < T := by
    refine bot_lt_iff_ne_bot.2 fun h => hT ?_
    rw [h]
    exact hbotImg
  obtain ⟨T', hT', hmax⟩ := (wellFounded_gt (α := Subrepresentation J)).has_min
    {B | B < T} ⟨⊥, hbot⟩
  have hcov : T' ⋖ T := ⟨hT', fun C hBC hCA => hmax C hCA hBC⟩
  have hImg' : whitImg ψ d J T' = ⊥ := by
    by_contra h
    exact hmin T' h hT'
  let τ : IrrRep (Levi k fun a => Fin (d a)) :=
    ⟨_, subQuot T T', IsSubquotient.isSmooth ⟨T, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩ hs, isIrreducible_subQuot hcov⟩
  obtain ⟨s, ⟨Φ⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
    k (Fin 2) (fun a => Fin (d a)) τ
  have hspan := GlobalTheory.T.whittaker_subquotient_equiv k ψ d X J T T' (fun a => (s a).V) (fun a => (s a).ρ) hT'.le Φ
  have hQ : Nontrivial ((whitImg ψ d J T).toSubmodule ⧸
      (whitImg ψ d J T').toSubmodule.comap (whitImg ψ d J T).toSubmodule.subtype) := by
    refine Submodule.Quotient.nontrivial_iff.2 fun h => hT ?_
    apply Subrepresentation.toSubmodule_injective
    refine le_antisymm (fun x hx => ?_) bot_le
    have hx' : (⟨x, hx⟩ : (whitImg ψ d J T).toSubmodule) ∈
        (whitImg ψ d J T').toSubmodule.comap (whitImg ψ d J T).toSubmodule.subtype := by
      rw [h]; trivial
    rw [Submodule.mem_comap, hImg'] at hx'
    exact hx'
  obtain ⟨f, hf⟩ : ∃ f : (s 0).ρ.IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')),
      f.toLinearMap ≠ 0 := by
    by_contra hno
    push_neg at hno
    have : (⨆ f : (s 0).ρ.IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')),
        LinearMap.range f.toLinearMap) = ⊥ := by
      refine le_antisymm (iSup_le fun f => ?_) bot_le
      rw [hno f, LinearMap.range_zero]
    rw [this] at hspan
    exact bot_ne_top hspan
  obtain ⟨g, hg⟩ := exists_injective_of_subQuot_bot (s 0).irr _ _ hImg' f hf
  exact ⟨s 0, g, hg⟩

end GlobalTheory.CompanionTheory.BZNuPair.WhitSub

end
