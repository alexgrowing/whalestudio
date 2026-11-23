import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOf

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem opt_ofChar (ξ : kˣ →* ℂˣ) (hξ) :
    (if h : ∃ ξ' : kˣ →* ℂˣ, ∃ hξ', (IrrGL.ofChar ξ hξ : IrrGL k) = IrrGL.ofChar ξ' hξ' then some h.choose else none)
      = some ξ := by
  have h : ∃ ξ' : kˣ →* ℂˣ, ∃ hξ', (IrrGL.ofChar ξ hξ : IrrGL k) = IrrGL.ofChar ξ' hξ' := ⟨ξ, hξ, rfl⟩
  rw [dif_pos h]
  obtain ⟨_, h2⟩ := h.choose_spec
  exact congrArg some (IrrGL.ofChar_inj.1 h2).symm

private theorem chs_cons_ofChar (ξ : kˣ →* ℂˣ) (hξ) (s : Multiset (IrrGL k)) :
    chs (IrrGL.ofChar ξ hξ ::ₘ s) = ξ ::ₘ chs s :=
  Multiset.filterMap_cons_some _ _ _ (opt_ofChar ξ hξ)

private theorem chs_cons_none {y : IrrGL k} (hy : ¬ ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ)
    (s : Multiset (IrrGL k)) : chs (y ::ₘ s) = chs s :=
  Multiset.filterMap_cons_none _ _ (dif_neg hy)

private theorem mem_chs_iff (s : Multiset (IrrGL k)) (ξ : kˣ →* ℂˣ) :
    ξ ∈ chs s ↔ ∃ hξ, IrrGL.ofChar ξ hξ ∈ s := by
  unfold chs
  rw [Multiset.mem_filterMap]
  constructor
  · rintro ⟨y, hy, e⟩
    by_cases h : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ
    · obtain ⟨ξ', hξ', rfl⟩ := h
      rw [opt_ofChar] at e
      obtain rfl := Option.some.inj e
      exact ⟨hξ', hy⟩
    · rw [dif_neg h] at e
      cases e
  · rintro ⟨hξ, h⟩
    exact ⟨_, h, opt_ofChar ξ hξ⟩

private theorem pol_cons (y : IrrGL k) (s : Multiset (IrrGL k)) (θ : kˣ →* ℂˣ) :
    pol (y ::ₘ s) θ = (if h : ∃ ξ : kˣ →* ℂˣ, (∃ hξ, y = IrrGL.ofChar ξ hξ) ∧ IsUnram (ξ * θ) then
      1 - C (((h.choose * θ) (unif k) : ℂˣ) : ℂ) * X else 1) * pol s θ := by
  unfold pol
  rw [Multiset.map_cons, Multiset.prod_cons]

private theorem lp_cons (a : ℂˣ) (A : Multiset ℂˣ) : lp (a ::ₘ A) = (1 - C ((a : ℂˣ) : ℂ) * X) * lp A := by
  unfold lp
  rw [Multiset.map_cons, Multiset.prod_cons]

private theorem pol_eq_lp (s : Multiset (IrrGL k)) (θ : kˣ →* ℂˣ) : pol s θ = lp (vals (chs s) θ) := by
  induction s using Multiset.induction with
  | empty => simp [pol, lp, vals, chs_zero]
  | cons y s ih =>
    rw [pol_cons, ih]
    by_cases hy : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ
    · obtain ⟨ξ, hξ, rfl⟩ := hy
      rw [chs_cons_ofChar]
      by_cases hu : IsUnram (ξ * θ)
      · have h : ∃ ξ' : kˣ →* ℂˣ, (∃ hξ', (IrrGL.ofChar ξ hξ : IrrGL k) = IrrGL.ofChar ξ' hξ') ∧ IsUnram (ξ' * θ) :=
          ⟨ξ, ⟨hξ, rfl⟩, hu⟩
        rw [dif_pos h]
        obtain ⟨⟨_, h2⟩, _⟩ := h.choose_spec
        have e : h.choose = ξ := (IrrGL.ofChar_inj.1 h2).symm
        rw [e]
        unfold vals
        rw [Multiset.filter_cons_of_pos (p := fun ξ => IsUnram (ξ * θ)) _ hu, Multiset.map_cons, lp_cons]
      · have h : ¬ ∃ ξ' : kˣ →* ℂˣ, (∃ hξ', (IrrGL.ofChar ξ hξ : IrrGL k) = IrrGL.ofChar ξ' hξ') ∧ IsUnram (ξ' * θ) := by
          rintro ⟨ξ', ⟨_, h2⟩, h3⟩
          obtain rfl := IrrGL.ofChar_inj.1 h2
          exact hu h3
        rw [dif_neg h, one_mul]
        unfold vals
        rw [Multiset.filter_cons_of_neg (p := fun ξ => IsUnram (ξ * θ)) _ hu]
    · have h : ¬ ∃ ξ : kˣ →* ℂˣ, (∃ hξ, y = IrrGL.ofChar ξ hξ) ∧ IsUnram (ξ * θ) := by
        rintro ⟨ξ, h2, _⟩
        exact hy ⟨ξ, h2⟩
      rw [dif_neg h, one_mul, chs_cons_none hy]

end Loc

theorem chsFacts : ChsFacts := by
  unfold ChsFacts
  intro k _ _ _ _ s
  refine ⟨fun ξ => ?_, fun ξ hξ => ?_, fun θ => pol_eq_lp s θ⟩
  · rw [mem_chs_iff]
    rfl
  · obtain ⟨h, _⟩ := (mem_chs_iff s ξ).1 hξ
    exact h

end UpperTheory.Gal.GamX
