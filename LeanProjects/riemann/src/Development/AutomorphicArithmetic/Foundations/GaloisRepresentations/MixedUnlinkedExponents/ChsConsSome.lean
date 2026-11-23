import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamMixedOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem chs_cons_some (ξ : kˣ →* ℂˣ) (hξ) (s : Multiset (IrrGL k)) :
    chs (IrrGL.ofChar ξ hξ ::ₘ s) = ξ ::ₘ chs s := by
  have h : ∃ η : kˣ →* ℂˣ, ∃ hη : IsSmoothChar η, IrrGL.ofChar ξ hξ = IrrGL.ofChar η hη := ⟨ξ, hξ, rfl⟩
  have hc : h.choose = ξ := by
    obtain ⟨hη, he⟩ := h.choose_spec
    exact (IrrGL.ofChar_inj.mp he).symm
  unfold chs
  rw [Multiset.filterMap_cons_some _ _ _ (by rw [dif_pos h])]
  rw [hc]

private theorem chs_cons_not {y : IrrGL k} (hy : ¬ ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ)
    (s : Multiset (IrrGL k)) : chs (y ::ₘ s) = chs s := by
  unfold chs
  rw [Multiset.filterMap_cons_none _ _ (by rw [dif_neg hy])]

end Loc

theorem UpperTheory.Gal.GamX.chsTr :
    UpperTheory.Gal.GamX.ChsTr := by
  intro k k' _ _ _ _ _ _ _ _ i hi' s
  induction s using Multiset.induction_on with
  | empty => simp [chs_zero]
  | cons y s ih =>
    rw [Multiset.map_cons]
    by_cases hy : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ
    · obtain ⟨ξ, hξ, rfl⟩ := hy
      have hξ' : IsSmoothChar (ξ.comp (Units.map (i.symm : k' →* k))) :=
        hξ.comp _ (Units.continuous_map hi')
      rw [GlobalTheory.CharLiftStep.trGL_ofChar i hi' ξ hξ _ hξ' (fun _ => rfl), chs_cons_some, chs_cons_some,
        Multiset.map_cons, ih]
    · have hy' : ¬ ∃ ξ : k'ˣ →* ℂˣ, ∃ hξ, GlobalTheory.SuppIne.trGL i hi' y = IrrGL.ofChar ξ hξ := by
        rintro ⟨ξ, hξ, he⟩
        have h1 : y.fst = 1 := congrArg Sigma.fst he
        exact hy (GlobalTheory.RoadU.PlainChars.exists_eq_ofChar y h1)
      rw [chs_cons_not hy', chs_cons_not hy, ih]
