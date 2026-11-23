import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.PrincGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycMemPrincIff

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.layerGen :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], HasMuQ l L → (∀ m, (layU l L Ω m).index = l ^ m) ∧
        ∀ γ : G L Ω, IsGen l ⊤ γ → PropA.IsLevel l (cycZ L Ω l γ : ℤ_[l]ˣ) (cZero l L) ∧ γ ∈ levU l ⊤ 1 ∧ ∀ m, IsGen l (layU l L Ω m) (γ ^ l ^ m) := by
  intro L Ω _ _ _ _ _ l _ hmu
  obtain ⟨-, h2, h3, -⟩ := muQ L Ω l
  have hq := h3.1 hmu
  have hr := cycRange L Ω l hmu
  obtain ⟨p1, p2, p3⟩ := princGen l _ hq
  have h0 : ∀ g, cycZ L Ω l g ∈ KStar.TotallyRealRoots.princ l (cZero l L) := fun g => hr ▸ ⟨g, rfl⟩
  have hU : ∀ n, Un L Ω l n = (KStar.TotallyRealRoots.princ l n).comap (cycZ L Ω l) := fun n =>
    Subgroup.ext fun g => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  have h1 : 1 ≤ cZero l L := by
    refine le_trans ?_ hq
    unfold qExp
    split_ifs <;> omega
  refine ⟨fun m => ?_, fun γ hγ => ?_⟩
  · rw [layU, hU, Subgroup.index_comap, hr, p3]
  · have hn : cycZ L Ω l γ ∉ KStar.TotallyRealRoots.princ l (cZero l L + 1) := by
      refine (p1 _ (h0 γ)).1 ?_
      rw [← hr, MonoidHom.range_eq_map]
      exact hγ.2
    obtain ⟨q1, q2⟩ := p2 _ (h0 γ) hn
    refine ⟨q1, ?_, fun m => ⟨?_, ?_⟩⟩
    · have : γ ∈ Un L Ω l 1 := by rw [(h2 1).2 h1]; trivial
      exact this
    · rw [layU, hU, Subgroup.mem_comap, map_pow]
      exact (q2 m).1
    · rw [layU, hU, map_pow]
      exact (Subgroup.map_comap_le _ _).trans
        (((princGen l (cZero l L + m) (hq.trans (Nat.le_add_right _ _))).1 _ (q2 m).1).2 (q2 m).2)
