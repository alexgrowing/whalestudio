import Formalism.SharpRestriction.GlobalSchurBounds.StatementTranslationInvariantSeventh

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3r7

namespace Formalism.MainNotions.Ext.CutA

def LevelRestrictionOfGroupLaw : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok →
    (∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (a : ι → κ → ℂ_[p] × ℂ_[p])
        (a' : ι' → κ → ℂ_[p] × ℂ_[p]), (∀ e k, a e k ∈ S) → (∀ e k, a' e k ∈ S) →
        SimeqW (sdL g a a') (sdR g a a')) →
    (∀ (κ ι : Type) [Fintype κ] [Fintype ι] (b b' : ι → κ → ℂ_[p] × ℂ_[p]), (∀ e k, b e k ∈ S) →
        (∀ e k, b' e k ∈ S) → DualIso b b' → SimeqW (g.PhOn (Sum.elim b b')) (g.beSum ι)) →
    ∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (b b' : ι → κ → ℂ_[p] × ℂ_[p])
      (b'' : ι' → κ → ℂ_[p] × ℂ_[p]), (∀ e k, b e k ∈ S) → (∀ e k, b' e k ∈ S) → (∀ e k, b'' e k ∈ S) →
      DualIso b b' → (∀ e f, hP (b e) (b'' f) = 0) → (∀ e f, hP (b' e) (b'' f) = 0) →
      SimeqW (g.PhOn (Sum.elim (Sum.elim b b') b''))
        (∑ e : ι, g.be (Xv (Sum.inl (Sum.inl e))) (Xv (Sum.inl (Sum.inr e))) + PhV g b'' (fun f => Xv (Sum.inr f)))

end Formalism.MainNotions.Ext.CutA
