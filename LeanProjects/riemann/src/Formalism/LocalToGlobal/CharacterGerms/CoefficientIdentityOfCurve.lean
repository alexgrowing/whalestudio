import Formalism.LocalToGlobal.CharacterGerms.IndependenceBoundRaw
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

section Closed

variable {C : Type} [Field C]

def PsiCurveFBSt : Prop :=
  AllFB fun C _ V _ I _ dd X => X.RankHyp → ∀ _H : ∀ g, X.CartHyp V g, X.AltC → ∀ g,
    ∃ M : JJ I g → JJ I g → C, (∀ q' q, V.Ge 0 (M q' q)) ∧
      ∀ x ∈ X.TySet V g, ∀ (γ : Fin dd → PowerSeries C) (lam : JJ I g → PowerSeries C),
        IsCv V γ → IsCv V lam →
        (∀ i, alongCv γ (X.lg i) =
          ∑ c : I g, X.u g c i • tyS V.l (fun s => Vpow 1 (Fs V.l x) s (Sum.inl c))) →
        (∀ q : JJ I g, tyS V.l (fun s => Vpow 1 (Fs V.l x) s (Sum.inr q)) =
          lam q - alongCv γ (X.sg (X.u (1 - g) q)) +
            ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
              X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => Vpow 1 (Fs V.l x) s (Sum.inl c)) else 0) →
        (∀ i, ∀ m < V.l ^ 2, PowerSeries.coeff m (γ i) = 0) →
        (∀ i, V.MM (PowerSeries.coeff (V.l ^ 2) (γ i))) →
        ∀ q, V.MM (PowerSeries.coeff V.l (lam q) ^ V.l -
          ∑ q', PowerSeries.coeff (V.l ^ 2) (lam q') * M q' q)

end Closed

end Formalism.L2.FormalSeriesBounds
