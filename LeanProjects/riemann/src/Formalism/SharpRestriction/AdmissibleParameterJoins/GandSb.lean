import Formalism.SharpRestriction.GrowthBounds.SelectionLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.UnusedSlot33 NumberField IsDedekindDomain
open scoped TensorProduct

def ArithLevel (D : D7) {p : ℕ} (G : GAtP p) : Prop :=
  ∃ (σ : D.host.E →ₐ[D.host.F] D.host.E) (J : Matrix (Fin D.R.k) (Fin D.R.k) D.host.E) (g : ℕ)
    (v : HeightOneSpectrum (𝓞 D.host.F)),
    (∀ x, σ x = D.host.conj x) ∧ IsHerm (σ : D.host.E →+* D.host.E) J ∧ IsDef σ J ∧ g.Prime ∧
    2 * D.R.f * D.R.k < g - 1 ∧ ((g : 𝓞 D.host.F) ∈ v.asIdeal) ∧
    letI := tensTop (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    letI := tensTop (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F)
    ∃ (U : Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
      (Uw : Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))),
      U ≤ UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
      IsCompact (U : Set (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))) ∧
      IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) | (x : GL _ _) ∈ U} ∧
      IsProG g Uw ∧ (∀ u ∈ U, bc (prV v) u ∈ Uw) ∧
      ∀ i : G.comp, ∃ emb : (G.lev i).Γ →*
          GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        Function.Injective emb ∧
        (∀ γ, emb γ ∈ ratPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        ∀ L : G.P.Tup, G.P.IsLatTup L →
          ∃ y ∈ UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
            ∀ γ, (G.lev i).smul γ L = L → emb γ ∈ U.map (MulAut.conj y).toMonoidHom

end Formalism.MainNotions.J

end
