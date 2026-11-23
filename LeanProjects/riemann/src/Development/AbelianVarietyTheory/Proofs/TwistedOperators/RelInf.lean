import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD

noncomputable section

namespace GlobalTheory.HoweGlobal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def opInf (Bs : Base F E) (G : Geo σ a a') (om : Rep σ G.V G.W) : Set (Module.End ℂ ↥(G.M.Pol Bs.ψ Bs.emb)) :=
  {g | (∃ k ∈ KInf σ G.W Bs.emb, ∀ f : ↥(G.M.Pol Bs.ψ Bs.emb),
      Acts (evI F) (om (1, k)) ⇑(f : SInf F (Fin a × Fin (a + a'))) ⇑((g f : ↥(G.M.Pol Bs.ψ Bs.emb)) : SInf F _)) ∨
    ∃ γ ∈ Lines σ G.W, ∀ f : ↥(G.M.Pol Bs.ψ Bs.emb),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) ⇑(f : SInf F (Fin a × Fin (a + a')))
        ⇑((g f : ↥(G.M.Pol Bs.ψ Bs.emb)) : SInf F _)}

def relInf (Bs : Base F E) (G : Geo σ a a') (om : Rep σ G.V G.W) : Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb) :=
  Submodule.span ℂ {x | (∃ γ ∈ Lines σ G.V, ∃ f ∈ G.M.Pol Bs.ψ Bs.emb,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) ⇑f ⇑(x : SInf F (Fin a × Fin (a + a')))) ∨
    ∃ k ∈ KInf σ G.V Bs.emb, ∃ f f₁ : ↥(G.M.Pol Bs.ψ Bs.emb),
      Acts (evI F) (om (k, 1)) ⇑(f : SInf F (Fin a × Fin (a + a'))) ⇑(f₁ : SInf F (Fin a × Fin (a + a'))) ∧ x = f₁ - f}

def opFin (G : Geo σ a a') (om : Rep σ G.V G.W) (v : Pl F) :
    Set (Module.End ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v))) :=
  {g | ∃ h ∈ UAt σ G.W (evFin F v), ∀ φ : ↥(SB (Fin a × Fin (a + a') → Fv F v)),
    Acts (evFin F v) (om (1, h)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ)
      ((g φ : ↥(SB (Fin a × Fin (a + a') → Fv F v))) : (Fin a × Fin (a + a') → Fv F v) → ℂ)}

def relFin (G : Geo σ a a') (om : Rep σ G.V G.W) (v : Pl F) : Submodule ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v)) :=
  (augAt om v).comap (SB (Fin a × Fin (a + a') → Fv F v)).subtype

end GlobalTheory.HoweGlobal

end
