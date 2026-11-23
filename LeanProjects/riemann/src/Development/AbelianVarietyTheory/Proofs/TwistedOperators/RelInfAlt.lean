import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

noncomputable section

namespace GlobalTheory.HoweGlobalPair

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def opInf (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W) :
    Set (Module.End ℂ ↥(M.Pol ψ emb)) :=
  {g | (∃ k ∈ KInf σ W emb, ∀ f : ↥(M.Pol ψ emb),
      Acts (evI F) (om (1, k)) ⇑(f : SInf F (Fin n × Fin d)) ⇑((g f : ↥(M.Pol ψ emb)) : SInf F _)) ∨
    ∃ γ ∈ Lines σ W, ∀ f : ↥(M.Pol ψ emb),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) ⇑(f : SInf F (Fin n × Fin d))
        ⇑((g f : ↥(M.Pol ψ emb)) : SInf F _)}

def relInf (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W) :
    Submodule ℂ ↥(M.Pol ψ emb) :=
  Submodule.span ℂ {x | (∃ γ ∈ Lines σ X, ∃ f ∈ M.Pol ψ emb,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) ⇑f ⇑(x : SInf F (Fin n × Fin d))) ∨
    ∃ k ∈ KInf σ X emb, ∃ f f₁ : ↥(M.Pol ψ emb),
      Acts (evI F) (om (k, 1)) ⇑(f : SInf F (Fin n × Fin d)) ⇑(f₁ : SInf F (Fin n × Fin d)) ∧ x = f₁ - f}

def opFin (om : Rep σ X W) (v : Pl F) : Set (Module.End ℂ ↥(SB (Fin n × Fin d → Fv F v))) :=
  {g | ∃ h ∈ UAt σ W (evFin F v), ∀ φ : ↥(SB (Fin n × Fin d → Fv F v)),
    Acts (evFin F v) (om (1, h)) (φ : (Fin n × Fin d → Fv F v) → ℂ)
      ((g φ : ↥(SB (Fin n × Fin d → Fv F v))) : (Fin n × Fin d → Fv F v) → ℂ)}

def relFin (om : Rep σ X W) (v : Pl F) : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)) :=
  (augAt om v).comap (SB (Fin n × Fin d → Fv F v)).subtype

end GlobalTheory.HoweGlobalPair

end
