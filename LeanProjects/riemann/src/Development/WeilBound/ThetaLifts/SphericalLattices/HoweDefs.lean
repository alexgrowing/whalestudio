import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

def LocData {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (v : Pl F) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : CharZero L) (_ : Valued L (WithZero (Multiplicative ℤ))) (_ : CompleteSpace L)
    (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (JS : GL (Fin n) L) (JT : GL (Fin d) L) (ψL : AddChar L ℂ)
    (ρL : Matrix (Fin d) (Fin n) L → Module.End ℂ (SB (Fin n × Fin d → Fv F v)))
    (ωL : Formalism.UG.UJ σL (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σL (JT : Matrix (Fin d) (Fin d) L) →*
      Module.End ℂ (SB (Fin n × Fin d → Fv F v)))
    (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin n) (Fin n) L) →* UA σ X.J)
    (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin d) (Fin d) L) →* UA σ W.J) (s : SB (Fin n × Fin d → Fv F v)),
    GlobalTheory.Hk3.LocPair ϖ σL q δ JS JT ψL ρL ωL ∧ s ≠ 0 ∧ GlobalTheory.Hk3.LocVac ρL s ∧
    Submodule.span ℂ (Set.range fun x => ρL x s) = ⊤ ∧ (s : (Fin n × Fin d → Fv F v) → ℂ) = M.vac v ∧
    (∀ g, ιS g ∈ UAt σ X (evFin F v)) ∧ (∀ h, ιT h ∈ UAt σ W (evFin F v)) ∧
    (∀ g : Formalism.UG.UJ σL (JS : Matrix (Fin n) (Fin n) L),
      (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ιS g ∈ GlobalTheory.InertSph.KAt σ X v) ∧
    (∀ h : Formalism.UG.UJ σL (JT : Matrix (Fin d) (Fin d) L),
      (h : GL (Fin d) L) ∈ Formalism.UG.GLint (Fin d) (Formalism.UG.intL L) → ιT h ∈ GlobalTheory.InertSph.KAt σ W v) ∧
    ∀ g h (m : SB (Fin n × Fin d → Fv F v)) (φ₁ : (Fin n × Fin d → Fv F v) → ℂ), φ₁ ∈ SB (Fin n × Fin d → Fv F v) →
      (Acts (evFin F v) (om (ιS g, ιT h)) (m : (Fin n × Fin d → Fv F v) → ℂ) φ₁ ↔
        ((ωL (g, h) m : SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) = φ₁)

theorem kAt_eq (X : Spc F E n) (v : Pl F) : KAt σ X v = GlobalTheory.InertSph.KAt σ X v := rfl

end PositivityTheory.Sph

end
