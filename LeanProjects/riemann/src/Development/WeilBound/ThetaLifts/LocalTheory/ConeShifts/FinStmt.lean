import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ArchCone

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open Classical in

def FinCone2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) e u ei ev, Cfg B M M₁ H H' e u → IsEvLoc M M₁ e ei ev →
    ∀ v : Pl F, (∀ l, ev v (opF v (M.co.rho B.ψ (idem F v • u l)) (M.vac v)) = if idem F v • u l ∈ latAtV X W v then M₁.vac v else 0) ∧
    (∀ l, idem F v • u l ∈ latAtV X W v → Acts (evFin F v) (M.co.rho B.ψ (idem F v • u l)) (M.vac v) (M.vac v)) ∧
    ∀ (K : Subgroup (UA σ X.J)) (m : LocMeas K), IsStab B K → m.Is → ∀ χX χW om r s r' s', IsPair B M χX χW om r s r' s' →
    ∀ (ν : Chr F E) (z : ℕ), Continuous ν → 2 ≤ z →
    ∃ Λ : Fl F v _ _ →ₗ[ℂ] Fl F v _ _, ∀ φ ∈ SB _, Λ φ = coneF B M om m v (ev v) u ν z φ ∧ Λ φ ∈ SB _ ∧ ∀ y,
      (∀ k : kAt K (evFin F v), @Integrable _ _ _ _ (borel _) (fun l : idAt E (evFin F v) =>
          ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • u l.1) (om (k.1, 1) Φ)) φ) y * wt ν z l.1) (m.xf v)) ∧
        Integrable (fun k : kAt K (evFin F v) => @integral _ _ _ _ (borel _) (m.xf v) fun l =>
          ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • u l.1) (om (k.1, 1) Φ)) φ) y * wt ν z l.1) (m.kf v)

end PositivityTheory.ThKG.Loc.Cone

end
