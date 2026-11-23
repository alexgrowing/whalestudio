import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory

noncomputable section

open Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace CompanionTheory.Rg.BcB.G3

structure IsFrame {k : Type} [Field k] {n : ℕ} (c : k →+* k) (δ : GL (Fin n) k) (s : k) {B : Type} [CommRing B] (d : B)
    (ρ : B →+* Matrix (Fin n) (Fin n) k) : Prop where
  inj : Function.Injective ρ
  sq : ρ d = (s ^ 2) • (1 : Matrix (Fin n) (Fin n) k)
  adj : ∀ a, ρ a * (δ.val * GlobalTheory.Tw.Phi n k) = δ.val * GlobalTheory.Tw.Phi n k * ((ρ a).map c)ᵀ
  comm : ∀ a, ρ a * (δ * thetaGL n c δ).val = (δ * thetaGL n c δ).val * ρ a
  span : ∀ x : Matrix (Fin n) (Fin n) k, x * (δ * thetaGL n c δ).val = (δ * thetaGL n c δ).val * x →
    ∃ a b, x = ρ a + s • ρ b

def pt {k : Type} [Field k] {n : ℕ} (δ : GL (Fin n) k) {B : Type} [CommRing B] (ρ : B →+* Matrix (Fin n) (Fin n) k)
    (t : Bˣ) : GL (Fin n) k := Units.map ρ.toMonoidHom t * δ

end CompanionTheory.Rg.BcB.G3

end
