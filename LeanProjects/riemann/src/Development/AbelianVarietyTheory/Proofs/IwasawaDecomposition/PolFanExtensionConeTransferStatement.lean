import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanExtensionConeTransfer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_positive_polFan_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ' : InvFun (𝓞 E)), IsPolFan H.bar q φ' → NoSelfInt H.bar q φ' → IsTwInv H φ' → ∃ φ'' : InvFun (𝓞 E), IsPolFan H.bar q φ'' ∧ NoSelfInt H.bar q φ'' ∧ IsTwInv H φ'' ∧ IsPosFn H φ'' ∧ (∀ (n k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ''.toFun n (fun a b => k * B a b) = k * φ''.toFun n B) ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ'' γ → IsCone H.bar φ' γ := by
  first | exact @GlobalTheory.PolFan.OffDom.exists_extension | exact GlobalTheory.PolFan.OffDom.exists_extension | (intros; apply GlobalTheory.PolFan.OffDom.exists_extension <;> assumption)
