import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef.AddDiv

theorem idlAlong_add {X : Scheme.{0}} (D₁ D₂ : GlobalTheory.EffCartierData X) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ X) :
    idlAlong (D₁.add D₂).idealSheaf ξ = idlAlong D₁.idealSheaf ξ * idlAlong D₂.idealSheaf ξ := by
  obtain ⟨i, hi⟩ := D₁.exists_mem (ξ (IsLocalRing.closedPoint R))
  obtain ⟨j, hj⟩ := D₂.exists_mem (ξ (IsLocalRing.closedPoint R))
  have hij : ξ (IsLocalRing.closedPoint R) ∈ (D₁.add D₂).U (i, j) := ⟨hi, hj⟩
  rw [idlAlong, idlAlong, idlAlong, (D₁.add D₂).stalkId_idealSheaf (i, j) _ hij, D₁.stalkId_idealSheaf i _ hi,
    D₂.stalkId_idealSheaf j _ hj, ← Ideal.map_mul, Ideal.span_singleton_mul_span_singleton]
  have e : (X.presheaf.germ _ _ hij).hom ((D₁.add D₂).f (i, j)) =
      (X.presheaf.germ _ _ hi).hom (D₁.f i) * (X.presheaf.germ _ _ hj).hom (D₂.f j) := by
    change (X.presheaf.germ _ _ hij).hom
      (resG X inf_le_left (D₁.f i) * resG X inf_le_right (D₂.f j)) = _
    exact (map_mul (X.presheaf.germ _ _ hij).hom _ _).trans
      (congrArg₂ (· * ·) (GlobalTheory.Cartier.germ_resG _ _ _ _) (GlobalTheory.Cartier.germ_resG _ _ _ _))
  rw [e]

theorem evalZ_comb_one {O : Type} [CommRing O] (ψ φ : InvFun O) {M : Type} [AddCommGroup M] [Module O M]
    [Module.Finite O M] (be : LinearMap.BilinForm ℤ M) :
    (comb 1 ψ 1 φ).evalZ be = ψ.evalZ be + φ.evalZ be := by
  simp only [InvFun.evalZ, InvFun.eval, comb]
  push_cast
  ring

theorem isPhiDiv_add : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (φ₁ φ₂ : InvFun (𝓞 E))
    (D₁ D₂ : GlobalTheory.EffCartierData Z.X), IsPhiDiv φ₁ Z D₁ → IsPhiDiv φ₂ Z D₂ → IsPhiDiv (comb 1 φ₁ 1 φ₂) Z (D₁.add D₂) := by
  intro E _ _ _ H D l Xo c O _ β Z φ₁ φ₂ D₁ D₂ h₁ h₂
  intro W _ _ _ hW ϖ hϖ χ t hχ P hr be hbe hm
  obtain ⟨n₁, hn₁, hI₁⟩ := h₁ W hW ϖ hϖ χ t hχ P hr be hbe hm
  obtain ⟨n₂, hn₂, hI₂⟩ := h₂ W hW ϖ hϖ χ t hχ P hr be hbe hm
  refine ⟨n₁ + n₂, ?_, ?_⟩
  · rw [evalZ_comb_one, ← hn₁, ← hn₂]
    push_cast
    ring
  · rw [idlAlong_add, hI₁, hI₂, Ideal.span_singleton_mul_span_singleton, pow_add]

end GlobalTheory.TorRef.AddDiv
