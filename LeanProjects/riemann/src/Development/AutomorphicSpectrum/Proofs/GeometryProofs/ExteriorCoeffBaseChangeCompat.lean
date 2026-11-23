import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLatticeGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LinePull

theorem wedge_eq_span_pull {X₀ X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
    {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {f : X ⟶ X₀} {i : Ω₀ →+* Ω}
    {V₀ V : Type} [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V] {j : V₀ →+ V}
    (hD : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) (hE : IsExtOver i j) {L₀ : Lat ξ₀ V₀} {L : Lat ξ V} {n : ℕ}
    {a₀ : ⋀[Ω₀]^n V₀} {a : ⋀[Ω]^n V} (x : Cpt ξ) (h : genPt ξ₀ ⤳ f x.1) {u : Fin n → V₀} {α : Ω₀} (hα : α ≠ 0)
    (hF : L₀.IsFrameAt u ⟨f x.1, h⟩) (hL : L x = L₀.pull ξ f j x)
    (hW : L₀.wedge n ⟨f x.1, h⟩ = Submodule.span (regAt ξ₀ ⟨f x.1, h⟩) {α • a₀})
    (hP : CptIn.IsPullWedge i j a₀ a) :
    L.wedge n x = Submodule.span (regAt ξ x) {i α • a} := by
  obtain ⟨_, hreg, -⟩ := pull_reg_and_gen X₀ Ω₀ ξ₀ X Ω ξ f i hD x
  have hF' := FlagPull.pull_isFrameAt hD hE x h hF
  have hFr : L.IsFrameAt (fun k => j (u k)) x := ⟨hF'.1, hL.trans hF'.2⟩
  obtain ⟨hw, -⟩ := WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ L n _ x hFr
  obtain ⟨hw₀, hne⟩ := WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ L₀ n u _ hF
  obtain ⟨ε, hε, e⟩ := ZUnit.exists_of_span_eq hne (hw₀.symm.trans hW)
  have hεα : ε * α ≠ 0 := mul_ne_zero hε.1 hα
  have ha₀ : a₀ = (ε * α)⁻¹ • exteriorPower.ιMulti Ω₀ n u := by
    rw [e, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hεα, one_smul]
  have ha := hP u _ ha₀
  have hne' : i ε ≠ 0 := (map_ne_zero i).2 hε.1
  have hiα : i α ≠ 0 := (map_ne_zero i).2 hα
  have e2 : exteriorPower.ιMulti Ω n (fun k => j (u k)) = i ε • i α • a := by
    rw [ha, smul_smul, smul_smul, ← map_mul, ← map_mul, mul_inv_cancel₀ hεα, map_one, one_smul]
  rw [hw, e2]
  have hu : i ε ∈ regAt ξ x := hreg _ hε.2.1
  have hv : (i ε)⁻¹ ∈ regAt ξ x := by
    rw [← map_inv₀]
    exact hreg _ hε.2.2
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · exact ⟨⟨i ε, hu⟩, rfl⟩
  · refine ⟨⟨(i ε)⁻¹, hv⟩, ?_⟩
    show (i ε)⁻¹ • i ε • i α • a = i α • a
    rw [inv_smul_smul₀ hne']

theorem isCoeffAt_pull : ∀ (X₀ X : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ X₀) (i : Ω₀ →+* Ω) (V₀ V : Type) [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V] (j : V₀ →+ V) (A₀ B₀ : Lat ξ₀ V₀) (A B : Lat ξ V) (p q : ℕ) (a₀ : ⋀[Ω₀]^p V₀) (b₀ : ⋀[Ω₀]^q V₀) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (x₀ : Cpt ξ₀) (u₁ : Fin p → V₀) (u₂ : Fin q → V₀), IsCptGen ξ₀ → IsCptGen ξ → Dominates ξ ξ₀ f i → IsExtOver i j → x₀.1 = f x.1 → A₀.IsFrameAt u₁ x₀ → B₀.IsFrameAt u₂ x₀ → A x = A₀.pull ξ f j x → B x = B₀.pull ξ f j x → IsCoeffAt A₀ B₀ p q a₀ b₀ x₀ 1 → CptIn.IsPullWedge i j a₀ a → CptIn.IsPullWedge i j b₀ b → IsCoeffAt A B p q a b x 1 := by
  intro X₀ X Ω₀ Ω _ _ ξ₀ ξ f i V₀ V _ _ _ _ j A₀ B₀ A B p q a₀ b₀ a b x x₀ u₁ u₂ _ _ hD hE hx hF₁ hF₂ hA hB hC hPa hPb
  obtain ⟨α, β, hα, -, hAw, hBw, hαβ⟩ := hC
  rw [one_mul] at hαβ
  subst hαβ
  obtain ⟨y, hy⟩ := x₀
  obtain rfl : y = f x.1 := hx
  exact ⟨i α, i α, (map_ne_zero i).2 hα, (map_ne_zero i).2 hα,
    wedge_eq_span_pull hD hE x hy hα hF₁ hA hAw hPa, wedge_eq_span_pull hD hE x hy hα hF₂ hB hBw hPb, one_mul _⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LinePull
