import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfAllStepsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsLocalTangentFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMapUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepAt
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM

namespace GlobalTheory.LocM.LatCover

theorem mult_le_rank : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V), Set.range x ⊆ Z.opn → ∀ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ), g ≫ B.π = Z.π ≫ τ → ∃ Φ : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G ≃ₗ[k] (Fin n → k), ∀ w : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v), v ≫ B.tMap.φ = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = Φ w l) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (U : Z.X.Opens) (hU : IsAffineOpen U) (V : B.X.Opens), U ≤ g ⁻¹ᵁ V → ∀ (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (σ : E →+* ℂ) (a : GL (Fin n) Γ(Z.X, U)), LatCover.StepAt Z B g L σ (Dw.mult σ) hU m a → ∀ x : Z.X, x ∈ U → Dw.mult σ ≤ n := by
  intro hc E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L g hg U hU V hUV n m hm σ a _ x hx
  obtain ⟨k, _, φ, u, hu⟩ := GlobalTheory.LocM.StepFrame.exists_flagAt Z hU hx
  obtain ⟨τ, mu, -, hπ⟩ := GlobalTheory.LocM.StepBasis.exists_isTrans hg x
  have ho : Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn := GlobalTheory.LocM.MapComp.range_subset_opn Z hu
  have h : ⊤ ≤ ((spMap φ ≫ hU.fromSpec) ≫ g) ⁻¹ᵁ V := by
    have h1 : ⊤ ≤ (spMap φ ≫ hU.fromSpec) ⁻¹ᵁ U := by
      rintro y -
      exact hU.range_fromSpec.le ⟨spMap φ y, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rintro y -
    have := hUV (h1 (Set.mem_univ y))
    simpa [Scheme.Hom.comp_apply] using this
  obtain ⟨Φ, -⟩ := hc E H Dw Xo p W hp hW Y i₀ Z B L g hg V n m hm k (spMap φ ≫ hU.fromSpec) h ho τ mu hπ
  obtain ⟨a₀, ψ₀, -, fu, -⟩ := hu
  by_contra hlt
  push_neg at hlt
  let b : Fin n → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM ((spMap φ ≫ hU.fromSpec) ≫ Z.π) (Y Z.i).t.G :=
    fun j => Φ.symm (Pi.single j 1)
  have hcomb : ∀ i : Fin (Dw.mult σ), (i : ℕ) < Dw.mult σ → ∃ cf : Fin n → k,
      (∀ j : Fin n, Dw.mult σ ≤ (j : ℕ) → cf j = 0) ∧
      IsCombAtG (Y Z.i).t ((spMap φ ≫ hU.fromSpec) ≫ Z.π) (fun j => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (b j)).left) cf (u σ i) := by
    intro i _
    have ht : IsTanAtG (Y Z.i).t ((spMap φ ≫ hU.fromSpec) ≫ Z.π) (u σ i) := (fu.1 σ i).1
    refine ⟨fun j => Φ (GlobalTheory.LieMet.tanOf ht) j, fun j hj => absurd (hj.trans_lt j.2) (lt_asymm hlt), ?_⟩
    refine (GlobalTheory.LieMet.isComb_iff b _ (GlobalTheory.LieMet.tanOf ht)).2 ?_
    apply Φ.injective
    ext l
    simp [b, map_sum, Pi.single_apply]
  have hs := GlobalTheory.LocM.StepFrame.step_eq fu le_rfl (fun j => GlobalTheory.LieMet.isTan_tv (b j)) hcomb
  omega

end GlobalTheory.LocM.LatCover
