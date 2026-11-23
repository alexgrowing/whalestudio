import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLevelGroupDataSameCovolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFullLevelGroupIffCongruenceLcm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA

noncomputable section

namespace GlobalTheory.EqCovol.CongrOrb

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory GlobalTheory.EqCovol
open scoped Matrix nonZeroDivisors

set_option maxHeartbeats 800000 in

theorem selfDual_and_congr_free (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H)
    (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ)
    (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (hq : 1 ≤ Dw.q) (k : U.Comp) :
    GlobalTheory.EqCovol.IsSelfDualTr (U.X k) ∧ ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ γ' : GL (Fin r) E,
      IsUStab (U.X k).Gm (U.X k).Λ γ' ∧
      (∀ v ∈ (U.X k).Λ, ∃ w ∈ (U.X k).Λ, (γ' : Matrix (Fin r) (Fin r) E).mulVec v - v = l.M' • w) ∧
      ∃ b ∈ Bor (U.X k).Ψ r, lact γ x = rmul (lact γ' x) b := by
  classical
  obtain ⟨hr, hty, -, h4, -, g, e, F, ik, φ, hef, hun⟩ := hU
  obtain ⟨φ0, hφe⟩ : ∃ φ0 : (F.Di (ik k)).La →ₗ[𝓞 E] (Fin r → E), ∀ a, φ0 a = (φ k a : Fin r → E) :=
    ⟨(U.X k).Λ.subtype ∘ₗ (φ k).toLinearMap, fun _ => rfl⟩
  have hΛ : LinearMap.range φ0 = (U.X k).Λ := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      rw [hφe]
      exact (φ k a).2
    · intro hy
      exact ⟨(φ k).symm ⟨y, hy⟩, by rw [hφe, LinearEquiv.apply_symm_apply]⟩
  have hlat : Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧
      (∀ a b, cc ((U.X k).Gm a b) = (U.X k).Gm b a) ∧ (U.X k).Gm.det ≠ 0 ∧
      ∀ x y, (((F.Di (ik k)).EF x y : ℤ) : ℚ) =
        Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ0 x) (φ0 y)) := by
    refine ⟨fun a b hab => ?_, ?_, (U.X k).Gm_herm, (U.X k).Gm_det, fun x y => ?_⟩
    · rw [hφe, hφe] at hab
      exact (φ k).injective (Subtype.ext hab)
    · rw [← LinearMap.coe_range, hΛ]
      exact (U.X k).Λ_span
    · rw [hφe, hφe]
      exact hef k x y
  have hξ := (U.X k).ξ0_im
  have hξ' : cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    unfold cc at hξ ⊢
    rw [map_neg, hξ]
  have hneg : ∀ τ ∈ (U.X k).Ψ, (τ (U.X k).ξ0).im < 0 := by
    obtain ⟨x, hx⟩ := GlobalTheory.UnifFamily.dom_nonempty (U.X k)
    obtain ⟨Pm, h1, h2, -⟩ := hun k ⟨x, hx⟩
    exact GlobalTheory.FrameSign.im_neg_of_isPeriod E H Dw l c σ g e _ r (U.X k) (φ k) hσ hr (hty k).1 (hty k).2 (hef k)
      x hx Pm h1 h2 (by omega)
  obtain ⟨m, hm, ht⟩ := GlobalTheory.T.transvection_mem_principalCongruenceGroup E H l _ r _ _ φ0 hξ hlat
  have hi := GlobalTheory.T.principalLevelGroup_finiteIndex_unitaryStabiliser E H l _ r _ _ φ0 hξ hlat
  have hf := GlobalTheory.T.principalGroup_acts_freely_on_flags E H l _ r _ _ φ0 hξ hlat (U.X k).Ψ (U.X k).p0 (hty k).2
  have hmem : ∀ γ : GL (Fin r) E, γ ∈ princ l (U.X k).Gm (F.Di (ik k)) φ0 ↔ IsUStab (U.X k).Gm (U.X k).Λ γ ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di (ik k)).La), ∃ b : (F.Di (ik k)).La,
        (γ : Matrix (Fin r) (Fin r) E).mulVec (φ k a : Fin r → E) =
          (φ k a : Fin r → E) + (l.M : ℕ) • (φ k b : Fin r → E)) ∧
      ∀ a : (F.Di (ik k)).La, ∃ b : (F.Di (ik k)).La,
        (γ : Matrix (Fin r) (Fin r) E).mulVec (φ k a : Fin r → E) =
          (φ k a : Fin r → E) + (l.A : ℕ) • (φ k b : Fin r → E) := by
    intro γ
    simp only [← hφe]
    rw [← hΛ]
    exact Iff.rfl
  have hs : ∀ γ ∈ princ l (U.X k).Gm (F.Di (ik k)) φ0, IsUStab (U.X k).Gm (U.X k).Λ γ :=
    fun γ hγ => ((hmem γ).1 hγ).1
  rw [hΛ] at hi ht
  set Y := reGrp (U.X k) _ m hs hi hf hm (ht _ (U.X k).κ0_xi) with hYdef
  have hL : GlobalTheory.EqCovol.IsLevGrp l Y := by
    intro γ
    refine (hmem γ).trans (and_congr Iff.rfl (and_congr ?_ ?_))
    · have hI : (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (U.X k).Λ =
          (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di (ik k)).La)).map φ0 := by
        rw [Submodule.map_smul'', Submodule.map_top, hΛ]
      show _ ↔ ∀ x ∈ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (U.X k).Λ, ∃ y ∈ (U.X k).Λ, _
      rw [hI]
      simp only [← hφe]
      rw [← hΛ]
      constructor
      · rintro h _ ⟨a, ha, rfl⟩
        obtain ⟨b, hb⟩ := h a ha
        exact ⟨_, ⟨b, rfl⟩, sub_eq_iff_eq_add'.2 hb⟩
      · intro h a ha
        obtain ⟨_, ⟨b, rfl⟩, hb⟩ := h _ ⟨a, ha, rfl⟩
        exact ⟨b, sub_eq_iff_eq_add'.1 hb⟩
    · show _ ↔ ∀ x ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, _
      simp only [← hφe]
      rw [← hΛ]
      constructor
      · rintro h _ ⟨a, rfl⟩
        obtain ⟨b, hb⟩ := h a
        exact ⟨_, ⟨b, rfl⟩, sub_eq_iff_eq_add'.2 hb⟩
      · intro h a
        obtain ⟨_, ⟨b, rfl⟩, hb⟩ := h _ ⟨a, rfl⟩
        exact ⟨b, sub_eq_iff_eq_add'.1 hb⟩
  have hS : GlobalTheory.EqCovol.IsSelfDualTr (U.X k) := by
    intro x
    have hd := (GlobalTheory.HermModel.rank_integral_selfDual E H _ r _ _ φ0 hξ' hlat).2.2.2 x
    show x ∈ (U.X k).Λ ↔ ∀ y ∈ (U.X k).Λ, ∃ n : ℤ,
      Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm x y) = n
    rw [← hΛ, ← hd]
    constructor
    · rintro h _ ⟨y, rfl⟩
      exact h y
    · exact fun h y => h _ ⟨y, rfl⟩
  have hSY : GlobalTheory.EqCovol.IsSelfDualTr Y := hS
  have orb : ∀ x ∈ (U.X k).dom, ∀ x' ∈ (U.X k).dom,
      (∃ γ ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r, x' = rmul (lact γ x) b) →
      ∃ γ ∈ Y.Γ, ∃ b ∈ Bor Y.Ψ r, x' = rmul (lact γ x) b := by
    intro x hx x' hx'
    rintro ⟨γ, hγ, b, hb, hxx⟩
    obtain ⟨t, hx0, hu, -⟩ := (h4 k k ⟨x, hx⟩ ⟨x', hx'⟩).2 ⟨γ, hγ, b, hb, by rw [← hxx]⟩
    obtain ⟨Pm, hPm, -, hxP, hd, -⟩ := hun k ⟨x, hx⟩
    obtain ⟨Pm', hPm', -, hxP', hd', -⟩ := hun k ⟨x', hx'⟩
    refine fib_single e F hσ hr (ik k) Y (φ k) (hty k)
      (fun _ _ => rfl) (hef k) hmem hneg ⟨x, hx⟩ ⟨x', hx'⟩ Pm Pm' _ _ hPm hPm'
      (hxP.symm.trans (hx0.symm.trans hxP')) hd hd' fun τ i => ?_
    obtain ⟨cf, hcf, htri, hcomb⟩ := hu τ i
    refine ⟨cf, by rw [hcf]; exact Units.isUnit _, htri, ?_⟩
    rw [hxP] at hcomb
    exact hcomb
  refine ⟨hS, fun γ hγ x hx => ?_⟩
  have hxg : lact γ x ∈ (U.X k).dom := Formalism.L2.Pj.dom_lact _ hx ((U.X k).Γ_stab γ hγ)
  obtain ⟨γ', hγ', b', hb', e'⟩ := orb x hx _ hxg
    ⟨γ, hγ, ExtFPf.oneF (U.X k), ExtFPf.oneF_mem (U.X k), (ExtFPf.rmul_oneF (U.X k) _).symm⟩
  obtain ⟨hU', hc⟩ := (GlobalTheory.EqCovol.mem_iff_congr_lcm E H l r Y hL hSY γ').1 hγ'
  exact ⟨γ', hU', hc, b', hb', e'⟩

end GlobalTheory.EqCovol.CongrOrb

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

theorem GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k : U.Comp, GlobalTheory.EqCovol.IsSelfDualTr (U.X k) ∧ ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ γ' : GL (Fin r) E, IsUStab (U.X k).Gm (U.X k).Λ γ' ∧ (∀ v ∈ (U.X k).Λ, ∃ w ∈ (U.X k).Λ, (γ' : Matrix (Fin r) (Fin r) E).mulVec v - v = l.M' • w) ∧ ∃ b ∈ Bor (U.X k).Ψ r, lact γ x = rmul (lact γ' x) b := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU _ _ hq k
  exact GlobalTheory.EqCovol.CongrOrb.selfDual_and_congr_free E H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hq k
