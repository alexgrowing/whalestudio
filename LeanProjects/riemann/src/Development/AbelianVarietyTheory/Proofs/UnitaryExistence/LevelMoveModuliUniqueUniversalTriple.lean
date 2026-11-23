import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory

open Moduli.LevelAction in

theorem levMove_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (_c : Coeff l), ∀ (ρ ρ' : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ν' : SABMap Xo.univ.t Xo.univ.t ρ') (gM gM' gA gA' : Dw.La →ₗ[𝓞 E] Dw.La), 1 ≤ Dw.p + Dw.q → (∀ a, gM a - gM' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA a - gA' a)) → IsIso ρ → IsIso ρ' → IsLevMove ρ ν gM gA → IsLevMove ρ' ν' gM' gA' → (∃ g : Sim Dw, (∀ a, g.f l.M a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ a, Dw.ModN l.A (g.f l.A a - gA a)) ∧ (l.A : ℤ) ∣ g.ν l.A - 1) → ρ = ρ' ∧ ν.φ = ν'.φ := by
  intro E _ _ _ H Dw l Xo _ ρ ρ' ν ν' gM gM' gA gA' hpq hM hA _ _ ⟨hs, e, eA⟩ ⟨hs', e', eA'⟩ ⟨g, hgM, hgA, hν⟩
  have hred : IsReduced Xo.X := by
    have := Xo.smooth
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s
      (SmoothOfRelativeDimension.smooth Dw.dim _)).1
  obtain ⟨o, m, a₁, b₁⟩ := exists_obj_twist_by_similitude SimAlg.sim_group E H Dw l _ _ _ _ Xo.univ g hpq hν
  obtain ⟨n, hn⟩ := exists_comp_sabMap m ν (Category.id_comp ρ)
  obtain ⟨n', hn'⟩ := exists_comp_sabMap m ν' (Category.id_comp ρ')
  have c₁ : ∀ a, (o.eta a).left ≫ n.φ = ρ ≫ (Xo.univ.eta a).left := fun a => by
    rw [hn, ← Category.assoc, a₁, eta_congr Xo.univ (hgM a), e]
  have c₂ : ∀ a, (o.etaA a).left ≫ n.φ = ρ ≫ (Xo.univ.etaA a).left := fun a => by
    rw [hn, ← Category.assoc, b₁, etaA_congr Xo.univ (hgA a), eA]
  have d₁ : ∀ a, (o.eta a).left ≫ n'.φ = ρ' ≫ (Xo.univ.eta a).left := fun a => by
    rw [hn', ← Category.assoc, a₁, eta_congr Xo.univ (hgM a), eta_congr Xo.univ (hM a), e']
  have d₂ : ∀ a, (o.etaA a).left ≫ n'.φ = ρ' ≫ (Xo.univ.etaA a).left := fun a => by
    rw [hn', ← Category.assoc, b₁, etaA_congr Xo.univ (hgA a), etaA_congr Xo.univ (hA a), eA']
  obtain rfl : ρ = ρ' := (Xo.rep _ Xo.s hred o).unique ⟨hs, ⟨⟨n, c₁, c₂⟩⟩⟩ ⟨hs', ⟨⟨n', d₁, d₂⟩⟩⟩
  refine ⟨rfl, ?_⟩
  have h := obj_rigid_closed firstFiveLaws.1 E H Dw l _ _ _ _ _ _ _ _ Xo.univ o ρ (Or.inl hred) n n'
    fun a => ⟨_, c₁ a, d₁ a⟩
  have : IsIso m.φ := m.cart.1.isIso_fst_of_isIso
  rw [hn, hn'] at h
  exact (cancel_epi m.φ).1 h

end GlobalTheory
