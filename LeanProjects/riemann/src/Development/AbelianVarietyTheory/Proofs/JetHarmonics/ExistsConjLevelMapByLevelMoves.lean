import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ConjLevelMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_inv {S : Scheme.{0}} {t : SAB H S} (e : S ≅ S) (n : SABMap t t e.hom) :
    ∃ n' : SABMap t t e.inv, n.φ ≫ n'.φ = 𝟙 _ := by
  obtain ⟨i, hi⟩ := ObjMaps.exists_sab_id t
  obtain ⟨i', hi'⟩ := LevelFibre.sab_cast e.inv_hom_id.symm i
  obtain ⟨n', hn'⟩ := ObjMaps.exists_sab_cancel n i'
  have h : n'.φ ≫ n.φ = 𝟙 _ := hn'.symm.trans (hi'.trans hi)
  have pn : IsPullback n.φ t.G.hom t.G.hom e.hom := n.cart.1
  have : IsIso n.φ := pn.isIso_fst_of_isIso
  refine ⟨n', ?_⟩
  rw [← cancel_mono n.φ, Category.assoc, h, Category.comp_id, Category.id_comp]

theorem conj_sec {S S₂ : Scheme.{0}} {t : SAB H S} {t₂ : SAB H S₂} {r r' : S₂ ⟶ S} {ρ : S ⟶ S} {ρ₂ : S₂ ≅ S₂}
    (m : SABMap t₂ t r) (m' : SABMap t₂ t r') (ν : SABMap t t ρ) (ν₂ : SABMap t₂ t₂ ρ₂.hom)
    (hr : ρ₂.hom ≫ r' = r ≫ ρ) (hφ : ν₂.φ ≫ m'.φ = m.φ ≫ ν.φ)
    {σ σ' : 𝟙_ (Over S₂) ⟶ t₂.G} {τ τ' : 𝟙_ (Over S) ⟶ t.G} (k : ℕ)
    (h₂ : σ'.left ≫ ν₂.φ = ρ₂.hom ≫ σ.left) (hm : (σ' ^ k).left ≫ m.φ = r ≫ τ'.left)
    (h : τ'.left ≫ ν.φ = ρ ≫ τ.left) : (σ ^ k).left ≫ m'.φ = r' ≫ τ.left := by
  have e := OverMove.pow_left_comp ν₂ h₂ k
  have a₁ : ρ₂.hom ≫ (σ ^ k).left ≫ m'.φ = ((σ' ^ k).left ≫ m.φ) ≫ ν.φ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m'.φ) e.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg ((σ' ^ k).left ≫ ·) hφ).trans (Category.assoc _ _ _).symm)))
  have a₂ : (r ≫ τ'.left) ≫ ν.φ = ρ₂.hom ≫ r' ≫ τ.left :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) h).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ τ.left) hr.symm).trans (Category.assoc _ _ _))))
  exact (cancel_epi ρ₂.hom).1 (a₁.trans ((congrArg (· ≫ ν.φ) hm).trans a₂))

end ConjLevelMap

open ConjLevelMap in

theorem exists_conj_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.EtaOK → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ≅ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂.hom) (gM gA gM₂ gA₂ : Dw.La →ₗ[𝓞 E] Dw.La), IsLevMove ρ ν gM gA → IsLevMove ρ₂.hom ν₂ gM₂ gA₂ → (∀ a, gM₂ a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA₂ a - gA a)) → ∃ (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂.hom ≫ r' = d.r ≫ ρ ∧ ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ ∧ DeltaDat.EtaOK { d with r := r', m := m' } := by
  intro E _ _ _ H Dw l Xo c n d hE ρ ν ρ₂ ν₂ gM gA gM₂ gA₂ h h₂ hM hA
  obtain ⟨i, hi⟩ := exists_inv ρ₂ ν₂
  obtain ⟨q, hq⟩ := ObjMaps.exists_sab_comp ν d.m
  obtain ⟨m', hm'⟩ := ObjMaps.exists_sab_comp q i
  have hr : ρ₂.hom ≫ ρ₂.inv ≫ d.r ≫ ρ = d.r ≫ ρ := ρ₂.hom_inv_id_assoc _
  have hφ : ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ := by
    rw [hm', hq, ← Category.assoc, hi, Category.id_comp]
  have eM : ∀ a, Xo.univ.eta (gM₂ a) = Xo.univ.eta (gM a) := fun a => by
    rw [← sub_add_cancel (gM₂ a) (gM a), Xo.univ.eta_add, Xo.univ.eta_ker _ (hM a), _root_.one_mul]
  have eA : ∀ a, Xo.univ.etaA (gA₂ a) = Xo.univ.etaA (gA a) := fun a => by
    obtain ⟨x, hx⟩ := hA a
    rw [← sub_add_cancel (gA₂ a) (gA a), Xo.univ.etaA_add, hx, Xo.univ.etaA_ker, _root_.one_mul]
  refine ⟨_, m', hr, hφ, fun a => ?_, fun a => ?_⟩
  · exact conj_sec d.m m' ν ν₂ hr hφ d.pd (h₂.2.1 a) (hE.1 (gM₂ a)) (by rw [eM]; exact h.2.1 a)
  · exact conj_sec d.m m' ν ν₂ hr hφ (d.l₂.A / l.A) (h₂.2.2 a) (hE.2 (gA₂ a)) (by rw [eA]; exact h.2.2 a)

end GlobalTheory
