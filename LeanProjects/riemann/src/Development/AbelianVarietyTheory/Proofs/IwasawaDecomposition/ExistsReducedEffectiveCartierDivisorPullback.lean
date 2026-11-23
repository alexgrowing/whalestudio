import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomRangeSubset

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

noncomputable section

namespace GlobalTheory.FlagBundle.DivPull

variable {F : Type} [Field F] {B Y : GlobalTheory.ProjVar.Var F} {φ : B.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ B.X}

theorem regAt_map (h : (ratOf B).IsHom (ratOf Y) φ f) {y : Y.X} {g : B.Fn} (hg : RegAt (f y) g) :
    RegAt y (φ g) :=
  mem_O_ratOf.1 (h.map_mem_O (z := y) (mem_O_ratOf.2 hg))

theorem unitAt_map (h : (ratOf B).IsHom (ratOf Y) φ f) {y : Y.X} {g : B.Fn} (hg : UnitAt (f y) g) :
    UnitAt y (φ g) :=
  (unitAt_iff ((map_ne_zero φ).2 hg.ne_zero)).2
    ⟨regAt_map h hg.regAt, by rw [← map_inv₀]; exact regAt_map h hg.inv.regAt⟩

theorem unitAt_of_map (h : (ratOf B).IsHom (ratOf Y) φ f) {y : Y.X} {g : B.Fn} (hg : RegAt (f y) g)
    (hu : UnitAt y (φ g)) : UnitAt (f y) g := by
  have h0 : g ≠ 0 := (map_ne_zero φ).1 hu.ne_zero
  exact (unitAt_iff h0).2 ⟨hg, mem_O_ratOf.1
    (h.inv_mem_O (z := y) (mem_O_ratOf.2 hg) h0 (mem_O_ratOf.2 hu.inv.regAt))⟩

theorem exists_pullback (h : (ratOf B).IsHom (ratOf Y) φ f) (D : B.Dv) :
    ∃ D' : Y.Dv, ∀ (y : Y.X) (g : B.Fnˣ), D.IsEqn (f y) g →
      D'.IsEqn y (Units.map (φ : B.Fn →* Y.Fn) g) := by
  choose e he using fun y : Y.X => D.exists_isEqn (f y)
  have key : ∀ (y : Y.X) (g : B.Fnˣ), D.IsEqn (f y) g →
      germOf y (Units.map (φ : B.Fn →* Y.Fn) (e y)) = germOf y (Units.map (φ : B.Fn →* Y.Fn) g) := by
    intro y g hg
    rw [germOf_eq_iff]
    have := unitAt_map h ((he y).iff_unitAt.1 hg)
    rw [map_div₀] at this
    exact this
  refine ⟨show cartierGroup Y.X from ⟨fun y => germOf y (Units.map (φ : B.Fn →* Y.Fn) (e y)), fun y => ?_⟩, key⟩
  obtain ⟨U, hU, g, hg⟩ := D.exists_isEqn_nhds (f y)
  exact ⟨f ⁻¹ᵁ U, hU, Units.map (φ : B.Fn →* Y.Fn) g, fun z hz => key z g (hg _ hz)⟩

theorem exists_reduced_pullback : ∀ (F : Type) [Field F] (B Y : GlobalTheory.ProjVar.Var F) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X) (D : B.Dv), (ratOf B).IsHom (ratOf Y) φ f → KeepsRad (ratOf B) (ratOf Y) φ f → D.Eff → (∀ (y : B.X) (g : B.Fnˣ), D.IsEqn y g → ∀ (a : B.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g)) → ∃ D' : Y.Dv, D'.Eff ∧ (∀ y, y ∈ D'.supp ↔ f y ∈ D.supp) ∧ ∀ (y : Y.X) (g : Y.Fnˣ), D'.IsEqn y g → ∀ (a : Y.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g) := by
  intro F _ B Y φ f D h hk hD hr
  obtain ⟨D', hD'⟩ := exists_pullback h D
  refine ⟨D', CartierDiv.eff_iff.2 fun y g hg => ?_, fun y => ?_, fun y g hg a n ha hn => ?_⟩
  · obtain ⟨e, he⟩ := D.exists_isEqn (f y)
    have h1 := ((hD' y e he).iff_unitAt.1 hg).regAt.mul (regAt_map h (CartierDiv.eff_iff.1 hD _ e he))
    have h0 : φ e ≠ 0 := (map_ne_zero φ).2 e.ne_zero
    have e1 : (g : Y.Fn) / φ e * φ e = g := div_mul_cancel₀ _ h0
    exact e1 ▸ h1
  · obtain ⟨e, he⟩ := D.exists_isEqn (f y)
    change ¬ D'.IsEqn y 1 ↔ ¬ D.IsEqn (f y) 1
    rw [not_iff_not, (hD' y e he).iff_unitAt, he.iff_unitAt, Units.val_one, Units.val_one, one_div, one_div]
    constructor
    · intro hu
      have := hu.inv
      rw [inv_inv] at this
      exact (unitAt_of_map h (CartierDiv.eff_iff.1 hD _ e he) this).inv
    · intro hu
      have := hu.inv
      rw [inv_inv] at this
      exact (unitAt_map h this).inv
  · obtain ⟨e, he⟩ := D.exists_isEqn (f y)
    have hR := hk y e ⟨e.ne_zero, mem_O_ratOf.2 (CartierDiv.eff_iff.1 hD _ e he), fun x m hx hm =>
      mem_O_ratOf.2 (hr _ e he x m (mem_O_ratOf.1 hx) (mem_O_ratOf.1 hm))⟩
    have hu : UnitAt y ((g : Y.Fn) / φ e) := (hD' y e he).iff_unitAt.1 hg
    have h0 : φ e ≠ 0 := (map_ne_zero φ).2 e.ne_zero
    have hg0 : (g : Y.Fn) ≠ 0 := g.ne_zero
    have e1 : a ^ n / g * ((g : Y.Fn) / φ e) = a ^ n / φ e := by field_simp
    have e2 : a / φ e * ((g : Y.Fn) / φ e)⁻¹ = a / g := by field_simp
    have h2 : RegAt y (a / φ e) :=
      mem_O_ratOf.1 (hR.2.2 a n (mem_O_ratOf.2 ha) (mem_O_ratOf.2 (e1 ▸ hn.mul hu.regAt)))
    exact e2 ▸ h2.mul hu.inv.regAt

end GlobalTheory.FlagBundle.DivPull
