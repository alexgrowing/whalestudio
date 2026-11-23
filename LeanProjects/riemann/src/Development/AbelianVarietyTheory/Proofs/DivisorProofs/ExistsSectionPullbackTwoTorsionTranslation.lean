import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TwoTorsTr

theorem tr_tr {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (a : 𝟙_ (Over (Sp R)) ⟶ G)
    (ha : a ^ 2 = 1) : ((toUnit G ≫ a) * 𝟙 G) ≫ ((toUnit G ≫ a) * 𝟙 G) = 𝟙 G := by
  rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (((toUnit G ≫ a) * 𝟙 G) ≫ toUnit G) (toUnit G),
    Category.comp_id, ← _root_.mul_assoc, ← MonObj.comp_mul, ← pow_two, ha, MonObj.comp_one, _root_.one_mul]

end GlobalTheory.TwoTorsTr

namespace GlobalTheory.TwoTorsTr

theorem secPull_invol {X : Scheme.{0}} (L L₂ : LB X) (hL : L.IsLB) (hL₂ : L₂.IsLB) (τ : X ⟶ X) (ττ : τ ≫ τ = 𝟙 X)
    (wL : LB.Iso L₂ (L.pull τ)) (hw : wL.IsGen) (σ : H0 L 1) : ∃ σ₂ : H0 L₂ 1,
    (∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (N : (Z ⟶ X) → L.ι) (N' : (Z ⟶ X) → L₂.ι),
      Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' →
      Geo.Tor.sval σ (r ≫ τ) z N = (Geo.Tor.gw wL r z (N (r ≫ τ)) (N' r)).val * Geo.Tor.sval σ₂ r z N') ∧
    ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) := by
  have hc : ∀ κ : Fin 1, (fun _ : Fin 1 => 𝟙 X) κ ≫ τ = τ ≫ (fun _ : Fin 1 => 𝟙 X) κ := fun _ => by
    simp only [Category.id_comp, Category.comp_id]
  obtain ⟨σ₂, hσ₂, -⟩ := SecPull.existsUnique_secPull _ _ _ _ L L₂ τ hL hL₂ wL hw (Fin 1)
    (fun _ => 𝟙 X) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) τ hc σ
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (N : (Z ⟶ X) → L.ι) (N' : (Z ⟶ X) → L₂.ι),
      Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' →
      Geo.Tor.sval σ (r ≫ τ) z N = (Geo.Tor.gw wL r z (N (r ≫ τ)) (N' r)).val * Geo.Tor.sval σ₂ r z N' := by
    intro Z r z N N' hN hN'
    have := ExpTrans.sec_val wL (fun _ : Fin 1 => 𝟙 X) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) τ hc σ σ₂
      r z (hσ₂ Z r z) hN hN'
    rw [this, Fin.prod_univ_one, zpow_natCast, pow_one, ExpTrans.om, Category.comp_id]
  refine ⟨σ₂, key, fun h0 j => ?_⟩
  refine ThetaScalar.eq_zero_of_sval hL σ (fun y J hJ => ?_) j
  choose J' hJ' using fun ψ : X ⟶ X => exists_chart hL₂ (ψ y)
  have e := key X τ y J J' hJ hJ'
  rw [ττ, ThetaScalar.sval_eq_zero σ₂ h0 τ y hJ', MulZeroClass.mul_zero] at e
  exact e

end GlobalTheory.TwoTorsTr

namespace GlobalTheory

theorem twoTors_secPull : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L L₂ : LB G.left), L.IsLB → L₂.IsLB → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ wL : LB.Iso L₂ (L.pull ((toUnit G ≫ a) * 𝟙 G).left), wL.IsGen → ∀ σ : H0 L 1, ∃ σ₂ : H0 L₂ 1, (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → L.ι) (N' : (Z ⟶ G.left) → L₂.ι), Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) := by
  intro R _ G _ _ L L₂ hL hL₂ a ha wL hw σ
  exact TwoTorsTr.secPull_invol L L₂ hL hL₂ _
    (by rw [← Over.comp_left, TwoTorsTr.tr_tr G a ha, Over.id_left]) wL hw σ

end GlobalTheory
