import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

namespace GlobalTheory.ShFam.GalCarry

theorem triEqn (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (Y : FlagCpt Z e) : TriEqn Y := by
  intro y φ f t a τ i
  obtain ⟨φ₁, f₁, t₁, a₁, h1⟩ := Y.gr_spec y
  have hι := IsFractionRing.injective (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField
  obtain rfl : φ₁ = φ := RingHom.ext fun x => hι ((RingHom.congr_fun a₁.2.1 x).symm.trans (RingHom.congr_fun a.2.1 x))
  obtain ⟨k₁, hk₁⟩ := f₁.exists_isMap _ a.2.1 a.1
  obtain ⟨k, hk⟩ := f.exists_isMap _ a.2.1 a.1
  have e1 (τ i d) : k₁.co Y.f0 τ d i = ∑ j, k.co Y.f0 τ j i * algebraMap _ Y.Y.X.functionField (f₁.co f τ d j) := by
    rw [← k₁.co_mul k, hk₁.co τ hk a.1, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hM (τ d i) (h : i < d) : f₁.co f τ d i = 0 := hι ((CoordUniq.tri_of_mul
    (M := fun i a => algebraMap _ Y.Y.X.functionField (f₁.co f τ a i)) (fun i a => (a₁.co τ hk₁).1 a i)
    (fun i a' => (a.co τ hk).1 a' i) (fun i => (a.co τ hk).2 i ▸ (t τ i).ne_zero) (e1 τ) i d h).trans (map_zero _).symm)
  have hu (τ i) : IsUnit (f₁.co f τ i i) := by
    have := f₁.isUnit_det_co f τ
    rw [Matrix.det_of_upperTriangular (M := f₁.co f τ) fun _ _ h => hM τ _ _ h] at this
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => f₁.co f τ i i) (Finset.mem_univ i)) this
  obtain ⟨u, hu'⟩ : ∃ u : (Y.Y.X.presheaf.stalk y)ˣ,
      t₁ τ i = t τ i * Units.map (algebraMap _ Y.Y.X.functionField).toMonoidHom u := by
    refine ⟨(hu τ i).unit, Units.ext ?_⟩
    rw [← (a₁.co τ hk₁).2, e1, Units.val_mul, ← (a.co τ hk).2]
    exact CoordUniq.diag_of_mul (M := fun i a => algebraMap _ Y.Y.X.functionField (f₁.co f τ a i))
      (fun i a' => (a.co τ hk).1 a' i) (fun i a h => by simp only [hM τ a i h, map_zero]) i
  refine (CartierDiv.IsEqn.iff_unitAt (h1 τ i)).2 ⟨(u⁻¹ : _ˣ), Units.isUnit _, ?_⟩
  rw [hu', Units.val_mul, div_mul_cancel_left₀ (Units.ne_zero _), ← Units.val_inv_eq_inv_val, ← map_inv]
  rfl

end GlobalTheory.ShFam.GalCarry
