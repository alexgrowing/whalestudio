import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem omega_pullback_intertwines : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (GG : PDivGroup p R) (θ : TorsionMap A GG) (c : Pdiv.omega A →ₗ[R] GG.omega), θ.IsOmega c → ∀ (f : A ⟶ A) (g : GG ⟶ GG), IsMonHom f → θ.Intertwines f g → ∀ w w' : Pdiv.omega A, (∀ x x' : Pdiv.LieG A, x'.1 = x.1 ≫ f → w'.1 x = w.1 x') → c w' = omegaMap GG GG g (c w) := by
  intro p _ R _ _ _ A _ _ GG θ c hc f g hf hfg w w' hw
  apply Subtype.ext
  funext n
  obtain ⟨hsurj, hker, htan⟩ := hc n
  have hp : ((p : R) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  obtain ⟨b, hb⟩ := AugCot.d_surjective (Bialgebra.counitAlgHom R (GG.A n)) ((c w).1 n)
  obtain ⟨u, hu⟩ := hsurj (cotMap (g.app n) ((c w).1 n))
  have key : ∀ x : Pdiv.LieG A, ∃ q : R, w'.1 x - u.1 x = (p : R) ^ n * q := by
    intro x
    let x' : Pdiv.LieG A := ⟨x.1 ≫ f, by rw [← Category.assoc, x.2, Category.assoc, IsMonHom.one_hom]⟩
    have h1 := htan x' w b hb
    have h2 := htan x u (g.app n b) (by rw [hu, ← hb]; exact (cotMap_d (g.app n) b).symm)
    have h3 := hfg n _ (tanTors p n x) (tanTors p n x') (Category.assoc _ _ _).symm
    have h4 : θ.pt n _ (tanTors p n x') b = θ.pt n _ (tanTors p n x) (g.app n b) := by
      rw [h3]; rfl
    rw [h4, h2, ← hw x x' rfl] at h1
    have h5 := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h1.symm)
    obtain ⟨q, hq⟩ := h5
    exact ⟨q, hq⟩
  choose q hq using key
  have hqm : q ∈ Pdiv.omega A := by
    refine ⟨fun x y h => mul_left_cancel₀ hp ?_, fun a x h => mul_left_cancel₀ hp ?_⟩
    · linear_combination -(hq ⟨_, h⟩) + hq x + hq y + w'.2.1 x y h - u.2.1 x y h
    · linear_combination -(hq ⟨_, h⟩) + a * hq x + w'.2.2 a x h - u.2.2 a x h
  have hdiff : w' - u = ((p : R) ^ n) • (⟨q, hqm⟩ : Pdiv.omega A) :=
    Subtype.ext (funext fun x => (hq x).trans rfl)
  have h0 := (hker (w' - u)).2 ⟨_, hdiff⟩
  rw [map_sub, hu, sub_eq_zero] at h0
  exact h0

end GlobalTheory.GroupBplus.Aff
