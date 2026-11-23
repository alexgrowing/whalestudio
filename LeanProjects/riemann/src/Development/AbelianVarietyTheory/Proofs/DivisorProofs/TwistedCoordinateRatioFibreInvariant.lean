import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TwCoordInv

open GlobalTheory.CoordCompare TorusCoord

theorem ratio_translate_invariant : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] [Mono β.left], g₂.pG ≫ β = g.pG → ∀ (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)) (χ₂ : D₂.X) (χ : D.X), (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A → r ≫ g₂.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D₂.P.A → val (g.t χ) r z J = val (g₂.t χ₂) r z J') → ∀ (a : 𝟙_ (Over (Sp R)) ⟶ G) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → r ≫ g.q.left = r' ≫ g.q.left → val (g.t χ) (r ≫ h) z J * ((∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r z J' * val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ = val (g.t χ) (r' ≫ h) z J * ((∏ k, gv w (r' ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r' ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r' ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r' z J' * val (gp.s χ) (r' ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ := by
  intro R _ _ I D D₂ e G _ _ g g₂ β _ _ hβ gp w χ₂ χ hker a₀ h hh hf Z r r' z J J' hJ hJ' hq
  obtain ⟨h₁, h₂⟩ := ratio_invariant g g₂ β hβ χ χ₂ hker r r' z J J' hJ hJ' hq
  have hw : r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom := by
    rw [← Over.w g.q, reassoc_of% hq]
  have hprod : ∀ k, r ≫ D₂.Oφ g₂.pG χ₂ k = r' ≫ D₂.Oφ g₂.pG χ₂ k := fun k =>
    Oφ_congr χ₂ g₂.pG r r' h₁ k
  let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (r' ≫ (thickObj R I e G).hom)
  let b : Z' ⟶ thickObj R I e G := Over.homMk r hw
  let b' : Z' ⟶ thickObj R I e G := Over.homMk r' rfl
  obtain ⟨τ, hτ⟩ := exists_torus g b b' (Over.OverMorphism.ext hq)
  let hO : thickObj R I e G ⟶ thickObj R I e G := Over.homMk h hh
  have hfO : (Over.map (thick R I e)).map hO ≫ fstG I e G =
      fstG I e G ≫ ((toUnit G ≫ a₀) * 𝟙 G) := Over.OverMorphism.ext hf
  have hsh : ∀ x : Z' ⟶ thickObj R I e G, (Over.map (thick R I e)).map (x ≫ hO) ≫ fstG I e G =
      (toUnit _ ≫ a₀) * ((Over.map (thick R I e)).map x ≫ fstG I e G) := fun x => by
    rw [Functor.map_comp, Category.assoc, hfO, ← Category.assoc, MonObj.comp_mul, comp_toUnit_assoc,
      Category.comp_id]
  have hkey : b ≫ hO = (τ ≫ g.i) * (b' ≫ hO) := by
    apply FormalPoint.eq_of_map_fstG
    rw [hsh, FormalPoint.map_mul_fstG, hsh, hτ, FormalPoint.map_mul_fstG, mul_left_comm]
  have v₁ := val_torus_mul g χ (Z := Z') hJ τ _ (b ≫ hO) (b' ≫ hO) rfl hkey
  have v₂ := val_torus_mul g χ (Z := Z') hJ τ _ b b' rfl hτ
  let k : Z ⟶ (thickObj R I e G).left := (τ ≫ g.i).left
  have v₁' : val (g.t χ) (r ≫ h) z J = val (g.t χ) k z J * val (g.t χ) (r' ≫ h) z J := v₁
  have v₂' : val (g.t χ) r z J = val (g.t χ) k z J * val (g.t χ) r' z J := v₂
  have hB : val (g₂.t χ₂) r z J' = val (g.t χ) k z J * val (g₂.t χ₂) r' z J' := by
    rw [v₂'] at h₂
    rw [mul_inv_eq_iff_eq_mul.1 h₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hP : (∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z
        (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i))
        (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) =
      ∏ k, gv w (r' ≫ D₂.Oφ g₂.pG χ₂ k) z
        (fun i => J ((r' ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i))
        (J' (r' ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k :=
    Finset.prod_congr rfl fun k _ => by rw [hprod k]
  have hS : val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J =
      val (gp.s χ) (r' ≫ (thickObj R I e G).hom ≫ thick R I e) z J := by
    rw [reassoc_of% hw]
  rw [hP, hS, v₁', hB]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TwCoordInv
