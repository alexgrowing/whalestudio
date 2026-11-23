import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeUnitStalkDataGermStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

private theorem eta_comp_mul_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : η[G] ≫ (𝟙 G * 𝟙 G) = η[G] := by
  rw [Hom.mul_def, ← Category.assoc, comp_lift, Category.comp_id]
  simpa using lift_comp_one_left (𝟙 _) η[G]

private theorem unitSec_comp_sqr {S : Scheme.{0}} (G : Over S) [GrpObj G] : unitSec G ≫ sqr G = unitSec G :=
  congrArg (·.left) (eta_comp_mul_self G)

theorem sqr_sub_two_mem : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], QuasiSeparated G.hom → ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2 := by
  intro S G _ hqs s π ε m hd f hf
  haveI := hqs
  obtain ⟨hπ, hε, hm⟩ := GlobalTheory.T.groupSchemeUnitStalkData_germ S G s π ε m hd
  have he : unitSec G ≫ G.hom = 𝟙 S := sec_hom η[G]
  obtain ⟨U₀, hU₀, g, rfl⟩ := G.left.presheaf.germ_exist f
  have hsq : sqr G (unitSec G s) = unitSec G s := by rw [← Scheme.Hom.comp_apply, unitSec_comp_sqr]
  have hb : G.hom (unitSec G s) = s := by rw [← Scheme.Hom.comp_apply, he]; rfl
  obtain ⟨U₁, hU₁, hs₁, -⟩ := QCoh.exists_affine_mem_le (U := (⊤ : S.Opens)) s trivial
  obtain ⟨W₁, hW₁, hx₁, k₁⟩ := QCoh.exists_affine_mem_le
    (U := U₀ ⊓ sqr G ⁻¹ᵁ U₀ ⊓ G.hom ⁻¹ᵁ U₁) (unitSec G s)
    ⟨⟨hU₀, show sqr G (unitSec G s) ∈ U₀ by rw [hsq]; exact hU₀⟩,
      show G.hom (unitSec G s) ∈ U₁ by rw [hb]; exact hs₁⟩
  obtain ⟨U, hsU, -, -, c⟩ := GlobalTheory.Conormal.exists_isChart_inf he hU₁ hW₁ (k₁.trans inf_le_right) hx₁
    (show s ∈ (⊤ : S.Opens) from trivial)
  have kW : W₁ ⊓ G.hom ⁻¹ᵁ U ≤ U₀ := inf_le_left.trans (k₁.trans (inf_le_left.trans inf_le_left))
  have kS : W₁ ⊓ G.hom ⁻¹ᵁ U ≤ sqr G ⁻¹ᵁ U₀ :=
    inf_le_left.trans (k₁.trans (inf_le_left.trans inf_le_right))
  have hxW : unitSec G s ∈ W₁ ⊓ G.hom ⁻¹ᵁ U := c.le hsU
  have hU0 : U ≤ unitSec G ⁻¹ᵁ U₀ := c.le.trans ((unitSec G).preimage_mono kW)

  have a1 := cotMap_d (𝟙 G * 𝟙 G) (eta_comp_mul_self G) hU0 c.le kS g
  have a2 := cotMap_d (𝟙 G) (Category.comp_id _) hU0 c.le kW g
  have hmul := cotMap_mul (x := 𝟙 G) (y := 𝟙 G) (Category.comp_id η[G]) (Category.comp_id η[G]) (eta_comp_mul_self G)
  have key : GlobalTheory.Conormal.d he c.le ((sqr G).appLE U₀ _ kS g) =
      GlobalTheory.Conormal.d he c.le (resG G.left kW g) + GlobalTheory.Conormal.d he c.le (resG G.left kW g) := by
    have := congrArg (fun φ => φ.app U (GlobalTheory.Conormal.d he hU0 g)) hmul
    simp only at this
    exact (a1.symm.trans this).trans (congrArg₂ (· + ·) a2 a2)
  letI := c.algebra
  let h : Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) := (sqr G).appLE U₀ _ kS g - (resG G.left kW g + resG G.left kW g)
  have hz : AugCot.d (c.aug he) h = 0 := (c.augCotEquiv he).injective (by
    rw [c.augCotEquiv_d he, map_zero, map_sub, map_add, key, sub_self])
  rw [AugCot.d_eq_zero_iff] at hz
  let gW := G.left.presheaf.germ (W₁ ⊓ G.hom ⁻¹ᵁ U) (unitSec G s) hxW
  have g1 : gW ((sqr G).appLE U₀ _ kS g) = m (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g) :=
    (hm U₀ hU₀ _ hxW kS g).symm
  have g2 : gW (resG G.left kW g) = G.left.presheaf.germ U₀ (unitSec G s) hU₀ g :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have gh : gW h = m (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g) -
      2 * G.left.presheaf.germ U₀ (unitSec G s) hU₀ g := by
    simp only [h, map_sub, map_add, g1, g2, two_mul]
  have hf0 : ε (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g) = 0 := hf
  have hker : ∀ x, c.aug he x = 0 → ε (gW x) = 0 := by
    intro x hx
    have hx' : (unitSec G).appLE _ U c.le x = 0 := hx
    rw [hε _ hxW U hsU c.le x, hx', map_zero]
  have hmap : ∀ y ∈ RingHom.ker (c.aug he) ^ 2, gW y ∈ RingHom.ker ε ^ 2 := by
    intro y hy
    have := Ideal.mem_map_of_mem (ConcreteCategory.hom gW) hy
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 (RingHom.mem_ker.2 (hker x (RingHom.mem_ker.1 hx)))) 2 this
  have hεm : ε (m (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g)) = 0 := by
    rw [← g1, hε _ hxW U hsU c.le, GlobalTheory.Conormal.appLE_appLE (unitSec_comp_sqr G) kS c.le hU0,
      ← hε U₀ hU₀ U hsU hU0 g, hf0]
  have hεh : ε (gW h) = 0 := by rw [gh, map_sub, map_mul, hεm, hf0, mul_zero, sub_zero]
  have halg : gW (algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) = 0 := by
    have e1 : gW (algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) =
        π (S.presheaf.germ U s hsU (c.aug he h)) := (hπ U hsU _ hxW c.le_base _).symm
    have e2 : S.presheaf.germ U s hsU (c.aug he h) = ε (gW h) := (hε _ hxW U hsU c.le h).symm
    rw [e1, e2, hεh, map_zero]
  rw [← gh, show gW h = gW (h - algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) +
      gW (algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) by rw [← map_add, sub_add_cancel],
    halg, add_zero]
  exact hmap _ hz
end GlobalTheory.Nef
