import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSpecAffineOpenFunctionsBijectiveStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
open GlobalTheory.Conormal

namespace GlobalTheory.LieVB

variable {O : Type} [CommRing O]

theorem surjective_sec_epsZero : Function.Surjective (sec (epsZero O)) := by
  intro t
  have hs : Function.Surjective (TrivSqZeroExt.fstHom O O O).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have ht : (t : PrimeSpectrum (DualNumber O)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom O O O).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro a ha
    have ha : a.fst = 0 := ha
    have h : a * a = 0 := by ext <;> simp [ha]
    have := (t : PrimeSpectrum (DualNumber O)).isPrime
    exact (this.mem_or_mem (h ▸ Ideal.zero_mem _)).elim id id
  exact ht

theorem appLE_sec_epsZero_epsFn {V : (Sp O).Opens} {T : (specO O (DualNumber O)).left.Opens}
    (h : V ≤ sec (epsZero O) ⁻¹ᵁ T) :
    (sec (epsZero O)).appLE T V h (resG _ le_top (epsFn O)) = 0 := by
  have e : (sec (epsZero O)).appLE ⊤ ⊤ (le_preimage_top _ _) (epsFn O) = 0 :=
    congr($(Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (TrivSqZeroExt.fstHom O O O).toRingHom)) DualNumber.eps).symm.trans
      (map_zero (Scheme.ΓSpecIso (.of O)).inv.hom)
  rw [GlobalTheory.DualPull.appLE_resG, ← GlobalTheory.DualPull.resG_appLE _ le_top (le_preimage_top _ _), e,
    map_zero]

variable {G : Over (Sp O)} [GrpObj G]

theorem sec_epsZero_comp (x : LieG G) : sec (epsZero O) ≫ x.1.left = unitSec G :=
  congrArg (·.left) (epsZero_comp x)

theorem preimage_le_of_lieG (x : LieG G) {U : (Sp O).Opens} {W : G.left.Opens}
    (h : U ≤ unitSec G ⁻¹ᵁ W) : (specO O (DualNumber O)).hom ⁻¹ᵁ U ≤ x.1.left ⁻¹ᵁ W := by
  intro t ht
  obtain ⟨s, rfl⟩ := surjective_sec_epsZero t
  have h₁ : s ∈ (sec (epsZero O) ≫ (specO O (DualNumber O)).hom) ⁻¹ᵁ U := ht
  rw [sec_hom] at h₁
  have h₂ := h h₁
  rw [← sec_epsZero_comp x] at h₂
  exact h₂

theorem appLE_lieG (x : LieG G) {U : (Sp O).Opens} (hU : IsAffineOpen U) {W : G.left.Opens}
    (h : U ≤ unitSec G ⁻¹ᵁ W) (f : Γ(G.left, W)) :
    x.1.left.appLE W _ (preimage_le_of_lieG x h) f =
      (specO O (DualNumber O)).hom.appLE U _ le_rfl ((unitSec G).appLE W U h f) +
        (specO O (DualNumber O)).hom.appLE U _ le_rfl
          (GlobalTheory.VB.dualApp (tangent x) le_top (dUnit G h f)) * resG _ le_top (epsFn O) := by
  obtain ⟨⟨a, b⟩, e⟩ := (GlobalTheory.T.dualNumberSpec_affineOpen_functions_bijective O U hU).2 (x.1.left.appLE W _ (preimage_le_of_lieG x h) f)
  have hV : U ≤ sec (epsZero O) ⁻¹ᵁ (specO O (DualNumber O)).hom ⁻¹ᵁ U :=
    (le_preimage_of_comp (sec_hom (epsZero O))).2 le_rfl
  have hb := dualApp_tangent_dUnit x h f hV le_rfl (preimage_le_of_lieG x h) a b e.symm
  have ha : (unitSec G).appLE W U h f = a := by
    have e' := congrArg ((sec (epsZero O)).appLE _ U hV) e
    simp only [map_add, map_mul] at e'
    rw [appLE_sec_epsZero_epsFn, mul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl,
      GlobalTheory.LB.resG_self, appLE_appLE (sec_epsZero_comp x) _ _ h] at e'
    exact e'.symm
  rw [ha, hb]
  exact e.symm

theorem tangent_injective (O : Type) [CommRing O] (G : Over (Sp O)) [GrpObj G] :
    Function.Injective (tangent : LieG G → Γ(Lie G, ⊤)) := by
  intro x y hxy
  refine Subtype.ext (Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun t => ?_))
  obtain ⟨U, W, hU, -, c⟩ := exists_isChart (sec_hom (MonObj.one (X := G))) (V := ⊤)
    (x := (specO O (DualNumber O)).hom t) trivial
  have hT : IsAffineOpen ((specO O (DualNumber O)).hom ⁻¹ᵁ U) := c.affine_base.preimage _
  have e : x.1.left.appLE W _ (preimage_le_of_lieG x c.le) =
      y.1.left.appLE W _ (preimage_le_of_lieG y c.le) := by
    ext f
    exact (appLE_lieG x c.affine_base c.le f).trans
      (hxy ▸ (appLE_lieG y c.affine_base c.le f).symm)
  refine ⟨(specO O (DualNumber O)).hom ⁻¹ᵁ U, hU, ?_⟩
  rw [← cancel_epi hT.isoSpec.inv, ← Category.assoc, ← Category.assoc, hT.isoSpec_inv_ι,
    ← c.affine.SpecMap_appLE_fromSpec _ hT (preimage_le_of_lieG x c.le),
    ← c.affine.SpecMap_appLE_fromSpec _ hT (preimage_le_of_lieG y c.le), e]

end GlobalTheory.LieVB
