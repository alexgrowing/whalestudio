import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem IsHom.valF_appLE {o Ω Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field Ω'] [Algebra o Ω']
    {M : RatModel o Ω} {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'} {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f)
    {U : M.Z.Opens} {V : M'.Z.Opens} (e : V ≤ f ⁻¹ᵁ U) (hV : (V : Set M'.Z).Nonempty) (g : Γ(M.Z, U)) :
    M'.res V hV ((f.appLE U V e).hom g) = φ (valF M.pt U g) := by
  rw [res_apply, ← hf.valF_app ⟨_, e hV.some_mem⟩ g]
  exact (valR_appLE M'.pt f e (M'.top_le_preimage_pt hV) g).trans (valR_comp M'.pt f U g)

theorem crd_mulVec_of_hasVal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N N' : RatModel o Ω') (a : N'.Z ⟶ N.Z) (q : N'.Z ⟶ M.Z) (W : M.Z.Opens) (H : LB N.Z) (d : H.ι → Ω') (J : Type) [Fintype J] (st : J → H.Sec) (σ : J → (H.pull a).Sec) (t u : J → Ω') (c : Matrix J J Γ(M.Z, W)), N.IsHom N' (AlgHom.id o Ω') a → M.IsHom N' φ q → (∀ z, q z ∈ W) → (∀ j, N.HasVal d (st j) (t j)) → (∀ j, N'.HasVal (H := H.pull a) (fun k => d (k PUnit.unit)) (σ j) (u j)) → t = (c.map fun g => φ (valF M.pt W g)).mulVec u → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ N'.Z) (w : J → R), Crd (H.pull a) σ x w → Crd H st (x ≫ a) ((c.map (valR (x ≫ q) W)).mulVec w) := by
  intro o Ω _ _ _ M Ω' _ _ φ N N' a q W H d J _ st σ t u c ha hq hW ht hu htu R _ x w hx
  obtain ⟨k, e, hk, hw⟩ := hx
  have ea : (H.pull a).U k ≤ a ⁻¹ᵁ H.U (k PUnit.unit) := LB.wchart_le H _ k PUnit.unit
  have eq : (H.pull a).U k ≤ q ⁻¹ᵁ W := fun z _ => hW z
  refine ⟨k PUnit.unit, e, le_preimage_comp x a ea hk, fun i => ?_⟩
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  have hC : (((H.pull a).U k : N'.Z.Opens) : Set N'.Z).Nonempty := ⟨x y, hk (x := y) trivial⟩
  have key : (a.appLE _ _ ea).hom ((st i).f (k PUnit.unit)) =
      ∑ j, (q.appLE _ _ eq).hom (c i j) * (σ j).f k := by
    apply N'.res_injective _ hC
    rw [map_sum, ha.valF_appLE ea hC, ht i _ ⟨_, ea hC.some_mem⟩, htu]
    simp only [map_mul, hq.valF_appLE eq hC, AlgHom.id_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [res_apply, hu j k hC, mul_div_assoc]
  rw [← valR_appLE x a ea hk, key, valR_eq x _ hk, map_sum, Finset.mul_sum]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← valR_eq x _ hk, ← valR_eq x _ hk, valR_appLE x q eq hk, hw j, mul_left_comm]

end GlobalTheory.ZH.RatModel
end
