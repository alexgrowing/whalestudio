import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem genPt_mem_cover : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (c : R), φ c ≠ 0 → ∀ (J : Type) (W : J → G.left.Opens), ⨆ i, W i = G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → ∃ i, ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ⁻¹ᵁ W i := by
  intro R _ G Ω _ _ φ x' hx c hc J W hW
  set K := FractionRing Ω
  have hK : (⊤ : (Sp K).Opens) ≤ (spMap (algebraMap Ω K) ≫ x') ⁻¹ᵁ (⨆ i, W i) := by
    rw [hW, ← Scheme.Hom.comp_preimage]
    rw [Category.assoc, hx]
    simp only [GlobalTheory.HeatV.bo, Scheme.affineBasicOpen_coe, Scheme.preimage_basicOpen_top]
    rw [Scheme.basicOpen_of_isUnit]
    have e : spMap (algebraMap Ω K) ≫ spMap φ = Spec.map (CommRingCat.ofHom ((algebraMap Ω K).comp φ)) := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e]
    have h1 := congrArg (fun f => f.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((algebraMap Ω K).comp φ)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    rw [← h1]
    refine IsUnit.map _ ?_
    refine isUnit_iff_ne_zero.mpr ?_
    intro h0
    exact hc ((IsFractionRing.injective Ω K) (by simpa using h0))
  obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
  have hp := hK (Set.mem_univ p)
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).mp hp
  refine ⟨i, fun q _ => ?_⟩
  have : q = p := Subsingleton.elim _ _
  subst this
  exact hi

end GlobalTheory
