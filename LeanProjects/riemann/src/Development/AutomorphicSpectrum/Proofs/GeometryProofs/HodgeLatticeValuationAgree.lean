import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeGenericAgree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsConnectedZeroSetOfIsProperStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineDegreeSpecialFibreStatement
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.COrder

theorem order_on_component : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (p q : ℕ) (𝓗 : HodgeLat L ρ bar (p + q)) (σ σ' : E →+* Ω) (v : Fin p → V) (w : Fin q → V) (u : Fin (p + q) → V × Module.Dual Ω V) (α κ : Ω) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → NormalCpt ξ → ConstClosed O Ω → (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O Ω).range) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω w → Submodule.span Ω (Set.range w) = HT.eigSp ρ σ' → IsAdapted 𝓗.ρH σ v w u → 𝓗.DegZero σ (algebraMap O Ω ϖ) → IsLineGenOn (L.inter (HT.eigSp ρ σ)) (L.inter (HT.eigSp ρ σ')) p q (α • exteriorPower.ιMulti Ω p v) (κ • exteriorPower.ιMulti Ω q w) (genFibre O ξ) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ x : Cpt ξ, OrderAt (detLat (𝓗.quot σ) u) (α / κ) (algebraMap O Ω ϖ) M a x := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar p q 𝓗 σ σ' v w u α κ O _ _ _ _ s _ ϖ hϖ hinj hs hg hn hc hσ h1 h2
    hv hvs hw hws had hdz hgen
  obtain ⟨hu, husp, -⟩ := AdaptedSpan.adapted_span X Ω ξ E V L ρ bar p q (p + q) 𝓗 σ σ' v w u h1 h2 hv hvs hw hws had
  have hO : ∀ (x : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ x := fun x o =>
    (ConstReg.regular_const X Ω ξ O s hs x o).1
  have hσr : ∀ (x : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ x := fun x a => by
    obtain ⟨o, ho⟩ := hσ a
    exact ho ▸ hO x o
  have hinv : ∀ x ∈ genFibre O ξ, ∀ b : 𝓞 E, (σ (b : E))⁻¹ ∈ regAt ξ x := fun x hx b => by
    obtain ⟨o, ho⟩ := hσ b
    rw [← ho]
    by_cases h0 : o = 0
    · rw [h0, map_zero, inv_zero]
      exact zero_mem _
    · exact (hx o h0).2.2
  refine GlobalTheory.T.line_degree_special_fibre X Ω ξ O s ϖ hϖ hinj hs hg hn (GlobalTheory.T.isConnected_zeroSet_uniformizer X Ω ξ O s ϖ hϖ hinj hs hg hc) _ _
    (𝓗.det_isVB σ hσr hu husp) (hdz u hu husp) fun x hx => ?_
  obtain ⟨ha, hb, hco⟩ := hgen
  have hα : α ≠ 0 := left_ne_zero_of_smul ha
  have hκ : κ ≠ 0 := left_ne_zero_of_smul hb
  refine (GenAgree.generic_agree X Ω ξ E V L ρ bar p q 𝓗 σ σ' v w u x (α / κ) hg h1 h2 (fun a => ?_)
    hv hvs hw hws had).2 ⟨div_ne_zero hα hκ, ?_⟩
  · obtain ⟨y, z, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
    have e : ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = (c : E) := fun _ => rfl
    rw [e, e, map_div₀, map_div₀, h1, h1, div_eq_mul_inv, div_eq_mul_inv]
    exact ⟨mul_mem (hσr x _) (hinv x hx _), mul_mem (hσr x _) (hinv x hx _)⟩
  · obtain ⟨a', b', ha', hb', hA, hB, e⟩ := hco x hx
    rw [one_mul] at e
    subst e
    refine ⟨a' * α, a' * κ, mul_ne_zero ha' hα, mul_ne_zero ha' hκ, by rw [hA, smul_smul], by rw [hB, smul_smul], ?_⟩
    field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.COrder
