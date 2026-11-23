import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulAFiniteFlatSurjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsEqPowOfTorsionCompEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTorsionMemClosureGenerators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomKillsTorsionOfComplexPointsOneEmbeddingStatement

set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.TorsGen

theorem exists_linear_pow_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (G : A.t.G ⟶ B.t.G),
    GlobalTheory.Serre.IsLinearHom A.t.act B.t.act G → ∀ m : ℕ, 0 < m →
    (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, x ^ m = 1 → x ≫ G = 1) →
    ∃ F : A.t.G ⟶ B.t.G, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act F ∧ F ^ m = G := by
  intro E _ _ _ H K _ _ σ A B G hG m hm hker
  have hGm := hG.isMonHom
  obtain ⟨_, hfl, hsu⟩ := GlobalTheory.PairKernel.mulA_finite_flat_surjective _ A.pol m hm
  have hc : IsCommMonObj A.t.G := A.ab.comm
  have hcB : IsCommMonObj B.t.G := B.ab.comm
  have hall := GlobalTheory.T.hom_kills_torsion_of_complexPoints_oneEmbedding E H K σ A B G hGm m hm hker
  obtain ⟨F, hF⟩ := GlobalTheory.DivisibleHom.exists_factor (A := A.t.G) m G hall
  have hFm : IsMonHom (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m ≫ F) := hF ▸ hGm
  have : IsMonHom F := GlobalTheory.DivisibleHom.isMonHom_of_factor m F
  refine ⟨F, ⟨this, fun c => ?_⟩, by rw [← hF, GlobalTheory.DivisibleHom.mulA_comp]⟩
  have := A.t.act.hom c
  have := B.t.act.hom c
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m)
  rw [← Category.assoc, GlobalTheory.DivisibleHom.mulA_comp, ← GlobalTheory.DivisibleHom.comp_mulA, Category.assoc, hF, hG.comm,
    ← Category.assoc, hF]

theorem gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (n : ℕ), 0 < n →
    ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
    y ∈ Submonoid.closure {w : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G |
      ∃ (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G) (f : (X.A true).t.G ⟶ X.B.t.G),
        x ^ n = 1 ∧ GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
        (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) ∧
        w = x ≫ f} := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X n hn y hy
  refine Submonoid.closure_mono ?_ (GlobalTheory.T.cm_torsion_mem_closure_generators E H hH K ρ σ₁ p X n hn y hy)
  rintro w ⟨m, x, z, hm, hx, hG, rfl⟩
  obtain ⟨F, hF, hFm⟩ := exists_linear_pow_eq E H K σ₁ (X.A true) X.B _
    (GlobalTheory.FlatCM.HomLat.isLinearHom_prod X z) m hm hG
  have := hF.isMonHom
  refine ⟨x ^ m, F, ?_, hF, ⟨m, hm, z, hFm⟩, ?_⟩
  · rw [← pow_mul, mul_comm, hx]
  · rw [← hFm, MonObj.comp_pow, MonObj.pow_comp]

end GlobalTheory.FlatCM.TorsGen

end
