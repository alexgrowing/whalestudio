import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingComplexEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFamilyPullbackFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFamilyPullbackSecondStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LatJet

theorem jet_pi_tau {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (J' : JetRing R' I n) (τ : J.B →+* J'.B)
    (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) : J'.π.comp τ = σ.comp J.π := by
  ext x; simp only [RingHom.comp_apply, J.π_eq, J'.π_eq, hτ]

theorem jet_pi_alg {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) :
    J.π.comp (algebraMap R J.B) = RingHom.id R := by
  ext r
  simp only [RingHom.comp_apply, RingHom.id_apply, J.π_eq, Algebra.algebraMap_eq_smul_one, map_smul, ← J.one]
  simp

theorem family_bc (H : GlobalTheory.Published.AbelianDeRham) {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (J' : JetRing R' I n) {X₀ : Obj F 𝔠 (Sp R)} {δ₀ : X₀.DetGen}
    {N : I → Module.End R (HdR X₀.A)} (Y : Family J X₀ δ₀ N) {X₁ : Obj F 𝔠 (Sp R')} {δ₁ : X₁.DetGen}
    {N₁ : I → Module.End R' (HdR X₁.A)} {p : X₁.A.left ⟶ X₀.A.left} (hp : X₁.IsPullBy X₀ (spMap σ) p)
    (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 R') (𝟙 _) X₁.A σ (spMap σ) p) (hδ : Obj.DetCorr σ p δ₀.1 δ₁.1)
    (hN : ∀ i x₀ x, m.Corr x₀ x → m.Corr (N i x₀) (N₁ i x)) (τ : J.B →+* J'.B)
    (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) (hτdp : IsDPMorphism J.κ J'.κ τ) :
    ∃ (Y' : Family J' X₁ δ₁ N₁) (q : Y'.X'.A.left ⟶ Y.X'.A.left),
      Y'.X'.IsPullBy Y.X' (spMap τ) q ∧ Obj.DetCorr τ q Y.δ'.1 Y'.δ'.1 := by
  obtain ⟨Z', q, hq⟩ := Obj.exists_isPullBy Y.X' (spMap τ)
  have e1 : spMap σ ≫ spMap J.π = spMap J'.π ≫ spMap τ := by
    rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, jet_pi_tau σ J J' τ hτ]
  have h1 := hp.comp Y.pull
  rw [e1] at h1
  obtain ⟨i', hi', hi'q⟩ := h1.cancel hq
  obtain ⟨δ', hδ', -⟩ := hq.existsUnique_detGen τ Y.δ'
  have hb : 𝟙 (Sp R') = spMap J'.π ≫ spMap (algebraMap R' J'.B) := by
    rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, jet_pi_alg]; exact (Spec.map_id _).symm
  have mor' : GrpMor (dp0 R') (𝟙 _) X₁.A J'.κ (spMap J'.π) X₁.A (algebraMap R' J'.B) (𝟙 _)
      (Over.Hom.left (𝟙 X₁.A)) := GrpMor.of_hom (isDPMorphism_of_eq_bot _ rfl _ _) hb (𝟙 X₁.A)
  exact ⟨{ X' := Z', i := i', pull := hi', mor := mor', δ' := δ'
           fil := GlobalTheory.T.jet_family_pullback_first H σ J J' Y hp m hN τ hτ hτdp hq hi' hi'q mor'
           gen := GlobalTheory.T.jet_family_pullback_second H σ J J' Y hp m hN τ hτ hτdp hq hi' hi'q mor' δ₁ hδ δ' hδ' }, q, hq, hδ'⟩

theorem jetBC_of_grothendieckDeformation_abelianDeRham : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → JetBC := by
  intro _ H E _ _ _ I _ 𝔠 φ L R _ _ _ σ n J J' X₀ δ₀ N Y T hT
  obtain ⟨p, m, hp, hδ, hN⟩ := hT
  obtain ⟨τ, hτ, hτdp⟩ := GlobalTheory.T.jet_ring_complex_embedding σ J J'
  obtain ⟨Y', q, hq, hδ'⟩ := family_bc H σ J J' Y hp m hδ hN τ hτ hτdp
  exact ⟨Y', τ, q, hτ, hq, hδ'⟩

end GlobalTheory.LatJet
