import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

theorem crys_exists_corr : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' B B' : Type} [CommRing R] [CommRing R'] [CommRing B] [CommRing B'] {K : Ideal B} {K' : Ideal B'}
    (κ : DividedPowers K) (κ' : DividedPowers K'), IsNilDP κ → IsNilDP κ' →
    ∀ (π : B →+* R) (π' : B' →+* R'), Function.Surjective π → Function.Surjective π' →
    RingHom.ker π = K → RingHom.ker π' = K' → ∀ (τ : B →+* B') (σ : R →+* R')
    {X₀ : Obj F 𝔠 (Sp R)} {Z : Obj F 𝔠 (Sp B)} {i : X₀.A.left ⟶ Z.A.left}, X₀.IsPullBy Z (spMap π) i →
    ∀ {X₁ : Obj F 𝔠 (Sp R')} {Z' : Obj F 𝔠 (Sp B')} {i' : X₁.A.left ⟶ Z'.A.left}, X₁.IsPullBy Z' (spMap π') i' →
    ∀ {q : Z'.A.left ⟶ Z.A.left}, Z'.IsPullBy Z (spMap τ) q → ∀ {p : X₁.A.left ⟶ X₀.A.left}, i' ≫ q = p ≫ i →
    ∀ (M : GrpMor κ (spMap π) X₀.A κ' (spMap π') X₁.A τ (spMap σ) p) (d : Crys κ (spMap π) X₀.A),
    ∃ d', M.Corr d d' := by
  intro H F _ _ 𝔠 R R' B B' _ _ _ _ K K' κ κ' hκ hκ' π π' hπ hπ' hK hK' τ σ X₀ Z i hi X₁ Z' i' hi'
    q hq p hpq M d
  letI := τ.toAlgebra
  have hbc := (H.2.2.1 B Z.A _ Z.ab Z.dim B' Z'.A q hq.grp).1
  obtain ⟨e', he'⟩ := hbc.exists (crysToDR κ hi.grp d)
  obtain ⟨d', hd'⟩ :=
    (GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective H.2.2.2.1 Z'.ab Z'.dim hκ' hπ' hK' hi'.grp).2 e'
  refine ⟨d', fun c ↦ ?_⟩
  obtain ⟨c₁, rfl⟩ := (H.2.2.2.1 B Z.A _ Z.ab Z.dim K κ hκ R π hπ hK X₀.A i hi.grp).2 c
  have k := (liftMor κ hi.grp).comp M
  rw [GrpMor.pull_pull (liftMor κ hi.grp) M k (fun _ ↦ rfl) rfl c₁,
    ← GrpMor.pull_pull (GlobalTheory.Published.AbelianDeRham.bcMor hq.grp) (liftMor κ' hi'.grp) k (fun _ ↦ rfl) hpq c₁,
    ← crysToDR_apply κ' hi'.grp, hd', he']
  rfl

end GlobalTheory.LatJet
