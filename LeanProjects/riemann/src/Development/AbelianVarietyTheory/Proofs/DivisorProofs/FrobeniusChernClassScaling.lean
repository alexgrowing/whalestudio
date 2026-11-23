import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkUniqueCharacterizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkPresentationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneCokernelKilledStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

namespace GlobalTheory.FrobRankOne

theorem isFrob_iso {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} [Fact p.Prime]
    {B : GlobalTheory.Vert.Model O} {F F₁ F₂ : B.X.Modules} (h₁ : IsFrob p F F₁) (h₂ : IsFrob p F F₂) :
    Nonempty (F₁ ≅ F₂) := by
  obtain ⟨h, ⟨e₁⟩⟩ := h₁
  obtain ⟨h', ⟨e₂⟩⟩ := h₂
  exact ⟨e₁ ≪≫ e₂.symm⟩

theorem ck_frob_rankOne : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (R R' : Pres B) (g : Γ(B.X, ⊤)), IsRootOfP p g p → R.r = 1 → Kills g R.mod → IsFrob p R.mod R'.mod → ∀ k : ℕ, R'.ck p k = ((p : ℚ) ^ k) • R.ck p k := by
  intro O _ _ _ p _ _ _ B hB R R' g hg hr hk hfr k
  obtain ⟨r, E, E', vb, vb', ψ, iso⟩ := R
  dsimp only at hr
  subst hr
  obtain ⟨F, F', hF, hF', χ, hχ, hfr', h1, h2, h3⟩ := GlobalTheory.T.rank_one_cokernel_killed O p B hB E E' vb vb' ψ g hg hk
  let R'' : Pres B := ⟨1, F, F', hF, hF', χ, hχ⟩
  have e := isFrob_iso hfr hfr'
  have hmod : R'.ck p k = R''.ck p k := GlobalTheory.T.ck_presentation_invariant O p B hB R' R'' e k
  rw [hmod]
  ext Q
  have a1 := ((GlobalTheory.T.ck_unique_characterization O p B hB F F' (GlobalTheory.Vert.Model.GenIso.ofHom χ) 1 k hF hF').2.2
    (GlobalTheory.Vert.Model.FlagPair.ofRankOne _ hF hF') Q)
  have a2 := ((GlobalTheory.T.ck_unique_characterization O p B hB E E' (GlobalTheory.Vert.Model.GenIso.ofHom ψ) 1 k vb vb').2.2
    (GlobalTheory.Vert.Model.FlagPair.ofRankOne _ vb vb') Q)
  simp only [Pres.ck, LinearMap.smul_apply, smul_eq_mul]
  rw [a1, a2]
  exact GlobalTheory.RootChernRules.ck_scale (Z := B.toITh p)
    ((GlobalTheory.Vert.Model.FlagPair.ofRankOne (GlobalTheory.Vert.Model.GenIso.ofHom ψ) vb vb').toFPair p)
    ((GlobalTheory.Vert.Model.FlagPair.ofRankOne (GlobalTheory.Vert.Model.GenIso.ofHom χ) hF hF').toFPair p) (p : ℚ)
    (fun i => by obtain rfl : i = 0 := Subsingleton.elim _ _; exact h1)
    (fun i => by obtain rfl : i = 0 := Subsingleton.elim _ _; exact h2)
    (fun i => by obtain rfl : i = 0 := Subsingleton.elim _ _; exact h3) k Q

end GlobalTheory.FrobRankOne
