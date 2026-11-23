import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsSeparateQuotientGenericFibreDescends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_separate_quotient_generic_fibre_descends : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [NumberField F] (σ : F →+* ℂ) (X X' W V : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral W] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (φ : X' ⟶ X) (q : X' ⟶ W) (sW : W ⟶ Sp F) (i : V ⟶ X) (ℓ : V ⟶ X'), IsProjOver sX → GeometricallyConnected sX → 1 ≤ n → IsProjOver (φ ≫ sX) → IsProjOver sW → IsFinite q → Surjective q → q ≫ sW = φ ≫ sX → IsOpenImmersion i → IsOpenImmersion ℓ → ℓ ≫ φ = i → letI := algebraΓOfHom sX; ∀ (K : CanonLB sX n) (δ N' B : LB X) (hδ : δ.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (N : LB W) (hN : N.IsLB) (m : ℕ), CechPic.pull q (cls N hN) = CechPic.pull φ (cls δ hδ) → IsNef F δ → IsBig F δ → IsNef F N' → (n + 1).choose 2 < m → cls B hB = m • cls δ hδ + cls N' hN' → ∀ (J : Type) [Fintype J] (v : J → (Sp ℂ ⟶ V)), Function.Injective v → (∀ j, v j ≫ i ≫ sX = spMap σ) → (∀ j j', v j ≫ ℓ ≫ q = v j' ≫ ℓ ≫ q) → (∃ j, ∀ s, (v j ≫ i) s = genericPoint X) → ∀ (k : J → (tens K.bundle B).ι) (hk : ∀ j, ⊤ ≤ (v j ≫ i) ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ), (∀ g : H0 sX (tens K.bundle B) ⊤, ∑ j, a j * H0.val (v j ≫ i) (k j) le_top (hk j) g = 0) → a = 0 := by
  first | exact @GlobalTheory.QuotSep.sections_separate_quotient_fibre | exact GlobalTheory.QuotSep.sections_separate_quotient_fibre | (intros; apply GlobalTheory.QuotSep.sections_separate_quotient_fibre <;> assumption)
