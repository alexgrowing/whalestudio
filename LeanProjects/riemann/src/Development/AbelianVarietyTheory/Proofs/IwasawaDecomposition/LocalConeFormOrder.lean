import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelFormAlongDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegVert
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeightOnePrimeEtaleStalkComapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteDvrOfLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConeRegularPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalHeightOneLocalizationStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.DivDescent

theorem span_map_eq_pow_of_height_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)), HasCones Cn Z → HasLinForms Cn φ → ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)) (_ : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R) t) {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (ℓ : LinearMap.BilinForm ℤ P.D.toPre.X →ₗ[ℤ] ℤ), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → Cn P.D.toPre.X m γ → InCone P.D.toPre γ → (∀ be : LinearMap.BilinForm ℤ P.D.toPre.X, (∀ y z, be y z = be z y) → ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal be = ∑ i, c i • toReal (γ i) → 0 ≤ ℓ be ∧ (ℓ be : ℝ) = φ.evalZ be) → ∀ h : R, h ≠ 0 → (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (g : R →+* W) (be : LinearMap.BilinForm ℤ P.D.toPre.X), (∀ y z, be y z = be z y) → FormAt P.D.toPre g ϖ be → ∃ n : ℕ, (n : ℤ) = ℓ be ∧ Associated (g h) (ϖ ^ n)) → ∀ q : Ideal (Z.X.presheaf.stalk (ξ (closedPoint R))), q ≠ ⊥ → ∃ n : ℕ, ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → Q.comap (Scheme.stalkClosedPointTo ξ).hom = q → (Ideal.span {h}).map (algebraMap R (Localization.AtPrime Q)) = (q ^ n).map ((algebraMap R (Localization.AtPrime Q)).comp (Scheme.stalkClosedPointTo ξ).hom) := by
  intro E _ _ _ H D l Xo c Z Cn φ hC hL R _ _ _ ξ t mξ P m γ ℓ hCN hEt hFU hTI hCn hIn hℓ h hh0 hh q hq
  obtain ⟨cq, hcq⟩ := GlobalTheory.T.local_cone_regular_point Z Cn φ hC ξ t mξ P hCN hEt hFU hTI q hq
  refine ⟨⌊cq⌋₊, fun Q _ hQ1 hQq => ?_⟩
  have hCN' := hCN
  obtain ⟨hNo, hIC, -, hch⟩ := hCN'
  have hQ0 : Q ≠ ⊥ := fun e => by rw [e, Ideal.height_bot] at hQ1; exact zero_ne_one hQ1
  have hdvr : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    ((IsDiscreteValuationRing.TFAE (Localization.AtPrime Q)
      (IsLocalization.AtPrime.not_isField R hQ0 _)).out 0 1).2 (ReciprocityTheory.ChartRestriction.G.T0.regVert_valuationRing Q hQ1)
  obtain ⟨W, _, _, _, ϖ, g, hW, hϖ, hinj, hunit, hπ⟩ := GlobalTheory.T.exists_complete_dvr_of_localization Q hdvr
  let gam : FractionRing R →+* FractionRing W := IsFractionRing.map (j := g) hinj
  have hgam : ∀ r, gam (algebraMap R _ r) = algebraMap W _ (g r) := fun r => IsLocalization.map_eq _ _
  obtain ⟨be, hbe, hfa⟩ := GlobalTheory.ChartForm.exists_balanced_formAt E H R t P hCN W hW ϖ hϖ g gam hgam
  have hsym : ∀ y z, be y z = be z y := ((mem_levelForms).1 hbe).1
  obtain ⟨n, hn, hass⟩ := hh W hW ϖ hϖ g be hsym hfa
  obtain ⟨cc, hcc0, hccsum⟩ := hIn W hW ϖ hϖ g be hsym hfa
  have h2 := (hℓ be hsym cc hcc0 hccsum).2
  have h3 := hcq Q hQ1 hQq W hW ϖ hϖ g hinj hunit hπ be hsym hfa
  have hnc : (n : ℝ) = cq := by rw [← h3, ← h2, ← hn]; norm_cast
  have hnf : ⌊cq⌋₊ = n := by rw [← hnc, Nat.floor_natCast]
  subst hQq
  rw [hnf, Ideal.map_pow, GlobalTheory.T.height_one_prime_etale_stalk_comap Z ξ hCN hEt hFU Q hQ1 hq]
  exact GlobalTheory.T.principal_height_one_localization Q hdvr ϖ hϖ g hinj hunit hπ h hh0 n hass

end GlobalTheory.DivDescent
