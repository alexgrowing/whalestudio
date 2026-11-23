import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieEigenbasisGenericFibreCmTripleStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.BarEqOfLamEqMultiplier
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHomsStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommonDenominatorOfValuationLeOne
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmHostRootNegDiscriminantNeNegSelf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilPairingIffOfCubeLBPairingIsoStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRosatiActionWeilPairingBalancedTripleStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMetrisedLineOfLieVectorStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignatureStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRingStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MapRtEqNegIff
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.LamF

theorem prod_ofFn_sum {M : Type} [Monoid M] {p q : ℕ} (f : Fin p ⊕ Fin q → M) :
    (List.ofFn fun i : Fin (p + q) => f (finSumFinEquiv.symm i)).prod =
      (List.ofFn fun i => f (Sum.inl i)).prod * (List.ofFn fun i => f (Sum.inr i)).prod := by
  rw [List.ofFn_add, List.prod_append]
  congr 2
  · congr 1
    funext i
    exact congrArg f (finSumFinEquiv_symm_apply_castAdd i)
  · congr 1
    funext i
    exact congrArg f (finSumFinEquiv_symm_apply_natAdd i)

theorem lamEq_adj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (a : 𝓞 E) : LamEq t.PP.L (t.act.act a) (𝟙 t.G) t.PP.L (𝟙 t.G) (t.act.act (H.bar a)) := by
  have := t.adj a
  unfold LamEq
  rw [Category.comp_id, Category.comp_id]
  exact this

theorem exists_lamObjGood_of_cmObj : Out.SecTwistSt → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l), (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (La : ℝ), (∀ τ, τ ∈ psiSet H ↔ labK c K τ (H.rt : E) = (ρ : K)) → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → ∀ (xB : KeyIn K) (φB : xB.P.A.left ⟶ X.B.pol.A.left), IsFibreOf X.B.pol xB (gmap K) φB → ∃ (oa : X.B.pol.OAct (𝓞 E)) (oaΨ : (X.A true).pol.OAct (𝓞 E)) (oa' : (X.A false).pol.OAct (𝓞 E)) (xΨ x' : KeyIn K) (φΨ : xΨ.P.A.left ⟶ (X.A true).pol.A.left) (φ' : x'.P.A.left ⟶ (X.A false).pol.A.left) (τΨ : Fin xΨ.P.g ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}) (τ' : Fin x'.P.g ≃ {τ : E →+* ℂ // τ (H.rt : E) ≠ H.rt0}) (ℓΨ : Fin xΨ.P.g → MLine K) (ℓ' : Fin x'.P.g → MLine K) (Tl LamL : MLine K), oa.act = X.B.t.act.act ∧ oaΨ.act = (X.A true).t.act.act ∧ oa'.act = (X.A false).t.act.act ∧ LamObjGood (LamObj.mk (c := c) (nΨ := p) (n' := q) K X.B.pol oa (X.A true).pol oaΨ (X.A false).pol oa' (fun i => X.φ (Sum.inl i)) (fun i => X.φ (Sum.inr i)) (fun i => X.hh (Sum.inl i)) (fun i => X.hh (Sum.inr i)) xB xΨ x' φB φΨ φ' τΨ τ' ℓΨ ℓ' Tl LamL) (Module.finrank ℚ E / 2) La := by
  intro hS hU hL hX E _ _ _ _ H l c hstar K _ _ _ ρ σ₁ p q X La hρ hLa xB φB hB
  obtain ⟨hbij, -, -, ρ', -, h₁, h₂, hc, -⟩ := labK_spec E H l c K
  have hfpos : 0 < Module.finrank ℚ E / 2 := by
    have e := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at e
    have : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  have hρρ : ρ' = ρ := by
    have : Nonempty (psiSet H) := (Nat.card_pos_iff.1 (hc ▸ hfpos)).1
    obtain ⟨τ, hτ⟩ := this
    exact Subtype.ext (((h₁ τ).1 hτ).symm.trans ((hρ τ).1 hτ))
  subst hρρ
  obtain ⟨oa, hoa, hR⟩ := GlobalTheory.T.exists_rosatiAction_weilPairing_balanced_triple hL E H hstar K X.B
  obtain ⟨oaΨ, hoaΨ, hRΨ⟩ := GlobalTheory.T.exists_rosatiAction_weilPairing_balanced_triple hL E H hstar K (X.A true)
  obtain ⟨oa', hoa', hR'⟩ := GlobalTheory.T.exists_rosatiAction_weilPairing_balanced_triple hL E H hstar K (X.A false)
  obtain ⟨xΨ, φΨ, τΨ, hFΨ, hgΨ, hTΨ⟩ := GlobalTheory.T.exists_lie_eigenbasis_genericFibre_cmTriple hS hL E H K (X.A true) oaΨ (psiSet H) (labK c K) ρ' hoaΨ hbij
    X.ρ_sq hρ X.typeP
  obtain ⟨x', φ', τ', hF', hg', hT'⟩ := GlobalTheory.T.exists_lie_eigenbasis_genericFibre_cmTriple hS hL E H K (X.A false) oa' (psiSet H)ᶜ (labK c K) (-ρ') hoa' hbij
    (by rw [neg_sq, X.ρ_sq]) h₂ ((hasType_neg_iff E H _ _ _ ρ' 0 1 X.ρ_sq).1 X.typeM)
  choose ℓΨ hℓΨ using GlobalTheory.T.exists_metrised_line_of_lieVector hS hU hL K _ xΨ φΨ hFΨ
  choose ℓ' hℓ' using GlobalTheory.T.exists_metrised_line_of_lieVector hS hU hL K _ x' φ' hF'
  obtain ⟨Tl, LamL, k₁, k₂, k₃, k₄, k₅⟩ := GlobalTheory.LamF.exists_keyLines hS hU hL hX K _ xB φB hB
  have pB := (isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) _ xB φB).1 hB
  have pΨ := (isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) _ xΨ φΨ).1 hFΨ
  have p' := (isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) _ x' φ').1 hF'
  have gB : X.B.g = Module.finrank ℚ E / 2 * (p + q) :=
    (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ' X.B ⟨xB.P, φB, pB, xB.v, xB.basis⟩ p q X.split X.typeB X.ρ_sq).2.2.2.1
  have gA : ∀ b, (X.A b).g = Module.finrank ℚ E / 2 := fun b => by
    cases b
    · exact p'.1.symm.trans hg'
    · exact pΨ.1.symm.trans hgΨ
  have hlam : ∀ j, LamEq X.B.pol.L (X.φ j) (X.φ j) (X.A j.isLeft).pol.L ((X.A j.isLeft).t.act.act (X.hh j))
      (𝟙 (X.A j.isLeft).pol.A) := fun j =>
    (GlobalTheory.T.cubeLBPairingIso_iff_weilPairingCompatible_over_ring hL (𝓞 K) (X.A j.isLeft).pol (X.A j.isLeft).pol X.B.pol (X.A j.isLeft).pol _ _ _ _
      (X.lin j).isMonHom (X.lin j).isMonHom ((X.A j.isLeft).t.act.hom _) inferInstance ℂ
      (σ₁.comp (algebraMap (𝓞 K) K))).2 inferInstance
      (σ₁.injective.comp (IsFractionRing.injective (𝓞 K) K)) (X.weil j)
  have hsym : ∀ j, star (X.hh j) = X.hh j := fun j => (hstar _).trans
    (GlobalTheory.LamF.bar_eq_of_lamEq_multiplier hL E H K (X.A j.isLeft).pol X.B.pol (X.A j.isLeft).t.act (X.φ j) (X.hh j)
      (by change 1 ≤ (X.A j.isLeft).g; rw [gA]; exact hfpos) (lamEq_adj _) (hlam j))
  have hpol := fun j : Fin p ⊕ Fin q => GlobalTheory.T.weilPairing_iff_of_cubeLBPairingIso hL K (X.A j.isLeft).pol X.B.pol (X.φ j) ((X.A j.isLeft).t.act.act (X.hh j))
    (X.lin j).isMonHom ((X.A j.isLeft).t.act.hom (X.hh j)) (hlam j)
  refine ⟨oa, oaΨ, oa', xΨ, x', φΨ, φ', τΨ, τ', ℓΨ, ℓ', Tl, LamL, hoa, hoaΨ, hoa', ?_⟩
  refine ⟨hR, hRΨ, hR', hB, hFΨ, hF', hgΨ, hg', pB.1.trans gB, hTΨ, hT', fun i a => ?_, fun i a => ?_,
    ⟨fun i => (X.lin (Sum.inl i)).isMonHom, fun i => (X.lin (Sum.inr i)).isMonHom, ?_⟩,
    ⟨fun i => hsym (Sum.inl i), fun i => hsym (Sum.inr i), fun i => ?_, fun i => ?_⟩,
    ⟨fun i => hLa (Sum.inl i), fun i => hLa (Sum.inr i)⟩, hℓΨ, hℓ', k₁, k₂, k₃, k₄, k₅⟩
  · dsimp only
    rw [hoa, hoaΨ]
    exact (X.lin (Sum.inl i)).comm a
  · dsimp only
    rw [hoa, hoa']
    exact (X.lin (Sum.inr i)).comm a
  · refine GlobalTheory.T.exists_inverse_isogeny_sum_of_cm_homs hU hL hX K σ₁ (X.A true).pol (X.A false).pol X.B.pol p q _ _
      (fun i => (X.lin (Sum.inl i)).isMonHom) (fun i => (X.lin (Sum.inr i)).isMonHom) ?_ fun y => ?_
    · change X.B.g = p * (X.A true).g + q * (X.A false).g
      rw [gB, gA, gA]
      ring
    · obtain ⟨x, hx⟩ := X.onto y
      exact ⟨fun i => x (Sum.inl i), fun i => x (Sum.inr i), hx.trans (prod_ofFn_sum fun j => x j ≫ X.φ j)⟩
  · dsimp only
    rw [hoaΨ]
    exact hpol (Sum.inl i)
  · dsimp only
    rw [hoa']
    exact hpol (Sum.inr i)

end GlobalTheory.LamF
end
