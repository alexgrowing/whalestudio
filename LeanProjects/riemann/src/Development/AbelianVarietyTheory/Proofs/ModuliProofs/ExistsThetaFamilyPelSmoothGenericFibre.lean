import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaObjectFamilyOpenClosureStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteTypeOfIsQProjOverAffineOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassUnitaryFullLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaFamIsPEL
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankTangentPELFamilyLeSymmetricDomainStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverIffLocallyOfFiniteTypeAndExistsIsAmpl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem ThetaFam.unram_of_mono {o : Type} [CommRing o] {g n N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {em : o →+* ℂ}
    {C : TObj g (N' ^ 2) J b (spMap em) → Prop} (F : ThetaFam n em C) {S : Scheme.{0}} (x : S ⟶ F.MM) [Mono x]
    {s : S ⟶ Sp o} (hs : x ≫ F.s = s) (t : TObj g (N' ^ 2) J b s) (ht : TMap t F.univ x) (K : Type) [Field K]
    (y : Sp (DualNumber K) ⟶ S) (t' : TObj g (N' ^ 2) J b (y ≫ s)) (hy : y ≫ s = constPt y ≫ s)
    (h₁ : TMap t' t y) (h₂ : TMap t' t (constPt y)) : y = constPt y := by
  subst hs
  have hc : constPt (y ≫ x) = constPt y ≫ x := by simp [constPt]
  rw [← cancel_mono x, ← hc]
  have key : ∀ (s' : Sp (DualNumber K) ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s'), s' = (y ≫ x) ≫ F.s →
      TMap t' F.univ (y ≫ x) → TMap t' F.univ (constPt (y ≫ x)) → y ≫ x = constPt (y ≫ x) := by
    rintro _ t' rfl h h'
    exact F.unram K (y ≫ x) t' (by rw [hc, Category.assoc, Category.assoc, hy]) h h'
  refine key _ t' (Category.assoc _ _ _).symm ?_ ?_
  · exact ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t t').2 x y ht).1 h₁
  · rw [hc]
    exact ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t t').2 x (constPt y) ht).1 h₂

theorem exists_thetaFam_isPEL_smooth : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∃ (F : ThetaFam n em (PELClass (b := b) D a bas ρ em)) (τ : SAB H F.MM), IsPEL D a bas ρ F.univ τ ∧ SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap o (FractionRing o)))) := by
  intro h1 h2 hcrit hgen hU E _ _ _ H D g J _ a w w' bas hD hbas hw hw' ha n hn hodd
  obtain ⟨Mat, κ, hcl⟩ := GlobalTheory.T.isGoodThetaComplexClass_unitaryFullLevel h1 h2 hgen hU E H D g J a w w' bas hD hbas hw hw' ha
  obtain ⟨j₁, hj₁⟩ := hcl n hn hodd
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.nonempty_thetaObject_family_open_closure h1 h2 hcrit g J Mat κ n w w' hn hodd
  refine ⟨max j₁ j₂, fun j hj o _ b em ρ hρ hb => ?_⟩
  have hgood := hj₁ j (le_of_max_le_left hj) _ rfl o b em ρ hρ
  obtain ⟨F⟩ := hj₂ j (le_of_max_le_right hj) o b em _ _ hb hgood
  obtain ⟨τ, hτ⟩ := GlobalTheory.thetaFam_isPEL h1 h2 hgen E H D g J a w w' bas hD hbas hw hw' ha n _ o b em ρ hρ hb F
  refine ⟨F, τ, hτ, ThetaFam.smooth_genericFibre h1 h2 g n _ J Mat κ w w' o b em _ _ F hb hgood ?_⟩
  intro R _ _ _ _ _ x hx hs hem
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull o g _ J b _ _ F.s _ x F.univ hs
  obtain ⟨τ', hτ'⟩ := GlobalTheory.PELPull.isPEL_pull E H D g _ J a bas o b ρ _ _ F.s _ x F.univ t τ hs ht hτ
  have hρ2 : ρ ^ 2 = -(H.d : o) := hb.2.2 (by rw [map_pow, hρ, H.sqrt_neg_disc_sq, map_neg, map_natCast])
  have hft : Algebra.FiniteType o R := by
    have := ((GlobalTheory.isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB F.s).1 F.qproj).1
    have h : LocallyOfFiniteType (spMap (algebraMap o R)) := hs ▸ inferInstance
    exact RingHom.finiteType_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h)
  exact GlobalTheory.T.finrank_tangent_PEL_family_le_symmetricDomain h1 h2 hgen hU E H D g J a w w' bas hD hbas hw hw' ha _ o b ρ R t τ' hρ2 hτ' hft
    (fun y t' hy h₁ h₂ => F.unram_of_mono x hs t ht ℂ y t' hy h₁ h₂)

end GlobalTheory.ZM
