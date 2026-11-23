import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvrStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectFibreFromComplexCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELFromSiegel

theorem exists_cast {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S : Scheme.{0}} {s₁ s₂ : S ⟶ Sp o}
    (e : s₁ = s₂) (t : TObj g k J b s₁) :
    ∃ u : TObj g k J b s₂, ∀ (S' : Scheme.{0}) (s' : S' ⟶ Sp o) (t' : TObj g k J b s') (f : S ⟶ S'),
      TMap t t' f → TMap u t' f := by
  subst e
  exact ⟨t, fun _ _ _ _ h => h⟩

theorem fromC_comp {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' : Scheme.{0}} {s : S ⟶ Sp o}
    {s' : S' ⟶ Sp o} {em : o →+* ℂ} {C : TObj g k J b (spMap em) → Prop} {t : TObj g k J b s} {t' : TObj g k J b s'}
    {f : S' ⟶ S} (hs : s' = f ≫ s) (h : TMap t' t f) {K : Type} [Field K] {x : Sp K ⟶ S'} (hx : FromC em C t' x) :
    FromC em C t (x ≫ f) := by
  obtain ⟨K₀, _, β, i, j, t₀, tx, tc, h1, h2, h3, h4, h5, h6⟩ := hx
  have e : x ≫ s' = (x ≫ f) ≫ s := by rw [hs, Category.assoc]
  obtain ⟨u, hu⟩ := exists_cast e tx
  exact ⟨K₀, _, β, i, j, t₀, u, tc, h1, e ▸ h2,
    hu _ _ _ _ (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b S S' (Sp K) s s' _ t t' tx).2 f x h).1 h3), hu _ _ _ _ h4, h5, h6⟩

theorem dense_range_generic (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] :
    Dense (Set.range (spMap (algebraMap V K))) := by
  have h : DenseRange (PrimeSpectrum.comap (algebraMap V K)) := by
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V K)]
    exact bot_le
  exact h

theorem exists_isPEL_extension : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y) → ∀ (k : ℕ) (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (em : o →+* ℂ) (ρ : o) (ζ : B) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (s₁ : Sp V ⟶ Sp B) (s' : Sp K ⟶ Sp o) (s₁' : Sp K ⟶ Sp B) (c : SiegPre g k ζ s₁) (c' : SiegPre g k ζ s₁') (t' : TObj g k J b s') (τ' : SAB H (Sp K)), (∃ N' : ℕ, k = N' ^ 2) → em ρ = H.rt0 → ArBase em → s' = spMap (algebraMap V K) ≫ spMap β → c.Principal → SiegPB c' c (spMap (algebraMap V K)) → TSieg bas bas' t' c' → IsPEL D a bas ρ t' τ' → ∃ (t : TObj g k J b (spMap β)) (τ : SAB H (Sp V)), IsPEL D a bas ρ t τ ∧ TMap t' t (spMap (algebraMap V K)) := by
  intro hL hL2 hT E _ _ _ H D g J _ a w w' bas h1 hb hw hw' hcl bas' _ k o B _ _ b em ρ ζ V K _ _ _ _ _ _ _ β s₁ s' s₁'
    c c' t' τ' hk hρ hA hs hc hcc hS hP
  obtain ⟨N', rfl⟩ := hk
  obtain ⟨t, ht⟩ := GlobalTheory.T.siegel_extension_over_dvr hL hL2 g _ J D.La bas bas' o B b ζ V K β s₁ s' s₁' c c' t' hs hc hcc hS
  have hF := fromC_comp hs ht
    (GlobalTheory.T.pelObject_fibre_from_complex_charZero hL hL2 E H D g J a w w' bas h1 hb hw hw' hcl N' o b em ρ hρ hA _ s' t' τ' hP K (𝟙 _))
  rw [Category.id_comp] at hF
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_isPELTriple_of_dense_fibres hL hL2 hT E H D g J a bas w w' h1 hb hw hw' hcl _ o b em ρ (Sp V) (spMap β) t hρ hA.2.2
    ((dense_range_generic V K).mono fun p hp => ⟨K, _, _, hp, hF⟩)
  exact ⟨t, τ, hτ, ht⟩

end GlobalTheory.PELFromSiegel
