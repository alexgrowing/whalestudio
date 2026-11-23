import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIdentifications
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackBaseChangeWithSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTorsionPointPolarisedFibreImageStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem torsion_theta_points_defOver : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ') (lam : Sp V ⟶ F'.X) (β : Q.B.left ⟶ F'.univ.A.left) (β₂ : (G2 Q.B).left ⟶ (G2 F'.univ.A).left), 1 ≤ n' → DefOver k₀ (spMap (ev.comp ρ) ≫ lam ≫ F'.s) → IsGrpPullback Q.B F'.univ.A lam β → IsSquare β β₂ → LBIso (abelian₂ Q.B Q.M.L) (F'.univ.P.pull β₂) → ∀ a, DefOver k₀ (spMap (ev.comp ρ) ≫ (Q.c a).left ≫ β) := by
  intro g l hl hlo W hW
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.conjugate_torsion_point_polarised_fibre_image g l hl hlo W hW
  refine ⟨j₀, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K _ _ ev k₀ hk₀ hu o' _ ζ' g' n' F' lam β β₂ hn' hdef hpb hsq hLB a
  obtain ⟨hpb0, φ₀₂, hsq0⟩ := GlobalTheory.GrpPB.baseChange_square F'.univ.A Q.B lam β hpb (spMap (ev.comp ρ))
  have hp : (spMap (ev.comp ρ) ≫ (Q.c a).left) ≫ Q.B.hom = 𝟙 _ ≫ spMap (ev.comp ρ) := by
    rw [Category.assoc, Over.w (Q.c a)]; simp
  let p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left :=
    pullback.lift (spMap (ev.comp ρ) ≫ (Q.c a).left) (𝟙 _) hp
  have hpf : p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left :=
    pullback.lift_fst _ _ _
  apply GlobalTheory.Poinc.Sep.defOver_of_finite_orbit K k₀ hk₀ _ _
  apply (GlobalTheory.SiegFibreFinite.finite_identifications o' ζ' g' n' F' hn' K _ _ _ φ₀₂ hpb0 hsq0 p).subset
  rintro P' ⟨σ, hσ, rfl⟩
  obtain ⟨x', φ, φ₂, h1, h2, h3, h4, h5⟩ := hj₀ j hj V V₁ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K ev k₀ hk₀ hu
    o' ζ' g' n' F' lam β β₂ hn' hdef hpb hsq hLB φ₀₂ hsq0 σ hσ a p hpf (pullback.lift_snd _ _ _)
  refine ⟨x', φ, φ₂, ?_, h2, h3, h4, ?_⟩
  · simpa only [Category.assoc] using h1
  · rw [← h5, reassoc_of% hpf]

end GlobalTheory.Poinc.Sep
