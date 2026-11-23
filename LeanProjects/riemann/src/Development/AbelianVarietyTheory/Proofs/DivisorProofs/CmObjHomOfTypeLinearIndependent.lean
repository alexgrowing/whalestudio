import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.InjectiveOfSumEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueExtendRingOfIntegersHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.CM.IntCoord
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.HomIndep

theorem phiP_independent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (x : Fin p → 𝓞 E),
    ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) = 1 → x = 0 := by
  intro E _ _ _ H K _ _ ρ σ₁ p q X x hx
  classical
  have hU := GlobalTheory.thetaUnifAV_all
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨τ, hτ⟩ := GlobalTheory.CM.NumInh.exists_char X.split X.ρ_sq
  have FA : ∀ b, GenFib (X.A b).pol := fun b =>
    (GenFib.nonempty_of_baseChange hL.polBaseChange K (X.A b).pol).some
  have FB : GenFib X.B.pol := (GenFib.nonempty_of_baseChange hL.polBaseChange K X.B.pol).some
  have hMex : ∀ j : Fin p ⊕ Fin q, ∃ M, (FA j.isLeft).IsDiffOf FB (X.φ j) M := fun j =>
    ((GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K _ (FA j.isLeft) _ FB (X.φ j) (X.lin j).isMonHom).1).exists
  choose M hM using hMex
  obtain ⟨-, hrank, hinj, hind, -⟩ := GlobalTheory.CM.Indep.letters_independent hU hL E H K ρ σ₁ p q X FA FB M hM
  funext a
  show x a = 0
  have hcA := integral_tangent_coordinates K _ (FA true)
  have hcB := integral_tangent_coordinates K _ FB

  have hne : (FA true).eigLat (X.A true).t.act τ ≠ ⊥ := by
    intro h0
    have h1 := hrank (Sum.inl a, τ)
    rw [if_pos (by simpa using hτ)] at h1
    change latRank K (((FA true).eigLat (X.A true).t.act τ).map ((M (Sum.inl a)).restrictScalars (𝓞 K))) = 1 at h1
    rw [h0] at h1
    have hb : Submodule.span K (((⊥ : Submodule (𝓞 K) (Fin (FA true).P₀.g → K)).map
        ((M (Sum.inl a)).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin FB.P₀.g → K)) : Set (Fin FB.P₀.g → K)) = ⊥ :=
      Submodule.span_eq_bot.2 fun z hz => by
        obtain ⟨y, hy, rfl⟩ := hz
        obtain rfl : y = 0 := (Submodule.mem_bot (𝓞 K)).1 hy
        exact map_zero _
    rw [latRank, hb, finrank_bot] at h1
    exact zero_ne_one h1
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨u, hu, heig⟩ := (hcA.2.2.2.2.2 _ _ τ e).1 he
  have hs : ∀ b, FB.IsCoord (u ≫ ((X.A true).t.act.act (x b) ≫ phiP X b)) (M (Sum.inl b) (τ (x b) • e)) := by
    intro b
    rw [← Category.assoc]
    exact hM (Sum.inl b) _ _ (isCoord_smul (FA true) hu (heig (x b)))
  have hprod : ∀ s : Finset (Fin p), FB.IsCoord (u ≫ ∏ b ∈ s, ((X.A true).t.act.act (x b) ≫ phiP X b))
      (∑ b ∈ s, M (Sum.inl b) (τ (x b) • e)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, comp_one]
      exact isCoord_one FB
    | insert b s hb ih =>
      rw [Finset.prod_insert hb, Finset.sum_insert hb, comp_mul]
      exact isCoord_mul FB (hs b) ih
  have hsum : ∑ b, M (Sum.inl b) (τ (x b) • e) = 0 := by
    have h1 := hprod Finset.univ
    rw [hx, comp_one] at h1
    exact (hcB.1 _ h1.1).unique h1 (isCoord_one FB)
  have hind' := hind.comp (f := fun b : Fin p => ((Sum.inl b, τ) : (Fin p ⊕ Fin q) × (𝓞 E →+* 𝓞 K)))
    (fun b b' h => Sum.inl_injective (Prod.ext_iff.1 h).1)
  have hva := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 hind' Finset.univ
    (fun b => M (Sum.inl b) (τ (x b) • e))
    (fun b _ => Submodule.subset_span (Submodule.mem_map_of_mem
      (f := (M (Sum.inl b)).restrictScalars (𝓞 K)) (Submodule.smul_mem _ (τ (x b)) he))) hsum a (Finset.mem_univ a)
  have h0 : τ (x a) • e = 0 := hinj (Sum.inl a) (by rw [hva]; exact (map_zero _).symm)
  rw [← algebraMap_smul K (τ (x a)) e, smul_eq_zero] at h0
  have hτa : τ (x a) = 0 :=
    (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).1 (h0.resolve_right he0)
  exact ringOfIntegers_hom_injective τ (by rw [hτa, map_zero])

end GlobalTheory.FlatCM.HomIndep

end
