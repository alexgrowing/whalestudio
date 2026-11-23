import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.EtaleLocInj

theorem exists_separating_pairs {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (h : φ.Etale) :
    ∃ s : Finset (S × S), ∑ p ∈ s, p.1 * p.2 = 1 ∧ ∀ e e' : S →+* ℂ, e.comp φ = e'.comp φ →
      ∑ p ∈ s, e p.1 * e' p.2 ≠ 0 → e = e' := by
  algebraize [φ]
  obtain ⟨t, ht, h1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := S)).1 inferInstance
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  refine ⟨s, ?_, fun e e' hee hne => ?_⟩
  · simpa [map_sum] using h1
  · letI : Algebra R ℂ := (e.comp φ).toAlgebra
    let a : S →ₐ[R] ℂ := { e with commutes' := fun _ => rfl }
    let a' : S →ₐ[R] ℂ := { e' with commutes' := fun r => (RingHom.congr_fun hee r).symm }
    let F := Algebra.TensorProduct.lift a a' (fun _ _ => Commute.all _ _)
    ext x
    have h2 := congrArg F (ht x)
    simp only [F, map_mul, map_sub, map_sum, Algebra.TensorProduct.lift_tmul, map_one, map_zero] at h2
    rcases mul_eq_zero.1 h2 with h3 | h3
    · have h4 := (sub_eq_zero.1 h3).symm
      rw [_root_.one_mul, _root_.mul_one] at h4
      exact h4
    · exact (hne h3).elim

theorem eq_of_valAtHom_eq {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x x' : Sp ℂ ⟶ X)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : valAtHom x U h = valAtHom x' U h') : x = x' := by
  rw [← AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x h,
    ← AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x' h']
  congr 2
  ext1
  exact e

theorem exists_open_injOn :
    ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ), Etale π → IsOpen B → b₀ ∈ B → IsHolTo B y → ∃ B' : Set (Fin m → ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ ∀ b ∈ B', ∀ b' ∈ B', y b ≫ π = y b' ≫ π → y b = y b' := by
  intro X Y π m B y b₀ hπ _ hb₀ hy
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (π (y b₀ (default : PrimeSpectrum ℂ)))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show y b₀ (default : PrimeSpectrum ℂ) ∈ ((π ⁻¹ᵁ V : X.Opens) : Set X) from hxV) (π ⁻¹ᵁ V).isOpen
  have e : U ≤ π ⁻¹ᵁ V := hUV
  obtain ⟨s, hs1, hs⟩ := exists_separating_pairs _ (π.etale_appLE hV hU e)
  set C : Set (Fin m → ℂ) := {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} with hC
  have hCo : IsOpen C := (hy U 0).1
  have h₀ : ⊤ ≤ y b₀ ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hxU
  have hb₀C : b₀ ∈ C := ⟨hb₀, h₀⟩
  have hc : ∀ f : Γ(X, U), ContinuousAt (fun b => valAt' (y b) U f) b₀ := fun f =>
    (hy U f).2.continuousOn.continuousAt (hCo.mem_nhds hb₀C)
  let F : (Fin m → ℂ) × (Fin m → ℂ) → ℂ := fun q => ∑ p ∈ s, valAt' (y q.1) U p.1 * valAt' (y q.2) U p.2
  have hF : ContinuousAt F (b₀, b₀) := by
    refine tendsto_finset_sum _ fun p _ => ?_
    exact ((hc p.1).comp_of_eq continuousAt_fst rfl).mul ((hc p.2).comp_of_eq continuousAt_snd rfl)
  have hF0 : F (b₀, b₀) ≠ 0 := by
    simp only [F, ← valAt'_mul, ← valAt'_sum, hs1, valAt'_one _ h₀]
    exact one_ne_zero
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 (hF.eventually_ne hF0)
  obtain ⟨B', hB'sub, hB'o, hB'⟩ := mem_nhds_iff.1
    (Filter.inter_mem (hCo.mem_nhds hb₀C) (Filter.inter_mem hu hv))
  refine ⟨B', hB'o, hB', fun b hb => (hB'sub hb).1.1, fun b hb b' hb' hbb => ?_⟩
  have h1 := (hB'sub hb).1.2
  have h2 := (hB'sub hb').1.2
  refine eq_of_valAtHom_eq hU _ _ h1 h2 (hs _ _ ?_ ?_)
  · ext f
    rw [RingHom.comp_apply, RingHom.comp_apply, ← valAt'_eq_valAtHom, ← valAt'_eq_valAtHom,
      valAt'_appLE _ _ _ _ _ _ h1, valAt'_appLE _ _ _ _ _ _ h2, hbb]
  · simp only [← valAt'_eq_valAtHom]
    have h3 : F (b, b') ≠ 0 := huv (Set.mk_mem_prod (hB'sub hb).2.1 (hB'sub hb').2.2)
    exact h3

end GlobalTheory.EtaleLocInj
