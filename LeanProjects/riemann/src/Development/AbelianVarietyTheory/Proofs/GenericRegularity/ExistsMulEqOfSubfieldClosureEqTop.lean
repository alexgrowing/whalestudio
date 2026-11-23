import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsNoetherianRingTensor
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsFractionRingSubringOfClosureEqTop
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory

theorem exists_mul_eq_of_subfield_closure_eq_top {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    {t : Set Ω} (ht : Subfield.closure (Set.range (algebraMap K Ω) ∪ t) = ⊤)
    (R : Subalgebra K Ω) (hR : t ⊆ R) (x : Ω) : ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a := by
  haveI : IsFractionRing R.toSubring Ω := isFractionRing_subring_of_closure_eq_top ht R.toSubring
    (Set.union_subset (by rintro _ ⟨a, rfl⟩; exact R.algebraMap_mem a) hR)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R.toSubring) x
  have hb0 : (b : Ω) ≠ 0 := fun h => nonZeroDivisors.ne_zero hb (Subtype.ext h)
  exact ⟨a, a.2, b, b.2, hb0, div_mul_cancel₀ _ hb0⟩

theorem exists_normal_charts_over_dvr :
    ∀ (K Ω O : Type) [Field K] [Field Ω] [Algebra K Ω] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (io : K →+* FractionRing O) (gens es : Finset Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → (∀ e ∈ es, e ≠ 0 ∧ e ∈ Subring.closure ((algebraMap K Ω '' {a | io a ∈ Set.range (algebraMap O (FractionRing O))}) ∪ (gens : Set Ω))) → (∀ e ∈ es, Algebra.Smooth K (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)))) → ∃ (J : Type) (_ : Finite J) (A : J → Type) (_ : ∀ j, CommRing (A j)) (_ : ∀ j, IsDomain (A j)) (_ : ∀ j, Algebra O (A j)) (α : ∀ j, Ω →+* FractionRing (A j)), (∀ j, Algebra.FiniteType O (A j) ∧ Module.Flat O (A j) ∧ IsIntegrallyClosed (A j)) ∧ (∀ j (k : K) (a b : O), io k * algebraMap O _ b = algebraMap O _ a → α j (algebraMap K Ω k) * algebraMap (A j) _ (algebraMap O (A j) b) = algebraMap (A j) _ (algebraMap O (A j) a)) ∧ (∀ j, ∀ g ∈ gens, α j g ∈ Set.range (algebraMap (A j) (FractionRing (A j)))) ∧ ∀ e ∈ es, ∀ (L : Type) [Field L] (W : ValuationSubring L) (χ : FractionRing O →+* L) (ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* L), (∀ k : K, ψ (algebraMap K _ k) = χ (io k)) → (∀ a : O, χ (algebraMap O _ a) ∈ W) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → ψ g ∈ W) → ∃ (j : J) (φ : A j →+* L), (∀ x, φ x ∈ W) ∧ (∀ a : O, φ (algebraMap O (A j) a) = χ (algebraMap O _ a)) ∧ ∀ (r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) (x s : A j), α j r * algebraMap (A j) _ s = algebraMap (A j) _ x → ψ r * φ s = φ x := by
  classical
  intro K Ω O _ _ _ _ _ _ _ io gens es hgen _ hsm
  letI : Algebra K (FractionRing O) := io.toAlgebra
  obtain ⟨J, hJ, Ω', hΩ', α, gm, hαgm, htop, hR⟩ :=
    GlobalTheory.BaseChangeComponents.components K (FractionRing O) Ω (Algebra.adjoin K (gens : Set Ω))
      (Subalgebra.fg_adjoin_finset gens)
      (exists_mul_eq_of_subfield_closure_eq_top hgen _ Algebra.subset_adjoin)
  have hαgm' : ∀ j (k : K), α j (algebraMap K Ω k) = gm j (io k) := hαgm
  letI : ∀ j, Algebra O (Ω' j) := fun j => ((gm j).comp (algebraMap O (FractionRing O))).toAlgebra
  have hO : ∀ j (a : O), algebraMap O (Ω' j) a = gm j (algebraMap O (FractionRing O) a) :=
    fun _ _ => rfl
  have hinj : ∀ j, Function.Injective (algebraMap O (Ω' j)) := fun j =>
    (gm j).injective.comp (IsFractionRing.injective O (FractionRing O))
  have hcl : ∀ j, Subfield.closure (Set.range (algebraMap O (Ω' j)) ∪
      ((gens.image (α j) : Finset (Ω' j)) : Set (Ω' j))) = ⊤ := by
    intro j
    set E := Subfield.closure (Set.range (algebraMap O (Ω' j)) ∪
      ((gens.image (α j) : Finset (Ω' j)) : Set (Ω' j))) with hE
    have hgm : ∀ a, gm j a ∈ E := by
      intro a
      obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := O) a
      rw [map_div₀, ← hO, ← hO]
      exact div_mem (Subfield.subset_closure (Or.inl ⟨x, rfl⟩))
        (Subfield.subset_closure (Or.inl ⟨y, rfl⟩))
    have hα : (⊤ : Subfield Ω) ≤ E.comap (α j) := by
      rw [← hgen, Subfield.closure_le]
      rintro x (⟨k, rfl⟩ | hx)
      · change α j _ ∈ E
        rw [hαgm']; exact hgm _
      · change α j _ ∈ E
        exact Subfield.subset_closure (Or.inr (by
          rw [Finset.coe_image]; exact ⟨x, hx, rfl⟩))
    rw [eq_top_iff, ← htop j, Subfield.closure_le]
    rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact hα (Subfield.mem_top y)
    · exact hgm y
  choose A hsA hft hfl hic hfr hmin hW using fun j =>
    GlobalTheory.exists_normalisation_adjoin_finset_dvr O (Ω' j) (hinj j) (gens.image (α j)) (hcl j)
  let ε : ∀ j, Ω' j ≃ₐ[A j] FractionRing (A j) := fun j =>
    (FractionRing.algEquiv (A j) (Ω' j)).symm
  have hε : ∀ j (x : A j), algebraMap (A j) (FractionRing (A j)) x = ε j (x : Ω' j) :=
    fun j x => ((ε j).commutes x).symm
  refine ⟨J, hJ, fun j => A j, inferInstance, inferInstance, inferInstance,
    fun j => ((ε j).toRingEquiv.toRingHom).comp (α j),
    fun j => ⟨hft j, hfl j, hic j⟩, ?_, ?_, ?_⟩
  · intro j k a b h
    rw [hε, hε]
    change ε j (α j _) * ε j (algebraMap O (Ω' j) b) = ε j (algebraMap O (Ω' j) a)
    rw [← map_mul, hαgm', hO, hO, ← map_mul, h]
  · intro j g hg
    refine ⟨⟨α j g, hsA j (by rw [Finset.coe_image]; exact ⟨g, hg, rfl⟩)⟩, ?_⟩
    rw [hε]; rfl
  · intro e he L _ W χ ψ hψ hχ hg
    have hsub : (gens : Set Ω) ⊆ Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) :=
      (Set.subset_insert _ _).trans Algebra.subset_adjoin
    obtain ⟨hD, hφ⟩ := hR (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) (hsm e he)
      (exists_mul_eq_of_subfield_closure_eq_top hgen _ hsub)
    obtain ⟨j, φ, h1, h2⟩ := hφ L χ ψ hψ
    have hgmD : ∀ a, gm j a ∈ Subring.closure (α j '' (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) : Set Ω) ∪ Set.range (gm j)) :=
      fun a => Subring.subset_closure (Or.inr ⟨a, rfl⟩)
    have hαD : ∀ r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), α j r ∈ Subring.closure (α j '' (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) : Set Ω) ∪ Set.range (gm j)) :=
      fun r => Subring.subset_closure (Or.inl ⟨r, r.2, rfl⟩)
    have hAD := hmin j _ (hD j) (fun a => hgmD _) (by
      rw [Finset.coe_image]
      rintro _ ⟨g, hg, rfl⟩
      exact hαD ⟨g, hsub hg⟩)
    let inc : A j →+* Subring.closure (α j '' (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) : Set Ω) ∪ Set.range (gm j)) :=
      ((A j).val : A j →+* Ω' j).codRestrict _ fun x => hAD x.2
    have hφO : ∀ a : O, (φ.comp inc) (algebraMap O (A j) a) = χ (algebraMap O _ a) :=
      fun a => h2 _ (hgmD _)
    refine ⟨j, φ.comp inc, hW j L W (φ.comp inc) (fun a => by rw [hφO]; exact hχ a) ?_, hφO, ?_⟩
    · intro x hx
      obtain ⟨g, hg', hgx⟩ := Finset.mem_image.mp hx
      have : inc x = ⟨α j (⟨g, hsub hg'⟩ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))), hαD _⟩ :=
        Subtype.ext hgx.symm
      rw [RingHom.comp_apply, this, h1]
      exact hg _ hg'
    · intro r x s h
      rw [hε, hε] at h
      have h' : α j r * (s : Ω' j) = x := (ε j).injective (by rw [map_mul]; exact h)
      rw [← h1 r (hαD r), RingHom.comp_apply, RingHom.comp_apply, ← map_mul]
      exact congrArg φ (Subtype.ext h')

end GlobalTheory
