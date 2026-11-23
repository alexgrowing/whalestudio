import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.FiniteValues
open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem exists_finset_point {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (B : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType B.hom] (p : TF (R := R) F ⟶ B) :
    ∃ S : Finset F, ∀ K : IntermediateField (FractionRing R) F, (S : Set F) ⊆ K →
      ∃ l : TF (R := R) K ⟶ B, extMap (R := R) (algebraMap K F) rfl ≫ l = p := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hpt, -⟩ := B.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p.left (IsLocalRing.closedPoint F))) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨f, hf⟩ : ∃ f : Γ(B.left, U) ⟶ CommRingCat.of F, Spec.map f ≫ hU.fromSpec = p.left := by
    refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec p.left ?_), ?_⟩
    · rintro _ ⟨y, rfl⟩
      rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum F) y (IsLocalRing.closedPoint F)]
      exact hpt
    · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of R ⟶ Γ(B.left, U), Spec.map g = hU.fromSpec ≫ B.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) F) :=
    Spec.map_injective (by
      rw [Spec.map_comp, hg, ← Category.assoc, hf, Spec.map_comp]
      exact Over.w p)
  have hV : ∀ r : R, f.hom (g.hom r) = algebraMap (FractionRing R) F (algebraMap R _ r) := fun r =>
    congrArg (fun q => q.hom r) hgf
  have hft : g.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra R Γ(B.left, U) := g.hom.toAlgebra
  obtain ⟨s, hs⟩ := (show Algebra.FiniteType R Γ(B.left, U) from hft).out
  refine ⟨s.image f.hom, fun K hK => ?_⟩
  have hr : ∀ a, f.hom a ∈ K := fun a => by
    have ha : a ∈ Algebra.adjoin R (s : Set Γ(B.left, U)) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hK (Finset.mem_image_of_mem _ hx)
    | algebraMap r => exact (hV r).symm ▸ K.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let f' : Γ(B.left, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (f.hom.codRestrict K hr)
  refine ⟨Over.homMk (Spec.map f' ≫ hU.fromSpec) ?_, Over.OverMorphism.ext ?_⟩
  · change (Spec.map f' ≫ hU.fromSpec) ≫ B.hom = Spec.map _ ≫ Spec.map _
    rw [Category.assoc, ← hg, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact hV r
  · change Spec.map _ ≫ Spec.map f' ≫ hU.fromSpec = _
    rw [← hf, ← Spec.map_comp_assoc]
    rfl

theorem exists_finite_field_of_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra.IsAlgebraic (FractionRing R) F] (N : NumD F) (_ : NumOf D F N) (T : Set N.A), T.Finite → ∃ (K₁ : IntermediateField (FractionRing R) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing R) K₁ ∧ (∀ x ∈ T, x ∈ A₀) ∧ (∀ χ, N.c χ ∈ A₀) ∧ (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) ∧ (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) ∧ (∀ x ∈ A₀, N.th x ∈ K₁) ∧ ∀ χ, (N.ψ χ : F) ∈ K₁ := by
  intro R _ _ D F _ _ _ N ν T hT
  haveI := D.P.isAb.proper
  choose S hS using fun x : N.A => exists_finset_point D.P.A (ν.eA x)
  let s : Set F := ⋃ x ∈ T, (S x : Set F)
  haveI : Finite s := (hT.biUnion fun x _ => (S x).finite_toSet).to_subtype
  let K := IntermediateField.adjoin (FractionRing R) s
  let f : K →+* F := algebraMap K F
  have hf : f.comp (algebraMap (FractionRing R) K) = algebraMap (FractionRing R) F := rfl
  let Φ : (TF (R := R) K ⟶ D.P.A) →* N.A :=
    MonoidHom.mk' (fun x => ν.eA.symm (extMap f hf ≫ x)) fun x y => by rw [MonObj.comp_mul, map_mul]
  have hΦ : ∀ x, ν.eA (Φ x) = extMap f hf ≫ x := fun x => ν.eA.apply_symm_apply _
  let J : (Sp K ⟶ D.P.A.left) → D.P.L.ι := fun ψ => ν.J (spMap f ≫ ψ)
  have hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ) := fun ψ z _ => by
    have h := ν.good (spMap f ≫ ψ) (Set.mem_univ (IsLocalRing.closedPoint F))
    rw [Subsingleton.elim (α := PrimeSpectrum K) z (spMap f (IsLocalRing.closedPoint F))]
    exact h
  have hJ' : ∀ ψ, ν.J (spMap f ≫ ψ) = J ψ := fun _ => rfl
  have hm : ∀ a : K, f a ∈ K := fun a => a.2
  have hv : ∀ {Y : Scheme.{0}} {I : Type} [Fintype I] {φ : I → (Y ⟶ D.P.A.left)} {ε : I → ℤ}
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : Sp K ⟶ Y), vF t (spMap f ≫ r) ν.J ∈ K := fun t r => by
    rw [vF_ext f hJ hJ']; exact hm _
  have hw : ∀ {Y : Scheme.{0}} {I : Type} [Fintype I] {φ : I → (Y ⟶ D.P.A.left)} {ε : I → ℤ}
      (t : LB.Sec (LB.LinComb D.P.L φ ε)) (r : Sp K ⟶ Y), sF t (spMap f ≫ r) ν.J ∈ K := fun t r => by
    rw [sF_ext f hJ hJ']; exact hm _
  have hrig : rigVal ν ∈ K := by
    rw [rigVal, ← Over.w (extMap (R := R) f hf)]
    exact hv _ _
  refine ⟨K, Φ.range, IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral,
    fun x hx => ?_, fun χ => ?_, ?_, ?_, ?_, fun χ => ?_⟩
  · obtain ⟨l, hl⟩ := hS x K ((Set.subset_biUnion_of_mem (u := fun x => (S x : Set F)) hx).trans
      (IntermediateField.subset_adjoin _ _))
    exact ⟨l, ν.eA.injective ((hΦ l).trans hl)⟩
  · exact ⟨DegPre.cF D K (ν.eX χ), ν.eA.injective ((hΦ _).trans ((DVR.comp_cP D _ _).trans (ν.c_eq χ).symm))⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _ ⟨u, rfl⟩
    rw [ν.θ_eq, hΦ, hΦ, hΦ, ← comp_lift, ← comp_lift]
    exact hv _ _
  · rintro _ ⟨x, rfl⟩
    rw [ν.σ_eq, hΦ]
    exact hv _ _
  · rintro _ ⟨x, rfl⟩
    have h0 : rigVal ν ≠ 0 := vF_ne_zero ν.good _ _
    rw [eq_div_of_mul_eq h0 (ν.th_eq (Φ x)), hΦ]
    exact div_mem (hw _ _) hrig
  · rw [ν.ψ_eq]
    refine mul_mem ?_ hrig
    rw [← (extMap_jFK (R := R) f hf).trans (Category.id_comp _)]
    exact hv _ _

end GlobalTheory.FiniteValues
end
