import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyPositivePolarizationProjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticSectionFromUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMapToProjectiveSpaceStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.CMTorsion.AlgMap

theorem exists_totPos (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) : ∃ c : 𝔠.elt, IsTotPos (c : F) := by
  have h0 : (𝔠 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔠.ne_zero
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := ((𝔠 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)) (by
    intro h; exact h0 (FractionalIdeal.coeToSubmodule_injective (by simpa using h)))
  obtain ⟨a, ha, hint⟩ := (𝔠 : FractionalIdeal (𝓞 F)⁰ F).isFractional
  obtain ⟨y, hy⟩ := hint x hx
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero, Algebra.smul_def] at hy
    exact mul_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 ha0) hx0 hy.symm
  have hm := Ideal.absNorm_mem (Ideal.span {y})
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
  set m := Ideal.absNorm (Ideal.span {y})
  have hm0 : m ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hy0
  have hmem : (m : F) ∈ 𝔠.elt := by
    have e : (m : F) = t • (a • x) := by
      rw [← hy, Algebra.smul_def, ← map_mul, ht, map_natCast]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hx)
  refine ⟨⟨_, hmem⟩, fun τ => ?_⟩
  simp only [map_natCast]
  exact_mod_cast Nat.pos_of_ne_zero hm0

end GlobalTheory.CMTorsion.AlgMap

namespace GlobalTheory.CMTorsion.AlgMap

theorem valAt'_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U from h)]
    unfold valAt
    congr 1
  · rw [dif_neg h, dif_neg (show ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U from h)]

theorem factor : ∀ (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ (Y : Scheme.{0}) (N : ℕ) (i : Y ⟶ PSpace ℂ N),
    IsClosedImmersion i → ∀ (ψ : scheme (curve Λ Ω) ⟶ PSpace ℂ N) (φ : ℂ → (Sp ℂ ⟶ Y)),
    (∀ z, pt Λ Ω z ≫ ψ = φ z ≫ i) → ∃ f : scheme (curve Λ Ω) ⟶ Y, f ≫ i = ψ := by
  intro Λ Ω hΩ Y N i hi ψ φ h
  refine GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset ψ i ?_
  have hc : IsClosed (ψ ⁻¹' Set.range i) := i.isClosedEmbedding.isClosed_range.preimage ψ.continuous
  have hJ : JacobsonSpace (scheme (curve Λ Ω)) := LocallyOfFiniteType.jacobsonSpace (toSpec (curve Λ Ω))
  have hcp : closedPoints (scheme (curve Λ Ω)) ⊆ ψ ⁻¹' Set.range i := by
    intro y hy
    have hy₁ : IsClosed {y} := hy
    obtain ⟨z, hz⟩ := GlobalTheory.T.elliptic_section_from_uniformization Λ Ω hΩ (pointOfClosedPoint (toSpec (curve Λ Ω)) y hy₁)
      (pointOfClosedPoint_comp _ _ _)
    obtain ⟨a⟩ : Nonempty (Sp ℂ) := inferInstance
    have hy' : pt Λ Ω z a = y := by rw [hz, pointOfClosedPoint_apply]
    refine ⟨φ z a, ?_⟩
    rw [← hy']
    simpa [Scheme.Hom.comp_apply] using (congrArg (fun g : Sp ℂ ⟶ PSpace ℂ N => g a) (h z)).symm
  have hu : closure (closedPoints (scheme (curve Λ Ω))) = Set.univ := by
    have := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := scheme (curve Λ Ω)) (S := Set.univ) isOpen_univ.isLocallyClosed
    rwa [Set.univ_inter, closure_univ] at this
  rintro _ ⟨y, rfl⟩
  have : y ∈ closure (closedPoints (scheme (curve Λ Ω))) := hu ▸ Set.mem_univ y
  exact (closure_minimal hcp hc) this

theorem main : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt) (n : ℕ) (u : HolUnif X.A (X.diag c) n) (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ β : Fin n → ℂ, (∀ l ∈ Λ.lattice, l • β ∈ u.Λ) → ∃ f : scheme (curve Λ Ω) ⟶ X.A.left, f ≫ X.A.hom = toSpec (curve Λ Ω) ∧ ∀ z, pt Λ Ω z ≫ f = (u.ex (z • β)).left := by
  intro F _ _ 𝔠 X c n u Λ Ω hΩ β hβ
  obtain ⟨c', hc'⟩ := exists_totPos F 𝔠
  obtain ⟨N, i, hi, hstr⟩ := GlobalTheory.RealMult.ProjOverC.isProjOver_A F 𝔠 X c' hc'
  let φ : ℂ → (Sp ℂ ⟶ X.A.left) := fun z => (u.ex (z • β)).left
  have hcomp : ∀ z, (φ z ≫ i) ≫ PSpace.str ℂ N = 𝟙 _ := fun z => by
    rw [Category.assoc, hstr]
    exact Over.w (u.ex (z • β))
  have hper : ∀ z, ∀ l ∈ Λ.lattice, φ (z + l) ≫ i = φ z ≫ i := fun z l hl => by
    have e : u.ex ((z + l) • β) = u.ex (z • β) := by
      rw [add_smul, u.ex_add, (u.ker _).2 (hβ l hl), _root_.mul_one]
    simp only [φ, e]
  have hhol : ∀ (U : (PSpace ℂ N).Opens) (s : Γ(PSpace ℂ N, U)), IsOpen {z | ⊤ ≤ (φ z ≫ i) ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (φ z ≫ i) U s) {z | ⊤ ≤ (φ z ≫ i) ⁻¹ᵁ U} := fun U s => by
    obtain ⟨h1, h2⟩ := u.hol (i ⁻¹ᵁ U) ((i.app U).hom s)
    have hL : Differentiable ℂ (fun z : ℂ => z • β) := differentiable_id.smul_const β
    have hset : {z : ℂ | ⊤ ≤ (φ z ≫ i) ⁻¹ᵁ U} = (fun z : ℂ => z • β) ⁻¹' {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (i ⁻¹ᵁ U)} := rfl
    rw [hset]
    refine ⟨h1.preimage hL.continuous, ?_⟩
    have e : (fun z => valAt' (φ z ≫ i) U s) = (fun w => valAt' (u.ex w).left (i ⁻¹ᵁ U) ((i.app U).hom s)) ∘ (fun z : ℂ => z • β) :=
      funext fun z => valAt'_comp _ _ _ _
    rw [e]
    exact h2.comp hL.differentiableOn (fun z hz => hz)
  obtain ⟨ψ, hψ1, hψ2⟩ := GlobalTheory.T.holomorphic_map_to_projective_space Λ Ω hΩ N (fun z => φ z ≫ i) hcomp hper hhol
  obtain ⟨f, hf⟩ := factor Λ Ω hΩ X.A.left N i hi ψ φ hψ2
  refine ⟨f, ?_, fun z => ?_⟩
  · rw [← hstr, ← Category.assoc, hf, hψ1]
  · rw [← cancel_mono i, Category.assoc, hf, hψ2]

end GlobalTheory.CMTorsion.AlgMap
