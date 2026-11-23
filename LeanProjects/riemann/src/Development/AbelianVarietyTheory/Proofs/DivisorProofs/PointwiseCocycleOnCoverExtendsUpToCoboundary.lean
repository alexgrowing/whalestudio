import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueElemOfNaturalFamilyOpenCoverPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPointwiseOneCocycleOpenCoverStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt.CocExt

theorem sm_comp {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens}
    {D E : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E) (x : Pt X D)
    (h : Sm W x) : Sm W (spOver ψ ≫ x) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, fun z _ ↦ ?_⟩
  have := hi (Set.mem_univ ((spOver ψ).left.base z))
  simpa [Over.comp_left, Scheme.Hom.comp_base, Scheme.Hom.comp_apply] using this

theorem cocycle_extends : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc W u → ∃ u' : Fn1 X, IsCoc (whole X) u' ∧ Cohom W u u' := by
  intro R _ X K W hW u hu
  have hB : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), ∃ σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), Sm W (spOver ψ ≫ x) → σ E' (θ.comp ψ) - θ (σ E ψ) = u E E' θ (spOver ψ ≫ x) :=
    fun D _ _ x ↦ GlobalTheory.T.exists_section_pointwiseOneCocycle_openCover R X K W hW u hu D x
  choose σ hσ using hB
  have uniq : ∀ (D : Type) [CommRing D] [Algebra R D] (y : Pt X D) (d d' : D),
      (∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), Sm W (spOver ψ ≫ y) → ψ d = ψ d') → d = d' := by
    intro D _ _ y d d' h
    obtain ⟨e, -, he⟩ := GlobalTheory.T.existsUnique_elem_of_natural_family_openCoverPoints R X K W hW D y (fun E _ _ ψ ↦ ψ d) (fun _ _ _ _ _ _ _ _ _ ↦ rfl)
    exact (he d (fun _ _ _ _ _ ↦ rfl)).trans (he d' (fun E _ _ ψ hψ ↦ h E ψ hψ)).symm
  have hA : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D),
      ∃ d : D', ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D' →ₐ[R] E), Sm W (spOver ψ ≫ spOver φ ≫ x) →
        σ D x E (ψ.comp φ) - σ D' (spOver φ ≫ x) E ψ = ψ d := by
    intro D _ _ D' _ _ φ x
    refine (GlobalTheory.T.existsUnique_elem_of_natural_family_openCoverPoints R X K W hW D' (spOver φ ≫ x)
      (fun E _ _ ψ ↦ σ D x E (ψ.comp φ) - σ D' (spOver φ ≫ x) E ψ) ?_).exists
    intro E _ _ E' _ _ ψ θ hψ
    have e : spOver ψ ≫ spOver φ ≫ x = spOver (ψ.comp φ) ≫ x := by rw [← Category.assoc, spOver_comp]
    have h1 := hσ D x E E' (ψ.comp φ) θ (by rw [← e]; exact hψ)
    have h2 := hσ D' (spOver φ ≫ x) E E' ψ θ hψ
    rw [← e] at h1
    simp only [map_sub]
    rw [show (θ.comp ψ).comp φ = θ.comp (ψ.comp φ) from rfl]
    linear_combination h1 - h2
  choose u' hu' using hA
  refine ⟨u', ?_, ?_⟩
  · intro D _ _ D' _ _ D'' _ _ φ ψ x _
    have e : spOver ψ ≫ spOver φ ≫ x = spOver (ψ.comp φ) ≫ x := by rw [← Category.assoc, spOver_comp]
    apply uniq D'' (spOver (ψ.comp φ) ≫ x)
    intro E _ _ ρ hρ
    have h2 : Sm W (spOver (ρ.comp ψ) ≫ spOver φ ≫ x) := by
      rw [← spOver_comp, Category.assoc, e]; exact hρ
    have h3 : Sm W (spOver ρ ≫ spOver ψ ≫ spOver φ ≫ x) := by rw [e]; exact hρ
    rw [map_add, ← AlgHom.comp_apply, ← hu' D D'' (ψ.comp φ) x E ρ hρ, ← hu' D D' φ x E (ρ.comp ψ) h2,
      ← hu' D' D'' ψ (spOver φ ≫ x) E ρ h3, e]
    rw [show (ρ.comp ψ).comp φ = ρ.comp (ψ.comp φ) from rfl]
    ring
  · refine ⟨fun D _ _ x ↦ σ D x D (AlgHom.id R D), ?_⟩
    intro D _ _ D' _ _ φ x hx
    have hx' : Sm W (spOver (AlgHom.id R D) ≫ x) := by rw [spOver_id, Category.id_comp]; exact hx
    have h1 := hσ D x D D' (AlgHom.id R D) φ hx'
    rw [spOver_id, Category.id_comp, AlgHom.comp_id] at h1
    have hφx : Sm W (spOver (AlgHom.id R D') ≫ spOver φ ≫ x) := by
      rw [spOver_id, Category.id_comp]; exact sm_comp φ x hx
    have h2 := hu' D D' φ x D' (AlgHom.id R D') hφx
    rw [AlgHom.id_comp, AlgHom.id_apply] at h2
    show u D D' φ x + -u' D D' φ x = _
    linear_combination h2 - h1

end GlobalTheory.PtExt.CocExt
