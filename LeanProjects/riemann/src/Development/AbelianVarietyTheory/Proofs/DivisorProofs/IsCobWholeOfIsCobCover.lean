import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatFamilyExistsUnique
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt

theorem isCob_whole_of_isCob_cover : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc (whole X) u → ∀ k : Fn0 X, IsCob W u k → ∃ k' : Fn0 X, IsCob (whole X) u k' := by
  intro R _ X K W hW u hu k hk
  have ex : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), ∃! d : D,
      ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), Sm W (spOver ψ ≫ x) →
        k E (spOver ψ ≫ x) - u D E ψ x = ψ d := by
    intro D _ _ x
    refine natFamily_existsUnique R X K W hW D x (fun E _ _ ψ ↦ k E (spOver ψ ≫ x) - u D E ψ x) ?_
    intro E _ _ E' _ _ ψ θ hψ
    have c := hu D E E' ψ θ x (sm_whole x)
    have b := hk E E' θ (spOver ψ ≫ x) hψ
    have e : spOver (θ.comp ψ) ≫ x = spOver θ ≫ spOver ψ ≫ x := by
      rw [← Category.assoc, spOver_comp]
    show k E' (spOver (θ.comp ψ) ≫ x) - u D E' (θ.comp ψ) x = θ (k E (spOver ψ ≫ x) - u D E ψ x)
    rw [e, c, b, map_sub]
    ring
  let k' : Fn0 X := fun D _ _ x ↦ (ex D x).exists.choose
  have hk' : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D) (E : Type) [CommRing E] [Algebra R E]
      (ψ : D →ₐ[R] E), Sm W (spOver ψ ≫ x) → k E (spOver ψ ≫ x) - u D E ψ x = ψ (k' D x) :=
    fun D _ _ x ↦ (ex D x).exists.choose_spec
  refine ⟨k', fun D _ _ D' _ _ φ x _ ↦ ?_⟩
  have huniq : k' D' (spOver φ ≫ x) = u D D' φ x + φ (k' D x) := by
    refine (ex D' (spOver φ ≫ x)).unique (hk' D' (spOver φ ≫ x)) ?_
    intro E _ _ ψ hψ
    have e : spOver (ψ.comp φ) ≫ x = spOver ψ ≫ spOver φ ≫ x := by
      rw [← Category.assoc, spOver_comp]
    have h1 := hk' D x E (ψ.comp φ) (by rw [e]; exact hψ)
    have c := hu D D' E φ ψ x (sm_whole x)
    rw [e, c, AlgHom.comp_apply] at h1
    rw [map_add, ← h1]
    ring
  rw [huniq]
  ring

end GlobalTheory.PtExt
