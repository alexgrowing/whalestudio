import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteHopfPointsSeparateStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tatePt_surjective_of_generic : ∀ (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (GG : PDivGroup p R) (GG₀ : PDivGroup p K) (e : GG₀ ≅ GG.baseChange K) (L : Type) [AddCommGroup L] (τ₀ : L →+ GG₀.Tate) (τ : L →+ GG.Tate), (∀ x, tateMap _ _ K e.hom (τ₀ x) = bcTate K (τ x)) → (∀ (n : ℕ) (φ : GG₀.A n →ₐ[K] K), ∃ x, tatePt (τ₀ x) n K = φ) → ∀ (n : ℕ) (k : Type) [Field k] [Algebra R k], (p : k) ≠ 0 → ∀ φ : GG.A n →ₐ[R] k, ∃ x, tatePt (τ x) n k = φ := by
  intro p _ R K _ _ _ _ _ _ _ _ GG GG₀ e L _ τ₀ τ hτ h0 n k _ _ _ φ
  obtain ⟨hfin, hsep, -⟩ := GlobalTheory.T.finite_hopf_points_separate R K (GG.A n)
  obtain ⟨s, hs⟩ := finiteAlg_fieldPoint_factors_through_base R K (GG.A n) hsep k φ
  let σ : K ⊗[R] GG.A n →ₐ[K] K :=
    Algebra.TensorProduct.lift (AlgHom.id K K) ((Algebra.ofId R K).comp s) fun _ _ => .all _ _
  obtain ⟨x, hx⟩ := h0 n (σ.comp (e.inv.app n : GG₀.A n →ₐ[K] K ⊗[R] GG.A n))
  refine ⟨x, ?_⟩
  have key : (τ x).pt n = s := by
    refine AlgHom.ext fun a => IsFractionRing.injective R K ?_
    have h1 := congrArg (fun t : (GG.baseChange K).Tate => t.pt n ((1 : K) ⊗ₜ[R] a)) (hτ x)
    have h2 := DFunLike.congr_fun hx (e.hom.app n ((1 : K) ⊗ₜ[R] a))
    have h3 : e.inv.app n (e.hom.app n ((1 : K) ⊗ₜ[R] a)) = (1 : K) ⊗ₜ[R] a :=
      congrArg (fun f : GG.baseChange K ⟶ GG.baseChange K => f.app n ((1 : K) ⊗ₜ[R] a)) e.inv_hom_id
    have h4 : ((τ₀ x).pt n) (e.hom.app n ((1 : K) ⊗ₜ[R] a)) = σ (e.inv.app n (e.hom.app n ((1 : K) ⊗ₜ[R] a))) := h2
    have h5 : ((τ₀ x).pt n) (e.hom.app n ((1 : K) ⊗ₜ[R] a)) = 1 * algebraMap R K ((τ x).pt n a) := h1
    have h6 : σ ((1 : K) ⊗ₜ[R] a) = 1 * algebraMap R K (s a) := rfl
    rw [h3, h6, h5, _root_.one_mul, _root_.one_mul] at h4
    exact h4
  rw [hs, tatePt, key]

end GlobalTheory
