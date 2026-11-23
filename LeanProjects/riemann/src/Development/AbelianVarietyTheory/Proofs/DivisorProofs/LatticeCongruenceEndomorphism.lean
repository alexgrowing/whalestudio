import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLinearApproxTower

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoLevel

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix

theorem exists_endo_approx_of_keeps_hat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (L Λ : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)) (h1 : L.FG)
    (h2 : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hΛ : (Λ : Set (Fin n → E)) = latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L)
    (hg : ∀ z ∈ hat F (L : Set (Fin n → E)), (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ z ∈ hat F (L : Set (Fin n → E)))
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin n → E)) (hi : Function.Injective ι)
    (hr : LinearMap.range ι = L) (N : ℕ) (hN : 0 < N) :
    ∃ γ₀ : La →ₗ[𝓞 E] La, ∀ a, ∃ w ∈ hat F (L : Set (Fin n → E)),
      (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ (fv F (ι a)) - fv F (ι (γ₀ a)) = N • w := by
  subst hr
  obtain ⟨f, hf, -, -⟩ := exists_linear_approx_tower F E n _ g Λ h1 h2 hΛ
  have hle : Λ ≤ LinearMap.range ι := by
    intro v hv
    have hv' : v ∈ (Λ : Set (Fin n → E)) := hv
    rw [hΛ] at hv'
    obtain ⟨z, hz, hzv⟩ := hv'
    refine ((hat_rational_points_and_approx F E n _ h1 h2).1 v).1 ?_
    rw [← hzv]
    exact hg z hz
  let e : La ≃ₗ[𝓞 E] LinearMap.range ι := LinearEquiv.ofInjective ι hi
  have he : ∀ x : LinearMap.range ι, ι (e.symm x) = x := fun x => by
    have : ((e (e.symm x) : LinearMap.range ι) : Fin n → E) = x := by rw [e.apply_symm_apply]
    exact this
  refine ⟨e.symm.toLinearMap ∘ₗ Submodule.inclusion hle ∘ₗ f N ∘ₗ e.toLinearMap, fun a => ?_⟩
  obtain ⟨w, hw, hfw⟩ := hf N hN (e a)
  refine ⟨-((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ w), neg_mem (hg w hw), ?_⟩
  have h3 : ι ((e.symm.toLinearMap ∘ₗ Submodule.inclusion hle ∘ₗ f N ∘ₗ e.toLinearMap) a) =
      (f N (e a) : Fin n → E) := he _
  have h4 : ((e a : LinearMap.range ι) : Fin n → E) = ι a := rfl
  rw [h3, hfw, h4, Matrix.mulVec_add, GlobalTheory.AdLat.Tower.mulVec_nsmul, smul_neg]
  abel

end General

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem exists_endo_approx : ∀ (D : D7) (V : HSp D) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ (N : ℕ), 0 < N → ∀ κ : GA D V, FinCong V 1 κ → ∃ γ₀ : La →ₗ[𝓞 D.host.E] La, ∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι (γ₀ a)) = N • w := by
  intro D V La _ _ ι hι N hN κ hκ
  obtain ⟨h1, h2, -, -, h5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V κ
  have hk := (GlobalTheory.Member.AALev.congruences_agree D V κ).1.2 hκ
  rw [h5] at hk ⊢
  exact exists_endo_approx_of_keeps_hat (F := D.host.F) (latG V 1) (latG V κ) (finHom V κ) h1 h2 h3 hk ι hι.1 hι.2 N hN

end GlobalTheory.GeoLevel
