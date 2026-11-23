import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NegIndexTransposeOfHasSignature

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem neg_baseElement_im_neg_baseEmbedding (D : D7) : (D.host.φ₀ (-D.host.xi0)).im < 0 := by
  have h1 := xi0_embedding_im_pos D D.host.φ₀ ((mem_cm_type_iff D _).2 rfl)
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
    rw [hφ]
    have hd : (0 : ℝ) < D.host.d := by exact_mod_cast d_pos D
    simpa using hd
  rw [if_pos hpos, Int.cast_one, _root_.one_mul] at h1
  rw [map_neg, Complex.neg_im]
  linarith

theorem sign_eq_one : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (j : ℕ), InR D j → (H.rt : D.host.E) = D.host.sqrtMinusD → H.rt0 = D.host.φ₀ D.host.sqrtMinusD → Dw.p = (D.R.sigW j).1 → Dw.q = (D.R.sigW j).2 → ∀ (φ : Dw.La →ₗ[𝓞 D.host.E] (D.sp.W j).V) (ε : ℤˣ), Function.Injective φ → Submodule.span D.host.E (Set.range φ) = ⊤ → (∀ x y, ((Dw.EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 * (D.sp.W j).hT (φ x) (φ y))) → ε = 1 := by
  intro D H Dw j hj hrt hrt0 hp _ φ ε hinj hspan0 hEF
  have hr := D.sp.W_rank j hj.1 hj.2
  let f := ((D.sp.W j).frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap
  have hio : Function.Injective (f ∘ₗ φ) := (D.sp.W j).frame.equivFun.injective.comp hinj
  have hdet := (GlobalTheory.RecDict.posIndex_gmW (D.sp.W j) (D.sp.W_sig j) hr D.host.φ₀).2
  have hherm := GlobalTheory.RecDict.cc_gmW (D.sp.W j) hr
  have hspan : Submodule.span D.host.E (Set.range (f ∘ₗ φ)) = ⊤ := by
    have : Set.range (f ∘ₗ φ) = (D.sp.W j).frame.equivFun.toLinearMap '' Set.range φ := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, hspan0, Submodule.map_top, LinearEquiv.range]
  rcases Int.units_eq_one_or ε with h | h
  · exact h
  exfalso
  subst h
  let c : (Fin (D.sp.W j).rank → D.host.E) ≃ₗ[D.host.E] (Fin D.R.r → D.host.E) :=
    LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr hr.symm)
  let ψ : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E) :=
    (c.restrictScalars (𝓞 D.host.E)).toLinearMap ∘ₗ f ∘ₗ φ
  have hψ : ∀ x, ψ x = (D.sp.W j).frame.equivFun (φ x) ∘ Fin.cast hr.symm := fun _ => rfl
  have hτ : D.host.φ₀ (H.rt : D.host.E) = H.rt0 := by rw [hrt, hrt0]
  have hξ : cc (-D.host.xi0) = -(-D.host.xi0) := by
    rw [cc, map_neg, conj_xi0_alt]
  have hsp : Submodule.span D.host.E (Set.range ψ) = ⊤ := by
    have : Set.range ψ = c.toLinearMap '' Set.range (f ∘ₗ φ) := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  obtain ⟨P, hP, hPg⟩ := (GlobalTheory.HermSign.signature_of_model D.host.E H Dw D.R.r (-D.host.xi0)
    _ ψ hξ ⟨c.injective.comp hio, hsp, hherm, hdet, fun x y => by
      rw [hEF, hψ, hψ, neg_mul, map_neg, GlobalTheory.RecDict.trace_herm_gmW]
      simp⟩ D.host.φ₀ hτ).2 (neg_baseElement_im_neg_baseEmbedding D)
  have hm := D.R.m_add_three_le_k
  have h1 := hj.1
  have h2 := hj.2
  have hle : Dw.p ≤ D.R.r := by
    rw [hp]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have h3 := (GlobalTheory.Inertia.gram_eq_sgn_iff D.host.φ₀ hherm hdet _).1 ⟨hle, P, hP, hPg⟩
  rw [(GlobalTheory.RecDict.posIndex_gmW (D.sp.W j) (D.sp.W_sig j) hr D.host.φ₀).1, D.sp.W_sigval j hj.1 hj.2, hp] at h3
  simp only [Ranks.sigW] at h3
  omega

end GlobalTheory.Member
