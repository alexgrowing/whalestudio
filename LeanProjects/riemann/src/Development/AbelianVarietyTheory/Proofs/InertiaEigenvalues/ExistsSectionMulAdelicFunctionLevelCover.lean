import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFactorComponentsOfAdelicInvariantFunctionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCombIdempotentSectionsNonnegOverPlaceStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOrthogonalIdempotentSectionsIndicatingCompStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompMulMemHolSub
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RdUMulApply
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.CompRat

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

theorem exists_sec_mul_adelic_fun : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → IsUnf U → FnAlgClosed Xo c → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∃ f' ∈ sec Xo c a n, (∀ h : GA D V, rdU U f' (dict h).1 (dict h).2 = σ (w h) * rdU U f (dict h).1 (dict h).2) ∧ (∀ la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (U.X k).Ψ r, rdU U f ∈ holSub0 U.X la → rdU U f' ∈ holSub0 U.X la) ∧ ∀ lam : HeightOneSpectrum (𝓞 c.F), (∀ h, lam.valuation c.F (w h) ≤ 1) → (∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f) → ∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f' := by
  intro D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hio hpq hA hσ hW hL hdom hU hF w hfin hQ hK a n f hf
  classical
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.T.exists_factor_components_of_adelic_invariant_function D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hio hpq hA hσ hW hL hdom
    w hfin hQ hK
  have hr1 : 1 ≤ r := hU.1 ▸ hpq
  obtain ⟨χ, hχ, hid, -, -, hrd⟩ := GlobalTheory.T.exists_orthogonal_idempotent_sections_indicating_components D.host.E H Dw l Xo c σ r U hr1 hσ hU hF
  let v : U.Comp → c.F := fun k => if ∃ h : GA D V, (dict h).1 = k then v₀ k else 0
  have hv : ∀ h : GA D V, v (dict h).1 = w h := fun h => by
    simp only [v]
    rw [if_pos ⟨h, rfl⟩, hv₀ h]
  have he : (∑ k, v k • χ k) ∈ sec Xo c 0 0 :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hχ k)
  have hval : ∀ k x, x ∈ (U.X k).dom → rdU U (∑ k, v k • χ k) k x = σ (v k) := by
    intro k x hx
    rw [map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single k]
    · rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, (hrd k k x hx).1 rfl, smul_eq_mul, mul_one]
    · intro k' _ hk
      rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, (hrd k' k x hx).2 hk.symm, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hmul : rdU U ((∑ k, v k • χ k) * f) = fun k x => σ (v k) * rdU U f k x := by
    funext k x
    rw [GlobalTheory.rdU_mul_apply D.host.E H Dw l Xo c σ r U]
    by_cases hx : x ∈ (U.X k).dom
    · rw [hval k x hx]
    · rw [rdU_mem_offZero U f k x hx, mul_zero, mul_zero]
  refine ⟨(∑ k, v k • χ k) * f, ?_, fun h => ?_, fun la hla => ?_, fun lam hw hint => ?_⟩
  · have := sec_mul Xo c 0 a 0 n he hf
    simpa only [zero_add] using this
  · rw [hmul, ← hv h]
  · rw [hmul]
    exact (GlobalTheory.CompRat.holSub_compMul D.host.E r U.Comp U.X la (fun k => σ (v k)) (rdU U f)).2 hla
  · have hvi : ∀ k, lam.valuation c.F (v k) ≤ 1 := by
      intro k
      by_cases hk : ∃ h : GA D V, (dict h).1 = k
      · obtain ⟨h, rfl⟩ := hk
        rw [hv h]
        exact hw h
      · simp only [v]
        rw [if_neg hk, map_zero]
        exact zero_le_one
    let ε := (Fintype.equivFin U.Comp).symm
    rw [← ε.sum_comp (fun k => v k • χ k)]
    exact GlobalTheory.T.integralComb_idempotentSections_nonneg_over_place D.host.E H Dw l Xo c lam _ (fun i => χ (ε i)) (fun i => v (ε i))
      (fun i => ⟨hχ _, hid _⟩) (fun i => hvi _) f hint

end GlobalTheory.CompRat
