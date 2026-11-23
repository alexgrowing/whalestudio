import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.ShFam.BdArc

open GlobalTheory.HolHom GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections LatSec

theorem exists_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (g' : ℕ) (ρ : ℝ) (e' : ∀ u, (Fin g' → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G)), IsArc Z σ φ x ψ r → 0 < ρ → ρ ≤ r → IsHolTo (Metric.ball (0 : ℂ) ρ ×ˢ Set.univ) (fun q : ℂ × (Fin g' → ℂ) => (show Sp ℂ ⟶ Z.t.G.left from (e' q.1 q.2).left)) → (∀ u ∈ Metric.ball (0 : ℂ) ρ, (∀ z w, e' u (z + w) = e' u z * e' u w) ∧ Function.Surjective (e' u) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (e' u z).left)) ∧ (∀ w, ∃! v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, IsDerivAt0 (fun z => (e' u z).left) w v.left) ∧ (∀ v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' u 0).left → ∃! w, IsDerivAt0 (fun z => (e' u z).left) w v.left)) → ∃ h : ℂ → (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ), ∀ u ∈ Metric.ball (0 : ℂ) ρ, (h u).IsInvertible ∧ ContinuousAt (fun u => (h u).inverse) u ∧ ∀ ex : (Fin g → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G), (∀ z z', ex (z + z') = ex z * ex z') → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (ex z).left)) → (∀ j, IsDerivAt0 (fun z => (ex z).left) (Pi.single j 1) (spMap (dualMap (ψ u)) ≫ fr.v (e j).1 (e j).2)) → ∀ z, ex z = e' u (h u z) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ r g e g' ρ e' harc hρ hρr hol hexp
  have hA : ∀ u ∈ Metric.ball (0 : ℂ) ρ, HolAt (fun z => (e' u z).left) 0 := fun u hu =>
    holAt_of_isHolTo (hexp u hu).2.2.1 trivial
  have hh : ∀ u, ∃ h : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ), u ∈ Metric.ball (0 : ℂ) ρ → h.IsInvertible ∧
      ∀ j, IsDerivAt (fun z => (e' u z).left) 0 (h (Pi.single j 1))
        (spMap (dualMap (ψ u)) ≫ fr.v (e j).1 (e j).2) := fun u => by
    by_cases hu : u ∈ Metric.ball (0 : ℂ) ρ
    · obtain ⟨D, hD⟩ := exists_lieEquiv Z.t (hexp u hu).1 (hA u hu) (hexp u hu).2.2.2.2
      obtain ⟨f, hf⟩ := GlobalTheory.T.exists_eigFrame_baseChange' E H Dw l Xo c O β Z A ℂ φ _ fr (ψ u)
      obtain ⟨b, hb⟩ := exists_basis f
      refine ⟨((b.reindex e.symm).equivFun.symm.trans D.symm).toContinuousLinearEquiv, fun _ => ⟨⟨_, rfl⟩, fun j => ?_⟩⟩
      have h1 := hD (D.symm (f.vec (e j).1 (e j).2))
      rw [D.apply_symm_apply] at h1
      have h2 : ((b.reindex e.symm).equivFun.symm.trans D.symm).toContinuousLinearEquiv (Pi.single j 1) =
          D.symm (f.vec (e j).1 (e j).2) := by simp [hb, Pi.single_apply]
      rw [← hf, ContinuousLinearEquiv.coe_coe, h2]
      exact h1
    · exact ⟨0, fun h => absurd h hu⟩
  choose h hh using hh
  refine ⟨h, fun u hu => ⟨(hh u hu).1, ?_, fun ex hadd hex hd z => ?_⟩⟩
  · refine ((hh u hu).1.contDiffAt_map_inverse (n := 1)).continuousAt.comp (continuousAt_clm_apply.2 fun z => ?_)
    have : ∀ u, h u z = ∑ j, z j • h u (Pi.single j 1) := fun u => by
      simp only [← map_smul, ← map_sum]
      exact congrArg _ (pi_eq_sum_univ' z)
    simp only [this]
    refine tendsto_finset_sum _ fun j _ => ContinuousAt.const_smul ?_ (z j)
    exact continuousAt_dir hol hu (hexp u hu).2.2.2.2 (fun b hb => (hh b hb).2 j) (continuousAt_snd (fun a =>
      ((harc.1.2 a).differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hρr hu))).continuousAt) _)
  · obtain ⟨hu1, -, hu2, -, hu3⟩ := hexp u hu
    obtain ⟨k, hk, -⟩ := existsUnique_linear hadd hu1 hex hu2 hu3
    have hkh : k = (h u).toLinearMap := (Pi.basisFun ℂ (Fin g)).ext fun i => by
      have h1 := (isDerivAt0_iff _ _ _).1 (hd i)
      simp only [hk] at h1
      have h2 := (isDerivAt_comp_iff (hA u hu) (LinearMap.toContinuousLinearMap k) _ _).1 h1
      rw [Pi.basisFun_apply]
      exact (hu3 (Over.homMk _ h2.over) h2.1).unique ((isDerivAt0_iff _ _ _).2 h2)
        ((isDerivAt0_iff _ _ _).2 ((hh u hu).2 i))
    rw [hk, hkh, ContinuousLinearMap.coe_coe]

end GlobalTheory.ShFam.BdArc
