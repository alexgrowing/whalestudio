import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPerHolOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusPointsSubsetHolPeriodicOneParamSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompactRepresentativesModTorusPointsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan

namespace GlobalTheory.PeriodSpan

theorem span_ker_eq_top : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsSemiAbelian G → ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective (e) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) ∧ (∀ w, ∃! v : epsPt (y) ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt (y) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) → Submodule.span ℂ {z | e z = 1} = ⊤ := by
  intro X G _ y g e hG ⟨hadd, hsurj, hhol, _, hd2⟩
  have hhol' : IsHolTo Set.univ (fun z => (e z).left) := hhol
  have h0 : e 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hsub : ∀ z w, e (z - w) = e z * (e w)⁻¹ := fun z w =>
    eq_mul_inv_of_mul_eq (by rw [← hadd, sub_add_cancel])
  by_contra hne
  obtain ⟨ℓ, hℓ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  have hℓK : ∀ z, e z = 1 → ℓ z = 0 := fun z hz => hle (Submodule.subset_span hz)
  have hℓeq : ∀ z w, e z = e w → ℓ z = ℓ w := fun z w h => by
    have := hℓK (z - w) (by rw [hsub, h, mul_inv_cancel])
    rwa [map_sub, sub_eq_zero] at this
  let lam : (Over.mk y ⟶ G) → ℂ := fun x => ℓ (hsurj x).choose
  have hlam : ∀ z, lam (e z) = ℓ z := fun z => hℓeq _ _ (hsurj (e z)).choose_spec
  let S : Subgroup (Over.mk y ⟶ G) :=
    { carrier := {x | lam x = 0}
      one_mem' := by
        show lam 1 = 0
        rw [← h0, hlam, map_zero]
      mul_mem' := by
        intro x x' hx hx'
        obtain ⟨a, rfl⟩ := hsurj x
        obtain ⟨b, rfl⟩ := hsurj x'
        show lam (e a * e b) = 0
        have hx : lam (e a) = 0 := hx
        have hx' : lam (e b) = 0 := hx'
        rw [← hadd, hlam, map_add, ← hlam, ← hlam, hx, hx', add_zero]
      inv_mem' := by
        intro x hx
        obtain ⟨a, rfl⟩ := hsurj x
        have hx : lam (e a) = 0 := hx
        show lam (e a)⁻¹ = 0
        have hinv : (e a)⁻¹ = e (-a) :=
          inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
        rw [hinv, hlam, map_neg, ← hlam, hx, neg_zero] }
  have hper : perHolSub G y ≤ S := by
    refine Subgroup.closure_le _ |>.2 (Set.iUnion₂_subset fun ψ hψ => Set.range_subset_iff.2 fun s => ?_)
    obtain ⟨hψadd, hψhol, hψper⟩ := hψ
    obtain ⟨h, hh, -⟩ := (GlobalTheory.holomorphic_hom_determined X G).2.2.1 y ℂ g ψ e hψadd hadd hψhol hhol' hd2
    have hlin : ∀ s : ℂ, h s = s • h 1 := fun s => by rw [← h.map_smul, smul_eq_mul, _root_.mul_one]
    have h1 : ℓ (h 1) = 0 := by
      have h2 : ℓ (h (2 * Real.pi * Complex.I)) = 0 := hℓK _ (by rw [← hh, hψper])
      rw [hlin, map_smul, smul_eq_mul] at h2
      refine (mul_eq_zero.1 h2).resolve_left ?_
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    show lam (ψ s) = 0
    rw [hh, hlam, hlin, map_smul, h1, smul_zero]
  obtain ⟨E⟩ := hG.fibres ℂ y
  have htor : ∀ x ∈ torusPts G y E, lam x = 0 := fun x hx => hper (GlobalTheory.T.torusPoints_subset_holPeriodicOneParamSpan X G y E hx)
  obtain ⟨C, hC, hCz⟩ := GlobalTheory.T.exists_compact_representatives_mod_torusPoints X G y g e E hG hadd hsurj hhol' hd2
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (LinearMap.continuous_of_finiteDimensional ℓ).continuousOn
  have hbd : ∀ z, ‖ℓ z‖ ≤ M := fun z => by
    obtain ⟨c, hc, hzc⟩ := hCz z
    have := htor _ hzc
    rw [hlam, map_sub, sub_eq_zero] at this
    rw [this]
    exact hM c hc
  apply hℓ0
  refine LinearMap.ext fun z => ?_
  by_contra hz0
  have hz : ℓ z ≠ 0 := by simpa using hz0
  have hpos : 0 < ‖ℓ z‖ := norm_pos_iff.2 hz
  have := hbd ((((|M| + 1) / ‖ℓ z‖ : ℝ) : ℂ) • z)
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    div_mul_cancel₀ _ hpos.ne'] at this
  linarith [le_abs_self M]

end GlobalTheory.PeriodSpan
