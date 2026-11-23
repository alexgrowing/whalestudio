import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechDeRhamClassOfQuasiPeriodicFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularSectionOfRegularDifferencesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegOfPeriodicOfIsRegSubStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularFderivConstantVectorUniformisedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOnOpenUniformisedOfLocallyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOnOpenUniformisedSubalgebraRestrictStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
open Filter Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer.OfCover

theorem fderiv_congr_on {g : ℕ} {S : Set (Fin g → ℂ)} (hS : IsOpen S) {f f' : (Fin g → ℂ) → ℂ}
    (e : ∀ z ∈ S, f z = f' z) {z : Fin g → ℂ} (hz : z ∈ S) : fderiv ℂ f z = fderiv ℂ f' z :=
  Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hS.mem_nhds hz) e)

theorem exists_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), ⨆ i, W i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) (pre u.ex (W i))) → (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i), h i (z + l) = h i z + q l) → ∃ x, IsPer u.ex u.Λ x q := by
  intro A _ g L u hA K W h q hW hd hr hq
  obtain ⟨bo, bd, bp, bv, bi, bm, bs, -, -, -, -, bt⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have ra := GlobalTheory.T.isRegularOnOpenUniformised_subalgebra_restrict A g L u
  have der := GlobalTheory.T.isRegular_fderiv_constant_vector_uniformised A g L u hA
  have glue := GlobalTheory.T.isRegularOnOpenUniformised_of_locally A g L u hA

  have dsub : ∀ (U : A.left.Opens) (k k' : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ), DifferentiableOn ℂ k (pre u.ex U) →
      DifferentiableOn ℂ k' (pre u.ex U) → IsReg u.ex U (k - k') →
      IsReg u.ex U ((fun z => fderiv ℂ k z w) - fun z => fderiv ℂ k' z w) := by
    rintro U k k' w hk hk' ⟨b, hb⟩
    refine (ra U).2.2.1 _ _ (der U b w) fun z hz => ?_
    have e := fderiv_congr_on (bo U) hb hz
    rw [← e, fderiv_sub (hk.differentiableAt ((bo U).mem_nhds hz)) (hk'.differentiableAt ((bo U).mem_nhds hz))]
    rfl
  have hreg : ∀ (w : Fin g → ℂ) i, IsReg u.ex (W i) fun z => fderiv ℂ (h i) z w := by
    intro w
    refine GlobalTheory.T.isReg_of_periodic_of_isReg_sub' A g L u hA K W (fun i z => fderiv ℂ (h i) z w) hW (fun i => ?_) (fun i l z hz => ?_) fun i j => ?_
    · have := (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn (bo (W i)) (hd i)).fderiv.differentiableOn
      exact this.clm_apply (differentiableOn_const w)
    · have e := fderiv_congr_on (bo (W i)) (f := fun z => h i (z + l)) (f' := fun z => h i z + q l) (hq i l) hz
      rw [fderiv_comp_add_right, fderiv_add_const] at e
      change fderiv ℂ (h i) (z + l) w = fderiv ℂ (h i) z w
      rw [e]
    · exact dsub _ _ _ w ((hd i).mono (bm _ _ inf_le_left)) ((hd j).mono (bm _ _ inf_le_right)) (hr i j)
  choose k hk using GlobalTheory.T.exists_regular_section_of_regular_differences A g L u hA K W h hW hr
  have cov : ∀ z, ∃ i, z ∈ pre u.ex (W i) := fun z => (bs K W z).1 (hW ▸ bt z)
  have kd : ∀ (U : A.left.affineOpens) i, DifferentiableOn ℂ (k U) (pre u.ex (U.1 ⊓ W i)) := fun U i => by
    have := ((ra _).2.2.2.2.1 _ (hk U i)).add ((hd i).mono (bm _ _ inf_le_right))
    simpa using this
  have mem : ∀ (U : A.left.Opens) z i, z ∈ pre u.ex U → z ∈ pre u.ex (W i) → z ∈ pre u.ex (U ⊓ W i) :=
    fun U z i h1 h2 => by rw [bi]; exact ⟨h1, h2⟩
  refine GlobalTheory.T.exists_cechDeRham_class_of_quasiPeriodic_functions A g L u hA k q (fun U z hz => ?_) (fun U V hVU => ?_) (fun U a => ?_) fun U l z hz => ?_
  · obtain ⟨i, hi⟩ := cov z
    exact ((kd U i).differentiableAt ((bo _).mem_nhds (mem _ _ _ hz hi))).differentiableWithinAt
  · refine glue _ _ fun z hz => ?_
    obtain ⟨i, hi⟩ := cov z
    refine ⟨V.1 ⊓ W i, inf_le_left, mem _ _ _ hz hi, ?_⟩
    have := ((ra _).2.1 _ _ (hk V i) ((ra _).2.2.2.1 _ (inf_le_inf_right (W i) (show V.1 ≤ U.1 from hVU)) _ (hk U i))).2.1
    simpa using this
  · refine glue _ _ fun z hz => ?_
    obtain ⟨i, hi⟩ := cov z
    refine ⟨U.1 ⊓ W i, inf_le_left, mem _ _ _ hz hi, ?_⟩
    have h1 := dsub _ _ _ (Pi.single a 1) (kd U i) ((hd i).mono (bm _ _ inf_le_right)) (hk U i)
    have h2 := (ra _).2.2.2.1 _ (inf_le_right : U.1 ⊓ W i ≤ W i) _ (hreg (Pi.single a 1) i)
    have := ((ra _).2.1 _ _ h1 h2).1
    simpa using this
  · obtain ⟨i, hi⟩ := cov z
    obtain ⟨b, hb⟩ := hk U i
    have h1 := hb z (mem _ _ _ hz hi)
    have h2 := hb (z + l) ((bp _ l z).2 (mem _ _ _ hz hi))
    rw [bv, Pi.sub_apply, hq i l z hi] at h2
    rw [Pi.sub_apply] at h1
    linear_combination h2 - h1

end GlobalTheory.CechPer.OfCover
