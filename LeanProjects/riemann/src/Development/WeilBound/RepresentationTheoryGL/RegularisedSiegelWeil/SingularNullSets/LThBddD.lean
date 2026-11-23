import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddC
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSummableBoundSchwartzMajorantRationalTransStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixSchwartzMajorantInvMulLeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ} {W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D W.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)}

theorem theta_cont (hθ : IsInfFam θ) (Φ : schwartzA θ W.rank n)
    (hcont : Continuous fun u : G D n × Mx D W.rank n => (ω u.1 Φ).1 u.2)
    (hmaj : ∀ C : Set (G D n), IsCompact C → ∃ M ∈ schwartzA θ W.rank n, ∀ g ∈ C, ∀ x, ‖(ω g Φ).1 x‖ ≤ ‖M x‖) :
    Continuous fun u : G D n × GA D W => theta ω Φ u.1 u.2 := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨Qg, hQg, hpg⟩ := exists_compact_mem_nhds p.1
  obtain ⟨Qh, hQh, hph⟩ := exists_compact_mem_nhds p.2
  obtain ⟨M, hM, hMb⟩ := hmaj Qg hQg
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ W.rank n
  obtain ⟨-, K, hK, hC⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ W.rank n M (GlobalTheory.T.isSchwartzBruhatAdelicMatrix_of_mem_adelicSchwartz D θ hθ W.rank n M hM)
  obtain ⟨K', hK', hmul⟩ := GlobalTheory.T.adelicMatrixSchwartzMajorant_inv_mul_le D θ hθ W n Qh hQh K hK
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨C₂, hC₂, hmul'⟩ := hmul N
  obtain ⟨b, hb, hb'⟩ := hN K' {0} hK' isCompact_singleton
  have hterm : ∀ ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
      Continuous fun u : G D n × GA D W => (ω u.1 Φ).1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n)) := fun ξ =>
    hcont.comp (continuous_fst.prodMk (((GlobalTheory.LatNhds.continuous_mt_inv W).comp continuous_snd).matrix_mul
      continuous_const))
  have hon : ContinuousOn (fun u : G D n × GA D W => ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
      (ω u.1 Φ).1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))) (Qg ×ˢ Qh) := by
    refine continuousOn_tsum (fun ξ => (hterm ξ).continuousOn) (hb.mul_left (|C| * C₂)) fun ξ u hu => ?_
    have h1 := hMb u.1 hu.1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))
    have h2 := hC (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))
    have h3 := hmul' u.2 hu.2 (rat ξ : Mx D W.rank n)
    have h4 := hb' 0 rfl ξ
    rw [zero_add] at h4
    have hm0 := GlobalTheory.Unf.maj_nonneg θ K N (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))
    calc ‖(ω u.1 Φ).1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))‖
        ≤ C * GlobalTheory.Unf.maj θ K N (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n)) := h1.trans h2
      _ ≤ |C| * GlobalTheory.Unf.maj θ K N (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hm0
      _ ≤ |C| * (C₂ * GlobalTheory.Unf.maj θ K' N (rat ξ : Mx D W.rank n)) := mul_le_mul_of_nonneg_left h3 (abs_nonneg C)
      _ ≤ |C| * (C₂ * b ξ) := by gcongr
      _ = |C| * C₂ * b ξ := by ring
  exact hon.continuousAt (prod_mem_nhds hpg hph)

theorem theta_full (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (h : GA D W) :
    theta ω Ψ' g h = ∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
      (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1)) := by
  unfold theta
  have hsupp : Function.support (fun ξ : Matrix (Fin W.rank) (Fin n) D.host.E => (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ))) ⊆
      {y : Matrix (Fin W.rank) (Fin n) D.host.E | y.rank = W.rank} := by
    intro ξ hξ
    by_contra hr
    exact hξ (term_zero hω hnb C hC Ψ Ψ' hΨ hΨ' hg h ξ hr)
  exact (tsum_subtype_eq_of_support_subset hsupp).symm

theorem bound_triv (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) (hLB : LatBound) (hθ : IsInfFam θ)
    (hmaj : ∀ Q : Set (G D n), IsCompact Q → ∃ M ∈ schwartzA θ W.rank n, ∀ g ∈ Q, ∀ x, ‖(ω g Ψ').1 x‖ ≤ ‖M x‖)
    (Q : Set (G D n)) (hQ : IsCompact Q) :
    ∃ b : ℝ, ∀ g ∈ Q, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1 → ∀ h, ‖theta ω Ψ' g h‖ ≤ b := by
  obtain ⟨M, hM, hMb⟩ := hmaj Q hQ
  obtain ⟨B, hB⟩ := hLB D θ hθ W n M hM
  refine ⟨B, fun g hg hgv h => ?_⟩
  rw [theta_full hω hnb C hC Ψ Ψ' hΨ hΨ' hgv h]
  have e : ‖∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
      (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1))‖ₑ ≤ B :=
    (enorm_tsum_le_tsum_enorm).trans ((ENNReal.tsum_le_tsum fun y => by
      have := hMb g hg (mm (mt W h⁻¹) (rat y.1))
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal this).trans (hB h))
  have e2 : ENNReal.ofReal ‖∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
      (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1))‖ ≤ ENNReal.ofReal B := by
    rw [ofReal_norm, ENNReal.ofReal_coe_nnreal]; exact e
  exact (ENNReal.ofReal_le_ofReal_iff B.2).1 e2

end PositivityTheory.Rg.Rsw.L.LThBdd

end
