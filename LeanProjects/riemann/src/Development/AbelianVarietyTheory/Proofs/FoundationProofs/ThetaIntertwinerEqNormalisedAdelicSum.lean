import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergRelativeIndexTranslateCompletedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRationalPointOfMemMovedThetaLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelic

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.IopSum

theorem act_inv_act {D : D7} {N N' : ℕ} (u : GA D N × GA D N') (ζ : XA D N N') :
    actA D N N' u⁻¹ (actA D N N' u ζ) = ζ := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem act_act_inv {D : D7} {N N' : ℕ} (u : GA D N × GA D N') (ζ : XA D N N') :
    actA D N N' u (actA D N N' u⁻¹ ζ) = ζ := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem mem_map_act {D : D7} {N N' : ℕ} (A : Submodule (𝓞 D.host.E) (XA D N N')) (u : GA D N × GA D N') (ζ : XA D N N') :
    ζ ∈ A.map (actA D N N' u) ↔ actA D N N' u⁻¹ ζ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [act_inv_act]
  · intro h
    exact ⟨_, h, act_act_inv u ζ⟩

theorem mem_moved {D : D7} {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} (g : GA D N) (g' : GA D N') (ζ : XA D N N') :
    ζ ∈ (latA D cc N N').map (actA D N N' (g, g')) ↔
      ∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * ζ *
        ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc := by
  rw [mem_map_act, Prod.inv_mk, actA_apply, mem_latA, Subgroup.coe_inv, Subgroup.coe_inv, inv_inv]

theorem pt_sub {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z z' : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z - z') = pt D (tor0 D cc δ) δ z - pt D (tor0 D cc δ) δ z' := by
  funext τ i j
  simp [pt, embV, tor0, mul_sub]

theorem sd_of_moves {D : D7} {N : ℕ} (g : GA D N) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, hLt, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  have : L = Lt g := Submodule.ext fun x => (h x).trans ((hLt g).1 x).symm
  rw [this]
  exact (hLt g).2

end GlobalTheory.FinWeil.IopSum

namespace GlobalTheory.FinWeil

open IopSum

theorem iop_eq_sumOp : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ (g : GA D N) (g' : GA D N') L₁ L₁', Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → SelfDual γ ((latA D cc N N').map (actA D N N' (g, g'))) → ∀ F : TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') F → Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') F = ((Real.sqrt (idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) : ℝ))⁻¹ : ℂ) • ((sumOp WA (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) F : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) := by
  intro D hG cc δ hC N N' w γ WA hM g g' L₁ L₁' hL hL' hSD F hF
  obtain ⟨hlat1, -, hlat3, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hG cc δ hC N N'
  have hidx := (GlobalTheory.T.heisenbergRelativeIndex_translate_completed_lattice D hG cc δ hC N N' g g').1
  have hidx' := (GlobalTheory.T.heisenbergRelativeIndex_translate_completed_lattice D hG cc δ hC N N' g⁻¹ g'⁻¹).1
  have hA := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hG cc δ hC.1.1 N N' g g' L₁ L₁' hL hL'
  have hB := GlobalTheory.NormSum.pt_mem_La_of_adelic D hG cc δ hC.1.1 N N' g g' L₁ L₁' hL hL'
  have hW := (GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' (La D (tor0 D cc δ) L₁ L₁')
    (Or.inr ⟨L₁, L₁', sd_of_moves g hL, sd_of_moves g' hL', rfl⟩)).2.1
  simp only [← mem_moved] at hA hB
  set A := latA D cc N N' with hAdef
  set B := A.map (actA D N N' (g, g')) with hBdef
  set La₂ := La D (tor0 D cc δ) L₁ L₁' with hLa₂
  set La₁ := La0 D (tor0 D cc δ) N N' with hLa₁

  have hm : ∀ a ∈ A, idx A (A.map (actA D N N' (g⁻¹, g'⁻¹))) • a ∈ B := by
    intro a ha
    rw [hBdef, mem_map_act, map_nsmul, Prod.inv_mk]
    exact AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup
      (K := (A.map (actA D N N' (g⁻¹, g'⁻¹))).toAddSubgroup) ⟨a, ha, rfl⟩
  choose z hz hzB using fun q : La₂ ⧸ La₁.addSubgroupOf La₂ => hA _ (Quotient.out q).2
  have hsub : ∀ x y : Matrix (Fin N') (Fin N) D.host.E, x.map (inc D) - y.map (inc D) ∈ A ↔
      pt D (tor0 D cc δ) δ x - pt D (tor0 D cc δ) δ y ∈ La₁ := by
    intro x y
    rw [← Matrix.map_sub _ (map_sub (inc D)), hlat1, pt_sub]
  have huniq : ∀ q q', (z q).map (inc D) - (z q').map (inc D) ∈ A → q = q' := by
    intro q q' h
    rw [hsub, ← hz, ← hz] at h
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', eq_comm, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using h
  have htr : ∀ b ∈ B, ∃! q, b - (z q).map (inc D) ∈ A := by
    intro b hb
    obtain ⟨y, a, ha, hy⟩ := hlat3 b _ (Nat.pos_of_ne_zero hidx')
    have hyB : y.map (inc D) ∈ B := hy ▸ B.add_mem hb (hm a ha)
    have hex : b - (z (QuotientAddGroup.mk ⟨_, hB y hyB⟩)).map (inc D) ∈ A := by
      have h1 : y.map (inc D) - (z (QuotientAddGroup.mk ⟨_, hB y hyB⟩)).map (inc D) ∈ A := by
        rw [hsub, ← hz]
        have h2 := QuotientAddGroup.out_eq' (QuotientAddGroup.mk ⟨_, hB y hyB⟩ : La₂ ⧸ La₁.addSubgroupOf La₂)
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h2
        simpa [neg_add_eq_sub] using h2
      have h3 := A.sub_mem h1 (nsmul_mem ha (idx A (A.map (actA D N N' (g⁻¹, g'⁻¹)))))
      rw [hy] at h3
      convert h3 using 1
      abel
    refine ⟨QuotientAddGroup.mk ⟨_, hB y hyB⟩, ?_, ?_⟩
    · exact hex
    · intro q hq
      refine huniq _ _ ?_
      have := A.sub_mem hex hq
      rwa [sub_sub_sub_cancel_left] at this
  haveI : Finite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero hidx
  haveI : Finite (La₂ ⧸ La₁.addSubgroupOf La₂) := by
    refine Finite.of_injective (fun q => (QuotientAddGroup.mk ⟨_, hzB q⟩ :
      B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)) fun q q' h => ?_
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    refine (huniq q' q ?_).symm
    simpa [neg_add_eq_sub] using h
  haveI := Fintype.ofFinite (La₂ ⧸ La₁.addSubgroupOf La₂)
  obtain ⟨h1, h2⟩ := (GlobalTheory.FinWeil.sumOp_transversal hM.1 A B hSD).1 F hF _ (fun q => (z q).map (inc D)) hzB htr
  rw [h1, h2]
  funext v
  rw [Iop, finsum_eq_sum_of_fintype, AddSubgroup.index, Nat.card_eq_fintype_card, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_sum, Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hM.2.2.2.1, ← hz, hW _ (Quotient.out q).2]

end GlobalTheory.FinWeil
