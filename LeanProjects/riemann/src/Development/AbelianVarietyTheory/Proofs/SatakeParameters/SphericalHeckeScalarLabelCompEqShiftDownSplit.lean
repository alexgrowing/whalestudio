import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualSplitLabelOperatorMulScalarOperator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentralShift

open Formalism.L2.NTheta GlobalTheory.SplitPlace GlobalTheory.DualSplitRel

variable {D : D7}

theorem split_of_primeIdem {P : Pl D.host.E} (hP : conjPl P ≠ P) {e f : AE D} (h : IsPrimeIdem P e f) :
    IsIdemAt e P ∧ f = e + cA D e := by
  rcases h with h | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
  · exact h
  · refine absurd (GlobalTheory.IdemSupport.eq_of_le (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)) hP
    have h2 := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at h2
    by_cases h0 : x = 0
    · rw [h0]; exact zero_mem _
    · exact (h2 x h0).2 ((ht x h0).1 hx)

theorem dual_shift (d : List ℤ) : dualLab ((dualLab (d.map fun x => x - 1)).map (· - 1)) = d := by
  simp [dualLab, List.map_reverse, List.map_map, Function.comp_def]

theorem shift {P : Pl D.host.E} (hP : conjPl P ≠ P) {V : HSp D} {d : List ℤ} {R : Finset (GA D V)} [DecidableEq (GA D V)]
    (hR : SphOp V P d R) : ∃ z : GA D V, (∀ γ ∈ R, γ * z = z * γ) ∧
      SphOp V P (splitLab V.rank V.rank) {z} ∧ SphOp V P (d.map fun x => x - 1) (R.image (· * z)) := by
  obtain ⟨e, f, ϖ, α, -, hpi, h1, h2, hd, -, -, hα, hD, hRs, hc⟩ := hR
  obtain ⟨he, rfl⟩ := split_of_primeIdem hP hpi
  have h0 : (ϖ : D.host.E) ≠ 0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
  obtain ⟨z, hs, hzc, hz⟩ := exists_central he.1 V h0
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  have hKl : locPart V (KsphC V ∅) e = (K : Set (GA D V)) := (hyp_eq_locPart he V).symm.trans hK
  have hKz : ∀ k ∈ locPart V (KsphC V ∅) e, k * z = z * k := fun k hk => hzc k hk.2
  have sh : ∀ {d : List ℤ} {g : GA D V} {R' : Finset (GA D V)}, SuppAt e V g → DivAt V e (ϖ : D.host.E) d g →
      (∀ γ ∈ R', SuppAt e V γ) → IsCosetRep V (locPart V (KsphC V ∅) e) g R' →
      (d.map (· - 1)).Pairwise (fun a b => b ≤ a) → SphOp V P (d.map (· - 1)) (R'.image (· * z)) := by
    intro d g R' sg dg sR hr hp
    obtain ⟨a, b⟩ := coset_mul hKz (fun γ hγ => (hr.1 γ hγ).2) hr.2
    have sup : ∀ γ ∈ R'.image (· * z), SuppAt e V γ := fun γ hγ => by
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
      exact suppAt_mul (sR δ hδ) hs
    exact sphOp_of he h1 h2 hp (suppAt_mul sg hs) (divAt_mul h0 hz dg) sup
      ⟨fun γ hγ => ⟨mem_GfC he.1 (sup γ hγ), a γ hγ⟩, b⟩
  have one : IsCosetRep V (locPart V (KsphC V ∅) e) 1 {1} := by
    have := coset_one K
    rw [← hKl] at this
    refine ⟨fun γ hγ => ⟨?_, this.1 γ hγ⟩, this.2⟩
    rw [Finset.mem_singleton.1 hγ]
    exact one_mem _
  have S0 := sh (GlobalTheory.SplitHecke.suppAt_one V)
    (GlobalTheory.SphLabelOps.divAt_one V he.1.1 (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem (Or.inl ⟨he, rfl⟩)) (ϖ : D.host.E))
    (fun γ hγ => by rw [Finset.mem_singleton.1 hγ]; exact GlobalTheory.SplitHecke.suppAt_one V) one
    (by rw [label_shift_zero]; simp [splitLab, List.pairwise_append, List.pairwise_replicate])
  rw [label_shift_zero, Finset.image_singleton, one_mul] at S0
  refine ⟨z, fun γ hγ => hzc γ (hRs γ hγ), S0, sh hα hD hRs hc ?_⟩
  exact List.pairwise_map.2 (hd.imp fun h => by omega)

theorem isLab_of_shift {P : Pl D.host.E} (hP : conjPl P ≠ P) {V : HSp D} {d : List ℤ}
    (h : IsLab V P (d.map fun x => x - 1)) : IsLab V P d := by
  obtain ⟨R, e, f, ϖ, α, -, hpi, h1, h2, hd, -, -, hα, hD, -, -⟩ := h
  obtain ⟨he, rfl⟩ := split_of_primeIdem hP hpi
  have h0 : (ϖ : D.host.E) ≠ 0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
  obtain ⟨z, hs, -, hz⟩ := exists_central he.1 V h0
  have D1 := (GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0 hD).1
  have D2 := divAt_mul h0 hz D1
  have D3 := (GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0 D2).1
  rw [dual_shift] at D3
  refine GlobalTheory.SphLabelOps.isLab_of_divAt hpi h1 h2 ?_ ?_ D3
  · exact (List.pairwise_map.1 hd).imp fun h => by omega
  · exact suppAt_inv (suppAt_mul (suppAt_inv hα) hs)

theorem central_shift : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ (d : List ℤ) (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (splitLab V.rank V.rank) 1) (opOf π P (Finsupp.single d 1) u) = opOf π P (Finsupp.single (d.map fun x => x - 1) 1) u := by
  classical
  intro D V P hP d M _ _ π u hu
  have c1 := (GlobalTheory.SphLabelOps.label_operators V P).1
  by_cases hl : IsLab V P d
  · obtain ⟨z, hzR, S0, S1⟩ := shift hP (GlobalTheory.SphLabelOps.sphOp_rep hl)
    have fw := (GlobalTheory.SphLabelOps.label_operators V P).2.1 (Finsupp.single d 1) M π u hu
    rw [← (c1 _ _ S0).2 M π _ fw, ← (c1 _ _ S1).2 M π u hu, Finset.sum_singleton, GlobalTheory.SphLabelOps.opOf_single,
      map_sum, Finset.sum_image (mul_left_injective z).injOn]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [hzR γ hγ, map_mul, Module.End.mul_apply]
  · have hl' : ¬ IsLab V P (d.map fun x => x - 1) := fun h => hl (isLab_of_shift hP h)
    have e0 : rep V P d = ∅ := by rw [Hk3.rep, dif_neg hl]
    have e1 : rep V P (d.map fun x => x - 1) = ∅ := by rw [Hk3.rep, dif_neg hl']
    rw [GlobalTheory.SphLabelOps.opOf_single π d, e0, Finset.sum_empty, map_zero, GlobalTheory.SphLabelOps.opOf_single, e1,
      Finset.sum_empty]

end GlobalTheory.CentralShift
