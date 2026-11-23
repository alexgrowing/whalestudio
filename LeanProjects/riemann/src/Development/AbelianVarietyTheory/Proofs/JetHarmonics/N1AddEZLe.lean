import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselGapStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRegularRepBesselBigCellVectorEqBesselStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilyFunctionalSpanDualStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepExteriorPowerStandardRep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FixesWedgeAndForm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermCmpWedgeEqDet

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SuppliedPieri

theorem n1_add_eZ_le {n : ℕ} (ν : Fin n → ℤ) (I : Finset (Fin n)) : n1 (ν + eZ I) ≤ n1 ν + I.card := by
  unfold n1
  have h1 : I.card = ∑ i : Fin n, (if i ∈ I then 1 else 0) := by
    rw [Finset.sum_boole]; simp
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply, eZ]
  split_ifs <;> omega

theorem JF_zero {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (g : B.Mat k r) :
    B.JF D 0 g = 0 := by
  simp [B.JF, Formalism.QuantumDeterminants.besselJ]

theorem supplied_pieri : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Sup p lam q0 R l l' dg s J tau → ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 → ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → (D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det • p.V (J ν) (TBB.bigPt P.r c) = ∑ I ∈ powersetCard (P.r + 1) (univ : Finset (Fin (2 * P.r + P.k + 1))), tau ν I • p.V (J (ν + eZ I)) (TBB.bigPt P.r c) := by
  intro H P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau hN hS ν hν c hc hG
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨γ, hγ, hZ, hV⟩ := GlobalTheory.T.exists_regularRep_besselBigCellVector_eq_bessel P Wp Wq p c hc hG
  simp only [hV]
  by_cases hJ : J ν = 0
  · rw [hJ, JF_zero, smul_zero]
    symm
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [hS.tau_zero ν I (Or.inl hJ), zero_smul]
  obtain ⟨c0, -, hdich⟩ := GlobalTheory.T.jN2_eq_const_mul_formal_degree_of_supG H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau hN hS
  obtain ⟨⟨-, -, -, -, hGap⟩, hfam⟩ := GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN
  have hν0 : n1 ν ≤ q0 := by omega
  have hνI : ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), n1 (ν + eZ I.1) ≤ q0 := by
    intro I
    have h1 := n1_add_eZ_le ν I.1
    rw [I.2] at h1
    have h2 : P.r + 1 ≤ (P.r + 1) * (P.r + 2) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  obtain ⟨io, pr, ep, hT, htau⟩ := hS.tau_eq ν hν
  have hnz : NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) := by
    by_contra hcon
    exact hJ (hS.zero ν fun hh => hcon hh.2)
  have key := GlobalTheory.T.tensor_weighted_bessel_gap H P.k P.r (Sub (2 * P.r + P.k + 1) (P.r + 1)) (Sub (2 * P.r + P.k + 1) (P.r + 1))
    (cmp (P.r + 1)) (cmp (P.r + 1) (Formalism.QuantumDeterminants.Hpk P.k P.r)) (P.r + 1) (R ν) (fun I => R (ν + eZ I.1)) io pr ep
    (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν a : ℝ))
    (fun I a => lam a + ((ν + eZ I.1) a : ℝ)) (h / 2) Wp Wq p.T.base
    (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z'))
    (l ν) (l' ν) (fun I => l (ν + eZ I.1)) (fun I => l' (ν + eZ I.1)) (J ν) (s ν)
    (fun I => J (ν + eZ I.1)) (fun I => s (ν + eZ I.1)) (fun I => tau ν I.1)
    (hS.fam ν hν0) (hfam ν hν0).2.2.1
    (fun I => ⟨hS.fam _ (hνI I), (hfam _ (hνI I)).2.2.1⟩) hGap
    (GlobalTheory.WedgeFRep.isFRep_cmp P.k P.r (P.r + 1)) hT
    (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form P.k P.r _ p.T.base.z_mem g hg).1)
    (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form P.k P.r _ p.T.base.z'_mem g hg).1)
    (fun I => ⟨(hS.left _ (hνI I)).1, (hS.right _ (hνI I)).1⟩)
    (hS.coef ν hν0 hnz.1 hnz.2).1
    (fun I => by
      rcases hdich _ (hνI I) with ⟨h0, -, hn⟩ | ⟨h0, hn, hn', hs, -⟩
      · exact Or.inl ⟨not_and_or.mp hn, hS.tau_zero ν I.1 (Or.inr h0)⟩
      · exact Or.inr ⟨(hS.coef _ (hνI I) hn hn').1, hs, htau I hJ h0⟩)
    γ hγ
  rw [GlobalTheory.TopMinorWedge.herm_cmp_wedge_eq_det, hZ] at key
  rw [key]
  symm
  exact Finset.sum_subtype _ (fun I => by simp) (fun I => tau ν I • B.JF p.T.base (J (ν + eZ I)) γ)

end GlobalTheory.SuppliedPieri
