import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugation
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SkewMod

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.CgMod

variable {D : D7} {n : ℕ}

def skewPart (D : D7) (n : ℕ) (x : Mx D n n) : Mx D n n := half D • (x - adj x)

theorem skewPart_add (x y : Mx D n n) : skewPart D n (x + y) = skewPart D n x + skewPart D n y := by
  simp only [skewPart, adj_add]
  rw [← smul_add]
  congr 1
  abel

def skewPartHom (D : D7) (n : ℕ) : Mx D n n →+ Mx D n n := AddMonoidHom.mk' (skewPart D n) skewPart_add

theorem skewPart_mem (x : Mx D n n) : skewPart D n x ∈ skewA D n := by
  rw [mem_skewA, skewPart, adj_smul, cA_half, adj_sub, adj_adj, ← smul_neg, neg_sub]

theorem skewPart_of_mem {s : Mx D n n} (hs : s ∈ skewA D n) : skewPart D n s = s := by
  rw [skewPart, mem_skewA.1 hs, sub_neg_eq_add, smul_add]
  exact half_smul_add s

theorem skewPart_anti {c : AE D} (hc : cA D c = -c) {s : Mx D n n} (hs : s ∈ skewA D n) :
    skewPart D n (c • s) = 0 := by
  rw [skewPart, adj_smul, mem_skewA.1 hs, hc, neg_smul, smul_neg, neg_neg, sub_self, smul_zero]

theorem skewPart_split {d e : AE D} (he : cA D e = -e) (hde : d * e = 1) (x : Mx D n n) :
    skewPart D n x + d • skewPart D n (e • x) = x := by
  have h : d * half D * e = half D := by rw [mul_comm d, mul_assoc, hde, mul_one]
  rw [skewPart, skewPart, adj_smul, he, neg_smul, sub_neg_eq_add, ← smul_add, smul_smul, smul_smul, h, smul_add,
    smul_sub]
  have := half_smul_add x
  rw [sub_add_add_cancel]
  exact this

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_skewPart : Continuous (skewPartHom D n) := by
  haveI : IsTopologicalAddGroup (Mx D n n) := (lattice_Mx D n n).1
  have h : Continuous fun x : Mx D n n => x - adj x := continuous_id.sub (continuous_adj (D := D) (m := n) (n := n))
  change Continuous fun x : Mx D n n => half D • (x - adj x)
  exact h.const_smul (half D)

theorem lr_skew (a : GL (Fin n) (AE D)) : ∀ s ∈ skewA D n, GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ s ∈ skewA D n :=
  fun s hs => (skewConj a.1 ⟨s, hs⟩).2

theorem lr_skew_symm (a : GL (Fin n) (AE D)) :
    ∀ s ∈ skewA D n, (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹).symm s ∈ skewA D n :=
  fun s hs => (skewConj (a⁻¹).1 ⟨s, hs⟩).2

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem map_skewConj : ∀ (D : D7) (r : ℕ) (κ : Measure (skewA D r)), κ.IsAddHaarMeasure → ∀ a : GL (Fin r) (AE D), κ.map (skewConj a.1) = ((absA D (Matrix.GeneralLinearGroup.det a) ^ r)⁻¹ : ℝ≥0) • κ := by
  intro D n κ hκ a
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (skewA D n) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (skewA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  have hcl : IsClosed (skewA D n : Set (Mx D n n)) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D n) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨d, e, hde, hd, he⟩ := exists_anti_units D
  have hsq := char_sq (skewA D n) (skewPartHom D n) continuous_skewPart skewPart_mem
    (fun s hs => skewPart_of_mem hs) (mulCE d e hde)
    (fun s hs => skewPart_anti hd hs) (fun s hs => skewPart_anti he hs)
    (fun x => skewPart_split he hde x) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹)
    (lr_smul a d e hde) (lr_skew a) (lr_skew_symm a)
  have hlr : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE _ _ D.sp.cm.sig (isCMExt_host D) n n a (ad a)⁻¹
    rw [h]
    exact congrArg (fun t => absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * t ^ n) (absA_det_ad_inv a)
  have hT : addEquivAddHaarChar (restr (skewA D n) _ (lr_skew a) (lr_skew_symm a)) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n :=
    (pow_left_inj₀ zero_le zero_le two_ne_zero).1 ((hsq.trans hlr).trans (sq _).symm)
  have h := addEquivAddHaarChar_smul_map κ (restr (skewA D n) _ (lr_skew a) (lr_skew_symm a))
  have e1 : (⇑(restr (skewA D n) _ (lr_skew a) (lr_skew_symm a)) : skewA D n → skewA D n) = skewConj a.1 := rfl
  rw [hT, e1] at h
  have hne : absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n ≠ 0 := pow_ne_zero _ (absA_pos _).ne'
  conv_rhs => rw [← h]
  rw [smul_smul, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.CompanionTheory.SkewMod
