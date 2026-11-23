import Formalism.GaussJetBounds.FrameJetEval
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

section Eval

lemma eval₂_jetPairPoly {F K : Type} [Field F] [Field K] {σ ι : Type} (φ : F →+* K) (x : σ → K)
    (P : MvPolynomial ι (MvPolynomial σ F)) (Th : MvPowerSeries ι F) :
    MvPolynomial.eval₂ φ x (jetPairPoly P Th) =
      jetPair (MvPolynomial.map (MvPolynomial.eval₂Hom φ x) P) (MvPowerSeries.map φ Th) := by
  classical
  unfold jetPairPoly jetPair
  rw [show MvPolynomial.eval₂ φ x = MvPolynomial.eval₂Hom φ x from rfl, map_sum]
  symm
  rw [Finset.sum_subset (MvPolynomial.support_map_subset _ P)]
  · refine Finset.sum_congr rfl fun κ _ => ?_
    simp [MvPolynomial.coeff_map, MvPowerSeries.coeff_map, mul_assoc]
  · intro κ _ hκ
    simp only [MvPolynomial.mem_support_iff, not_not] at hκ
    simp [hκ]

lemma ringMap_minorProd {R S : Type} [CommRing R] [CommRing S] {σ : Type} {N0 N1 C : ℕ}
    (ψ : MvPolynomial σ R →+* MvPolynomial σ S)
    (row : Fin N0 → Fin N1 → MvPolynomial σ R) (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) :
    ψ (minorProd row p hp I) = minorProd (fun i b => ψ (row i b)) p hp I := by
  unfold minorProd
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det]
  rfl

end Eval

section Maps

variable {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)
  {d N0 N1 : ℕ} [NeZero d] {ι : Type} [Fintype ι]

lemma constantCoeff_linSub (M : ZV d N0 N1 → ι → K) (z : ZV d N0 N1) :
    MvPowerSeries.constantCoeff (linSub M z) = 0 := by
  simp [linSub]

lemma constantCoeff_bSum (M : ZV d N0 N1 → ι → K) (be : MvPowerSeries (ZMod d) K)
    (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.constantCoeff (bSum M be) = 0 := by
  unfold bSum
  rw [map_sum]
  refine Finset.sum_eq_zero fun ab _ => ?_
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => constantCoeff_linSub M _)
    (fun s => constantCoeff_linSub M _) hbe

lemma map_linSub (M : ZV d N0 N1 → ι → F) (z : ZV d N0 N1) :
    MvPowerSeries.map φ (linSub M z) = linSub (fun z i => φ (M z i)) z := by
  unfold linSub
  simp [map_sum]

lemma map_bSum (M : ZV d N0 N1 → ι → F) (be : MvPowerSeries (ZMod d) F) :
    MvPowerSeries.map φ (bSum M be) = bSum (fun z i => φ (M z i)) (MvPowerSeries.map φ be) := by
  unfold bSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [MvPowerSeries.map_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => constantCoeff_linSub M _)]
  simp only [map_linSub]

lemma map_mvExp (f : MvPowerSeries ι F) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.map φ (mvExp f) = mvExp (MvPowerSeries.map φ f) := by
  unfold mvExp
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hf)]
  congr 1
  exact PowerSeries.map_exp φ

lemma map_idM : (fun (z i : ZV d N0 N1) => φ (idM z i)) = (idM : ZV d N0 N1 → ZV d N0 N1 → K) := by
  funext z i
  unfold idM
  split_ifs <;> simp

lemma map_thetaZ (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) F)
    (U : MvPowerSeries (ZV d N0 N1) F) (ε : F) (be : MvPowerSeries (ZMod d) F)
    (hg : ∀ y, MvPowerSeries.constantCoeff (g y) = 0) (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.map φ (thetaZ g U ε be) =
      thetaZ (fun y => MvPowerSeries.map φ (g y)) (MvPowerSeries.map φ U) (φ ε)
        (MvPowerSeries.map φ be) := by
  have hsm : ∀ (c : F) (f : MvPowerSeries (ZV d N0 N1) F),
      MvPowerSeries.map φ (c • f) = φ c • MvPowerSeries.map φ f := by
    intro c f
    ext n
    simp [MvPowerSeries.coeff_map]
  unfold thetaZ
  rw [map_mul,
    MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun z => constantCoeff_linSub idM z),
    MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hg),
    map_mvExp φ _ (by rw [MvPowerSeries.constantCoeff_smul, constantCoeff_bSum idM be hbe, smul_zero]),
    hsm, map_bSum]
  simp only [map_linSub, map_idM]

end Maps

section Change

variable {K : Type} [NormedField K] [CharZero K] {d N0 N1 : ℕ} [NeZero d]

lemma theta_subst (M Mg A : ZV d N0 N1 → ZV d N0 N1 → K)
    (h : ∀ z i, Mg z i = ∑ y, M z y * A i y) (G : MvPowerSeries (ZV d N0 N1) K) (ε : K)
    (be : MvPowerSeries (ZMod d) K) (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.subst (linSub Mg) G * mvExp (ε • bSum Mg be) =
      MvPowerSeries.subst
        (fun j : ZV d N0 N1 => (∑ i : ZV d N0 N1, MvPowerSeries.C (A i j) * MvPowerSeries.X i :
          MvPowerSeries (ZV d N0 N1) K))
        (MvPowerSeries.subst (linSub M) G * mvExp (ε • bSum M be)) := by
  set aa : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K := fun j =>
    ∑ i : ZV d N0 N1, MvPowerSeries.C (A i j) * MvPowerSeries.X i with haa
  have hs : MvPowerSeries.HasSubst aa :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => by simp [haa]
  have hlin : ∀ z, MvPowerSeries.subst aa (linSub M z) = linSub Mg z := subst_linSub _ _ _ h
  have hbS : MvPowerSeries.subst aa (bSum M be) = bSum Mg be := by
    unfold bSum
    rw [← MvPowerSeries.coe_substAlgHom hs, map_sum]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [MvPowerSeries.coe_substAlgHom hs, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => constantCoeff_linSub M _) hs]
    simp only [hlin]
  rw [MvPowerSeries.subst_mul hs, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_linSub M)) hs,
    subst_mvExp hs _ (by
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, constantCoeff_bSum _ _ hbe, mul_zero]),
    MvPowerSeries.subst_smul hs, hbS]
  simp only [hlin]

lemma frameM_idM (x : ZMod d × Fin N0 × Fin N0 → K) (z i : ZV d N0 N1) :
    frameM (N1 := N1) x z i =
      ∑ y, (idM : ZV d N0 N1 → ZV d N0 N1 → K) z y * frameM (N1 := N1) x y i := by
  simp [idM]

lemma sum_frameM_row (x : ZMod d × Fin N0 × Fin N0 → K) (s : ZMod d) (i : Fin N0) (b : Fin N1) :
    (∑ j : ZV d N0 N1, MvPolynomial.C (frameM (N1 := N1) x j (s, i, b)) * MvPolynomial.X j :
      MvPolynomial (ZV d N0 N1) K) =
      ∑ a : Fin N0, MvPolynomial.C (x (s, i, a)) * MvPolynomial.X (s, a, b) := by
  rw [show (∑ j : ZV d N0 N1, MvPolynomial.C (frameM (N1 := N1) x j (s, i, b)) * MvPolynomial.X j :
      MvPolynomial (ZV d N0 N1) K) =
      ∑ j : ZV d N0 N1, if j.1 = s ∧ j.2.2 = b then
        MvPolynomial.C (x (s, i, j.2.1)) * MvPolynomial.X (s, j.2.1, b) else 0 from
    Finset.sum_congr rfl fun j _ => ?_]
  · rw [Fintype.sum_prod_type]
    simp [Fintype.sum_prod_type, ite_and]
  · obtain ⟨t, a, c⟩ := j
    simp only [frameM]
    by_cases h : t = s ∧ c = b
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [if_neg (fun hh => h ⟨hh.1.symm, hh.2.symm⟩), if_neg h]
      simp

end Change

theorem frame_jet_evaluation : FrameJetEval := by
  intro F K _ _ _ _ φ d N0 N1 _ g U ε be hg hbe colN p hp I x
  unfold frameJet
  have hbe' : MvPowerSeries.constantCoeff (MvPowerSeries.map φ be) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hbe, map_zero]
  rw [eval₂_jetPairPoly, map_thetaZ φ g U ε be hg hbe,
    theta_subst idM (frameM x) (fun i y => frameM x y i) (fun z i => frameM_idM x z i) _ _ _ hbe',
    jet_pair_linearity K]
  unfold thetaZ
  congr 1
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [ringMap_minorProd]
  symm
  refine (ringMap_minorProd (MvPolynomial.aeval _).toRingHom _ _ _ _).trans ?_
  congr 1
  funext i b
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
  rw [sum_frameM_row]
  simp [MvPolynomial.map_C, MvPolynomial.map_X]

end Formalism.DworkPowerSeriesWeights
