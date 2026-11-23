import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixBlockThreeMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenDomP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbWords
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AutomorphicInSphericalLevel

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section conj

variable {k p ρ : ℕ}

theorem muP_conj_unipotent (q : Matrix (Fin p) (Fin p) ℂ) (hq : IsUnit q.det) (a : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ)
    (b : Matrix (Fin p) (Fin p) ℂ) (c : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) :
    U.muP k p ρ q * U.blk3 1 a b 0 1 c 0 0 1 * U.muP k p ρ q⁻¹ =
      U.blk3 1 (q * a) (q * b * (G.wMat p * (q⁻¹)ᴴ⁻¹ * G.wMat p)) 0 1 (c * (G.wMat p * (q⁻¹)ᴴ⁻¹ * G.wMat p)) 0 0 1 := by
  unfold U.muP
  rw [Ux3.block3_mul, Ux3.block3_mul]
  have hq' : IsUnit qᴴ.det := by rw [Matrix.det_conjTranspose]; exact hq.star
  have e1 : (G.wMat p * qᴴ⁻¹ * G.wMat p) * (G.wMat p * (q⁻¹)ᴴ⁻¹ * G.wMat p) = 1 := by
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hq']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (G.wMat p) (G.wMat p), Ux3.wMat_mul_self, Matrix.one_mul,
      ← Matrix.mul_assoc qᴴ⁻¹, Matrix.nonsing_inv_mul _ hq', Matrix.one_mul, Ux3.wMat_mul_self]
  congr 1 <;> simp [Matrix.mul_nonsing_inv _ hq, Matrix.mul_assoc]
  simp only [Matrix.mul_assoc] at e1 ⊢
  exact e1

theorem embG_uni_conj (y : B.Mat k ρ) (hy : IsUnit y.det) (a : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ)
    (b : Matrix (Fin p) (Fin p) ℂ) (c : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) :
    U.embG k p ρ y * U.blk3 1 a b 0 1 c 0 0 1 * U.embG k p ρ y⁻¹ =
      U.blk3 1 (a * y⁻¹) b 0 1 (y * c) 0 0 1 := by
  unfold U.embG
  rw [Ux3.block3_mul, Ux3.block3_mul]
  congr 1 <;> simp [Matrix.mul_nonsing_inv _ hy]

theorem rn_uni (x : U.RC k p ρ) : ∃ a b c, U.Rn k p ρ x = U.blk3 1 a b 0 1 c 0 0 1 :=
  ⟨_, _, _, Ux3.rn_eq x⟩

end conj

section gN

variable {k r : ℕ}

theorem gN_conjTranspose (a : B.Mat k r) : B.gN aᴴ = B.gN a := by
  unfold B.gN
  congr 1
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply, Complex.normSq_conj]

theorem gv_eq_hinv {u : B.Mat k r} (hu : u ∈ B.GV k r) : u = Hpk k r * (u⁻¹)ᴴ * Hpk k r := by
  have h1 := Formalism.FourierDecayAlt.P.B6.inv_eq_hermitian_form_conjTranspose (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hu)
  rw [Matrix.nonsing_inv_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hu)] at h1
  exact h1

theorem gN_le_inv {u : B.Mat k r} (hu : u ∈ B.GV k r) : B.gN u ≤ B.gN (Hpk k r) ^ 2 * B.gN u⁻¹ := by
  conv_lhs => rw [gv_eq_hinv hu]
  calc B.gN (Hpk k r * (u⁻¹)ᴴ * Hpk k r) ≤ B.gN (Hpk k r * (u⁻¹)ᴴ) * B.gN (Hpk k r) := Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _
    _ ≤ B.gN (Hpk k r) * B.gN ((u⁻¹)ᴴ) * B.gN (Hpk k r) :=
        mul_le_mul_of_nonneg_right (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _) (Formalism.FourierDecayAlt.P.B6.gN_nonneg _)
    _ = _ := by rw [gN_conjTranspose]; ring

end gN

section mid

variable {k p ρ : ℕ}

theorem embG_uni_mid (ν : B.Mat k ρ) (a : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (b : Matrix (Fin p) (Fin p) ℂ)
    (c : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (i j : Fin (2 * ρ + k + 1)) :
    (U.embG k p ρ ν * U.blk3 1 a b 0 1 c 0 0 1) (U.eB k p ρ (Sum.inl (Sum.inr i))) (U.eB k p ρ (Sum.inl (Sum.inr j))) =
      ν i j := by
  unfold U.embG
  rw [Ux3.block3_mul, Ux3.block3_apply]
  simp

end mid

section proper

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem cont_embG : Continuous (fun y : B.Mat k ρ => U.embG k p ρ y) := by
  have e : (fun y : B.Mat k ρ => U.embG k p ρ y) = fun y => ιLev k p ρ y := by
    funext y; exact (Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG p ρ y).symm
  rw [e]
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold ιLev
  split_ifs <;> first | exact (continuous_apply _).comp (continuous_apply _) | exact continuous_const

theorem closedGV (k r : ℕ) : IsClosed (B.GV k r) := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).closed

theorem properA (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq)
    (hmuP : ∀ q : Matrix (Fin p) (Fin p) ℂ, IsUnit q.det → U.muP k p ρ q ∈ B.GV k (p + ρ))
    (hM : ∀ y ∈ domP k (p + ρ) p B0.z B0.z', y ∈ B.GV k (p + ρ) →
      ∃ q : Matrix (Fin p) (Fin p) ℂ, IsUnit q.det ∧ ∃ V ∈ nhds y, IsCompact V ∧
        ∀ g ∈ V, g ∈ B.GV k (p + ρ) → U.muP k p ρ q * g ∈ JF.Om k (p + ρ) B0.z B0.z')
    (Cs : Set (B.Mat k (p + ρ))) (hCs : IsCompact Cs) :
    PartialBesselProperness.Proper Bj B0 rfl Cs (domP k (p + ρ) p B0.z B0.z') := by
  intro y hy
  by_cases hyG : y ∈ B.GV k (p + ρ)
  swap
  · exact ⟨(B.GV k (p + ρ))ᶜ, (closedGV k (p + ρ)).isOpen_compl.mem_nhds hyG, ∅, isCompact_empty,
      fun g hg hgG => absurd hgG hg⟩
  obtain ⟨q, hq, V, hV, hVc, hVO⟩ := hM y hy hyG
  have hqi : IsUnit q⁻¹.det := by rw [Matrix.det_nonsing_inv]; exact hq.ringInverse

  set KO := (fun g => U.muP k p ρ q * g) '' (V ∩ B.GV k (p + ρ)) with hKOdef
  have hKOc : IsCompact KO :=
    (hVc.inter_right (closedGV k (p + ρ))).image (continuous_const.mul continuous_id)
  have hKO : KO ⊆ JF.Om k (p + ρ) B0.z B0.z' := by
    rintro _ ⟨g, ⟨hgV, hgG⟩, rfl⟩; exact hVO g hgV hgG
  obtain ⟨C, hC0, hC⟩ := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.orbit B0.z B0.z' KO hKOc hKO

  have hW : IsCompact (UWset k ρ Bj.z) := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k ρ Bj.z Bj.z_mem Bj.T_pos
  have hW' : IsCompact (UWset k (p + ρ) B0.z') :=
    Formalism.FourierDecayAlt.P.weyl_subgroup_compact k (p + ρ) B0.z' B0.z'_mem B0.T'_pos
  set Kc := (fun t : B.Mat k ρ × B.Mat k (p + ρ) × B.Mat k (p + ρ) =>
    U.embG k p ρ t.1 * U.muP k p ρ q * t.2.1 * (Hpk k (p + ρ) * t.2.2ᴴ * Hpk k (p + ρ))) ''
      (UWset k ρ Bj.z ×ˢ Cs ×ˢ UWset k (p + ρ) B0.z') with hKcdef
  have hKcc : IsCompact Kc := by
    refine (hW.prod (hCs.prod hW')).image ?_
    have h1 : Continuous (fun t : B.Mat k ρ × B.Mat k (p + ρ) × B.Mat k (p + ρ) => U.embG k p ρ t.1) :=
      (cont_embG (k := k) (p := p) (ρ := ρ)).comp continuous_fst
    exact ((h1.mul continuous_const).mul continuous_snd.fst).mul
      ((continuous_const.mul continuous_snd.snd.matrix_conjTranspose).mul continuous_const)
  obtain ⟨M, hMb⟩ := hKcc.exists_bound_of_continuousOn Formalism.FourierDecayAlt.P.B6.gN_continuous.continuousOn
  set M0 : ℝ := max M 0 with hM0
  have hM00 : 0 ≤ M0 := le_max_right _ _
  set B1 : ℝ := C * M0 ^ (2 * (p + ρ) + 1) with hB1
  have hB10 : 0 ≤ B1 := mul_nonneg hC0 (pow_nonneg hM00 _)

  have hνc : IsCompact (Metric.closedBall (0 : Mt k ρ) B1) := isCompact_closedBall _ _
  have hfν : Continuous (fun ν : Mt k ρ => B.gN (U.embG k p ρ (Hpk k ρ * (Matrix.of ν : B.Mat k ρ)ᴴ * Hpk k ρ))) := by
    have hof : Continuous (fun ν : Mt k ρ => (Matrix.of ν : B.Mat k ρ)) := continuous_id
    exact Formalism.FourierDecayAlt.P.B6.gN_continuous.comp (cont_embG.comp
      ((continuous_const.mul hof.matrix_conjTranspose).mul continuous_const))
  obtain ⟨cν, hcν⟩ := hνc.exists_bound_of_continuousOn hfν.continuousOn

  have hfW : Continuous (fun t : B.Mat k ρ => B.gN (U.embG k p ρ t) + B.gN (U.embG k p ρ (Hpk k ρ * tᴴ * Hpk k ρ)) +
      B.gN t) := by
    refine ((Formalism.FourierDecayAlt.P.B6.gN_continuous.comp cont_embG).add (Formalism.FourierDecayAlt.P.B6.gN_continuous.comp (cont_embG.comp
      ((continuous_const.mul continuous_id.matrix_conjTranspose).mul continuous_const)))).add
      Formalism.FourierDecayAlt.P.B6.gN_continuous
  obtain ⟨cW, hcW⟩ := hW.exists_bound_of_continuousOn hfW.continuousOn
  set gH : ℝ := B.gN (Hpk k (p + ρ)) with hgH
  set B2 : ℝ := gH ^ 2 * (max cν 0 * B1) with hB2
  set B3 : ℝ := B.gN (U.muP k p ρ q⁻¹) * (max cW 0 * B2 * max cW 0) * B.gN (U.muP k p ρ q) with hB3
  set Rb : ℝ := max (max (max cW 0) B1) B3 with hRb
  refine ⟨V, hV, Metric.closedBall 0 Rb, isCompact_closedBall _ _, ?_⟩
  intro g hgV hgG x hx hxK ξ hξ hcC
  apply hxK
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl] at hcC

  set h : B.Mat k ρ := Matrix.of x.1.1 with hhdef
  set ν : B.Mat k ρ := Matrix.of x.1.2 with hνdef
  set n' : B.Mat k (p + ρ) := Matrix.of ξ.2 with hn'def
  set h' : B.Mat k (p + ρ) := Matrix.of ξ.1 with hh'def
  have hhW : h ∈ UWset k ρ Bj.z := hx.1
  have hνN : ν ∈ Nset k ρ := hx.2
  have hhG : h ∈ B.GV k ρ := hx.1.1
  have hνG : ν ∈ B.GV k ρ := hx.2.1
  have hhu : IsUnit h.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hhG
  have hνu : IsUnit ν.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hνG
  have hsP : sP Bj x = U.Rn k p ρ (-x.2) * U.embG k p ρ (h⁻¹ * ν⁻¹) := by unfold sP; rw [if_pos hx]
  have hembG : ∀ y : B.Mat k ρ, y ∈ B.GV k ρ → U.embG k p ρ y ∈ B.GV k (p + ρ) := fun y hy => by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]; exact Formalism.FourierDecayAlt.P.Dx2.Tower.lev_GV p ρ y hy

  obtain ⟨a0, b0, c0, hRn⟩ := rn_uni (k := k) (p := p) (ρ := ρ) (-x.2)
  set R' := U.muP k p ρ q * U.Rn k p ρ (-x.2) * U.muP k p ρ q⁻¹ with hR'def
  have hR'G : R' ∈ B.GV k (p + ρ) :=
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (hmuP q hq) (LeftFubiniLemmas.rn_nset _).1) (hmuP q⁻¹ hqi)
  set U1 := U.embG k p ρ h * R' * U.embG k p ρ h⁻¹ with hU1def
  have hU1G : U1 ∈ B.GV k (p + ρ) :=
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (hembG h hhG) hR'G) (hembG _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hhG))
  have hU1form : U1 = U.blk3 1 (q * a0 * h⁻¹) (q * b0 * (G.wMat p * (q⁻¹)ᴴ⁻¹ * G.wMat p)) 0 1
      (h * (c0 * (G.wMat p * (q⁻¹)ᴴ⁻¹ * G.wMat p))) 0 0 1 := by
    rw [hU1def, hR'def, hRn, muP_conj_unipotent q hq, embG_uni_conj h hhu]
  have hU1N : U1 ∈ Nset k (p + ρ) := by
    have hG' := hU1G
    rw [hU1form] at hG' ⊢
    exact Formalism.FourierDecayAlt.P.Ux3.uni_nset _ _ _ hG'
  set n1inv := U1 * U.embG k p ρ ν⁻¹ with hn1invdef
  have hn1invN : n1inv ∈ Nset k (p + ρ) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul hU1N (LeftFubiniLemmas.embG_nset (Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hνN))
  set n1 := n1inv⁻¹ with hn1def
  have hn1N : n1 ∈ Nset k (p + ρ) := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn1invN
  have hn1inv : n1⁻¹ = n1inv := Matrix.nonsing_inv_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hn1invN.1)

  have hq1 : U.muP k p ρ q⁻¹ * U.muP k p ρ q = 1 := by
    rw [Formalism.FourierDecayAlt.P.Dx2.Split.leviElement_mul, Matrix.nonsing_inv_mul _ hq, Formalism.FourierDecayAlt.P.PBM.muP_one]
  have hcomm : ∀ (y : B.Mat k ρ) (X : B.Mat k (p + ρ)),
      U.embG k p ρ y * (U.muP k p ρ q * X) = U.muP k p ρ q * (U.embG k p ρ y * X) := fun y X => by
    rw [← Matrix.mul_assoc, LeftFubiniLemmas.embedded_group_measure_preserving k p ρ y q, Matrix.mul_assoc]
  have hh'u : h' * h'⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hξ.1.1)
  have hmid : ∀ X : B.Mat k (p + ρ), U.muP k p ρ q⁻¹ * (U.embG k p ρ h⁻¹ * (U.embG k p ρ ν⁻¹ *
      (U.muP k p ρ q * X))) = U.embG k p ρ h⁻¹ * (U.embG k p ρ ν⁻¹ * X) := fun X => by
    rw [hcomm ν⁻¹ X, hcomm h⁻¹, ← Matrix.mul_assoc, hq1, Matrix.one_mul]
  have key : n1inv * (U.muP k p ρ q * g) * n' =
      U.embG k p ρ h * U.muP k p ρ q * (sP Bj x * g * n' * h') * h'⁻¹ := by
    rw [hsP, LeftFubiniLemmas.embG_mul, hn1invdef, hU1def, hR'def]
    simp only [Matrix.mul_assoc]
    rw [hmid, hh'u, Matrix.mul_one]
  have hKc : n1inv * (U.muP k p ρ q * g) * n' ∈ Kc := by
    rw [key]
    refine ⟨(h, sP Bj x * g * n' * h', h'), ⟨hhW, hcC, hξ.1⟩, ?_⟩
    simp only []
    rw [Formalism.FourierDecayAlt.P.B6.inv_eq_hermitian_form_conjTranspose hξ.1.1]
  have hg'KO : U.muP k p ρ q * g ∈ KO := ⟨g, ⟨hgV, hgG⟩, rfl⟩
  have hbd1 := (hC _ hg'KO n1 hn1N n' hξ.2).1
  rw [hn1inv] at hbd1
  have hgNle : B.gN (n1inv * (U.muP k p ρ q * g) * n') ≤ M0 := by
    have := hMb _ hKc
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hn1b : B.gN n1 ≤ B1 := hbd1.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Formalism.FourierDecayAlt.P.B6.gN_nonneg _) hgNle _) hC0)

  have hn1form : n1 = U.embG k p ρ ν * U1⁻¹ := by
    rw [hn1def, hn1invdef, Matrix.mul_inv_rev, LeftFubiniLemmas.embG_inv hνu,
      Matrix.nonsing_inv_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh (hembG ν hνG))]
  have hνb : ‖x.1.2‖ ≤ B1 := by
    refine (pi_norm_le_iff_of_nonneg hB10).2 fun i => (pi_norm_le_iff_of_nonneg hB10).2 fun j => ?_
    have e := embG_uni_mid (p := p) ν (-(q * a0 * h⁻¹))
      ((q * a0 * h⁻¹) * (h * (c0 * (G.wMat p * (q⁻¹)ᴴ⁻¹ * G.wMat p))) -
        q * b0 * (G.wMat p * (q⁻¹)ᴴ⁻¹ * G.wMat p)) (-(h * (c0 * (G.wMat p * (q⁻¹)ᴴ⁻¹ * G.wMat p)))) i j
    rw [← Formalism.FourierDecayAlt.P.Ux3.uni_inv, ← hU1form, ← hn1form] at e
    show ‖ν i j‖ ≤ B1
    rw [← e]
    exact (Formalism.FourierDecayAlt.P.Ux6.entry_le_gN _ _ _).trans hn1b

  have hU1inv : U1⁻¹ = U.embG k p ρ ν⁻¹ * n1 := by
    rw [hn1form, ← Matrix.mul_assoc, LeftFubiniLemmas.embG_inv hνu, Matrix.nonsing_inv_mul _
      (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh (hembG ν hνG)), Matrix.one_mul]
  have hνinv : ν⁻¹ = Hpk k ρ * (Matrix.of x.1.2 : B.Mat k ρ)ᴴ * Hpk k ρ := Formalism.FourierDecayAlt.P.B6.inv_eq_hermitian_form_conjTranspose hνG
  have hcνb : B.gN (U.embG k p ρ ν⁻¹) ≤ max cν 0 := by
    rw [hνinv]
    have := hcν x.1.2 (by rw [Metric.mem_closedBall, dist_zero_right]; exact hνb)
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hU1ib : B.gN U1⁻¹ ≤ max cν 0 * B1 := by
    rw [hU1inv]
    exact (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _).trans (mul_le_mul hcνb hn1b (Formalism.FourierDecayAlt.P.B6.gN_nonneg _) (le_max_right _ _))
  have hU1b : B.gN U1 ≤ B2 :=
    (gN_le_inv hU1G).trans (mul_le_mul_of_nonneg_left hU1ib (pow_nonneg (Formalism.FourierDecayAlt.P.B6.gN_nonneg _) _))

  have hWb : ∀ t ∈ UWset k ρ Bj.z, B.gN (U.embG k p ρ t) ≤ max cW 0 ∧
      B.gN (U.embG k p ρ (Hpk k ρ * tᴴ * Hpk k ρ)) ≤ max cW 0 ∧ B.gN t ≤ max cW 0 := by
    intro t ht
    have := hcW t ht
    rw [Real.norm_eq_abs] at this
    have h0 := Formalism.FourierDecayAlt.P.B6.gN_nonneg (U.embG k p ρ t)
    have h1 := Formalism.FourierDecayAlt.P.B6.gN_nonneg (U.embG k p ρ (Hpk k ρ * tᴴ * Hpk k ρ))
    have h2 := Formalism.FourierDecayAlt.P.B6.gN_nonneg t
    have hle := (le_abs_self _).trans this
    refine ⟨?_, ?_, ?_⟩ <;> exact le_max_of_le_left (by linarith)
  have hR'eq : R' = U.embG k p ρ h⁻¹ * U1 * U.embG k p ρ h := by
    rw [hU1def, LeftFubiniLemmas.embG_inv hhu]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh (hembG h hhG)), Matrix.mul_one,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh (hembG h hhG)), Matrix.one_mul]
  have hhinv : h⁻¹ = Hpk k ρ * hᴴ * Hpk k ρ := Formalism.FourierDecayAlt.P.B6.inv_eq_hermitian_form_conjTranspose hhG
  have hR'b : B.gN R' ≤ max cW 0 * B2 * max cW 0 := by
    rw [hR'eq]
    refine (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _).trans ?_
    refine mul_le_mul ((Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _).trans (mul_le_mul ?_ hU1b (Formalism.FourierDecayAlt.P.B6.gN_nonneg _)
      (le_max_right _ _))) (hWb h hhW).1 (Formalism.FourierDecayAlt.P.B6.gN_nonneg _)
      (mul_nonneg (le_max_right _ _) (le_trans (Formalism.FourierDecayAlt.P.B6.gN_nonneg _) hU1b))
    rw [hhinv]; exact (hWb h hhW).2.1
  have hRneq : U.Rn k p ρ (-x.2) = U.muP k p ρ q⁻¹ * R' * U.muP k p ρ q := by
    rw [hR'def]
    simp only [Matrix.mul_assoc]
    rw [hq1, Matrix.mul_one, ← Matrix.mul_assoc, hq1, Matrix.one_mul]
  have hxRb : ‖x.2‖ ≤ B3 := by
    rw [← norm_neg]
    refine (Formalism.FourierDecayAlt.P.Ux6.norm_le_gN_Rn _).trans ?_
    rw [hRneq]
    refine (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (Formalism.FourierDecayAlt.P.B6.gN_nonneg _))
    exact (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _).trans (mul_le_mul_of_nonneg_left hR'b (Formalism.FourierDecayAlt.P.B6.gN_nonneg _))
  have hhb : ‖x.1.1‖ ≤ max cW 0 :=
    (Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet.norm_le_gN x.1.1).trans (hWb h hhW).2.2
  rw [Metric.mem_closedBall, dist_zero_right]
  refine max_le (max_le ?_ ?_) ?_
  · exact hhb.trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact hνb.trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact hxRb.trans (le_max_right _ _)

end proper

end Formalism.FourierDecayAlt.P.PBQ
