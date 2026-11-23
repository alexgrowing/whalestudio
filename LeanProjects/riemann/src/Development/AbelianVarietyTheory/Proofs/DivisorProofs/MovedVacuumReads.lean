import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairUnitModulusFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockVacuumOfReadsGaussianEntireStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairMovesPhasedHeisenbergTranslateStatement

noncomputable section

section Entire
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.FockPos

namespace GlobalTheory.VacLine

theorem fock_real_entire : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 →
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) →
    ∃ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ ∧ ∀ w : WO S T, w.map (finPart D) = 0 →
      f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w) := by
  intro D ψ θ S T frS frT hS hT hψ hθ f hft hff
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨hF, hann⟩ := GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ hσ ψ hψ S T (fun _ => 1) (fun _ => 1) f
    hft hff
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hFdef
  set X := frLin frS frT with hX
  set r := Formalism.L2.Pj.xiR D with hr
  set E : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ := fun Z =>
    Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) with hE
  have hU : ∀ {k : ℕ} (fr : GL (Fin k) D.host.E) τ, IsUnit (frAt fr τ).det := fun fr τ =>
    isUnit_iff_ne_zero.2 (frAt_det_ne fr τ)
  have hG : Differentiable ℝ (fun Z => F (X Z)) := hF.comp (X.restrictScalars ℝ).differentiable
  have hdG : ∀ Z Y, fderiv ℝ (fun Z => F (X Z)) Z Y = fderiv ℝ F (X Z) (X Y) := fun Z Y => by
    have h : HasFDerivAt (fun Z => F (X Z)) ((fderiv ℝ F (X Z)).comp (X.restrictScalars ℝ)) Z :=
      (hF (X Z)).hasFDerivAt.comp Z (X.restrictScalars ℝ).hasFDerivAt
    rw [h.fderiv]
    rfl
  refine ⟨fun Z => F (X Z) * E Z,
    differentiable_mul_of_cr (fun Z => F (X Z)) E
      (fun Z Y => (2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ))
      hG (gauss_cr r).1 (fun Z Y => ?_) (gauss_cr r).2, fun w hw => ?_⟩
  · rw [hdG, hdG]
    have hj : jO S T (fun _ => 1) (fun _ => 1) (X Y) = X (Complex.I • Y) := by
      rw [X.map_smul]
      funext τ
      rw [jO_apply]
      change Complex.I • ((1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) * Matrix.of (X Y τ) *
        (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) = _
      rw [Matrix.one_mul, Matrix.mul_one]
      rfl
    have h := hann (X Z) (X Y)
    rw [hj] at h
    have hom : ∀ Y' : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank, omO S T (X Z) (X Y') =
        ∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y' τ a b)).re := by
      intro Y'
      rw [omO_apply]
      refine Finset.sum_congr rfl fun τ _ => ?_
      show 2 * (tauE D τ D.host.xi0 * hAt S T τ (X Z τ) (X Y' τ)).re = _
      unfold hAt
      rw [hX, frLin_apply, frLin_apply, trace_frames _ _ _ _ (frAt_on frS hS τ) (frAt_on frT hT τ), xi_zero_eq_host τ]
      rfl
    rw [hom, hom] at h
    have hs2 : ∀ τ, (∑ a, ∑ b, Z τ a b * starRingEnd ℂ ((Complex.I • Y) τ a b)) =
        -Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) := fun τ => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    simp only [hs2] at h
    have key : ((∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)).re : ℝ) : ℂ) +
        Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * (-Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b))).re : ℝ) : ℂ) =
        2 * Complex.I * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) := by
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      set s := ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)
      apply Complex.ext <;> simp <;> ring
    show _ = -((2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ) * F (X Z))
    have h' : fderiv ℝ F (X Z) (X Y) - Real.pi * Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)).re : ℝ) : ℂ) * F (X Z) +
      Complex.I * (fderiv ℝ F (X Z) (X (Complex.I • Y)) - Real.pi * Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * (-Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b))).re : ℝ) : ℂ) * F (X Z)) = 0 := h
    linear_combination h' + Real.pi * Complex.I * F (X Z) * key +
      2 * Real.pi * r * (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)) * F (X Z) * Complex.I_sq
  · have e1 : X (zCo θ frS frT w) = piW θ T S w := by
      funext τ
      rw [hX, frLin_apply]
      change frAt frT τ * ((frAt frT τ)⁻¹ * compAt θ τ w * frAt frS τ) * (frAt frS τ)⁻¹ = _
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.mul_one]
      rfl
    show f w = gaussO θ frS frT w * (f (iotaW σ T S (X (zCo θ frS frT w))) * E (zCo θ frS frT w))
    rw [e1, hσ.iota_pi hw, ← mul_assoc, mul_comm _ (f w), mul_assoc, hE, gaussO, ← Complex.exp_add]
    have e2 : -((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ) +
        ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ) = 0 := by
      rw [hr]; push_cast; ring
    rw [e2, Complex.exp_zero, mul_one]

end GlobalTheory.VacLine
end Entire

section Classical
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.VacMove
open scoped BigOperators Pointwise

namespace GlobalTheory.VacLine

theorem mem_thSp_of_lift {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ}
    {e0 : VC D N N' → ℂ} (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (hne : e0 ≠ 0)
    (g : GA D N) (g' : GA D N') {L₁ L₁'} (h : Moves D (g : GL (Fin N) (AE D)) L₁)
    (h' : Moves D (g' : GL (Fin N') (AE D)) L₁') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G)
    (hlift : ∀ z : Matrix (Fin N') (Fin N) D.host.E, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0 = e0 →
      ∃ m : ℕ, 0 < m ∧ ∀ z', CloseTo D cc m (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) z z' →
        G = Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') G) :
    G ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') := by
  have hcc : cc ≠ ⊥ := hc.1.1
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := klat _ (moves_one D N) (moves_one D N')
  have k1 := klat (tor0 D cc δ) h h'
  obtain ⟨-, hF, -, hinv⟩ := GlobalTheory.T.intertwinerUnitary_all D cc δ hc N N' _ _ k0 k1 e0 he
  have hF0 : Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 ≠ 0 := by
    intro h0
    rw [h0, iop_zero] at hinv
    exact hne hinv.symm
  obtain ⟨-, hW, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hc N N' _ k1
  refine ⟨hG, fun x hx => ?_⟩
  suffices hs : Wd D (tor0 D cc δ) x G = G by
    rw [hW x hx] at hs; exact congrFun hs
  have hmul : ∀ a ∈ La D (tor0 D cc δ) L₁ L₁', ∀ b ∈ La D (tor0 D cc δ) L₁ L₁', ∀ F,
      Wd D (tor0 D cc δ) a (Wd D (tor0 D cc δ) b F) = Wd D (tor0 D cc δ) (a + b) F := by
    intro a ha b hb F
    obtain ⟨φ, hφ⟩ := wd_wd D (tor0 D cc δ) a b
    have h2 := hφ (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0)
    rw [wd_fix (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc k1 hF hb, wd_fix (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc k1 hF ha, wd_fix (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc k1 hF (add_mem ha hb)] at h2
    have h3 : φ = 1 := by
      by_contra hne
      apply hF0
      have : (φ - 1) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 = 0 := by
        rw [sub_smul, one_smul, ← h2, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    rw [hφ, h3, one_smul]
  obtain ⟨z', rfl, hz'⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hcc N N' g g' L₁ L₁' h h' x hx
  have hlatb := GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hcc N N' g g' L₁ L₁' h h'
  have hlat0 := GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hcc N N' 1 1 _ _ (moves_one D N) (moves_one D N')
  simp only [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at hlat0
  simp only [← MI_one] at hz' hlatb hlat0
  obtain ⟨m0, hm0, hl0⟩ := hlift 0 (by rw [VacMove.pt_zero, VacMove.wd_zero])
  set P : Matrix (Fin N') (Fin N') (AE D) := ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) with hP
  set P' : Matrix (Fin N') (Fin N') (AE D) :=
    (((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) with hP'
  set Q : Matrix (Fin N) (Fin N) (AE D) := ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) with hQ
  set Q' : Matrix (Fin N) (Fin N) (AE D) :=
    (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) with hQ'
  have ePP : P * P' = 1 := Units.mul_inv _
  have eP'P : P' * P = 1 := Units.inv_mul _
  have eQQ : Q * Q' = 1 := Units.mul_inv _
  have eQ'Q : Q' * Q = 1 := Units.inv_mul _
  have e1 : ∀ M : Matrix (Fin N') (Fin N) (AE D), P * (P' * M * Q) * Q' = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ePP, Matrix.one_mul, Matrix.mul_assoc, eQQ, Matrix.mul_one]
  have e2 : ∀ M : Matrix (Fin N') (Fin N) (AE D), P' * (P * M * Q') * Q = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, eP'P, Matrix.one_mul, Matrix.mul_assoc, eQ'Q, Matrix.mul_one]
  obtain ⟨n, hn, hb⟩ := MI_bound hcc P Q'
  obtain ⟨n', hn', hb'⟩ := MI_bound hcc P' Q
  obtain ⟨z, hz⟩ := MI_approx hcc (P' * z'.map (inc D) * Q) (n * m0) (Nat.mul_pos hn hm0)
  have hz0 : MI D cc 1 (z.map (inc D)) := by
    simpa using (hz.of_dvd (one_dvd _)).add hz'
  obtain ⟨m, hm, hl⟩ := hlift z (wd_fix (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc k0 he (hlat0 z hz0))
  obtain ⟨w, hw⟩ := MI_approx hcc (P * z.map (inc D) * Q') (n' * (m * m0)) (by positivity)
  have hw1 : MI D cc 1 (P' * w.map (inc D) * Q) := by
    have := ((hb' _ _ hw).of_dvd (one_dvd _)).add hz0
    rwa [Matrix.mul_sub, Matrix.sub_mul, e2, sub_add_cancel] at this
  have hd : (w - z').map (inc D) = w.map (inc D) - z'.map (inc D) := by
    ext i j; simp
  have hd' : (z' - w).map (inc D) = z'.map (inc D) - w.map (inc D) := by
    ext i j; simp
  have hdiff : MI D cc m0 ((z' - w).map (inc D)) := by
    have h1 := hb _ _ hz
    rw [Matrix.mul_sub, Matrix.sub_mul, e1] at h1
    have h2 : MI D cc m0 (0 : Matrix (Fin N') (Fin N) (AE D)) := fun i j => ⟨0, zero_mem _, by simp⟩
    have := (h2.sub h1).sub (hw.of_dvd (m := m0) ⟨n' * m, by ring⟩)
    rw [hd']
    convert this using 1
    abel
  have f1 := hl w (hw.of_dvd (m := m) ⟨n' * m0, by ring⟩)
  have f2 := hl0 (z' - w) (by
    intro i j
    have h0 : (0 : Matrix (Fin N') (Fin N) D.host.E).map (inc D) = 0 := by ext; simp
    rw [h0, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    exact hdiff i j)
  have hdl : MI D cc 1 (P' * (z' - w).map (inc D) * Q) := by
    rw [hd', Matrix.mul_sub, Matrix.sub_mul]
    exact hz'.sub hw1
  have := hmul _ (hlatb w hw1) _ (hlatb _ hdl) G
  rw [← f2, ← f1, ← pt_add, add_sub_cancel] at this
  exact this.symm

theorem eq_smul_of_lift {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ}
    {e0 : VC D N N' → ℂ} (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0)
    (g : GA D N) (g' : GA D N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G)
    (hlift : ∀ z : Matrix (Fin N') (Fin N) D.host.E, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0 = e0 →
      ∃ m : ℕ, 0 < m ∧ ∀ z', CloseTo D cc m (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) z z' →
        G = Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') G) :
    ∃ c : ℂ, G = c • W.Om g g' e0 := by
  obtain ⟨Lt, h1, -⟩ := exists_lattice_of_adelic_point D N
  obtain ⟨Lt', h1', -⟩ := exists_lattice_of_adelic_point D N'
  have h := (h1 g).1
  have h' := (h1' g').1
  have hT := vac_TT (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 hc he
  have hO := mem_thSp_of_lift hc he W.nz g g' h h' (W.maps g g' e0 hT).1 (fun z hz => by
    obtain ⟨m, hm, hl⟩ := W.lift g g' z e0 hT
    rw [hz] at hl
    exact ⟨m, hm, hl⟩)
  have hO0 : W.Om g g' e0 ≠ 0 := by
    intro h0
    have h2 := W.mul g⁻¹ g g'⁻¹ g' e0 hT
    have h3 := W.smul g⁻¹ g'⁻¹ 0 e0 hT
    rw [zero_smul, zero_smul] at h3
    rw [inv_mul_cancel, inv_mul_cancel, W.one e0 hT, h0, h3] at h2
    exact W.nz h2
  exact (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hc N N' _ (klat (tor0 D cc δ) h h')).1 _
    (mem_thSp_of_lift hc he W.nz g g' h h' hG hlift) _ hO hO0

end GlobalTheory.VacLine
end Classical

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacLine

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem factor_ne (hset : Setup ψ θ S T cc δ r) (τ : D.what₂.Tau) : δ * embT D τ r ≠ 0 :=
  mul_ne_zero (delta_ne_zero hset.crv) ((map_ne_zero _).2 (hset.scale.ne_zero hset.crv.1.1))

theorem reads_inj {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} (hset : Setup ψ θ S T cc δ r) {G G' : VC D a d → ℂ}
    {f : WO S T → ℂ} (h : Reads ψ θ hS hT cc δ r G f) (h' : Reads ψ θ hS hT cc δ r G' f) : G = G' := by
  subst hS hT
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hset.inf
  funext Y
  set Z : GlobalTheory.FockCompare.RW T S := fun τ i j => (δ * embT D τ r)⁻¹ * Y τ i j with hZ
  have hw : (GlobalTheory.FockCompare.iotaW σ T S Z).map (finPart D) = 0 := by funext i j; exact hσ.fin _
  have hY : coordY θ rfl rfl δ r (GlobalTheory.FockCompare.iotaW σ T S Z) = Y := by
    funext τ i j
    show δ * embT D τ r * θ τ (infPart D (σ fun τ' => Z τ' i j)) = _
    rw [hσ.comp, hZ]
    exact mul_inv_cancel_left₀ (factor_ne hset τ) _
  have h1 := (h.2 _ hw).symm.trans (h'.2 _ hw)
  rw [hY] at h1
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) h1

theorem exists_reads {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (hset : Setup ψ θ S T cc δ r) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) :
    ∃ G : VC D a d → ℂ, Differentiable ℂ G ∧ Reads ψ θ hS hT cc δ r G f := by
  subst hS hT
  have hon : ∀ V : HSp D, V.gram = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)
      (1 : GL (Fin V.rank) D.host.E).1 * V.gram * (1 : GL (Fin V.rank) D.host.E).1 = 1 := by
    intro V hV
    rw [hV, Units.val_one, Matrix.mul_one, Matrix.mul_one]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, hij, Ne.symm hij, Matrix.one_apply]
  obtain ⟨Φ, hΦ, hw⟩ := fock_real_entire ψ θ S T 1 1 (hon S hset.gS) (hon T hset.gT) hset.std hset.inf f hf hv
  refine ⟨fun Y => Φ fun τ i j => (δ * embT D τ r)⁻¹ * Y τ i j, hΦ.comp (by fun_prop), ?_⟩
  rw [reads_iff hset.crv hset.scale]
  refine ⟨hf, fun w hw0 => ?_⟩
  rw [hw w hw0]
  congr 2
  funext τ i j
  exact (inv_mul_cancel_left₀ (factor_ne hset τ) _).symm

theorem moved_vacuum_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∃ c : ℂ, Reads ψ θ hS hT cc δ r (c • W.Om x y e0) (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hset e0 W χS χT om hom _ t0 _ _ he _ _ f₀ hf₀ x y g h hg hh
  have hθ := hset.inf
  have hv0 := GlobalTheory.T.isFockVacuum_of_readsGaussianEntire ψ θ S T hS hT cc δ r hset e0 f₀ he.1.1 hf₀
  have e : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (om (g, h) f₀) =
      om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀) := by
    intro τ z
    rw [GlobalTheory.OrientedHeis.om_dRho hom hθ g h τ z hf₀.1, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hh.1,
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S (inv_mem hg.1), Matrix.one_mul, Matrix.mul_one]
  have hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) (om (g, h) f₀) := by
    intro τ z
    have h0 := hv0 τ z
    unfold annih at h0 ⊢
    rw [e, e, ← map_smul, ← map_add, h0, map_zero]
  obtain ⟨G, hG, hR⟩ := exists_reads hS hT hset (hom.om_pres (g, h) f₀ hf₀.1) hv
  have hRt : ∀ (F : VC D a d → ℂ) (f' : WO S T → ℂ), Reads ψ θ hS hT cc δ r F f' → ∀ z,
      Reads ψ θ hS hT cc δ r (Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F)
        (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) • heisO ψ S T (finPt hS hT r z) f') := by
    intro F f' hF z
    exact (GlobalTheory.NormExact.heisO_finPt_reads ψ θ S T hS hT cc δ r hset F f' hF z).smul _
  obtain ⟨c, hc⟩ := eq_smul_of_lift hset.crv he.1 W x y hG (fun z hz => by
    obtain ⟨n, hn, hL⟩ := GlobalTheory.T.weilPair_moves_phasedHeisenbergTranslate ψ θ S T hS hT cc δ r hset χS χT om hom x y g h hg hh f₀ hf₀.1 z
    refine ⟨n, hn, fun z' hz' => ?_⟩
    have h1 := hRt e0 f₀ hf₀ z
    rw [hz] at h1
    have h2 := hL z' hz'
    rw [← map_smul, ← hf₀.unique h1] at h2
    have h3 := hRt G _ hR z'
    rw [← h2] at h3
    exact reads_inj hset hR h3)
  exact ⟨c, hc ▸ hR⟩

end GlobalTheory.VacLine

end
