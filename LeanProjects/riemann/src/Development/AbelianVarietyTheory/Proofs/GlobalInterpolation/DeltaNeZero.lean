import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InterTransport
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgreeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MovedVacuumMemThetaFunctionsAndMovesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticFormIntegralOfSelfDualPeriodLatticesStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.ThetaMove.SeamMoves

variable {X : Fields} {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
  (cD : D.what₂.Tau → ℂ)

def reidx (a b : ℕ) : VCx X.Tau a b ≃ₗ[ℂ] TaylorLogMetric.VC D a b := LinearEquiv.funCongrLeft ℂ (Fin b → Fin a → ℂ) s.iT.symm

theorem form_reidx (A : ℝ) (a b : ℕ) (x y : VCx X.Tau a b) :
    formV A D.what₂.Tau a b (reidx s a b x) (reidx s a b y) = Formalism.L2.Ker.HV A⁻¹ x y := by
  change (∑ τ, ∑ i, ∑ j, x (s.iT.symm τ) i j * (starRingEnd ℂ) (y (s.iT.symm τ) i j)) / (A : ℂ) =
    ((A⁻¹ : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)
  rw [Equiv.sum_comp s.iT.symm (fun τ => ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)), Complex.ofReal_inv, div_eq_inv_mul]

theorem isHerm_formV (A : ℝ) (n : Type) [Fintype n] (a b : ℕ) : IsHerm (formV A n a b) := by
  intro x y
  simp [formV, map_sum, mul_comm]

theorem iop_eq {a b : ℕ} (Λ₁ Λ₂ : AddSubgroup (TaylorLogMetric.VC D a b)) (G : TaylorLogMetric.VC D a b → ℂ) :
    TaylorLogMetric.Iop D B.tor Λ₁ Λ₂ G = inter (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) Λ₁ Λ₂ G := rfl

theorem alV_eq {a b : ℕ} (x : VCx X.Tau a b) {m : ℤ}
    (hm : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D B.tor (reidx s a b x) (reidx s a b x)).re = (m : ℝ)) :
    alV D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x = TaylorLogMetric.al D B.tor (reidx s a b x) := by
  have h1 : TaylorLogMetric.Hf D B.tor (reidx s a b x) (reidx s a b x) = Formalism.L2.Ker.HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x x :=
    form_reidx s _ a b x x
  unfold TaylorLogMetric.al
  rw [hm, round_intCast]
  rw [h1] at hm
  unfold alV alphaQ Formalism.L2.Th1.H.qOf
  rw [hm, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

include B in
theorem delta_ne_zero : δ ≠ 0 := by
  rintro rfl
  have h1 : B.L.ω₁ ∈ B.L.lattice.toAddSubgroup := B.L.ω₁_mem_lattice
  have h2 : TaylorLogMetric.lamOf D cc 0 ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨c, -, rfl⟩
    simp
  rw [B.lat] at h1
  have h3 : B.L.ω₁ = 0 := AddSubgroup.mem_bot.1 (h2 h1)
  exact B.L.indep.ne_zero 0 h3

theorem aa_ne_bot (hcc : cc ≠ ⊥) : (ambOf s B χ cD).AA ≠ ⊥ := by
  intro h
  have h1 : ((Ideal.absNorm cc : ℕ) : X.E) ∈ (ambOf s B χ cD).AA := by
    refine Submodule.subset_span ⟨_, Ideal.absNorm_mem cc, 1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, ?_⟩
    simp
  rw [h, Submodule.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at h1
  exact hcc h1

theorem aa_fg : (ambOf s B χ cD).AA.FG := by
  let j : 𝓞 D.host.E →+* 𝓞 X.E := RingOfIntegers.mapRingHom (s.iE.symm : D.host.E →+* X.E)
  have hj : ∀ a : 𝓞 D.host.E, ((j a : 𝓞 X.E) : X.E) = s.iE.symm (a : D.host.E) := fun _ => rfl
  obtain ⟨z, hz, hden⟩ := D.host.AA0.isFractional
  have hz0 : j z ≠ 0 := fun h => nonZeroDivisors.ne_zero hz (by
    have h1 := hj z
    rw [h] at h1
    have h2 : (z : D.host.E) = 0 := s.iE.symm.injective (by rw [← h1]; simp)
    exact RingOfIntegers.coe_injective (by simpa using h2))
  have hfr : IsFractional (nonZeroDivisors (𝓞 X.E)) (ambOf s B χ cD).AA := by
    refine (FractionalIdeal.isFractional_span_iff).2 ⟨j z, mem_nonZeroDivisors_of_ne_zero hz0, ?_⟩
    rintro r ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := hden t ht
    refine ⟨j (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩
    rw [Algebra.smul_def]
    change ((j _ : 𝓞 X.E) : X.E) = ((j z : 𝓞 X.E) : X.E) * _
    rw [hj, hj, ← map_mul]
    congr 1
    have e : ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w : 𝓞 D.host.E) : D.host.E) =
      ((c : D.host.K) : D.host.E) * (w : D.host.E) := rfl
    have hw' : (w : D.host.E) = (z : D.host.E) * t := by rw [Algebra.smul_def] at hw; exact hw
    rw [e, hw']
    ring
  exact FractionalIdeal.fg_of_isNoetherianRing le_rfl ⟨_, hfr⟩

theorem vac_eq {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (h : Base.chiFac χ a b (s.lat N) (s.lat N') ≠ 0) :
    vac (ambOf s B χ cD) N N' = fun z => B.thMoved a b (s.lat N) (s.lat N') (reidx s a b z) := by
  funext z
  exact inv_mul_cancel_left₀ h _

theorem moves_ambOf : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsChi D χ → B.EqP χ → B.LatAll → B.ThZeroMem a b → Even a → Even b → Moves (ambOf s B χ cD) a b := by
  intro X D s cc δ B χ cD a b hX hs hcc hχ hE hL hZ ha hb
  obtain ⟨hsd, hlam⟩ := GlobalTheory.T.fieldIso_selfDual_and_periodLattices_agree X D s cc δ B χ cD hs
  obtain ⟨hth, hm1, hm2⟩ := GlobalTheory.T.movedVacuum_mem_thetaFunctions_and_moves D cc δ B χ a b hχ hE hL hZ ha hb
  have hq := GlobalTheory.T.quadraticForm_integral_of_selfDual_periodLattices D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  have key := fun (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E a)) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)) (h : IsSdLat N₂)
      (h' : IsSdLat N₂') (θ : TaylorLogMetric.VC D a b → ℂ) =>
    Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N₁ N₁') (lam (ambOf s B χ cD) N₂ N₂') (TaylorLogMetric.La D B.tor (s.lat N₁) (s.lat N₁'))
      (TaylorLogMetric.La D B.tor (s.lat N₂) (s.lat N₂')) θ (form_reidx s _ a b) (hlam a b N₁ N₁') (hlam a b N₂ N₂')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N₂ N₂' h h') (reidx s a b x) ((hlam a b N₂ N₂' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N₂ N₂' h h')).1 (hL.1 a b _ _ (hadm N₂ N₂' h h')).2
  refine ⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, aa_fg s B χ cD, aa_ne_bot s B χ cD hcc.1, ?_, ?_, ?_⟩
  · intro N N' h h'
    obtain ⟨hc, han, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    obtain ⟨h1, h2, h3⟩ := (key N N N' N' h h' 0).1
    refine ⟨hc, ?_, h1, h2⟩
    rw [vac_eq s B χ cD N N' hc]
    refine ⟨fun z _ => ?_, h3 _ hfix⟩
    exact (han _ (Set.mem_univ _)).comp ((reidx s a b).toLinearMap.toContinuousLinearMap.analyticAt z)
  · intro N N' N'' h h' h''
    obtain ⟨hc, -, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    rw [vac_eq s B χ cD N N' hc, vac_eq s B χ cD N N'' (hth _ _ (hsd _ _ h) (hsd _ _ h'')).1,
      (key N N N' N'' h h'' _).2 hfix (hL.2 a b _ _ _ _ (hadm N N' h h') (hadm N N'' h h'')).1,
      hm1 _ _ _ (hsd _ _ h) (hsd _ _ h') (hsd _ _ h''), iop_eq]
  · intro N N₁ N' h h₁ h'
    obtain ⟨hc, -, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    rw [vac_eq s B χ cD N N' hc, vac_eq s B χ cD N₁ N' (hth _ _ (hsd _ _ h₁) (hsd _ _ h')).1,
      (key N N₁ N' N' h₁ h' _).2 hfix (hL.2 a b _ _ _ _ (hadm N N' h h') (hadm N₁ N' h₁ h')).1,
      hm2 _ _ _ (hsd _ _ h) (hsd _ _ h₁) (hsd _ _ h'), iop_eq]

end GlobalTheory.ThetaMove.SeamMoves
