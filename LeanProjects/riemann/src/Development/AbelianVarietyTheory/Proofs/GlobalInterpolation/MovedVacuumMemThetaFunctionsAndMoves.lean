import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetIdNormOneMul

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.Moved

theorem sd_stdL (D : D7) (N : ℕ) : StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D N) := by
  letI := D.host.cmStar
  have hr : ∀ x : D.host.E, x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ x := fun x =>
    ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hm : ∀ x : Fin N → D.host.E, x ∈ StandardLatticesGL3.stdL D N ↔ ∀ k, IsIntegral ℤ (x k) := fun x => by
    simp only [StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    exact forall_congr' fun k => hr (x k)
  have hs : ∀ k : Fin N, (Pi.single k 1 : Fin N → D.host.E) ∈ StandardLatticesGL3.stdL D N := fun k => by
    rw [hm]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using hs k
  · rw [hr]
    rw [hm] at hx hy
    exact IsIntegral.sum _ fun i _ => ((hx i).map (starRingEnd D.host.E).toIntAlgHom).mul (hy i)
  · rw [hm]
    intro k
    have := h _ (hs k)
    rw [hr] at this
    simpa [Formalism.BasicNotions.stdH, Pi.single_apply, apply_ite] using this

theorem isHerm_formV (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) : IsHerm (formV A n N N') := by
  intro x y
  simp [formV, map_sum, mul_comm]

theorem inter_mem_Th {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] {H : Sesq V} {α : V → ℂ}
    (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} (hf : relIdx A₁ A₂ ≠ 0)
    (hs₁ : IsSemiChar H A₁ α) (hd₂ : IsSelfDual H A₂) (hs₂ : IsSemiChar H A₂ α)
    {F : V → ℂ} (hF : F ∈ Th H α A₁) : inter H α A₁ A₂ F ∈ Th H α A₂ := by
  have : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := Nat.finite_of_card_ne_zero hf
  refine ⟨?_, GlobalTheory.ThetaInter.inter_mem_fixedBy hH hs₁ hd₂ hs₂ hF.2⟩
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  have hU : ∀ x z, AnalyticAt ℂ (opU H x F) z := fun x z => by
    have h : AnalyticAt ℂ (fun z => H z x) z := (LinearMap.toContinuousLinearMap (H.flip x)).analyticAt z
    have h2 : AnalyticAt ℂ (fun z => F (z + x)) z :=
      AnalyticAt.comp (f := fun z => z + x) (hF.1 _ (Set.mem_univ _)) (analyticAt_id.add analyticAt_const)
    exact h2.mul ((analyticAt_const.mul h).sub analyticAt_const).cexp
  rw [GlobalTheory.ThetaInter.inter_eq]
  intro z _
  exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun c _ => analyticAt_const.mul (hU _ z))

theorem iop_eq (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (A₁ A₂ : AddSubgroup (TaylorLogMetric.VC D a b)) (G : TaylorLogMetric.VC D a b → ℂ) :
    TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) A₁ A₂ G =
      inter (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) A₁ A₂ G := rfl

theorem iop_mul (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (A B : AddSubgroup (TaylorLogMetric.VC D N N')) (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ)
    (z : TaylorLogMetric.VC D N N') : TaylorLogMetric.Iop D T A B (fun w => c * G w) z = c * TaylorLogMetric.Iop D T A B G z := by
  unfold TaylorLogMetric.Iop
  rw [mul_left_comm, mul_finsum _ c]
  congr 1
  refine finsum_congr fun q => ?_
  simp only [TaylorLogMetric.U]; ring

variable {D : D7} {χ : TaylorLogMetric.IdE D → ℂ} {n : ℕ} {L L' L'' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}

theorem chi_detId_mul (hχ : TaylorLogMetric.IsChi D χ) (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') (h'' : StandardLatticesGL3.SD D L'') :
    χ (TaylorLogMetric.detId D L L'') = χ (TaylorLogMetric.detId D L L') * χ (TaylorLogMetric.detId D L' L'') := by
  rw [(GlobalTheory.RelDetIdeal.detId_normOne_mul D n L L' L'' h h' h'').2]
  exact hχ.1 _ _ (GlobalTheory.RelDetIdeal.detId_normOne_mul D n L L' L'' h h' h'').1 (GlobalTheory.RelDetIdeal.detId_normOne_mul D n L' L'' L'' h' h'' h'').1

theorem chi_detId_ne_zero (hχ : TaylorLogMetric.IsChi D χ) (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') : χ (TaylorLogMetric.detId D L L') ≠ 0 := by
  obtain ⟨⟨𝔟, -, hb⟩, h2⟩ := GlobalTheory.RelDetIdeal.detId_normOne_mul D n L L L h h h
  have h1 : TaylorLogMetric.detId D L L = 1 := by
    rw [← mul_one (TaylorLogMetric.detId D L L), ← hb, ← mul_assoc, ← h2]
  have h3 := chi_detId_mul hχ h h' h
  have h4 : χ 1 = 1 := by simpa [Submodule.one_eq_span] using hχ.2 1
  rw [h1, h4] at h3
  exact left_ne_zero_of_mul_eq_one h3.symm

theorem thMoved_mem_and_moves : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (a b : ℕ), TaylorLogMetric.IsChi D χ → B.EqP χ → B.LatAll → B.ThZeroMem a b → Even a → Even b → (∀ L L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Base.chiFac χ a b L L' ≠ 0 ∧ B.thMoved a b L L' ∈ Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L L')) ∧ (∀ L L' L'', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.SD D L'' → B.thMoved a b L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved a b L L')) ∧ ∀ L L₁ L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L₁ → StandardLatticesGL3.SD D L' → B.thMoved a b L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved a b L L') := by
  intro D cc δ B χ a b hχ hE hL h0 ha hb
  have sa := sd_stdL D a
  have sb := sd_stdL D b
  have hne : ∀ L L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Base.chiFac χ a b L L' ≠ 0 := fun L L' h h' =>
    mul_ne_zero (zpow_ne_zero _ (chi_detId_ne_zero hχ sa h)) (zpow_ne_zero _ (chi_detId_ne_zero hχ sb h'))
  have step : ∀ L₁ L₁' L₂ L₂', StandardLatticesGL3.SD D L₁ → StandardLatticesGL3.SD D L₁' → StandardLatticesGL3.SD D L₂ → StandardLatticesGL3.SD D L₂' → ∀ F,
      F ∈ Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L₁ L₁') →
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂') F ∈
        Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L₂ L₂') := by
    intro L₁ L₁' L₂ L₂' h₁ h₁' h₂ h₂' F hF
    have A₁ : TaylorLogMetric.admitted D a b L₁ L₁' := ⟨ha, hb, h₁, h₁'⟩
    have A₂ : TaylorLogMetric.admitted D a b L₂ L₂' := ⟨ha, hb, h₂, h₂'⟩
    rw [iop_eq]
    exact inter_mem_Th (isHerm_formV _ _ _ _) (hL.2 a b _ _ _ _ A₁ A₂).1 (hL.1 a b _ _ A₁).2 (hL.1 a b _ _ A₂).1
      (hL.1 a b _ _ A₂).2 hF
  refine ⟨fun L L' h h' => ⟨hne L L' h h', step _ _ _ _ h sb h h' _ (step _ _ _ _ sa sb h sb _ h0)⟩, ?_, ?_⟩
  · intro L L' L'' h h' h''
    funext z
    have e : Base.chiFac χ a b L L'' * B.thMoved a b L L'' z = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'')
          (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
      congrFun (hE.2.1 a b ⟨L, h⟩ ⟨L', h'⟩ ⟨L'', h''⟩ ha hb) z
    have f : Base.chiFac χ a b L L'' = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
      unfold Base.chiFac
      rw [chi_detId_mul hχ sb h' h'', mul_zpow]
      ring
    rw [iop_mul, ← mul_assoc, ← f] at e
    exact mul_left_cancel₀ (hne _ _ h h'') e
  · intro L L₁ L' h h₁ h'
    funext z
    have e : Base.chiFac χ a b L₁ L' * B.thMoved a b L₁ L' z = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L')
          (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
      congrFun (hE.2.2 a b ⟨L, h⟩ ⟨L₁, h₁⟩ ⟨L', h'⟩ ha hb) z
    have f : Base.chiFac χ a b L₁ L' = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
      unfold Base.chiFac
      rw [chi_detId_mul hχ sa h h₁, mul_zpow]
      ring
    rw [iop_mul, ← mul_assoc, ← f] at e
    exact mul_left_cancel₀ (hne _ _ h₁ h') e

end GlobalTheory.ThetaMove.Moved
