import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MovedVacuumMemThetaFunctionsAndMoves
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOffSplitOfEqOffSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelFunctionsCommonLinearOperatorOffSplitPrimeStatement

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.KerRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eqOffSplit_of_eqOff : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ) (L L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), GL3Theta.SplitP D P → GL3Theta.EqOff D P L L₀ → GL3Theta.EqOffSplit D L L₀ := GlobalTheory.T.eqOffSplit_of_eqOff_splitPrime

theorem kerTh_common : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.LatAll → B.VecP χ → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ T : (TaylorLogMetric.VC D a b → ℂ) →ₗ[ℂ] (TaylorLogMetric.VC D a b → ℂ), ∀ i, kerTh B χ SS cl (N i) (N' i) Ξ = T (B.eNat χ a b (N i) (N' i)) := GlobalTheory.T.kernelFunctions_common_linearOperator_off_splitPrime

theorem eqOffSplit_refl (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : GL3Theta.EqOffSplit D L L :=
  ⟨1, one_ne_zero, fun Q hQ => (Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hQ isUnit_one)).elim,
    fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩

theorem eqOffSplit_symm {D : D7} {n : ℕ} {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : GL3Theta.EqOffSplit D L₁ L₂) : GL3Theta.EqOffSplit D L₂ L₁ := by
  obtain ⟨a, ha0, hsa, ha1, ha2⟩ := h
  exact ⟨a, ha0, hsa, ha2, ha1⟩

theorem mem_Th_const_mul (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {F : TaylorLogMetric.VC D a b → ℂ} (hF : F ∈ TaylorLogMetric.Th D T L L') (k : ℂ) :
    (fun z => k * F z) ∈ TaylorLogMetric.Th D T L L' := by
  refine ⟨hF.1.const_mul k, fun x hx z => ?_⟩
  have := hF.2 x hx z
  simp only [TaylorLogMetric.U] at this ⊢
  rw [← this]; ring

theorem chiFac_ne_zero (D : D7) {χ : TaylorLogMetric.IdE D → ℂ} (hχ : TaylorLogMetric.IsChi D χ) {a b : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') : Base.chiFac χ a b L L' ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (GlobalTheory.ThetaMove.Moved.chi_detId_ne_zero hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D a) h))
    (zpow_ne_zero _ (GlobalTheory.ThetaMove.Moved.chi_detId_ne_zero hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D b) h'))

theorem thMoved_move_right (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (hχ : TaylorLogMetric.IsChi D χ) (hE : B.EqP χ) (ha : Even a) (hb : Even b) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' L'' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') (h'' : StandardLatticesGL3.SD D L'') :
    B.thMoved a b L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved a b L L') := by
  funext z
  have e : Base.chiFac χ a b L L'' * B.thMoved a b L L'' z = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) *
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'')
        (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
    congrFun (hE.2.1 a b ⟨L, h⟩ ⟨L', h'⟩ ⟨L'', h''⟩ ha hb) z
  have f : Base.chiFac χ a b L L'' = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
    unfold Base.chiFac
    rw [GlobalTheory.ThetaMove.Moved.chi_detId_mul hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D b) h' h'', mul_zpow]
    ring
  rw [GlobalTheory.ThetaMove.Moved.iop_mul, ← mul_assoc, ← f] at e
  exact mul_left_cancel₀ (chiFac_ne_zero D hχ h h'') e

theorem thMoved_move_left (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (hχ : TaylorLogMetric.IsChi D χ) (hE : B.EqP χ) (ha : Even a) (hb : Even b) (L L₁ : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (h : StandardLatticesGL3.SD D L) (h₁ : StandardLatticesGL3.SD D L₁) (h' : StandardLatticesGL3.SD D L') :
    B.thMoved a b L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved a b L L') := by
  funext z
  have e : Base.chiFac χ a b L₁ L' * B.thMoved a b L₁ L' z = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) *
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L')
        (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
    congrFun (hE.2.2 a b ⟨L, h⟩ ⟨L₁, h₁⟩ ⟨L', h'⟩ ha hb) z
  have f : Base.chiFac χ a b L₁ L' = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
    unfold Base.chiFac
    rw [GlobalTheory.ThetaMove.Moved.chi_detId_mul hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D a) h h₁, mul_zpow]
    ring
  rw [GlobalTheory.ThetaMove.Moved.iop_mul, ← mul_assoc, ← f] at e
  exact mul_left_cancel₀ (chiFac_ne_zero D hχ h₁ h') e

theorem kerTh_relation_of_indicator : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → TaylorLogMetric.IsChi D χ → B.LatAll → B.VecP χ → B.EqP χ → GL3Theta.modelXi D → GL3Theta.movesCompose D → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∀ c : ι → ℂ, (∑ i, c i • Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) (1 : Matrix (Fin b) (Fin a) (GL3Theta.EP D P) → ℂ)) = 0 → ∀ z, ∑ i, c i * (((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) * (Base.chiFac χ a b (N i) (N' i))⁻¹ * kerTh B χ SS cl (N i) (N' i) Ξ z) = 0 := by
  intro D cc δ B χ hcc hδ hδ0 hχ hL hV hE hModel hMoves SS cl hcl hSS a b P hP hPS hPS' hcP hcP' N₀ N₀' Ξ hA0 hD ι _ N N' hN c hrel z
  obtain ⟨T, hT⟩ := kerTh_common D cc δ B χ hcc hδ hδ0 hL hV SS cl hcl hSS a b P hP hPS hPS' hcP hcP' N₀ N₀' Ξ hA0 hD ι N N' hN
  obtain ⟨ha, hb, h0, h0'⟩ := hA0
  have hth0 : B.thMoved a b N₀ N₀' ∈ TaylorLogMetric.Th D (TaylorLogMetric.tor0 D cc δ) N₀ N₀' := by
    have hm := mem_Th_const_mul D (TaylorLogMetric.tor0 D cc δ) (hV a b N₀ N₀' ⟨ha, hb, h0, h0'⟩).1 (Base.chiFac χ a b N₀ N₀')⁻¹
    convert hm using 1
    funext w
    show _ = _ * (Base.chiFac χ a b N₀ N₀' * _)
    rw [← mul_assoc, inv_mul_cancel₀ (chiFac_ne_zero D hχ h0 h0'), one_mul]
  obtain ⟨Xi, -, hXi⟩ := hModel cc δ hcc hδ a b N₀ N₀' ⟨ha, hb, h0, h0'⟩ P hP _ hth0
  have hmove : ∀ i, B.thMoved a b (N i) (N' i) =
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor N₀ N₀') (TaylorLogMetric.La D B.tor (N i) (N' i)) (B.thMoved a b N₀ N₀') := by
    intro i
    obtain ⟨⟨-, -, hi, hi'⟩, ho, ho'⟩ := hN i
    rw [thMoved_move_right D cc δ B χ hχ hE ha hb (N i) N₀' (N' i) hi h0' hi',
      thMoved_move_left D cc δ B χ hχ hE ha hb N₀ (N i) N₀' h0 hi h0']
    exact hMoves cc δ hcc hδ a b N₀ (N i) (N i) N₀' N₀' (N' i) ⟨ha, hb, h0, h0'⟩ ⟨ha, hb, hi, h0'⟩ ⟨ha, hb, hi, hi'⟩
      (eqOffSplit_symm (eqOffSplit_of_eqOff D P _ _ _ hP ho)) (eqOffSplit_refl D _) (eqOffSplit_refl D _)
      (eqOffSplit_symm (eqOffSplit_of_eqOff D P _ _ _ hP ho')) _ hth0
  have key : ∀ i, ((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) *
      (Base.chiFac χ a b (N i) (N' i))⁻¹ * kerTh B χ SS cl (N i) (N' i) Ξ z =
      T (Xi (Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) 1)) z := by
    intro i
    obtain ⟨⟨-, -, hi, hi'⟩, -, -⟩ := hN i
    set s : ℂ := ((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) with hs
    set X := Xi (Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) 1) with hX
    have hm : B.thMoved a b (N i) (N' i) = fun w => s⁻¹ * X w := by
      rw [hmove i, hXi (N i) (N' i) ⟨ha, hb, hi, hi'⟩ (hN i).2.1 (hN i).2.2]
      funext w
      push_cast
      rfl
    have he : B.eNat χ a b (N i) (N' i) = (Base.chiFac χ a b (N i) (N' i) * s⁻¹) • X := by
      funext w
      show Base.chiFac χ a b (N i) (N' i) * B.thMoved a b (N i) (N' i) w = _
      rw [hm, Pi.smul_apply, smul_eq_mul, mul_assoc]
    have hs0 : s ≠ 0 := by
      intro h0s
      apply (hV a b (N i) (N' i) ⟨ha, hb, hi, hi'⟩).2.1
      rw [he, h0s, inv_zero, mul_zero, zero_smul]
    rw [hT i, he, map_smul, Pi.smul_apply, smul_eq_mul]
    field_simp [chiFac_ne_zero D hχ hi hi']
  simp_rw [key]
  have hsum := congrArg (fun f => T (Xi f) z) hrel
  simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hsum
  exact hsum

end GlobalTheory.KerRel
