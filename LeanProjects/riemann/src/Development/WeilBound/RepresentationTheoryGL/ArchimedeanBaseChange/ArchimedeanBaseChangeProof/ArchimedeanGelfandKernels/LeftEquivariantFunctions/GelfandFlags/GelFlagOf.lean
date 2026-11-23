import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.UnitaryMemGLs
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.KerComm
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.KerNId
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.SecondCountableG
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.TrZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.GelFlag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnOfIteratedFDerivZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsWaveTranslateSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivTwoClm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjMemNilSet

namespace PositivityTheory.RgBcC.VC

theorem vcOf : PositivityTheory.RgBcC.VCOf := by
  intro hWE hWS hMA hGC hGF hFF hNU hKZ
  have hKC : KerComm := kerComm_of GlobalTheory.CompanionTheory.WaveInv.waveN GlobalTheory.CompanionTheory.WaveField.waveA
  have hKN : KerNId := kerNId_of' GlobalTheory.CompanionTheory.LgBound.lgCpt
  have hNA : NAvg := nAvg_of GlobalTheory.CompanionTheory.ParamInt.intSmooth GlobalTheory.CompanionTheory.LgBound.lgCpt hNU
  intro n lam E Fr ε ι S Γ T hCx _ _ μ _ k val τ hMult d W₁ W₂ hW hW1 hd2 hd1 N hN ν _
  letI : NormedAddCommGroup (RgTw.Mat n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (RgTw.Mat n) := Matrix.normedSpace
  obtain ⟨H, hHs, hHh, hHtr, hHk, hHq, hHd⟩ := hFF n W₁ W₂ hW hW1
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := hMult
  have hcl : IsClosed (N : Set (RgTw.G n)) := by
    rw [hN]
    have hc : ∀ v : Fin n → ℂ, Continuous (fun u : RgTw.G n => ((u : RgTw.Mat n) - 1).mulVec v) := fun v =>
      (Units.continuous_val.sub continuous_const).matrix_mulVec continuous_const
    have e : nilSet W₁ W₂ = (⋂ v, (fun u : RgTw.G n => ((u : RgTw.Mat n) - 1).mulVec v) ⁻¹' (W₂ : Set (Fin n → ℂ))) ∩
        (⋂ v ∈ W₂, (fun u : RgTw.G n => ((u : RgTw.Mat n) - 1).mulVec v) ⁻¹' (W₁ : Set (Fin n → ℂ))) ∩
        (⋂ v ∈ W₁, (fun u : RgTw.G n => ((u : RgTw.Mat n) - 1).mulVec v) ⁻¹' {0}) := by
      ext u
      simp only [nilSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
        SetLike.mem_coe, Set.mem_singleton_iff, and_assoc]
    rw [e]
    refine ((isClosed_iInter fun v => W₂.closed_of_finiteDimensional.preimage (hc v)).inter
      (isClosed_biInter fun v _ => W₁.closed_of_finiteDimensional.preimage (hc v))).inter
      (isClosed_biInter fun v _ => isClosed_singleton.preimage (hc v))
  let A : RgTw.Mat n → E.V →L[ℂ] E.V := fun x => ε (H x)
  have hA : IsField E A := by
    refine ⟨(LinearMap.toContinuousLinearMap ε).contDiff.comp_contDiffOn hHs, ?_⟩
    intro x hx k0
    have hkG : ((k0 : Matrix (Fin n) (Fin n) ℂ) : RgTw.Mat n) ∈ GLs n := by
      have hu := Matrix.det_of_mem_unitary k0.2
      exact right_ne_zero_of_mul_eq_one hu.1
    have h := hCx.frε _ hkG (H x) (hHh x hx)
    rw [hCx.onK] at h
    show ε (H (x * k0)) = E.ρ k0⁻¹ * ε (H x) * E.ρ k0
    rw [hHk x hx k0, mul_assoc (E.ρ k0⁻¹), h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hQ : QInv W₁ W₂ A := by
    intro q hq h1 h2 x hx
    simp only [A, hHq q hq h1 h2 x hx]
  have hdG : (d : RgTw.Mat n) ∈ GLs n := mem_GLs d
  have hAd : A d = -A 1 := by
    simp only [A, hHd _ hdG hd2 hd1, map_neg]
  have hone : ∀ i, MeasureTheory.Integrable (fun u : N => trT T (ks i ((u : RgTw.G n) * (d : RgTw.Mat n)))) ν ∧
      ∫ u : N, trT T (ks i ((u : RgTw.G n) * (d : RgTw.Mat n))) ∂ν = 0 := by
    intro i
    obtain ⟨hb, hker⟩ := hks i
    obtain ⟨hsm, ⟨R, hR⟩, hbi, -⟩ := hker
    have hI : MeasureTheory.Integrable (fun u : N => ks i ((u : RgTw.G n) * (d : RgTw.Mat n))) ν :=
      KN.integrable_N GlobalTheory.CompanionTheory.LgBound.lgCpt hcl ν (ks i) hsm.continuousOn R hR _ hdG
    refine ⟨(trT T).integrable_comp hI, ?_⟩
    rw [ContinuousLinearMap.integral_comp_comm _ hI]
    have hcomm := hKC hWE hWS hGC hGF GlobalTheory.CompanionTheory.ParamInt.intSmooth n μ E (w i) (g i) τ (ks i) hb (hks i).2
      W₁ W₂ hW A hA hQ
    have key := hKN hNU hKZ hNA n μ E (ks i) hsm ⟨R, hR⟩ hbi W₁ W₂ hW N hN ν A hA hQ hcomm _ hdG
    rw [hAd] at key
    have h1G : (1 : RgTw.Mat n) ∈ GLs n := one_mem_GLs
    rw [trT_apply]
    refine trZero E.V _ T (ε (H 1)) (ι (H 1)) ((H 1 * H 1).trace) hHtr
      (hCx.car _ _ (hHh 1 h1G) (hHh 1 h1G)) ?_ (hCx.Tε _)
    have : ∀ B : E.V →L[ℂ] E.V, B * -ε (H 1) = -(B * ε (H 1)) := fun B => by rw [mul_neg]
    rw [this] at key
    exact key.symm
  have hsum : ∀ u : N, phiOf E T k ((u : RgTw.G n) * d) =
      ∑ i, c i * trT T (ks i ((u : RgTw.G n) * (d : RgTw.Mat n))) := by
    intro u
    have hm : (((u : RgTw.G n) * d : RgTw.G n) : RgTw.Mat n) ∈ GLs n := mem_GLs _
    rw [phiOf, ← trT_apply, hk _ hm, map_sum]
    simp only [map_smul, smul_eq_mul, Units.val_mul]
  simp only [hsum]
  rw [MeasureTheory.integral_finset_sum _ (fun i _ => (hone i).1.const_mul (c i))]
  simp [MeasureTheory.integral_const_mul, (hone _).2]

end PositivityTheory.RgBcC.VC
