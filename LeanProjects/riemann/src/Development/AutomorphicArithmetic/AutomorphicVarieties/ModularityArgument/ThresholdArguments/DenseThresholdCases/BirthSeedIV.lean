import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaUnramifiedOfKillsRootsOfUnity
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuDefsA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PromodularityCaseThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SeedOf4P

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu in
theorem UpperTheory.V.Cu.fourth_initial_of_rank_four_data : AlNe → _root_.UpperTheory.V.Cu.TauExAlt → RankFourAutomorphyOfTensor → RhoExP → TwEx4 → PairOf4 → ResOf4 → ContOf4 → EntOf4 → OverOf4 → WtsOf4 → IrrOf4 →
    AutOf4 → _root_.UpperTheory.V.Af.Hypotheses' → PropEGP → _root_.UpperTheory.V.Cu.SeedIVAlt := by
  intro hne hTau hAQ hRho hTw hPair hRes hCont hEnt hOver hWts hIrr hAut hH hP Ω _ _ _ l _ c D T₀ hc hok h4 ι 𝔞
  have hg : D.Good := hc.1
  obtain ⟨K', _, hq⟩ := h4.quad
  have hfix : ∀ (T : Tower D) (g : G T.F Ω), resQ T.F g ∈ T.F.fixingSubgroup := fun T g x => g.commutes x
  have hg0 : resQ T₀.F T₀.g0 ∉ K'.fixingSubgroup := by
    intro hm
    have h1 := hq.on _ hm
    apply hok.dist 0 1 (by decide)
    have h2 : residue c.O (((chi D T₀.pr 0 (resQ T₀.F T₀.g0) * (chi D T₀.pr 1 (resQ T₀.F T₀.g0))⁻¹) ^ (1 : ℤ) *
        (chi D T₀.pr 0 (resQ T₀.F T₀.g0) * (chi D T₀.pr 2 (resQ T₀.F T₀.g0))⁻¹) ^ (0 : ℤ) : c.Oˣ) : c.O) = 1 := h1
    rw [zpow_one, zpow_zero, mul_one] at h2
    have h3 := congrArg (· * residue c.O (chi D T₀.pr 1 (resQ T₀.F T₀.g0) : c.O)) h2
    simp only [← map_mul, ← Units.val_mul, inv_mul_cancel_right, one_mul] at h3
    exact h3
  obtain ⟨m, c₀, κ, hκ⟩ := hTau hH Ω l ι K' hg.l_odd hq.deg hq.imag hq.disc hq.split ⟨D.cc, hg.isCC⟩ _ hg0
  obtain ⟨w, θ, k, ρ, c₁, h, ρ₁, x, hw, hsp, hθl, hθm, hB, hk, hE, ⟨hI, hrw⟩, h₀, hM⟩ :=
    hRho hP Ω l c D T₀ hc hok h4 ι (2 * (m * 9) + 3) c₀
  obtain ⟨j, j1, j9, hj⟩ := hAQ Ω l ι K' hq.deg hq.imag ρ hE.cont hE.aut hI hrw _ m c₁ κ hg0 (hκ c₁ h₀ 1 le_rfl)
  obtain ⟨τ, s, hτ⟩ := hκ c₁ h₀ j j1
  obtain ⟨δ, hδ⟩ := hTw Ω l c D T₀ hc k (by omega) hk
  have hbig : 2 * (m * j) + 3 ≤ k := le_trans (by have := Nat.mul_le_mul_left m j9; omega) hB
  obtain ⟨hunr, hdies⟩ := UpperTheory.theta_unramified_of_kills_roots_of_unity Ω l w hw θ hθl hθm
  let d : Dat Ω l := ⟨ι, c, D, T₀, hc, hok, K', hq, k, m * j, hbig, hk, δ, hδ, θ, ρ, hE, hI, c₁, h, ρ₁, x, hM, τ, s, κ ^ j, hτ,
    (hj ρ₁ τ s hM.iso hτ).1, w, hw, hsp, hunr⟩
  have hf : ∀ y ∈ maximalIdeal c₁.O, 𝔞.red c₁ y = 0 := fun y hy =>
    (residue_eq_zero_iff _).2 (map_nonunit (𝔞.a c₁) y hy)
  have hred : 𝔞.red c = (𝔞.red c₁).comp (inc h) := RingHom.ext fun y => congrArg (residue 𝔞.V) (𝔞.compat c c₁ h y).symm
  have hle : T₀.Le T₀ := ⟨rfl, rfl, le_rfl, ⟨0, fun g hg => by simpa using hg⟩, ⟨0, by simp⟩⟩
  obtain ⟨r1, r2, -, r3⟩ := hRes Ω l d T₀ hle {w} 𝔞.k (𝔞.red c₁) hf
  refine ⟨w, (d.Q T₀).map (𝔞.red c₁), hw, hsp, ⟨?_, ?_, (hCont Ω l d T₀).2 _ _ hf⟩, r2,
    fun T hT tok hd => ⟨c₁, h, d.Q T, ⟨?_, (hCont Ω l d T).1, ?_, ?_⟩, hOver Ω l d T hT _ _ hf,
      (hRes Ω l d T hT ∅ 𝔞.k (𝔞.red c₁) hf).2.2.1, hEnt Ω l d T hT tok _ _ hf⟩⟩
  · rw [hred]
    exact hPair Ω l d T₀ hle hok {w} 𝔞.k (𝔞.red c₁) (fun g _ => r3 g) fun A hA g hg =>
      hunr A (fun p hp => hA p (Finset.mem_insert_of_mem hp)) hg
  · rw [hred]
    exact r1
  · have := hPair Ω l d T hT tok ∅ c₁.O (RingHom.id _) (fun g hg => hM.det g (hdies T.F hd hg)) fun A _ g _ =>
      hdies T.F hd (hfix T g)
    have e : (d.Q T).map (RingHom.id c₁.O) = d.Q T := by
      ext <;> rfl
    rwa [e, RingHom.id_comp] at this
  · exact (hRes Ω l d T hT ∅ _ (residue c₁.O) fun y hy => (residue_eq_zero_iff _).2 hy).1
  · exact _root_.UpperTheory.V.Cu.tower_is_initial_of_ok hne hWts hIrr hAut Ω l d T hT tok (hj ρ₁ τ s hM.iso hτ).2
end
end
