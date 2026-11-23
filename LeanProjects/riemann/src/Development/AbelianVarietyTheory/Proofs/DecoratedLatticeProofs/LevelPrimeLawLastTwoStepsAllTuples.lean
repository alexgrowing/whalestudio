import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiVacuumOperatorZeroOrLeftInvertibleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumAtSplitPlacesProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDoubleLiftAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAllGluedPlacesProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastKernelDatumInLastLineFrameAtLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLastStageCharsUnramifiedAtLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatTensorIndicatorCharacterFacts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.TLastAll

theorem combAt_fin {D : D7} {P : Pl D → Prop} {S T : HSp D} {c : WO S T →₀ ℂ} (h : CombAt P c) : IsFinComb c := by
  intro u hu
  ext i j
  have := (Ideal.mem_inf.1 (h u hu i j)).1
  simpa using this

set_option maxHeartbeats 1000000 in

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ OpAt (· ∈ v.tP) op ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.tP) Ψ₂ → BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP) (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ∧ ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, ∀ f, IsContAut c.T f → ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ = o.mono r e (t.sBF j 0 h).χW * ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)))) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ := by
  intro D c v k _ _ _ _ ι o hc hv hS j h
  have hPl : Places o.p o.I (· ∈ v.tP) :=
    ⟨hS.pre.nodup, hS.pre.all, hS.pre.inj, hS.pre.tP, fun i => (hS.pre.char i).2⟩
  have hstd := hc.std
  have hjm : j + 1 < D.R.m := by omega
  have hx0 : IsSelfDualC _ (c.x j).L := (hc.x j (by omega)).sd
  have hx1 : IsSelfDualC _ (c.x (j + 1)).L := (hc.x (j + 1) (by omega)).sd
  have hx2 : IsSelfDualC _ (c.x (j + 1 + 1)).L := (hc.x (j + 1 + 1) (by omega)).sd
  have hpl : Nonempty (Pl D) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (NumberField.RingOfIntegers D.host.F)
    exact ⟨⟨M, hM.isPrime, (Ideal.bot_lt_of_maximal M (NumberField.RingOfIntegers.not_isField D.host.F)).ne'⟩⟩
  have hM : IsSelfDualC _ (o.M j 0 h) := ((hS.good (Classical.arbitrary _)).bf j 0 h).sdV₀
  obtain ⟨lam, hlam, hlamv⟩ := hS.pre.lam j h
  obtain ⟨ε', hε'⟩ := GlobalTheory.T.lastSeeSawDatumAtSplitPlaces_proof D k ι o.p o.I (· ∈ v.tP) hPl o.q c.ψ hstd o.χ o.hχ (fun i => (hS.pre.char i).1)
    (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) (Fin c.T.rank) (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1))
    (c.X (j + 1 + 1)) c.T c.Lz (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (c.bes j 0 h).ζ o.ζ₀ (c.bes j 0 h).line hS.pre.line
    (v.τ j h) lam hlam (fun i => (hlamv i).1) (hS.pre.tau j h)
  obtain ⟨Λ, hΛ, u, hγ, hrep⟩ := GlobalTheory.T.lastKernelDatum_in_lastLineFrame_at_levelPrime D c v k ι o hc hv hS j h
  haveI : ∀ i, (Λ i).IsLattice k := hΛ
  let ε : ι → 𝓀[k]ˣ := fun i => (ε' i)⁻¹ * u i
  let Q : ι → Pair k (Fin (c.X (j + 1)).rank) := fun i => ε i • o.Q (j + 1) i
  obtain ⟨r, e, hr, hSm⟩ := GlobalTheory.T.smallPairPairingAllGluedPlaces_proof D k ι o.p o.I (· ∈ v.tP) hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) o.q o.χ o.hχ
  have hAC := GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D
  let Ψ' : ι → Matrix (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank ⊕ Fin 1) k → ℂ := fun i =>
    tensCol (phiOne (o.Q j i) (o.Q (j + 1) i)) (charInd (resChar (o.χ i) (o.hχ i) o.q) (Q i))
  have hAC1 := hAC k ι o.p o.I (· ∈ v.tP) hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank ⊕ Fin 1) c.ψ hstd
    (c.bes j 0 h).V₀ (c.X (j + 1)) (o.β₀ j 0 h) (o.β (j + 1)) (o.M j 0 h) (c.x (j + 1)).L hM hx1 Ψ'
  obtain ⟨e0, he0⟩ := hAC1.1 fun i => Comm.tensCol_mem (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _) (SBFacts.charInd_mem _ _)
  have hrep' : Reps c.ψ (o.β (j + 1)) (o.γ₀ (j + 1 + 1) h) (c.x (j + 1)).L (c.x (j + 1 + 1)).L
      (fun i => phiOne (ε' i • Q i) (lastPair o.q (Λ i))) o.I (· ∈ v.tP) (v.dT (j + 1)) := by
    have hf : (fun i => phiOne (ε' i • Q i) (lastPair o.q (Λ i))) =
        (fun i => phiOne (u i • o.Q (j + 1) i) (lastPair o.q (Λ i))) := by
      funext i
      simp only [Q, ε, smul_smul, mul_inv_cancel_left]
    rw [hf]
    exact hrep
  obtain ⟨e₁, e₂, he₁, he₂, hE⟩ := hε' (o.β j) (o.β₀ j 0 h) (o.β (j + 1)) o.γ (o.γ₀ (j + 1 + 1) h)
    (fun i => ⟨(hS.glued j 0 h i).sum, (hS.pre.topT (j + 1 + 1) h i).1⟩) Q Λ
    (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) (c.x j).L (c.x (j + 1)).L v.NT (c.x (j + 1 + 1)).L (o.M j 0 h)
    hx0 hx1 hv.sdT hx2 hM (fun i => ⟨hS.pre.latT (j + 1) (by omega) i, hγ i⟩) (v.dT j) (v.dT (j + 1))
    ⟨(hv.atT j).1, hS.rep j (by omega)⟩ hrep'
  have hLO := GlobalTheory.T.lastSeeSaw_combinations_operatorDatum D c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz
    (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (c.bes j 0 h).line.1 hS.pre.line.1 (hS.pre.tau j h)
  obtain ⟨op0, hop0, hop0e⟩ := (hLO (· ∈ v.tP)).1 e0 he0.1
  obtain ⟨op, hop, hope⟩ := ((GlobalTheory.T.biVacuumOperator_zero_or_left_invertible D) k ι o.p o.I _ hPl c.ψ hstd _ _ _ op0 hop0).2 e₁ e₂ he₁ he₂
  refine ⟨ε, op, r, e, hr, hop, ?_⟩
  intro t ht hW hU hK Ψ₁ Ψ₂ hΨ₁ hΨ₂
  obtain ⟨χA, χz, χS', χT, omz, omT', omz'', hχV, hwA, hwz, hwX, hwT, hwTi, hwz''⟩ := hW.last j h
  have hunrT := GlobalTheory.T.seesawLastStage_chars_unramified_at_levelPrime D c v k ι o hS j h t hU hK χz χS' χT hwX hwTi
  have hFV := GlobalTheory.T.flatMapPreservesVacuum_proof D c.ψ (· ∈ v.tP)
  have hΞ : Vac c.ψ (c.bes j 0 h).V₀ (c.X (j + 1)) (o.M j 0 h) (c.x (j + 1)).L (· ∈ v.tP) (flatBF (t.sBF j 0 h) Ψ₁) :=
    hFV.1 0 (c.B j 0 h) (c.J j 0 h) (t.sBF j 0 h) (v.N j) (o.M j 0 h) (v.N (j + 1)) (c.x (j + 1)).L
      (fun x _ => (hS.good x).bf j 0 h) Ψ₁ hΨ₁
  have hΦ : Vac c.ψ (c.X (j + 1)) c.T (c.x (j + 1)).L v.NT (· ∈ v.tP) (fun w => Ψ₂ ((c.jac j 0 h).d.ext0 c.T w)) :=
    hFV.2.2 (c.V (j + 1)) (c.X (j + 1)) c.T (c.jac j 0 h).d (v.N (j + 1)) (c.x (j + 1)).L v.NT (hv.sd (j + 1) hjm) hx1
      hv.sdT (fun x _ => ((hS.good x).bf j 0 h).monoW) Ψ₂ hΨ₂
  set Ξ := flatBF (t.sBF j 0 h) Ψ₁ with hΞdef
  set Φ₂ : WO (c.X (j + 1)) c.T → ℂ := fun w => Ψ₂ ((c.jac j 0 h).d.ext0 c.T w) with hΦdef
  have hΞ' := he0.2 Ξ hΞ
  obtain ⟨hBV, hEq⟩ := hE Ξ (comb c.ψ _ _ e0 Ξ) Φ₂ hΞ hΞ' hΦ
  have hlst : c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂ = lastBi (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) Ξ Φ₂ := rfl
  have hopX : op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) = biComb c.ψ _ _ _ e₁ e₂
      (lastBi (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (comb c.ψ _ _ e0 Ξ) Φ₂) := by
    rw [hope, hlst, ← hop0e]
  refine ⟨hopX ▸ hBV, ?_⟩
  intro d d' hd hd' φ hφ f hf
  rw [hopX, ← hEq]
  obtain ⟨N, a, b, hab, hdec⟩ := (hLO (· ∉ v.tP)).2 d d' hd hd'
  rw [hlst, hdec, hdec]
  have hAC2 := hAC k ι o.p o.I (· ∈ v.tP) hPl (Fin c.T.rank) (Fin (c.X (j + 1)).rank) c.ψ hstd (c.X (j + 1)) c.T
    (o.β (j + 1)) o.γ (c.x (j + 1)).L v.NT hx1 hv.sdT (fun _ _ => 0)
  have hw₁ : IsWeilDatumO c.ψ _ _ (χA * χz) (t.sBF j 0 h).χW (t.sBF j 0 h).om₀ := by
    rw [← hχV]; exact (t.sBF j 0 h).weil₀
  have hSS := GlobalTheory.T.lastSeeSaw_doubleLift_additive D c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz
    (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (c.bes j 0 h).line.1 hS.pre.line.1 (hS.pre.tau j h)
    (hc.x j (by omega)).cpt (hc.x (j + 1) (by omega)).cpt hc.cpt χA χz (t.sBF j 0 h).χW χS' χT (t.sBF j 0 h).om₀
    (t.kom j) omz (t.kom (j + 1)) omT' omz'' hw₁ hwA hwz hwX hwT hwz'' (c.x j).vol (c.x (j + 1)).vol c.volT N
  have hRam : PairDat.Ram (⟨o.β j, o.β₀ j 0 h, o.Q j⟩ : PairDat o.p (c.X j) (c.bes j 0 h).V₀ (Fin (c.X j).rank)) φ := hφ
  have hRam' := (GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces D k ι o.p o.q o.χ o.hχ ε (Fin (c.X j).rank) (c.X j) (c.bes j 0 h).V₀
    ⟨o.β j, o.β₀ j 0 h, o.Q j⟩ hS.pre.inj o.I).1.mapsTo hRam
  have L1 := hSS (fun i => comb c.ψ _ _ (a i) Ξ) (fun i => comb c.ψ _ _ (b i) Φ₂)
    (fun i => ⟨((hAC1.2.2 (a i) (hab i).1 Ξ hΞ).1).1, ((hAC2.2.2 (b i) (hab i).2 Φ₂ hΦ).1).1⟩) φ f hφ.1 hf
  have L2 := hSS (fun i => comb c.ψ _ _ (a i) (comb c.ψ _ _ e0 Ξ)) (fun i => comb c.ψ _ _ (b i) Φ₂)
    (fun i => ⟨GlobalTheory.AvgMid.theta_comb hstd (combAt_fin (hab i).1) (GlobalTheory.AvgMid.theta_comb hstd (combAt_fin he0.1) hΞ.1),
      ((hAC2.2.2 (b i) (hab i).2 Φ₂ hΦ).1).1⟩) (o.S (fun _ => ε) j φ) f hRam'.1 hf
  beta_reduce at L1 L2
  unfold Comm.bl
  rw [L1, L2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hSm c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) c.T (c.bes j 0 h).o (c.bes j 0 h).ζ
    (c.bes j 0 h).line (hc.x j (by omega)).cpt (hc.x (j + 1) (by omega)).cpt hc.cpt (t.sBF j 0 h).χV (t.sBF j 0 h).χW
    χS' χT (t.sBF j 0 h).om₀ omT' (t.sBF j 0 h).weil₀ hwT
    (fun x hx => ⟨(hU.bf j 0 h x hx).1, (hU.bf j 0 h x hx).2, (hunrT x hx).1, (hunrT x hx).2⟩)
    (c.x j).vol (c.x (j + 1)).vol c.volT ⟨o.β j, o.β₀ j 0 h, o.Q j⟩ ⟨o.β (j + 1), o.Q (j + 1)⟩ ε (o.M j 0 h)
    (c.x (j + 1)).L v.NT hM hx1 hv.sdT
    (fun i => ⟨(hS.glued j 0 h i).sum, (hS.glued j 0 h i).lat, hS.pre.latT (j + 1) (by omega) i⟩)
    (comb c.ψ _ _ (a i) Ξ) (comb c.ψ _ _ (a i) (comb c.ψ _ _ e0 Ξ)) (comb c.ψ _ _ (b i) Φ₂)
    (hAC1.2.2 (a i) (hab i).1 Ξ hΞ).1 (hAC2.2.2 (b i) (hab i).2 Φ₂ hΦ).1
    ((hAC1.2.2 (a i) (hab i).1 Ξ hΞ).2 _ hΞ') φ hRam f hf

end GlobalTheory.FinPl.TLastAll

end
