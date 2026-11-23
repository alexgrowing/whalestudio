import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeReadingEigenvaluePlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RatHeckeBall
set_option maxHeartbeats 1600000 in
theorem ratHecke_keeps_ball_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∀ (j k : ℕ) (Pl : PlE (Dof x).host), 1 ≤ j → j ≤ (Dof x).R.m → IsSplitPl (Dof x).host Pl → Pl ∉ SbD (Dof x) → k ≤ (Dof x).R.r → ∀ la : HeightOneSpectrum (𝓞 (SOf x).Ks), (∀ q : ℕ, q.Prime → (q : 𝓞 (Dof x).host.E) ∈ Pl.asIdeal → (q : 𝓞 (SOf x).Ks) ∉ la.asIdeal) → ∀ (f : (SOf x).WL j) (hf : f ∈ ((SOf x).A j).WK) (hg : hL' j k Pl f ∈ ((SOf x).A j).WK), (∀ y, ((SOf x).A j).nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, ((SOf x).A j).nrm la y ⟨hL' j k Pl f, hg⟩ ≤ 1 := by
  intro hLL hDec hI hT hRT
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  have hId : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  refine ((hId.and (ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  intro P x _ hL' hstab hRd j k v hj1 hj2 hsp hPS hk la hla g hg hhg hball
  obtain ⟨hHo, -⟩ := H.1.2 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := H.2 (w.st x.o.Z) hO
  have hfin : Finite (TupU w.I (usedOf w.I T P.Wt)) := by
    have hs : ({τ | τ = (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T P.Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T P.Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T P.Wt)).finite_toSet
    exact hs.to_subtype
  let X := GlobalTheory.TwInputs.RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo hfin hHo hStd hSize
  have hS := GlobalTheory.T.heckeOperator_preserves_supLattice_realSide hDec hI hT hRT (Dof x) X (idxOf (Dof x) j)
  have hlow : ∀ p ∈ lowAll (Dof x), p ≠ 0 → ((p : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := by
    intro p hp hp0 hm
    apply hPS
    rw [SbD, Set.Finite.mem_toFinset]
    exact ⟨p, hp, hp0, hm⟩
  have hgP : ∀ kk : Fin 2, (((Dof x).host.g kk : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := fun kk =>
    hlow _ (by fin_cases kk <;> simp [lowAll]) ((Dof x).host.g_prime kk).ne_zero
  have hso : Bridge.SplitOff v (X.R.Sb : Set (Formalism.L2.DIV.Pl (Dof x).host.E)) := by
    have hAll : X.R.Sb = X.R.Pg := X.char.allPl
    have hPg := X.char.lev.Pg
    refine ⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff v).1 hsp, fun h => ?_, fun Q hQ h => ?_⟩
    · rw [Finset.mem_coe, hAll] at h
      obtain ⟨kk, hkk⟩ := (hPg v).1 h
      exact hgP kk (GlobalTheory.StepLaw.typePrime_mem_of_div hkk)
    · rw [Finset.mem_coe, hAll] at hQ
      obtain ⟨kk, hkk⟩ := (hPg Q).1 hQ
      have hm := GlobalTheory.StepLaw.typePrime_mem_of_div hkk
      rw [h, Formalism.L2.Col.conjIdeal_asIdeal, Formalism.L2.Col.mem_conjP, map_natCast] at hm
      exact hgP kk hm
  obtain ⟨α, Rc, ha, hR⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt X.char.lev X.char.fam (idxOf (Dof x) j) hso hk
  have hg01 : (((Dof x).host.g 0 * (Dof x).host.g 1 : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := by
    intro hm
    rw [Nat.cast_mul] at hm
    rcases v.isPrime.mem_or_mem hm with h | h
    exacts [hgP 0 h, hgP 1 h]
  have hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData X.R.toRealDat (idxOf (Dof x) j) v k α Rc := ⟨hso, hg01, hk, ha, hR⟩
  have hkd : HkDat x.m.z.R (SbD (Dof x)) (idxOf (Dof x) j) k v α Rc :=
    ⟨hsp, hPS, hlow 2 (by simp [lowAll, lowPr]) two_ne_zero, hk, ha, hR⟩
  have e : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.hkC X.R.toRealDat (idxOf (Dof x) j) v k = hkNorm x.m.z.R (idxOf (Dof x) j) k v := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.hkC, hkNorm, inv_pow]
    all_goals rfl
  have hK := hS v k α Rc hd (hL' j k v) (fun y => by rw [e]; exact hRd j k v α Rc hj1 hj2 hkd y)
    (fun y hy => hstab j hj1 hj2 k v y hy) la hla
  exact hK.sup ⟨g, hg⟩ hball
end GlobalTheory.RatHeckeBall
end
