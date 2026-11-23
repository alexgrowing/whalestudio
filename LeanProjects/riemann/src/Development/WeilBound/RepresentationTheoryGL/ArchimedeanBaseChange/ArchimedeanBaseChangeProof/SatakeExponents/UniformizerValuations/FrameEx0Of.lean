import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.FrameBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalExistenceOfUnramified
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.AllLeavesMono
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.StFull

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F.Ex0
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.Ex0

set_option maxHeartbeats 1000000 in
theorem frameEx0_of (hW : WeightEx) (hun : Rig.UnrAE) (hMu : MuEx) (hSec : SecEx) (hU : UnifEx) (hLev : LevelEx) (hS : SplitEx)
    (hB : BadEx2) (hK : KEx) (hT : TranslEx) (hC : ChainEx) (hA : ArchEx) (hWx : F0.WEx) : FrameEx0 := by
  intro hR E _ _ _ hE n hn π hπ S hS1
  choose lam hlam using fun v : InfinitePlace E => hW E n π hπ v.embedding
  obtain ⟨μ, e, hμ, hin, hae, hop⟩ := hMu E hE
  obtain ⟨Sec, d, h⟩ := local_existence_of_unramified hSec hU hLev hS hB hE π hπ (hun E n π hπ) S hS1 μ hin hae hop
  choose u hu using hT E
  obtain ⟨C⟩ := hC E hE n hn μ e hμ lam
  have A := fun i : C.ι => (hA E hE (C.a i) (n - C.a i) (C.l₁ i) (C.l₂ i) _ _ _ _ (C.hG (C.a i)) (C.hG (n - C.a i))
    (C.hC (C.a i)) (C.hC (n - C.a i))).some
  obtain ⟨K, k1, k2, k3, k4, k5⟩ := hK E n Sec h.hSec (d.S₀ ∪ d.Bad)
    (fun w hw => (Finset.mem_union.1 hw).elim (fun a => (h.S₀ w a).1) fun a => (h.bad w a).1) (fun w => μ.loc w) hop d.L h.ok₀.L
  obtain ⟨W, w1, w2⟩ := hWx hR E n μ e lam C A
  have hk : ∀ w : Pl E, ∃ k : ℕ, w ∈ d.Bad → ¬ IsSplitAt w → 1 ≤ k ∧ (∀ γ : UL n w, γ ∈ d.KB w ↔ γ.1 ∈ MB.congK n w k) ∧
      ∀ a ≤ n, d.fix a w = fun y => (((d.KB w).relIndex (KL n w) : ℕ) : ℂ) * MB.pairIndicatorMatch n a (n - a) w k y := fun w => by
    by_cases hw : w ∈ d.Bad ∧ ¬ IsSplitAt w
    · obtain ⟨k, a1, -, a2, a3⟩ := h.mok₀.badI w hw.1 hw.2
      exact ⟨k, fun _ _ => ⟨a1, a2, a3⟩⟩
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ hw⟩
  choose kB hkB using hk
  refine ⟨{ lam := lam, hlam := hlam, μ := μ, e := e, hμ := hμ, Sec := Sec, hSec := h.hSec, d₀ := d, ok₀ := h.ok₀, T₀ := h.T₀
            μloc := h.μloc, unif := h.unif, S₀ := h.S₀, S_le := h.S_le, bad := h.bad, good := h.good, kB := kB
            kB_pos := fun w a b => (hkB w a b).1, KBs := d.KB, KBs_lev := fun w a b => (h.mok₀.badS w a b).1
            KB_def := fun w => ?_, fix_def := fun a ha w => ?_, K'_lev := fun w a => (h.mok₀.S w a).2.2
            levFam := h.levFam, level := h.level, fix := h.fix, u₁ := fun a => u a, u₂ := fun a => u (n - a)
            hu := fun a => ⟨hu a, hu (n - a)⟩, C := C, A := A, K := K, hK := k1, Kc := k2, K_good := k3, K_bad := k4
            K_conj := k5, W := W, hW := w1, W_join := w2 }⟩
  · split_ifs with a b
    · rfl
    · have : {γ : UL n w | γ.1 ∈ MB.congK n w (kB w)} = (d.KB w : Set (UL n w)) := Set.ext fun γ => ((hkB w a b).2.1 γ).symm
      rw [this, Subgroup.closure_eq]
    · exact (h.off w a).1
  · split_ifs with b c
    · exact (h.mok₀.badS w b c).2 a ha
    · exact (hkB w b c).2.2 a ha
    · exact (h.off w b).2 a

end PositivityTheory.Rg.BcB.F.Ex0

end
