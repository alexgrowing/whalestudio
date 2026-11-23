import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeMulFd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramifiedStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchCas
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchBump
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchPhi

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.F0

open PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA

theorem cas_infOf_im {n : ℕ} (lam : Fin n → ℤ) : (cas (infOf lam)).im = 0 :=
  cas_infOf_im' lam

theorem bump_one (ι : Type) [Fintype ι] (c : ι → ℂ) (hc : ∀ i, (c i).im = 0) :
    ∃ (g : ℝ → ℝ) (T : ℝ), 0 ≤ T ∧ IsBump g T ∧ ∏ i, coshT g (c i) = 1 :=
  bump_one' ι c hc

theorem phiOf_cs {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (M : KMod n) (Tθ : M.V →L[ℂ] M.V)
    (k : Mat n → (M.V →L[ℂ] M.V)) (val : Inf n → ℂ) (T : ℝ) (h : IsMult μ M k val T) :
    Continuous (phiOf M Tθ k) ∧ HasCompactSupport (phiOf M Tθ k) :=
  phiOf_cs' μ M Tθ k val T h

theorem archEx_of (hG : PositivityTheory.Rg.BcB.E1.GrowthJ) (hC : CompatEx) (hL : Lef) (hV : VCBridge) (hP : LefPair)
    (hK : KerEx) : ArchEx := by
  intro E _ _ _ hE a b l₁ l₂ μ₁ μ₂ μa μb h₁ h₂ ha hb
  haveI : Nontrivial (InfinitePlace E) := GlobalTheory.T.nontrivial_infinite_place_of_unramified E hE
  haveI : BorelSpace (GA E a) := ⟨rfl⟩
  haveI : BorelSpace (GA E b) := ⟨rfl⟩
  haveI : BorelSpace (G a) := ⟨rfl⟩
  haveI : BorelSpace (G b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E a b) := ⟨rfl⟩
  have := h₁
  have := h₂
  have := ha
  have := hb
  obtain ⟨D, hD⟩ := hG E a b μ₁ μ₂
  obtain ⟨ν, hν, hν', hcomp⟩ := hC E a b D μa μb
  obtain ⟨-, -, ca, hca0, hca⟩ := GlobalTheory.CompanionTheory.Growth.size_facts E a
  obtain ⟨-, -, cb, hcb0, hcb⟩ := GlobalTheory.CompanionTheory.Growth.size_facts E b
  have LA := fun v : InfinitePlace E => hL a (l₁ v).w (l₁ v).anti
  have LB := fun v : InfinitePlace E => hL b (l₂ v).w (l₂ v).anti
  obtain ⟨bump, T, hT, hbump, hone⟩ := bump_one (InfinitePlace E ⊕ InfinitePlace E)
    (Sum.elim (fun v => cas (infOf (l₁ v).w)) fun v => cas (infOf (l₂ v).w))
    (fun i => by cases i <;> exact cas_infOf_im _)
  obtain ⟨_, hKa⟩ := hK a
  obtain ⟨_, hKb⟩ := hK b
  let Ma : Mods E a := fun v => (LA v).choose
  let Mb : Mods E b := fun v => (LB v).choose
  let Ta : Ops Ma := fun v => (LA v).choose_spec.choose
  let Tb : Ops Mb := fun v => (LB v).choose_spec.choose
  have sa := fun v => (LA v).choose_spec.choose_spec
  have sb := fun v => (LB v).choose_spec.choose_spec
  let ka : List (Bool × ℕ) → Kers Ma := fun w v => ((hKa μa (Ma v)).1 w bump T hbump).choose
  let kb : List (Bool × ℕ) → Kers Mb := fun w v => ((hKb μb (Mb v)).1 w bump T hbump).choose
  exact ⟨{
    D := D
    Ma := Ma
    Mb := Mb
    ν := ν
    ha := ha
    hb := hb
    hν := hν
    hν' := hν'
    compat := hcomp
    c := max ca cb
    c_nonneg := le_max_of_le_left hca0
    ca := fun g h => (hca g h).trans (by gcongr; exact le_max_left _ _)
    cb := fun g h => (hcb g h).trans (by gcongr; exact le_max_right _ _)
    growth := fun κ _ => hD (Io Ma Mb κ)
    Ta := Ta
    Tb := Tb
    vca := fun v k val T' hm => hV a μa (Ma v) (Ta v) k val T' (sa v).1 hm ((sa v).2.2.2 μa k val T' hm).1
    vcb := fun v k val T' hm => hV b μb (Mb v) (Tb v) k val T' (sb v).1 hm ((sb v).2.2.2 μb k val T' hm).1
    lef := fun v k k' val val' T' hm hm' => hP a b μa μb (l₁ v) (l₂ v) _ _ _ _
      ⟨(phiOf_cs μa (Ma v) (Ta v) k val T' hm).1, (phiOf_cs μa (Ma v) (Ta v) k val T' hm).2,
        fun d z hd hz hi => ((sa v).2.2.2 μa k val T' hm).2 d z hd hz hi |>.2⟩
      ⟨(phiOf_cs μb (Mb v) (Tb v) k' val' T' hm').1, (phiOf_cs μb (Mb v) (Tb v) k' val' T' hm').2,
        fun d z hd hz hi => ((sb v).2.2.2 μb k' val' T' hm').2 d z hd hz hi |>.2⟩
    bump := bump
    T := T
    T_nonneg := hT
    isBump := hbump
    ka := ka
    kb := kb
    kera := fun w v => ((hKa μa (Ma v)).1 w bump T hbump).choose_spec
    kerb := fun w v => ((hKb μb (Mb v)).1 w bump T hbump).choose_spec
    one := by simpa [Fintype.prod_sum_type] using hone }⟩

end PositivityTheory.Rg.BcB.F.F0

end
