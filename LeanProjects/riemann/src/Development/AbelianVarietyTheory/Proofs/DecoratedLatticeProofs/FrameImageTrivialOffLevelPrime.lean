import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoStabTrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardDatumSplitPlacesOverLevelPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointDecoratedLatticeAllTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NeConjOfIdemSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.FrameTriv

theorem frame_trivial_off : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 → ∀ (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (δ : TC.GA B (B.R.N j)), δ.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) →
    ∀ w : HeightOneSpectrum (𝓞 B.fields.E), (w ∈ (B.primes X).vGs ∨ w ∈ I.SQ ∨ (w ∈ (B.primes X).vT u ∧ w ≠ v.1)) →
      ∀ r r', adAt B.host.F w ((δ⁻¹).1 r r') = if r = r' then 1 else 0 := by
  intro B X I hI _ l Z u a k _ _ _ _ ι p β Q L _ j hj i v hidem g δ hδ w hw r r'
  classical
  have hPr : (B.primes X).Ok := l.pr
  have hv : (p i).v = v.1.under (𝓞 B.host.F) := GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under (p i) hidem
  have hvT : v.1 ∈ (B.primes X).vT u := v.2
  have hTv : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ v.1.asIdeal := T_mem_vT hPr u ⟨v.1, hvT⟩
  have hne : w.under (𝓞 B.host.F) ≠ (p i).v := by
    intro hwv
    rw [hv] at hwv
    have hTw : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
      have h1 : (((B.primes X).T u : ℕ) : 𝓞 B.host.F) ∈ (w.under (𝓞 B.host.F)).asIdeal := by
        rw [hwv]
        show algebraMap _ (𝓞 B.fields.E) _ ∈ v.1.asIdeal
        rw [map_natCast]
        exact hTv
      have h2 : algebraMap _ (𝓞 B.fields.E) (((B.primes X).T u : ℕ) : 𝓞 B.host.F) ∈ w.asIdeal := h1
      rwa [map_natCast] at h2
    rcases hw with h | h | ⟨h, hwne⟩
    · exact Formalism.L2.Col.T_notMem_vGs hPr u ⟨w, h⟩ hTw
    · have hg := (GlobalTheory.Mem.LevTwist.good_of_mem hI h).2
      have e := (GlobalTheory.Mem.ReadTwist.plc_under_eq_iff (F := B.host.F) w (hPr.T_prime u)).2 hTw
      refine hg.2.2 ?_
      rw [e]
      exact hI.T_mem u
    · rcases GlobalTheory.GridPlaces.eq_or_eq_conjP (D := I.rec7 l Z) hwv with e | e
      · exact hwne e
      · have hT0 : (B.primes X).piT u ≠ 0 := fun h0 => by
          have := hPr.piT_norm u
          rw [h0, zero_mul] at this
          exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
        have a1 : (B.primes X).piT u ∈ v.1.asIdeal := (Formalism.L2.Col.mem_divs hT0 _).1 hvT
        have a2 : (B.primes X).piT u ∈ w.asIdeal := (Formalism.L2.Col.mem_divs hT0 _).1 h
        rw [e] at a2
        have a3 : B.fields.conjO ((B.primes X).piT u) ∈ v.1.asIdeal := (Formalism.L2.Col.mem_conjP _ _).1 a2
        obtain ⟨x, y, hxy⟩ := hPr.piT_cop u
        have : (1 : 𝓞 B.fields.E) ∈ v.1.asIdeal := by
          rw [← hxy]
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ a1) (Ideal.mul_mem_left _ _ a3)
        exact v.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hb : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F))) δ = 1 :=
    GlobalTheory.T.splitFrameGL_finiteMatrix_offPlace_eq_one (I.rec7 l Z) k (p i) ((I.rec7 l Z).sp.X j) _ (β j i) g _ (rankN (I.rec7 l Z) j hj) δ hδ _ hne
  have hb' : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F))) δ⁻¹ = 1 := by
    rw [map_inv, hb, inv_one]
  have h2 : Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F)) ((δ⁻¹).1 r r') = if r = r' then 1 else 0 := by
    have := congrArg (fun x : GL (Fin (B.R.N j)) _ => x.1 r r') hb'
    simp only [Units.val_one, Matrix.one_apply] at this
    exact this
  have h3 : Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F)) ((δ⁻¹).1 r r' - if r = r' then 1 else 0) = 0 := by
    rw [map_sub, h2]
    split_ifs <;> simp
  have h4 := (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff B.host.F B.host.E _ _).1.1 h3 w rfl
  rw [map_sub, sub_eq_zero] at h4
  rw [h4]
  split_ifs <;> simp

end GlobalTheory.AdForm.FrameTriv

end
