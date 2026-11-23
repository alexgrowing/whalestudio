import Formalism.LocalToGlobal.Columns.RecChainYKmap
import Formalism.LocalToGlobal.Columns.StabilizerMapMaximalIndex

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col.Sc

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Col

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L₀ : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {u : Pr.Word} {m2 : ℕ}
  {Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))}
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} {hSG : Pr.vGs ⊆ SG'} {ΛM : LevFam X.E X.K (R.N R.m - 1) SG'} {hm : R.m = m2 + 2}
  (sec : SecY W sel mu cst (L₀.withTop m2 Λt Θt) u m2)

attribute [local instance] ptYAct

def stabilizerMapMaximalIndex (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →*
      MulAction.stabilizer ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).mem (topIdx L₀ m2 Λt Θt hm)).G
        (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).rep
          (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).mem (topIdx L₀ m2 Λt Θt hm)).cls
            (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c)))) where
  toFun s := ⟨(((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).mv
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c)))⁻¹ *
      extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) *
      ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).mv
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c)), by
    have h1 := ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).mv_smul
      (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c))
    refine MulAction.mem_stabilizer_iff.2 ?_
    show (_ * _ * _) • ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).rep
      (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).mem (topIdx L₀ m2 Λt Θt hm)).cls
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c))) = _
    rw [mul_smul, mul_smul, h1, extYg_smul, inv_smul_eq_iff, h1]⟩
  map_one' := by
    apply Subtype.ext
    show _ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ 1 _ * _ = 1
    have e : extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) 1 (one_smul _ _) = 1 := by
      have e1 : (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)) = 1 := map_one (extR R hSG)
      apply Prod.ext
      · show (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).1 = 1
        rw [e1]
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          show (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).2 = 1
          rw [e1]
          rfl
        · apply Subtype.ext
          funext P
          apply Subtype.ext
          show (frameOfY u P.1 _)⁻¹ * ((extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).1.1) * frameOfY u P.1 _ = 1
          rw [e1]
          have e2 : ((1 : UF X.E (R.N R.m) × GLG X.E (R.N R.m) Pr.vGs).1 : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) = 1 := rfl
          rw [e2]
          group
    rw [e, mul_one, inv_mul_cancel]
  map_mul' s t := by
    apply Subtype.ext
    show _ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ (s.1 * t.1) _ * _ =
      (_ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) * _) *
        (_ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ t.1 (MulAction.mem_stabilizer_iff.1 t.2) * _)
    have e : extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) (s.1 * t.1) (MulAction.mem_stabilizer_iff.1 (s * t).2) =
        extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) *
          extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ t.1 (MulAction.mem_stabilizer_iff.1 t.2) := by
      have em : extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1) = extR R hSG (s.1.1, s.1.2.1) * extR R hSG (t.1.1, t.1.2.1) :=
        map_mul (extR R hSG) (s.1.1, s.1.2.1) (t.1.1, t.1.2.1)
      apply Prod.ext
      · show (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).1 = (extR R hSG (s.1.1, s.1.2.1)).1 * (extR R hSG (t.1.1, t.1.2.1)).1
        rw [em]
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          show (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).2 = (extR R hSG (s.1.1, s.1.2.1)).2 * (extR R hSG (t.1.1, t.1.2.1)).2
          rw [em]
          rfl
        · apply Subtype.ext
          funext P
          apply Subtype.ext
          show (frameOfY u P.1 _)⁻¹ * (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).1.1 * frameOfY u P.1 _ =
            ((frameOfY u P.1 _)⁻¹ * (extR R hSG (s.1.1, s.1.2.1)).1.1 * frameOfY u P.1 _) *
              ((frameOfY u P.1 _)⁻¹ * (extR R hSG (t.1.1, t.1.2.1)).1.1 * frameOfY u P.1 _)
          rw [em]
          show _ * ((extR R hSG (s.1.1, s.1.2.1)).1.1 * (extR R hSG (t.1.1, t.1.2.1)).1.1) * _ = _
          group
    rw [e]
    group

def stabMapY (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →*
      FamStabS (chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m) (tilY W cst L₀ u m2 Λt Θt hSG ΛM hm c) :=
  stabilizerMapMaximalIndex (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) sec hPr hpi hL hQ c

end Top

end Formalism.L2.Col.Sc
