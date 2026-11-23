import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem om_sub' {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    g ∈ Q.Glev k r 0 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  obtain ⟨hG, hD, hGf⟩ := hg
  refine ⟨⟨hG, fun a ha => by simp at ha⟩, hGf, fun a => hD _ (by show (a : ℕ) + 1 ≤ r; omega)⟩

theorem stab_fix_gq {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (q : (Fin r → ℂ) × ℂ) {p : Q.Mx k r × Q.Mx k r} (hp : p ∈ NF.Stab k r z z' μsec q.2) :
    p.1 * bigCell k r q.1 (μsec q.2) * p.2 = bigCell k r q.1 (μsec q.2) := by
  obtain ⟨h1, -, h3⟩ := hp
  obtain ⟨-, hsub, hcomm⟩ := Formalism.FourierDecayAlt.P.TwoByOneBlock.uWbFacts k r
  have hc := hcomm q.1 p.1 (hsub z h1)
  have hf := (Formalism.FourierDecayAlt.P.TwoByOneBlock.bigCellFactor k r q.1 (μsec q.2)).1
  have h3' : p.1 * B2.embWb k r (μsec q.2) * p.2 = B2.embWb k r (μsec q.2) := h3
  rw [hf]
  calc p.1 * (bigCell k r q.1 1 * B2.embWb k r (μsec q.2)) * p.2
      = (p.1 * bigCell k r q.1 1) * B2.embWb k r (μsec q.2) * p.2 := by simp only [Matrix.mul_assoc]
    _ = bigCell k r q.1 1 * (p.1 * B2.embWb k r (μsec q.2) * p.2) := by rw [hc]; simp only [Matrix.mul_assoc]
    _ = bigCell k r q.1 1 * B2.embWb k r (μsec q.2) := by rw [h3']

theorem fibre_membership_holds : FibMem := by
  unfold FibMem
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v hP J hJ q hq
  simp only [NF.Fib, Set.mem_setOf_eq]
  intro p hp
  have hdom : q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := by
    obtain ⟨hq1, hq2⟩ := hq
    refine ⟨hq1, ?_⟩
    rw [hP.2.2.2.1, hP.2.2.2.2.1]
    exact hq2
  have hg := om_sub' (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hdom)
  have hfix := stab_fix_gq (T v).base.μsec q hp
  have hJe := hJ.2.2.2 (B.gq (T v).base q) ⟨hg.1, hg.2⟩ p.1 hp.1 p.2 hp.2.1
  exact hJe.symm.trans (congrArg J hfix)

end Formalism.FourierDecayAlt.P.CutMP.En
