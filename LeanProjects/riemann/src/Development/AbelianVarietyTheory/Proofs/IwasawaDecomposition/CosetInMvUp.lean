import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2

theorem cosetIn_mv_up : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (j : ℕ), X.Ok → Pr.Ok → (∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) → ∀ (q : PtAt R sel mu cst u j) (P : Pr.vT u) (x : Sp X.E (R.N j)), x ∈ q.1.1.deco.1.N → q.1.1.deco.1.f P x = 1 → cosetIn (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x) : PtAt R sel mu cst u j) = cosetIn q := by
  intro X Pr R sel S mu cst u j hX hPr hQ q P x hx hf
  have hP := moveHyp_of_ok hPr u P
  have h := mv_up (Pr.T u) q P hP (T_unif hX hPr u P) (fun w => ne_of_T_notMem hPr u P (hQ w.1 w.2))
    (ysAt_off sel mu cst hPr u hQ j P) hx hf
  have hs := (upN_spec q.1.1.deco.2.lat q.1.1.deco.2.uni P.1 hP.ne hx).2.2.1
  have key : ∀ w : Pr.vGs, (q.1.1.deco.1.up P (Pr.T u : 𝓞 X.E) x).at w.1 = q.1.1.deco.1.at w.1 := fun w =>
    (hs w.1 (hP.sg w).1 (hP.sg w).2).localization_eq
  have hfr : frsF sel mu (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x)).1.1 = frsF sel mu q.1.1 := by
    funext P'
    unfold frsF
    split_ifs with hw
    · show (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x)).1.1.deco.1.liftFr ⟨P'.1, hw⟩ = q.1.1.deco.1.liftFr ⟨P'.1, hw⟩
      rw [h.1]
      unfold Deco.liftFr
      rw [key ⟨P'.1, hw⟩]
      rfl
    · show (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x)).1.1.1.2 _ = q.1.1.1.2 _
      rw [h.2.1]
  funext P'
  unfold cosetIn
  rw [hfr, h.2.2]

end GlobalTheory.Mem.Col2

end
