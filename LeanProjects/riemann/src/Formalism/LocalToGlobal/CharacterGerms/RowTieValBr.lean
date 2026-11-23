import Formalism.LocalToGlobal.CharacterGerms.ValueEquationOfProjectors
import Formalism.LocalToGlobal.CharacterGerms.RowTieProj

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def EndoLogSt (Y : FBChart C V O dd) : Prop :=
  ∀ ε : Pt C 1 dd, (∀ i, MvPowerSeries.constantCoeff (ε i) = 0) →
    comp1 ε (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 ε (pt C (n := 2) dd 0)) (comp1 ε (pt C (n := 2) dd 1)) →
    ∀ (τ : Type) [Finite τ] (a : Fin dd → MvPowerSeries τ C), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) →
    ∀ i, MvPowerSeries.subst (fun q : Fin 1 × Fin dd => VP.exAt Y a q.2) (ε i) =
      VP.exAt Y (fun m => ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ε m) • a j) i

def KillSt (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) : Prop :=
  PairsSep Y p → ∀ (o : Orb) (g : Fin 2) (ε : Pt C 1 dd), (∀ i, MvPowerSeries.constantCoeff (ε i) = 0) →
    (∀ a, comp1 ε (Y.B.A.act a) = comp1 (Y.B.A.act a) ε) →
    (∀ v : Fin dd → C, ∃ b : I o g → C, linAct ε v = ∑ c, b c • (p o).u g c) →
    ∀ w : WVO I, (w.1, w.2.1) ≠ (o, g) → linAct ε ((p w.1).u w.2.1 w.2.2) = 0

theorem projPull_of (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (hE : EndoLogSt Y) (hK : KillSt Y p)
    (hP : ∀ o, ProjSt Y (p o)) : ProjPullSt Y p := by
  intro hs o g
  have h := hP o
  unfold ProjSt at h
  obtain ⟨e, h1, h2, hhom, -, hcomm, hfix, himg, -⟩ := h
  refine ⟨e g, h1 g, h2 g, fun i => ?_⟩

  set A : Fin dd → MvPowerSeries (WVO I) C := fun m =>
    ∑ w : WVO I, (p w.1).u w.2.1 w.2.2 m • (MvPowerSeries.X w : MvPowerSeries (WVO I) C) with hA
  have hAc : ∀ m, MvPowerSeries.constantCoeff (A m) = 0 := fun m => by simp [hA]

  have hlin : (fun m => ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (e g m) • A j) =
      zePart Y p (o, g) := by
    funext m
    simp only [hA, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have hterm : ∀ w : WVO I, (∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (e g m) *
        (p w.1).u w.2.1 w.2.2 j) = linAct (e g) ((p w.1).u w.2.1 w.2.2) m := fun w => rfl
    simp only [hterm]
    unfold zePart
    rw [Fintype.sum_sigma, Finset.sum_eq_single o]
    · rw [Fintype.sum_sigma, Finset.sum_eq_single g]
      · refine Finset.sum_congr rfl fun c _ => ?_
        dsimp only
        rw [hfix g c]
      · intro g' _ hg'
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [hK hs o g (e g) (h2 g) (hcomm g) (himg g) ⟨o, ⟨g', c⟩⟩ (by simp [hg'])]
        simp
      · simp
    · intro o' _ ho'
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [hK hs o g (e g) (h2 g) (hcomm g) (himg g) ⟨o', x⟩ (by simp [ho'])]
      simp
    · simp
  rw [toAllS_expPt, ← hlin, ← hE (e g) (h2 g) (hhom g) (WVO I) A hAc i]
  rfl

end Formalism.L2.FormalSeriesBounds
