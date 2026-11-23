import Formalism.LocalToGlobal.GlobalTheory.LinkTiesOm

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory NumberField

def H1 (Λ : AddSubgroup ℂ) (z w : ℂ) : ℂ := z * (starRingEnd ℂ) w / (TaylorLogMetric.area Λ : ℂ)

def al1 (d : ℕ) (Λ : AddSubgroup ℂ) (x : ℂ) : ℂ := (-1 : ℂ) ^ (round (Real.sqrt d / 2 * (H1 Λ x x).re))

def U1 (Λ : AddSubgroup ℂ) (x : ℂ) (G : ℂ → ℂ) : ℂ → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * H1 Λ z x - (Real.pi : ℂ) * H1 Λ x x / 2)

def IsTheta0 (d : ℕ) (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : Prop :=
  Differentiable ℂ G ∧ (∀ x ∈ Λ, ∀ z, al1 d Λ x * U1 Λ x G z = G z) ∧ G 0 = 1

def normSq1 (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : ℝ :=
  let Fd : Set ℂ := Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (H1 Λ z z).re)

def normConj (D : D7) (δ : ℂ) (e : TaylorLogMetric.FamE D) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : ℝ :=
  TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D D.host.ccK δ) M ρ)
    (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D D.host.ccK δ) M ρ) L L') (TaylorLogMetric.fnConj D M ρ (e N N' L L'))

def ThetaCompatible (D : D7) (δ : ℂ) (e : TaylorLogMetric.FamE D) : Prop :=
  ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (eL : D.what₂.LL ≃+* M),
    (∀ y, ((eL y : M) : ℂ) = D.what₂.embLL y) ∧
    TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D D.host.ccK δ) M ∧
    (∀ s : D.what₂.LL →+* ℂ, ∃ G, IsTheta0 D.host.d (TaylorLogMetric.lamConj M (conjOf eL s) (TaylorLogMetric.lamOf D D.host.ccK δ)) G ∧
      D.gx.thOne s ^ 2 = normSq1 (TaylorLogMetric.lamConj M (conjOf eL s) (TaylorLogMetric.lamOf D D.host.ccK δ)) G) ∧
    ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ (c : (D.mem u).C.cls i) (c' : (D.mem u).C.cls (i + 1)),
      ∃ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E))
        (L' : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E)),
        TaylorLogMetric.admitted D (D.R.N i) (D.R.N (i + 1)) L L' ∧ TaylorLogMetric.CoefIn D (e (D.R.N i) (D.R.N (i + 1)) L L') M ∧
        ∀ s : D.what₂.LL →+* ℂ,
          (D.fm u).thFree i s c c' ^ 2 = normConj D δ e M (conjOf eL s) (D.R.N i) (D.R.N (i + 1)) L L'

def ThPow (D : D7) (δ : ℂ) (e : TaylorLogMetric.FamE D) : Prop :=
  ∀ (M : IntermediateField ℚ ℂ) [NumberField M], TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D D.host.ccK δ) M →
    ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → TaylorLogMetric.CoefIn D (e N N' L L') M → ∀ (ρ : M →ₐ[ℚ] ℂ) (G : ℂ → ℂ),
      IsTheta0 D.host.d (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK δ)) G →
      normConj D δ e M ρ N N' L L' = normSq1 (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK δ)) G ^ (D.R.f * N * N')

private theorem normConj_eq_lemma {D : D7} {δ : ℂ} {e : TaylorLogMetric.FamE D} (M : IntermediateField ℚ ℂ) [NumberField M]
    (eL : D.what₂.LL ≃+* M) (hdata : TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D D.host.ccK δ) M)
    (hth : ∀ s : D.what₂.LL →+* ℂ, ∃ G, IsTheta0 D.host.d (TaylorLogMetric.lamConj M (conjOf eL s) (TaylorLogMetric.lamOf D D.host.ccK δ)) G ∧
      D.gx.thOne s ^ 2 = normSq1 (TaylorLogMetric.lamConj M (conjOf eL s) (TaylorLogMetric.lamOf D D.host.ccK δ)) G)
    (hp : ThPow D δ e) (u : D.what₂.Word) (i : ℕ)
    {L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E)}
    (hadm : TaylorLogMetric.admitted D (D.R.N i) (D.R.N (i + 1)) L L')
    (hcoef : TaylorLogMetric.CoefIn D (e (D.R.N i) (D.R.N (i + 1)) L L') M) (s : D.what₂.LL →+* ℂ) :
    normConj D δ e M (conjOf eL s) (D.R.N i) (D.R.N (i + 1)) L L' = Formalism.MainNotions.flipTwoThree.thetaLocalFactorAtIndex D u i s ^ 2 := by
  obtain ⟨G, hG, hG2⟩ := hth s
  rw [hp M hdata _ _ L L' hadm hcoef (conjOf eL s) G hG, ← hG2, Formalism.MainNotions.flipTwoThree.thetaLocalFactorAtIndex, ← pow_mul, ← pow_mul,
    mul_comm 2]

theorem thFree_of_tied {D : D7} {δ : ℂ} {e : TaylorLogMetric.FamE D} (h : ThetaCompatible D δ e) (hp : ThPow D δ e) : ThFree D := by
  obtain ⟨M, hM, eL, -, hdata, hth, htie⟩ := h
  intro u i hi s c c'
  obtain ⟨L, L', hadm, hcoef, hsq⟩ := htie u i hi c c'
  have e1 := hsq s
  rw [normConj_eq_lemma M eL hdata hth hp u i hadm hcoef s] at e1
  have hb : 0 ≤ Formalism.MainNotions.flipTwoThree.thetaLocalFactorAtIndex D u i s := pow_nonneg (D.gx.thOne_pos s).le _
  have ha : 0 ≤ (D.fm u).thFree i s c c' := by
    first
      | exact ((D.fm u).thFree_pos i s c c').le
      | exact (D.fm u).thFree_nonneg i s c c'
      | positivity
  first
    | exact (pow_left_inj₀ ha hb two_ne_zero).mp e1
    | exact le_antisymm (by nlinarith) (by nlinarith)

theorem thLinkLe_of_tied {D : D7} {δ : ℂ} {e : TaylorLogMetric.FamE D} (h : ThetaCompatible D δ e) (hp : ThPow D δ e)
    (hne : ∀ u i, i ≤ D.R.m → Nonempty ((D.mem u).C.cls i)) : ThLinkLe D (TaylorLogMetric.tor0 D D.host.ccK δ) e := by
  obtain ⟨M, hM, eL, -, hdata, hth, htie⟩ := h
  intro u i hi
  obtain ⟨c⟩ := hne u i hi.le
  obtain ⟨c'⟩ := hne u (i + 1) hi
  obtain ⟨L, L', hadm, hcoef, -⟩ := htie u i hi c c'
  refine ⟨L, L', hadm, M, inferInstance, hdata, hcoef, le_of_eq ?_⟩
  unfold Formalism.MainNotions.TaylorLogMetric.meanLogNormSq
  rw [← (conjEquiv eL).sum_comp]
  have hcard : (Fintype.card (D.what₂.LL →+* ℂ) : ℝ) = (Module.finrank ℚ M : ℝ) := by
    rw [Fintype.card_congr (conjEquiv eL), AlgHom.card]
  rw [hcard]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← normConj_eq_lemma M eL hdata hth hp u i hadm hcoef s]
  rfl

end Formalism.L2.GlobalTheoryTheory

end
