import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem eqAt_symm' {D : D7} {p N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : EqAt D p L L₁) : EqAt D p L₁ L := by
  obtain ⟨s, hs, h1, h2⟩ := h
  exact ⟨s, hs, h2, h1⟩

theorem intS_of_pair (hPair : PairFact) {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {p : ℕ} [Fact p.Prime]
    {lam : Qbar →+* ℂ_[p]} {N N' : ℕ}
    {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hE : EqAt D p L L₁) (hE' : EqAt D p L' L₁') {F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]}
    (h : IntS D (tor0 D cc δ) p lam L₁ L₁' F) : IntS D (tor0 D cc δ) p lam L L' F := by
  intro C wq r b hC hwq hb hon
  exact h C wq r b hC hwq ((hPair D cc δ p N N' L L₁ L' L₁' hE hE').1 r b hb) hon

theorem thZeroInt (hAlg : AlgFact) (hBI : BasisInv) (hTens : TensFact) (hMM : ThFourInt)
    {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (χ : IdE D → ℂ) (hχ : IsChi D χ) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hin : jacobiSym (-(D.host.d : ℤ)) p = -1) (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (hN : Even N) (hN' : Even N')
    (s : VC D N N') (hs : TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) s) :
    IntS D B.tor p lam (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') (pSer D lam (U D B.tor s (B.thZero N N'))) :=
  hBI D cc δ hcc hδ p hp hin lam N N' _ _ _
    (hTens D cc δ B hcc hδ p hp hin lam (fun s1 hs1 =>
      ⟨(hAlg D cc δ B hcc hδ χ hχ p hp hin 2 2).2 s1 hs1,
       hMM D cc δ B hcc hδ p hp hin lam s1 hs1,
       hBI D cc δ hcc hδ p hp hin lam 2 2 _ _ _ (hMM D cc δ B hcc hδ p hp hin lam s1 hs1)⟩) N N' hN hN' s hs)

theorem stdInt (hComb : CombFact) (hPair : PairFact) (hAlg : AlgFact) (hLin : PSerLin) (hStd : StdStep)
    (hBI : BasisInv) (hTens : TensFact) (hMM : ThFourInt)
    {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (χ : IdE D → ℂ) (hχ : IsChi D χ) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hin : jacobiSym (-(D.host.d : ℤ)) p = -1) (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
    (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hA : admitted D N N' M M') (hE : EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N) M) (hE' : EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N') M')
    (t : VC D N N') (ht : TorsPrime D p (La D B.tor M M') t) :
    IntS D B.tor p lam M M' (pSer D lam (U D B.tor t (B.eNat χ N N' M M'))) := by
  obtain ⟨m, c, s, hc, hs, heq⟩ := hStd D cc δ B hcc hδ χ hχ p hp hin lam N N' M M' hA hE hE' t ht
  have hL := hLin D p lam N N' m c (fun k => U D B.tor (s k) (B.thZero N N')) (fun k => (hc k).1)
    (fun k => (hAlg D cc δ B hcc hδ χ hχ p hp hin N N').2 (s k) (hs k))
  rw [heq]
  show IntS D B.tor p lam M M'
    (pSer D lam (fun z => ∑ k, c k * (fun k => U D B.tor (s k) (B.thZero N N')) k z))
  rw [hL]
  exact hComb D B.tor p lam N N' M M' m (fun k => lamC lam (c k)) _ (fun k => (hc k).2)
    (fun k => intS_of_pair hPair (eqAt_symm' hE) (eqAt_symm' hE')
      (thZeroInt hAlg hBI hTens hMM B hcc hδ χ hχ p hp hin lam N N' hA.1 hA.2.1 (s k) (hs k)))

theorem transOne (hComb : CombFact) (hPair : PairFact) (hWA : WeakApprox) (hPT : PullTors) (hPull : PullFact)
    (hAlg : AlgFact) (hLin : PSerLin) (hStd : StdStep) (hBI : BasisInv) (hTens : TensFact) (hMM : ThFourInt)
    {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (χ : IdE D → ℂ) (hχ : IsChi D χ) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hin : jacobiSym (-(D.host.d : ℤ)) p = -1) (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hA : admitted D N N' L L') (t : VC D N N') (ht : TorsPrime D p (La D B.tor L L') t) :
    IntS D B.tor p lam L L' (pSer D lam (U D B.tor t (B.eNat χ N N' L L'))) := by
  letI := D.host.cmStar
  obtain ⟨γ, γ', M, M', hAM, hE, hE', rfl, rfl⟩ := hWA D p hp hin N N' L L' hA
  have hEq : Formalism.MainNotions.TaylorLogMetric.eq22 D B.tor χ (B.eNat χ) := Formalism.L2.PairingIndexBounds.Eq.SqG.eulerProduct_eq_of_curve_ideal B hcc hδ χ hχ
  obtain ⟨h1, -, -⟩ := hEq
  obtain ⟨hN, hN', hSM, hSM'⟩ := id hAM
  have hcov : pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
      (B.eNat χ N N' M M') =
      B.eNat χ N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M') :=
    h1 N N' ⟨M, hSM⟩ ⟨M', hSM'⟩ hN hN' γ γ'
  rw [← hcov]
  have ht' := hPT D cc δ p N N' γ γ' M M' t ht
  exact hPull D cc δ p lam N N' γ γ' M M' t (B.eNat χ N N' M M')
    ((hAlg D cc δ B hcc hδ χ hχ p hp hin N N').1 M M' hAM hE hE' _ ht')
    (stdInt hComb hPair hAlg hLin hStd hBI hTens hMM B hcc hδ χ hχ p hp hin lam N N' M M' hAM hE hE' _ ht')

theorem intInert_of (hComb : CombFact) (hPair : PairFact) (hWA : WeakApprox) (hPT : PullTors) (hPull : PullFact)
    (hAlg : AlgFact) (hLin : PSerLin) (hStd : StdStep) (hBI : BasisInv) (hTens : TensFact) (hMM : ThFourInt) :
    IntInert := by
  unfold IntInert
  intro D cc δ B hcc hδ χ hχ p _ hp hin lam N N' L L' _hA
  unfold IntFirst
  intro F hF
  obtain ⟨m, r, t, L₁, L₁', hr, ht, hL, rfl⟩ := hF
  refine hComb D B.tor p lam N N' L L' m r _ hr (fun k => ?_)
  obtain ⟨hA₁, hE, hE'⟩ := hL k
  exact intS_of_pair hPair hE hE'
    (transOne hComb hPair hWA hPT hPull hAlg hLin hStd hBI hTens hMM B hcc hδ χ hχ p hp hin lam N N' (L₁ k) (L₁' k)
      hA₁ (t k) ((hPair D cc δ p N N' L (L₁ k) L' (L₁' k) hE hE').2 (t k) (ht k)))

end Formalism.L2.KerInert
