import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FourthPowerTheta
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodModelTwoScaleOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOneOfDisc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormTwelveCubedEqOneOfFiveLePrime

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

open scoped ComplexConjugate

theorem GlobalTheory.ThLoc.jetsIntegral_three (hIn : GlobalTheory.ThLoc.Inputs) {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} (ha : 0 < a₀) (hd : 0 < dK)
    (lam : ℂ) (hlam : lam ≠ 0) (hd3 : dK % 3 = 2) {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (ι : ℂ ≃+* ℂ_[3])
    (hL : GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ dK ha hd lam hlam h Λ θ 3 ι) (W : WeierstrassCurve ℂ_[3])
    (hU : Unif 3 (cmL a₀ b₀ dK ha hd lam hlam) ι W) (hW : IntCurve W)
    {κx : Type} [Fintype κx] (r : κx → ℂ_[3]) (t : κx → n → ℂ) (M : ℕ) (hr : ∀ k, ‖r k‖ ≤ 1) (hM : 0 < M)
    (hpM : ¬ 3 ∣ M) (ht : ∀ k, (M : ℂ) • t k ∈ Λ) {J : Type} [Fintype J] (v : J → n → ℂ)
    (hv : ∀ j, InMul (cmL a₀ b₀ dK ha hd lam hlam) Λ (v j)) {ν : Type} [Fintype ν] (A : J → ν → ℂ_[3])
    (hA : ∀ j x, ‖A j x‖ ≤ 1) :
    JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[3]) h θ r t (frameM (ι : ℂ →+* ℂ_[3]) v A)) := by
  obtain ⟨hcmok, l2, l3, l4, l5⟩ := hL
  obtain ⟨-, -, hcm⟩ := GlobalTheory.ThLoc.LocJets.data ha hd lam hlam hcmok
  have hω : lam * (a₀ : ℂ) ∈ (cmL a₀ b₀ dK ha hd lam hlam).lattice :=
    (cmL a₀ b₀ dK ha hd lam hlam).ω₁_mem_lattice
  have hω1 : Formalism.L2.Th1.CM.omegaK dK * (lam * (a₀ : ℂ) / 2) ∉ (cmL a₀ b₀ dK ha hd lam hlam).lattice := by
    have := GlobalTheory.ThLoc.LocJets.half_notMem ha hd lam hlam hcmok 1 (Or.inl rfl)
    simpa [Formalism.L2.Th1.CM.omegaK] using this
  have hω2 : conj (Formalism.L2.Th1.CM.omegaK dK) * (lam * (a₀ : ℂ) / 2) ∉ (cmL a₀ b₀ dK ha hd lam hlam).lattice := by
    have := GlobalTheory.ThLoc.LocJets.half_notMem ha hd lam hlam hcmok (-1) (Or.inr rfl)
    rw [GlobalTheory.ThLoc.LocJets.conj_omegaK]
    simpa [sub_eq_add_neg] using this
  obtain ⟨g₁, ε, hiso, hidx, hidx', hε, hten⟩ := l5
  obtain ⟨Dm, q0, hD, hq0, hfac, hgram⟩ :=
    GlobalTheory.ThLoc.LocJets.gram_transfer a₀ b₀ c₀ dK ha hd lam hlam hcmok n h Λ g₁ hiso 3 ι hidx J v hv
  obtain ⟨Cm, q1, hCm, -, hfacC, -⟩ :=
    Formalism.L2.Th1.GD.FrameCompose_proof ℂ_[3] (Fin 4 × n) n J ν
      (fun w w' => ι (g₁.symm (Pi.single w' 1) w)) Dm (fun i j => ι (v j i))
      (fun j k => ι (Formalism.L2.Th1.GD.hOK (cmL a₀ b₀ dK ha hd lam hlam) h (v j) (v k))) _ q0 A hD hq0 hA hfac hgram
  have key : ∀ k, JetsIntegral (Formalism.L2.Th1.G.linSub (frameM (ι : ℂ →+* ℂ_[3]) v A)
        (MvPowerSeries.map (ι : ℂ →+* ℂ_[3]) (taylorMv (Formalism.L2.Th1.H.opU (matH h) (t k) θ)))) := by
    intro k
    obtain ⟨κ, _, r', s', N', hr', hN', h2N', hs', he⟩ := GlobalTheory.ThLoc.LocJets.fourth_power_theta a₀ b₀ c₀ dK ha hd
      lam hlam hcmok n h Λ l2 l3 θ l4 3 ι g₁ ε hiso hidx hidx' hε hten (t k) M hM hpM (ht k)
    have hj := hIn.jetsThree dK _ hcmok.2.2.1 hd3 hcm ι W hU hW (lam * a₀) hω hω1 hω2
      (Fin 4 × n) κ r' s' N' hr' hN' h2N' hs'
    rw [← he] at hj
    exact GlobalTheory.ThLoc.LocJets.jets_linear ℂ_[3] n _ _ hj ν (frameM (ι : ℂ →+* ℂ_[3]) v A) Cm hCm hfacC
  exact GlobalTheory.ThLoc.LocJets.jets_comb r _ hr key

theorem GlobalTheory.ThLoc.jetsIntegral_away_disc : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam h Λ θ p ι → p ≠ D.host.d → (p = 3 → D.host.d % 3 = 2) → ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (M : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < M → ¬ p ∣ M → (∀ k, (M : ℂ) • t k ∈ Λ) → ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ D.host.d ha hd lam hlam) Λ (v j)) → ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ 1) → JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) := by
  intro hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat n _ _ h Λ θ p _ ι hL hpd h3 κx _ r t M hr hM hpM ht
    J _ v hv ν _ A hA
  have hpr : p.Prime := Fact.out
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨l1, l2, l3, l4, l5⟩ := hL
    obtain ⟨W, hU, hW, ha1⟩ := GlobalTheory.ThLoc.goodModelTwo_scaleOne hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat ι
    exact (hIn.jetsTwo a₀ b₀ c₀ _ ha hd lam hlam l1 n h Λ l2 l3 θ l4 ι W hU hW ha1 l5 κx r t M hr hM hpM ht
      J v hv ν A hA).1
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨W, hU, hW⟩ := GlobalTheory.ThLoc.ModelThree.goodModelThree hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat ι
    exact GlobalTheory.ThLoc.jetsIntegral_three hIn ha hd lam hlam (h3 rfl) h Λ θ ι hL W hU hW r t M hr hM hpM ht v hv A hA
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  have h4 : p ≠ 4 := by rintro rfl; exact absurd hpr (by decide)
  have h5 : 5 ≤ p := by have := hpr.two_le; omega
  have hW := GlobalTheory.GoodModelFive.goodModel_five hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat p h5 ι
  have hnd : ¬ p ∣ D.host.d := fun hdv => hpd ((Nat.prime_dvd_prime_iff_eq hpr l1.2.2.2).1 hdv)
  exact (hIn.jetsOdd a₀ b₀ c₀ _ ha hd lam hlam l1 n h Λ l2 l3 θ l4 p hp2 hnd ι hW l5 κx r t M hr hM hpM ht
    J v hv ν A hA).1
