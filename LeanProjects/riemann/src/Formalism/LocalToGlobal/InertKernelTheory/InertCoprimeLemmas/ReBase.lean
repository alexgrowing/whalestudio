import Formalism.LocalToGlobal.InertKernelTheory.StatementReBase
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.HalfTorsionNotMemCmLattice
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.KappaSelfDualFourthPowerLattice
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IsTorsionPointStandardCM

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (CmOK cmL matH stdH stdLat pow4 imgLat relIdx StdData Th alphaQ kernel4 tens4 stdChar)
open Formalism.L2.Th1.Top (IsLTNorm)

namespace ReBase

theorem odd_norm {D : D7} {cc : Ideal (𝓞 D.host.K)} (hcc : TaylorLogMetric.IsCurveIdeal D cc) : Odd (Ideal.absNorm cc) := by
  have hc2 : Nat.Coprime (Ideal.absNorm cc) 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 _) hcc.2
  rcases Nat.even_or_odd (Ideal.absNorm cc) with he | ho
  · exact absurd (Nat.Coprime.coprime_dvd_left (even_iff_two_dvd.1 he) hc2) (by decide)
  · exact ho

theorem cm_change_of_base : CmReBase := by
  intro D cc δ B hcc hδ
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, hcm, hN, -, hlat⟩ := curve_lattice_compatible D cc δ hcc.1 (odd_norm hcc) hδ
  have hlat' : (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ := hlat.symm
  refine ⟨a₀, g, b₀, c₀, ha, hd, hl, hcm, hN, hlat', KS.isTorsionPoint_standard_CM a₀ b₀ c₀ ha hd _ hl hcm hlat', ?_⟩
  have e : (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = 1 - Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
    rw [KS.theta_val']; ring
  have h := KS.half_period_unique_CM a₀ b₀ c₀ D.host.d ha hd _ hl hcm (B.ω₀ / 2)
    ((KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat' _).1 B.t0.1)
    (by rw [← KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat', KS.theta_val']; exact B.t0.2.1)
    (by rw [← KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat', ← e]; exact B.t0.2.2)
  rw [KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat',
    show (B.ω₀ - (g : ℂ) * δ * a₀) / 2 = B.ω₀ / 2 - (g : ℂ) * δ * a₀ / 2 by ring]
  exact h

theorem isThMM_eq {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B B' : Base D cc δ) (hγ : B'.gC = B.gC)
    (hκ : B'.kappa = B.kappa) (hω : (B.ω₀ - B'.ω₀) / 2 ∈ B'.L.lattice) : B'.IsThMM = B.IsThMM := by
  have h := KS.lattice_eq B B'
  have e : IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa = IsThM B'.L B'.ω₀ B.cq B.lamM B.gC B.kappa := by
    funext θ
    unfold IsThM kernel4 Formalism.L2.Th1.H.F0 Formalism.L2.Th1.H.stdLat
    rw [KS.hOne_congr h, KS.stdH_congr h, KS.thetaNull_congr_lattice h hω (Base.half_not_mem B'), h]
  show IsThM B'.L B'.ω₀ B.cq B.lamM B'.gC B'.kappa = IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa
  rw [hγ, hκ, e]

theorem theta_change_of_base : ThMMReBase := by
  intro D cc δ B hcc
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, hcm, hN, hlat, ht, hω⟩ := cm_change_of_base D cc δ B hcc (delta_ne_of_base B)
  have hω' : (B.ω₀ - (g : ℂ) * δ * a₀) / 2 ∈ (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice :=
    (KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat _).1 hω
  refine ⟨a₀, g, b₀, c₀, ha, hd, hl, KS.cmBase B a₀ b₀ c₀ ha hd ((g : ℂ) * δ) hl hcm hlat, hcm, hN,
    KS.cmBase_isCm B a₀ b₀ c₀ ha hd _ hl hcm hlat, KS.lattice_eq _ B, rfl, rfl, rfl,
    (KS.lattice_eq B (KS.cmBase B a₀ b₀ c₀ ha hd ((g : ℂ) * δ) hl hcm hlat)) ▸ hω',
    isThMM_eq B _ rfl rfl hω', (KS.thMM_reBase B _ hlat _ (KS.isTorsionPoint_standard_CM a₀ b₀ c₀ ha hd _ hl hcm hlat) hω').symm⟩

theorem stdLat_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : Type) : stdLat L n = stdLat L' n := by
  unfold Formalism.L2.Th1.H.stdLat; rw [h]

theorem isLTNorm_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 s2 ε : MaximalUnramifiedExtension l) : IsLTNorm l L ι g2 g3 s2 ε ↔ IsLTNorm l L' ι g2 g3 s2 ε := by
  obtain ⟨-, -, -, -, hs, -, -, h2, h3⟩ := Formalism.L2.Th1.F.latticeOnly L L' h
  unfold IsLTNorm
  rw [h2, h3, hs]

theorem th0Char_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) {ω₀ ω₀' : ℂ} (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice)
    {x : ℂ} (hx : x ∈ L'.lattice) : Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ x = Formalism.L2.Th1.F.thetaZeroCharacter L' ω₀' x := by
  obtain ⟨-, -, -, hA, -, -, -, -, -⟩ := Formalism.L2.Th1.F.latticeOnly L L' h
  obtain ⟨k, hk⟩ := Formalism.L2.Th1.F.altEInt L' x ((ω₀ - ω₀') / 2) hx hω
  have e0 : x * (starRingEnd ℂ) ω₀ / (Formalism.L2.Th1.F.area L' : ℂ) = x * (starRingEnd ℂ) ω₀' / (Formalism.L2.Th1.F.area L' : ℂ) +
      2 * (x * (starRingEnd ℂ) ((ω₀ - ω₀') / 2) / (Formalism.L2.Th1.F.area L' : ℂ)) := by
    simp only [map_div₀, map_sub, map_ofNat]; ring
  have e1 : Formalism.L2.Th1.F.altE L x ω₀ = Formalism.L2.Th1.F.altE L' x ω₀' + 2 * Formalism.L2.Th1.F.altE L' x ((ω₀ - ω₀') / 2) := by
    simp only [Formalism.L2.Th1.F.altE, Formalism.L2.Th1.F.herm, hA]
    rw [e0]
    simp [Complex.add_im, Complex.mul_im]
  unfold Formalism.L2.Th1.F.thetaZeroCharacter Formalism.L2.Th1.F.semiChar
  rw [h, e1, hk]
  congr 1
  rw [show ((Formalism.L2.Th1.F.altE L' x ω₀' + 2 * (k : ℝ) : ℝ) : ℂ) = (Formalism.L2.Th1.F.altE L' x ω₀' : ℂ) + (k : ℂ) * 2 by
    push_cast; ring]
  rw [mul_add, Complex.exp_add, show (Real.pi : ℂ) * Complex.I * ((k : ℂ) * 2) = (k : ℂ) * (2 * Real.pi * Complex.I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem stdData_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) {ω₀ ω₀' : ℂ} (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice)
    (hn : ω₀ / 2 ∉ L.lattice) {n : Type} [Fintype n] [DecidableEq n] {hh : Matrix n n ℂ} {Λ : AddSubgroup (n → ℂ)}
    {α : (n → ℂ) → ℂ} {β : (Fin 4 × n → ℂ) → ℂ} {g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)}
    (S : StdData L' ω₀' hh Λ α β g) : StdData L ω₀ hh Λ α β g := by
  have hS := KS.stdH_congr h (Fin 4 × n)
  have hL := stdLat_congr h (Fin 4 × n)
  refine ⟨?_, hn, ?_, S.alpha0, ?_, ?_, S.betaAlpha, ?_, ?_, ?_⟩
  · rw [h, show ω₀ = ω₀' + ((ω₀ - ω₀') / 2 + (ω₀ - ω₀') / 2) by ring]
    exact add_mem S.per (add_mem hω hω)
  · rw [hS]; exact S.isom
  · intro x hx
    have hx' : x ∈ stdLat L' (Fin 4 × n) := hL ▸ hx
    rw [S.betaStd x hx']
    unfold Formalism.L2.Th1.H.stdChar
    exact (Finset.prod_congr rfl fun i _ => th0Char_congr h hω (hx' i (Set.mem_univ i))).symm
  · rw [hS]; exact S.betaSemi
  · rw [hS]; exact S.selfDual
  · rw [hL]; exact S.idx₁
  · rw [hL]; exact S.idx₂

theorem k1ThetaAllBases : FirstKernelThetaAllBases := by
  intro D cc δ B hcc hδ l _ h5 hj ι
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, B', hcm, -, hIs, hlat, -, -, -, hω, -, hth⟩ := theta_change_of_base D cc δ B hcc
  have h : B.L.lattice = B'.L.lattice := hlat.symm
  have hω' : (B.ω₀ - B'.ω₀) / 2 ∈ B'.L.lattice := h ▸ hω
  obtain ⟨G, hS, hidx, hK⟩ := Kap.K1_theta_inert_prime D cc δ B' hcc hδ a₀ b₀ c₀ ha hd _ hl hcm hIs l h5 hj ι
  refine ⟨G, ?_, ?_, ?_⟩
  · have hS' := hS
    rw [← KS.hOne_congr h, ← KS.stdH_congr h] at hS'
    exact stdData_congr h hω' (Base.half_not_mem B) hS'
  · rw [stdLat_congr h]; exact hidx
  · intro g2 g3 ε s2 hN hg2 hg3 hD hε hth' t N hN0 hlN hNt σ γ B'' hF
    have := hK g2 g3 ε s2 ((isLTNorm_congr h l ι g2 g3 s2 ε).1 hN) hg2 hg3 hD hε hth' t N hN0 hlN hNt σ γ B'' hF
    rw [← KS.hOne_congr h, hth] at this
    exact this

end ReBase

end Formalism.L2.KerInert
