import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.InertKernelTheory.StatementReBase
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.HalfTorsionNotMemCmLattice
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IsTorsionPointStandardCM
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormKappaSqMulDetSplitPrimeStatement

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN Formalism.L2.KerInert
open Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity
open Formalism.L2.Th1.F (cmTheta)

namespace GlobalTheory.CmThetaMoment

theorem cmTheta_odd (b : ℤ) (hb : Odd b) (d : ℕ) : ∃ k : ℤ, cmTheta b d = cmTheta 1 d + (k : ℂ) := by
  obtain ⟨k, rfl⟩ := hb
  refine ⟨k, ?_⟩
  simp only [cmTheta]
  push_cast
  ring

theorem stable_of_one {V : Type*} [AddCommGroup V] [Module ℂ V] (Λ : AddSubgroup V) (d : ℕ)
    (h : ∀ x ∈ Λ, cmTheta 1 d • x ∈ Λ) (b : ℤ) (hb : Odd b) : ∀ x ∈ Λ, cmTheta b d • x ∈ Λ := by
  intro x hx
  obtain ⟨k, hk⟩ := cmTheta_odd b hb d
  rw [hk, add_smul]
  refine Λ.add_mem (h x hx) ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Λ.zsmul_mem hx k

theorem odd_of_cmOK {a : ℕ} {b c : ℤ} {d : ℕ} (h : CmOK a b c d) : Odd b := by
  by_contra hb
  obtain ⟨k, rfl⟩ := Int.not_odd_iff_even.1 hb
  have h1 := h.1
  have h8 := h.2.2.1
  have h2 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k) := by
    have : (k + k) ^ 2 = 4 * (k * k) := by ring
    rw [this] at h1
    linarith
  generalize (a : ℤ) * c - k * k = t at h2
  omega

theorem hermitianSelfDual_of_fourfoldBlock {n : Type} [Fintype n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (hsd : IsSelfDual (matH (blk4 h)) (pow4 Λ)) : IsSelfDual (matH h) Λ := by
  have key : ∀ (x : n → ℂ) (y : Fin 4 × n → ℂ), altE (matH (blk4 h)) (CmData.embA 0 x) y = altE (matH h) x (slice 0 y) := by
    intro x y
    simp only [altE, matrixForm_fourfoldBlock, CmData.slice_embA]
    rw [Finset.sum_eq_single (0 : Fin 4)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  ext x
  constructor
  · intro hx
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      intro y hy
      obtain ⟨m, hm⟩ := hx (slice 0 y) (hy 0)
      exact ⟨m, by rw [key, hm]⟩
    rw [hsd] at h1
    have h2 := h1 0
    rwa [CmData.slice_embA, if_pos rfl] at h2
  · intro hx y hy
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      rw [hsd]
      exact CmData.embA_mem Λ 0 hx
    obtain ⟨m, hm⟩ := h1 _ (CmData.embA_mem Λ 0 hy)
    refine ⟨m, ?_⟩
    rw [key, CmData.slice_embA, if_pos rfl] at hm
    exact hm

section Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem selfDual_fourfold_curveIdeal_lattice (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (blk4 (hOne B.L D.what₂.Tau))) (pow4 B.lamM) := by
  have h := ((B.latAll hcc hδ (base_linkage_nonempty D cc δ B)).1 2 2 _ _
    (Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D 2 2 even_two even_two)).1
  rw [show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = _ from B.areaOK, show TaylorLogMetric.La D B.tor _ _ = _ from B.lat0OK 2 2] at h
  have h2 := SO.selfDual_img _ _ (SO.reix D.what₂.Tau) (SO.reix_isom B.L D.what₂.Tau) _ h
  rw [SO.reix_pow] at h2
  exact h2

theorem selfDual_lamM (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (hOne B.L D.what₂.Tau)) B.lamM :=
  hermitianSelfDual_of_fourfoldBlock _ _ (selfDual_fourfold_curveIdeal_lattice B hcc hδ)

theorem stable_lamM (b : ℤ) (hb : Odd b) : ∀ x ∈ B.lamM, cmTheta b D.host.d • x ∈ B.lamM := by
  refine stable_of_one _ _ (fun x hx => ?_) b hb
  have := SO.lamMM_smul (AR.om D) hx
  rw [← SO.theta_eq] at this
  exact this

end Base

theorem odd_norm {D : D7} {cc : Ideal (𝓞 D.host.K)} (hcc : TaylorLogMetric.IsCurveIdeal D cc) : Odd (Ideal.absNorm cc) := by
  have hc2 : Nat.Coprime (Ideal.absNorm cc) 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 _) hcc.2
  rcases Nat.even_or_odd (Ideal.absNorm cc) with he | ho
  · exact absurd (Nat.Coprime.coprime_dvd_left (even_iff_two_dvd.1 he) hc2) (by decide)
  · exact ho

theorem cmReBase' : CmReBase := by
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

theorem thMMReBase' : ThMMReBase := by
  intro D cc δ B hcc
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, hcm, hN, hlat, ht, hω⟩ := cmReBase' D cc δ B hcc (delta_ne_of_base B)
  have hω' : (B.ω₀ - (g : ℂ) * δ * a₀) / 2 ∈ (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice :=
    (KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat _).1 hω
  refine ⟨a₀, g, b₀, c₀, ha, hd, hl, KS.cmBase B a₀ b₀ c₀ ha hd ((g : ℂ) * δ) hl hcm hlat, hcm, hN,
    KS.cmBase_isCm B a₀ b₀ c₀ ha hd _ hl hcm hlat, KS.lattice_eq _ B, rfl, rfl, rfl,
    (KS.lattice_eq B (KS.cmBase B a₀ b₀ c₀ ha hd ((g : ℂ) * δ) hl hcm hlat)) ▸ hω',
    isThMM_eq B _ rfl rfl hω', (KS.thMM_reBase B _ hlat _ (KS.isTorsionPoint_standard_CM a₀ b₀ c₀ ha hd _ hl hcm hlat) hω').symm⟩

theorem stdLat_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : Type) : stdLat L n = stdLat L' n := by
  unfold Formalism.L2.Th1.H.stdLat; rw [h]

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

theorem kernel4_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) {ω₀ ω₀' : ℂ}
    (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice) (hn : ω₀' / 2 ∉ L'.lattice) {n : Type} [Fintype n] [DecidableEq n]
    (Λ : AddSubgroup (n → ℂ)) (cq : ℝ) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) :
    kernel4 L ω₀ Λ (alphaQ cq (stdH L (Fin 4 × n))) g = kernel4 L' ω₀' Λ (alphaQ cq (stdH L' (Fin 4 × n))) g := by
  unfold kernel4 F0 stdLat
  rw [KS.stdH_congr h, KS.thetaNull_congr_lattice h hω hn, h]

theorem isomStdCm (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0)
    (hcm : CmOK a₀ b₀ c₀ D.host.d) (hB : B.IsCm a₀ b₀ ha hd lam hlam) (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (hj : jacobiSym (-(D.host.d : ℤ)) q = 1) (hco : Nat.Coprime (Ideal.absNorm cc) q) (ι : ℂ ≃+* ℂ_[q]) :
    ∃ (g : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (e : ℂ),
      StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
        (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) g ∧
      ¬ q ∣ relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
        (imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ∧
      ‖ι e‖ = 1 ∧
      tens4 B.thMM = e • kernel4 B.L B.ω₀ B.lamM (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) g := by
  have hK := GlobalTheory.T.norm_kappa_sq_mul_det_splitPrime D cc δ B hcc hδ q hq2 hj hco ι
  obtain ⟨hL, hω⟩ := hB
  have hS : StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
    (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := B.stdOK hcc hδ
  have hsd := selfDual_lamM B hcc hδ
  have hst := stable_lamM B b₀ (odd_of_cmOK hcm)
  have hspec := B.thMM_spec (B.stdOK hcc hδ)
  have h2 : tens4 B.thMM = B.kappa • kernel4 B.L B.ω₀ B.lamM
      (alphaQ (Real.sqrt D.host.d / 2) (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := hspec.2
  have iso := hS.isom
  have i1 := hS.idx₁
  have i2 := hS.idx₂
  rw [hω] at h2 ⊢
  rw [hL] at h2 hK iso i1 i2 hsd ⊢
  have hsda := CmData.selfDual_img _ _ B.gC iso _ (CmData.isSelfDual_matH_blk4_pow4 _ B.lamM hsd)
  have hsta : ∀ x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM),
      cmTheta b₀ D.host.d • x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM) := by
    rintro x ⟨x', hx', rfl⟩
    refine ⟨cmTheta b₀ D.host.d • x', fun a' => hst _ (hx' a'), ?_⟩
    simp
  obtain ⟨u, huiso, hufix, j1, jl, j2⟩ := localStandard a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (Fin 4 × D.what₂.Tau) _
    hsda hsta i1 i2 q Fact.out
  have hκu := hK u huiso j1 jl j2
  rw [← KR.imgLat_trans] at j1 jl j2
  have hg₁ : IsIsom (matH (blk4 (hOne (cmL a₀ b₀ D.host.d ha hd lam hlam) D.what₂.Tau)))
      (stdH (cmL a₀ b₀ D.host.d ha hd lam hlam) (Fin 4 × D.what₂.Tau))
      ((B.gC.trans u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) :
        (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) := by
    intro x y
    have h1 := huiso (B.gC x) (B.gC y)
    have h0 := iso x y
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply] at h0 h1 ⊢
    rw [h1, h0]
  have D0 := stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM B.gC iso hsd hst i1 i2
  have D1 := stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM (B.gC.trans u) hg₁
    hsd hst j1 j2
  have hcomp : B.gC.symm.trans (B.gC.trans u) = u := by
    ext x
    simp
  have hfix : ∀ x, (B.gC.trans u) x = B.gC x → x = 0 := by
    intro x hx
    have h1 : B.gC x = 0 := hufix _ hx
    simpa using congrArg B.gC.symm h1
  rw [← hcomp] at hκu
  obtain ⟨c, hc8, hc⟩ := kernelRatio _ _ D.what₂.Tau _ B.lamM _ _ B.gC (B.gC.trans u) D0 D1 hfix
  exact ⟨B.gC.trans u, B.kappa * c, D1, jl, KR.norm_mul_eq_one ι B.kappa c _ hc8 hκu,
    by rw [h2, hc, smul_smul]; rfl⟩

theorem isomStd : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∃ (g : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (e : ℂ), Formalism.L2.Th1.H.StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau))) (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau))) g ∧ ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) ∧ ‖ι e‖ = 1 ∧ Formalism.L2.Th1.H.tens4 B.thMM = e • Formalism.L2.Th1.H.kernel4 B.L B.ω₀ B.lamM (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau))) g := by
  intro D cc δ B hcc hδ q _ hq2 hj hco ι
  obtain ⟨a₀, gg, b₀, c₀, ha, hd, hl, B', hcm, -, hIs, hlat, -, -, -, hω, -, hth⟩ := thMMReBase' D cc δ B hcc
  have h : B.L.lattice = B'.L.lattice := hlat.symm
  obtain ⟨G, e, hS, hidx, he, hten⟩ := isomStdCm D cc δ B' hcc hδ a₀ b₀ c₀ ha hd _ hl hcm hIs q hq2 hj hco ι
  have hωB' : (B.ω₀ - B'.ω₀) / 2 ∈ B'.L.lattice := h ▸ hω
  have hω' : (B'.ω₀ - B.ω₀) / 2 ∈ B.L.lattice := by
    have := neg_mem hω
    rwa [show -((B.ω₀ - B'.ω₀) / 2) = (B'.ω₀ - B.ω₀) / 2 by ring] at this
  have hk : kernel4 B'.L B'.ω₀ B'.lamM (alphaQ B'.cq (stdH B'.L (Fin 4 × D.what₂.Tau))) G
      = kernel4 B.L B.ω₀ B.lamM (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) G :=
    kernel4_congr hlat hω' (Base.half_not_mem B) B.lamM B.cq G
  refine ⟨G, e, ?_, ?_, he, ?_⟩
  · have hS' := hS
    rw [← KS.hOne_congr h, ← KS.stdH_congr h] at hS'
    exact stdData_congr h hωB' (Base.half_not_mem B) hS'
  · rw [stdLat_congr h]; exact hidx
  · rw [← hth, hten, hk]

end GlobalTheory.CmThetaMoment
