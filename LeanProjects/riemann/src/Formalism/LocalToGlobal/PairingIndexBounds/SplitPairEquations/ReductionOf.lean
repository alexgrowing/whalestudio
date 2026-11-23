import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.CharacterFactorUnitaryAction

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Ker.Base D cc δ}

theorem Iop_smulF (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La₁ La₂ : AddSubgroup (TaylorLogMetric.VC D N N')) (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.Iop D T La₁ La₂ (c • G) = c • TaylorLogMetric.Iop D T La₁ La₂ G :=
  funext fun z => Iop_smul' D T La₁ La₂ c G z

theorem e3a (hP : PullIop D B.tor) (hTL : Tr0L D B.tor) (hSm : SmulSD D) (hL : B.LatAll) (hJ : J1 B)
    {N N' : ℕ} (hN : Even N) (hN' : Even N') (h0 : B.ThZeroMem N N') :
    letI := D.host.cmStar
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (X : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D X →
    TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (1 : Matrix (Fin N') (Fin N') D.host.E) (B.thMoved N N' L X) =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) •
        B.thMoved N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) X := by
  letI := D.host.cmStar
  intro γ L X hLs hX
  have e1 : ((1 : Matrix.unitaryGroup (Fin N') D.host.E) : Matrix (Fin N') (Fin N') D.host.E) = 1 := rfl
  have hγL := hSm N L γ hLs
  have hγ0 := hSm N (StandardLatticesGL3.stdL D N) γ (sd0 N)
  have hH := mvTh B hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' hLs (sd0 N')) h0
  have p1 := (hP N N' L L (StandardLatticesGL3.stdL D N') X γ 1 hN hN' hLs hLs (sd0 N') hX (B.thHalf N N' L)
    (mem_ThSp_of' _ _ _ _ hH)).2
  have p2 := (hP N N' (StandardLatticesGL3.stdL D N) L (StandardLatticesGL3.stdL D N') (StandardLatticesGL3.stdL D N') γ 1 hN hN' (sd0 N) hLs (sd0 N') (sd0 N')
    (B.thZero N N') (mem_ThSp_of' _ _ _ _ h0)).2
  rw [e1, Formalism.BasicNotions.Examples₂.smulLat_one, Formalism.BasicNotions.Examples₂.smulLat_one] at p1
  rw [e1, Formalism.BasicNotions.Examples₂.smulLat_one] at p2
  have j := hJ N N' γ hN hN'
  have t : TaylorLogMetric.Iop D B.tor
      (TaylorLogMetric.La D B.tor (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N)) (StandardLatticesGL3.stdL D N'))
      (TaylorLogMetric.La D B.tor (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) (StandardLatticesGL3.stdL D N'))
      (B.thHalf N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))) =
      B.thHalf N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) :=
    hTL N N' _ _ hN hN' hγ0 hγL _ (mem_ThSp_of' _ _ _ _ h0)
  show TaylorLogMetric.pull D B.tor _ _ (TaylorLogMetric.Iop D B.tor _ _ (B.thHalf N N' L)) = _ • TaylorLogMetric.Iop D B.tor _ _ (B.thHalf N N' _)
  rw [p1]
  show TaylorLogMetric.Iop D B.tor _ _ (TaylorLogMetric.pull D B.tor _ _ (TaylorLogMetric.Iop D B.tor _ _ (B.thZero N N'))) = _
  rw [p2, j, Iop_smulF, Iop_smulF, t]

theorem e3b (hP : PullIop D B.tor) (hSq : SqP D B.tor) (hTR : Tr0R D B.tor) (hSm : SmulSD D) (hL : B.LatAll)
    (hJ : J2 B) {N N' : ℕ} (hN : Even N) (hN' : Even N') (h0 : B.ThZeroMem N N') :
    letI := D.host.cmStar
    ∀ (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' →
    TaylorLogMetric.pull D B.tor (1 : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thMoved N N' L L') =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2) •
        B.thMoved N N' L (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') := by
  letI := D.host.cmStar
  intro γ' L L' hLs h1
  have e1 : ((1 : Matrix.unitaryGroup (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) = 1 := rfl
  have hγL' := hSm N' L' γ' h1
  have hγ0 := hSm N' (StandardLatticesGL3.stdL D N') γ' (sd0 N')
  have hΦ := mvTh B hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' (sd0 N) h1) h0
  have p1 := (hP N N' (StandardLatticesGL3.stdL D N) L L' L' 1 γ' hN hN' (sd0 N) hLs h1 h1 _ (mem_ThSp_of' _ _ _ _ hΦ)).2
  have p2 := (hP N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') L' 1 γ' hN hN' (sd0 N) (sd0 N) (sd0 N') h1
    (B.thZero N N') (mem_ThSp_of' _ _ _ _ h0)).2
  rw [e1, Formalism.BasicNotions.Examples₂.smulLat_one, Formalism.BasicNotions.Examples₂.smulLat_one] at p1
  rw [e1, Formalism.BasicNotions.Examples₂.smulLat_one] at p2
  have j := hJ N N' γ' hN hN'

  have hself : ∀ M : Submodule (𝓞 D.host.E) (Fin N' → D.host.E), B.thMoved N N' (StandardLatticesGL3.stdL D N) M =
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) M)
        (B.thZero N N') := by
    intro M
    show TaylorLogMetric.Iop D B.tor _ _ (TaylorLogMetric.Iop D B.tor _ _ (B.thZero N N')) = _
    rw [iopSelf D B.tor N N' _ _ (mem_ThSp_of' _ _ _ _ h0)]
  have t := hTR N N' _ _ hN hN' hγ0 hγL' _ (mem_ThSp_of' _ _ _ _ h0)
  rw [S1 hSq hL hN hN' h0 hLs h1, p1, p2, j, hself, Iop_smulF, Iop_smulF, t, S1 hSq hL hN hN' h0 hLs hγL']

theorem reduction_of (hM : DetMul D) (hS : DetSmul D) (hU : NormOneUnitIdeal D) (hSm : SmulSD D)
    (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hL : B.LatAll)
    (h0 : ∀ N N', Even N → Even N' → B.ThZeroMem N N')
    (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) (hP : PullIop D B.tor) (hJ1 : J1 B) (hJ2 : J2 B) :
    B.EqP χ := by
  letI := D.host.cmStar
  refine ⟨?_, ?_, ?_⟩
  · intro N N' L L' hN hN' γ γ'
    have h1 := hSm N' L'.1 γ' L'.2
    show TaylorLogMetric.pull D B.tor _ _ (Ker.Base.chiFac χ N N' L.1 L'.1 • B.thMoved N N' L.1 L'.1) =
      Ker.Base.chiFac χ N N' _ _ • B.thMoved N N' _ _
    rw [pull_smul, pull_comp, e3b hP hSq hTR hSm hL hJ2 hN hN' (h0 N N' hN hN') γ' L.1 L'.1 L.2 L'.2, pull_smul,
      e3a hP hTL hSm hL hJ1 hN hN' (h0 N N' hN hN') γ L.1 _ L.2 h1, smul_smul, smul_smul,
      character_factor_unitary_action χ hχ hS hU hN hN' L.1 L'.1 γ γ' L.2 L'.2]
    congr 1
    ring
  · intro N N' L L' L'' hN hN'
    funext z
    show Ker.Base.chiFac χ N N' L.1 L''.1 * B.thMoved N N' L.1 L''.1 z =
      χ (TaylorLogMetric.detId D L'.1 L''.1) ^ (-((N / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor _ _ (fun v => Ker.Base.chiFac χ N N' L.1 L'.1 * B.thMoved N N' L.1 L'.1 v) z
    rw [Iop_smul', e1path hSq hTR hL hN hN' (h0 N N' hN hN') L.2 L'.2 L''.2,
      character_factor_change_right χ hχ hM hN' L.1 L'.2 L''.2]
    ring
  · intro N N' L L₁ L' hN hN'
    funext z
    show Ker.Base.chiFac χ N N' L₁.1 L'.1 * B.thMoved N N' L₁.1 L'.1 z =
      χ (TaylorLogMetric.detId D L.1 L₁.1) ^ (((N' / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor _ _ (fun v => Ker.Base.chiFac χ N N' L.1 L'.1 * B.thMoved N N' L.1 L'.1 v) z
    rw [Iop_smul', e2path hSq hTL hL hN hN' (h0 N N' hN hN') L.2 L₁.2 L'.2,
      character_factor_change_left χ hχ hM hN L'.1 L.2 L₁.2]
    ring

end Formalism.L2.PairingIndexBounds.Eq
