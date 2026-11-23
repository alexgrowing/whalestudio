import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.CharacterFactorUnitaryAction

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Cd.Base D cc δ}

theorem Iop_smulF (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La₁ La₂ : AddSubgroup (TaylorLogMetric.VC D N N')) (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.Iop D T La₁ La₂ (c • G) = c • TaylorLogMetric.Iop D T La₁ La₂ G := by
  funext z
  simp only [TaylorLogMetric.Iop, TaylorLogMetric.U, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm c, ← smul_eq_mul c (∑ᶠ _, _), smul_finsum]
  congr 1
  refine finsum_congr fun q => ?_
  simp only [smul_eq_mul]
  ring

theorem e3a (hP : PullIop D B.tor) (hTL : Tr0L D B.tor) (hSm : SmulSD D) (hL : B.LatAll) (hJ : J1 B)
    {N N' : ℕ} (hN : Even N) (hN' : Even N') (h0 : B.ThZeroMem N N') :
    letI := D.host.cmStar
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (X : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D X →
    TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (1 : Matrix (Fin N') (Fin N') D.host.E) (B.thMoved N N' L X) =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) •
        B.thMoved N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) X := by
  intro γ L X hLs hXs
  have sS : ∀ n, SD D (StandardLatticesGL3.stdL D n) := fun n => Inhab.stdL_isSD D n
  have h1 : ((1 : Matrix.unitaryGroup (Fin N') D.host.E) : Matrix (Fin N') (Fin N') D.host.E) = 1 := by simp
  have hs1 : ∀ Y : Submodule (𝓞 D.host.E) (Fin N' → D.host.E),
      SDLat.smulLat (1 : Matrix (Fin N') (Fin N') D.host.E) Y = Y := by
    intro Y
    simp [SDLat.smulLat]
  have hγS := hSm N (StandardLatticesGL3.stdL D N) γ (sS N)
  have hγL := hSm N L γ hLs
  have m0 : B.thZero N N' ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') := mem_ThSp_of' _ _ _ _ h0
  have mH : B.thHalf N N' L ∈ TaylorLogMetric.Th D B.tor L (StandardLatticesGL3.stdL D N') :=
    mem_ThSp_of' _ _ _ _ (mvTh B hL (admissible_of_integral_conj_le hN hN' (sS N) (sS N')) (admissible_of_integral_conj_le hN hN' hLs (sS N')) h0)
  have eB := (hP N N' (StandardLatticesGL3.stdL D N) L (StandardLatticesGL3.stdL D N') (StandardLatticesGL3.stdL D N') γ 1 hN hN' (sS N) hLs (sS N')
    (sS N') _ m0).2
  have eA := (hP N N' L L (StandardLatticesGL3.stdL D N') X γ 1 hN hN' hLs hLs (sS N') hXs _ mH).2
  simp only [h1, hs1] at eA eB
  have eC := hJ N N' γ hN hN'
  have eE := hTL N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))
    (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) hN hN' hγS hγL _ m0
  have eH : TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) 1 (B.thHalf N N' L) =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) •
        B.thHalf N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) := by
    change TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) 1
      (TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
        (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (B.thZero N N')) = _
    rw [eB, eC, Iop_smulF]
    congr 1
  simp only [Cd.Base.thMoved]
  rw [eA, eH, Iop_smulF]

theorem e3b (hP : PullIop D B.tor) (hSq : SqP D B.tor) (hTR : Tr0R D B.tor) (hSm : SmulSD D) (hL : B.LatAll)
    (hJ : J2 B) {N N' : ℕ} (hN : Even N) (hN' : Even N') (h0 : B.ThZeroMem N N') :
    letI := D.host.cmStar
    ∀ (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' →
    TaylorLogMetric.pull D B.tor (1 : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thMoved N N' L L') =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2) •
        B.thMoved N N' L (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') := by
  intro γ' L L' hLs hL's
  have sS : ∀ n, SD D (StandardLatticesGL3.stdL D n) := fun n => Inhab.stdL_isSD D n
  have h1 : ((1 : Matrix.unitaryGroup (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) = 1 := by simp
  have hs1 : ∀ Y : Submodule (𝓞 D.host.E) (Fin N → D.host.E),
      SDLat.smulLat (1 : Matrix (Fin N) (Fin N) D.host.E) Y = Y := by
    intro Y
    simp [SDLat.smulLat]
  have hγS := hSm N' (StandardLatticesGL3.stdL D N') γ' (sS N')
  have hγL := hSm N' L' γ' hL's
  have m0 : B.thZero N N' ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') := mem_ThSp_of' _ _ _ _ h0
  have mH : TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') (B.thZero N N') ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D N) L' :=
    mem_ThSp_of' _ _ _ _ (mvTh B hL (admissible_of_integral_conj_le hN hN' (sS N) (sS N')) (admissible_of_integral_conj_le hN hN' (sS N) hL's) h0)
  have sq1 := hSq N N' (StandardLatticesGL3.stdL D N) L (StandardLatticesGL3.stdL D N') L' hN hN' (sS N) hLs (sS N') hL's _ m0
  have sq2 := hSq N N' (StandardLatticesGL3.stdL D N) L (StandardLatticesGL3.stdL D N')
    (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') hN hN' (sS N) hLs (sS N') hγL _ m0
  have eA := (hP N N' (StandardLatticesGL3.stdL D N) L L' L' 1 γ' hN hN' (sS N) hLs hL's hL's _ mH).2
  have eB := (hP N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') L' 1 γ' hN hN' (sS N) (sS N)
    (sS N') hL's _ m0).2
  simp only [h1, hs1] at eA eB
  have eC := hJ N N' γ' hN hN'
  have eI := iopSelf D B.tor N N' (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) _ m0
  have eR := hTR N N' (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N'))
    (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') hN hN' hγS hγL _ m0
  have eT : B.thMoved N N' (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) =
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')))
        (B.thZero N N') := by
    simp only [Cd.Base.thMoved, Cd.Base.thHalf]
    rw [eI]
  simp only [Cd.Base.thMoved, Cd.Base.thHalf]
  rw [sq1, sq2, eA, eB, eC, Iop_smulF, Iop_smulF, eT, eR]

theorem reduction_of (hM : DetMul D) (hS : DetSmul D) (hU : NormOneUnitIdeal D) (hSm : SmulSD D)
    (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hL : B.LatAll)
    (h0 : ∀ N N', Even N → Even N' → B.ThZeroMem N N')
    (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) (hP : PullIop D B.tor) (hJ1 : J1 B) (hJ2 : J2 B) :
    B.EqP χ := by
  letI := D.host.cmStar
  refine ⟨?_, ?_, ?_⟩
  · intro N N' L L' hN hN' γ γ'
    have h1 := hSm N' L'.1 γ' L'.2
    show TaylorLogMetric.pull D B.tor _ _ (Cd.Base.chiFac χ N N' L.1 L'.1 • B.thMoved N N' L.1 L'.1) =
      Cd.Base.chiFac χ N N' _ _ • B.thMoved N N' _ _
    rw [pull_smul, pull_comp, e3b hP hSq hTR hSm hL hJ2 hN hN' (h0 N N' hN hN') γ' L.1 L'.1 L.2 L'.2, pull_smul,
      e3a hP hTL hSm hL hJ1 hN hN' (h0 N N' hN hN') γ L.1 _ L.2 h1, smul_smul, smul_smul,
      character_factor_unitary_action χ hχ hS hU hN hN' L.1 L'.1 γ γ' L.2 L'.2]
    congr 1
    ring
  · intro N N' L L' L'' hN hN'
    funext z
    show Cd.Base.chiFac χ N N' L.1 L''.1 * B.thMoved N N' L.1 L''.1 z =
      χ (TaylorLogMetric.detId D L'.1 L''.1) ^ (-((N / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor _ _ (fun v => Cd.Base.chiFac χ N N' L.1 L'.1 * B.thMoved N N' L.1 L'.1 v) z
    rw [Iop_smul', e1path hSq hTR hL hN hN' (h0 N N' hN hN') L.2 L'.2 L''.2,
      character_factor_change_right χ hχ hM hN' L.1 L'.2 L''.2]
    ring
  · intro N N' L L₁ L' hN hN'
    funext z
    show Cd.Base.chiFac χ N N' L₁.1 L'.1 * B.thMoved N N' L₁.1 L'.1 z =
      χ (TaylorLogMetric.detId D L.1 L₁.1) ^ (((N' / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor _ _ (fun v => Cd.Base.chiFac χ N N' L.1 L'.1 * B.thMoved N N' L.1 L'.1 v) z
    rw [Iop_smul', e2path hSq hTL hL hN hN' (h0 N N' hN hN') L.2 L₁.2 L'.2,
      character_factor_change_left χ hχ hM hN L'.1 L.2 L₁.2]
    ring

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
