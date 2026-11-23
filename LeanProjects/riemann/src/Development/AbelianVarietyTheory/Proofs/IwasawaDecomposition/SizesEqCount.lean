import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Top

def duPre (B : Pre) (u : B.Word) : ℝ :=
  (letI := B.host.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm B.host.E B.R.k) (StandardLattice.stdLat B.host.E B.R.k)) *
    (StandardLattice.idxColLoc (B.host.g 0) B.R.k ^ B.R.f * StandardLattice.idxColLoc (B.host.g 1) B.R.k ^ B.R.f) *
    ∏ τ : Tau B.R, StandardLattice.dimV (fun i : Fin B.R.k => (((B.hcW u τ).u i : ℚ) : ℝ))

def DsPre (B : Pre) : ℝ :=
  (letI := B.host.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm B.host.E B.R.r) (StandardLattice.stdLat B.host.E B.R.r)) *
    (StandardLattice.idxRowLoc (B.host.g 0) B.R.k B.R.m ^ B.R.f * StandardLattice.idxRowLoc (B.host.g 1) B.R.k B.R.m ^ B.R.f) *
    ∏ τ : Tau B.R, Vol.trueDsig B.R (B.hc τ)

theorem Ctx.Over.sizes {K : Ctx} {B : Pre} (h : K.Over B) :
    (∀ u, (B.duStar u : ℝ) = duPre B u) ∧ B.Dstar = DsPre B := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  exact ⟨fun u => K.du_eq u, K.Ds_eq⟩

theorem sigYD_zero (R : Ranks) : 2 ≤ (sigYD R 0).1 ∧ (sigYD R 0).1 + (sigYD R 0).2 = R.r := by
  have h1 := R.two_le_m
  have h2 := R.m_add_three_le_k
  simp only [sigYD, Ranks.rankY, Ranks.r]
  omega

theorem sizes_eq_count (K : Ctx) (X : Stages) (hO : K.Over X.B.toPre) (hv : StandardLattice.VolumeEqMass₂ X.toD7)
    (hd : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)) :
    (∀ u, ((X.toD7.mem u).A.duStar : ℝ) = StandardLattice.duStarU X.toD7 u) ∧ X.toD7.what₂.Dstar = StandardLattice.DstarD X.toD7 := by
  obtain ⟨h1, h2⟩ := hO.sizes
  refine ⟨fun u => ?_, ?_⟩
  · have e : (X.toD7.mem u).A.duStar = X.B.duStar u := X.C.A_duStar u
    rw [e]
    refine (h1 u).trans ?_
    unfold duPre StandardLattice.duStarU StandardLattice.duStarP
    congr 1
  · have e : X.toD7.what₂.Dstar = X.B.Dstar := (X.toD7.Dstar_eq X.toD7.u₀).symm.trans (X.C.A_Dstar _)
    rw [e, h2]
    have hvol : StandardLattice.volY0 X.toD7 = StandardLattice.massI X.toD7 X.B.R.r := by
      letI := X.toD7.host.cmStar
      have := hv.2 (X.toD7.sp.Y 0) (sigYD X.B.R 0).1 (sigYD X.B.R 0).2 (X.toD7.sp.Y_sig 0)
        (fun τ => X.toD7.Y_sigval 0 (Nat.zero_le _) τ) (sigYD_zero _).1
      rw [(sigYD_zero _).2] at this
      exact this
    unfold DsPre StandardLattice.DstarD StandardLattice.DstarP
    rw [hvol]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => (hd τ).symm

end GlobalTheory.Mem.Top

end
