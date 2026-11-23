import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory

set_option maxHeartbeats 4000000 in
open GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.BigTop.Fun in

theorem Mem.LiteralAutomorphy.trSq_holds : GlobalTheory.Mem.LiteralAutomorphy.TrSq := by
  intro X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι h M σ hs
  obtain ⟨⟨hpre, -, -, ⟨f, f', hff, hC, hC'⟩, hbase, hxi, -, -⟩, hg, -, -⟩ := h
  clear S S' W W'
  obtain ⟨B, C₁, W₁, V₁, S₁, N₁, G₁⟩ := X
  obtain ⟨B', C₂, W₂, V₂, S₂, N₂, G₂⟩ := X'
  cases B; cases B'
  dsimp only at hpre
  subst hpre
  obtain rfl := eq_of_heq hff
  have hv0 : G'.pl.v0 = G.pl.v0 := eq_of_heq hg.v0
  have hw : G'.pl.w = G.pl.w := eq_of_heq hg.w
  have hchi : G'.ch.chiH = G.ch.chiH := eq_of_heq hg.chiH
  have hx : L'.xiH μ₀' = L.xiH μ₀ := by have := eq_of_heq (hxi μ₀'); rwa [hbase] at this
  have e_levQ : levQ G'.pl = levQ G.pl := by
    unfold levQ Places.S0 condExp; rw [hv0]; exact (Eq.refl (levQ G.pl))
  have e_condE : SqNum.condE G'.pl = SqNum.condE G.pl := by
    unfold SqNum.condE Places.S0 condExp; rw [hv0, hw]; exact (Eq.refl (SqNum.condE G.pl))
  have e_condF : condF G'.pl = condF G.pl := by
    unfold condF Places.S0 condExp; rw [hv0]; exact (Eq.refl (condF G.pl))
  have hmu : L'.C.mu0 = L.C.mu0 := by rw [hC, hC']; exact (Eq.refl f'.mu0)
  have heta : L'.C.eta = L.C.eta := by rw [hC, hC']; exact (Eq.refl f'.eta)
  have hd1 : L'.C.del = L.C.del := by rw [hC, hC']; exact (Eq.refl f'.del)
  have hd2 : L'.C.del' = L.C.del' := by rw [hC, hC']; exact (Eq.refl f'.del')
  have e_nu : ∀ i j, nuH G' μ₀' i j = nuH G μ₀ i j := by
    intro i j; unfold nuH; rw [hmu, hx, hchi]; exact (Eq.refl (nuH G μ₀ i j))
  have e_beta : ∀ i j, betaH G' i j = betaH G i j := by
    intro i j; unfold betaH; rw [heta, hchi]; exact (Eq.refl (betaH G i j))
  have e_alpha : ∀ i j, alphaH L' μ₀' i j = alphaH L μ₀ i j := by
    intro i j; unfold alphaH; rw [hmu, hx, heta]; exact (Eq.refl (alphaH L μ₀ i j))
  have e_del : ∀ c, delOf L' c = delOf L c := by
    intro c; unfold delOf; rw [hd1, hd2]; exact (Eq.refl (delOf L c))
  have eT : ∀ i j s χ x, IsTor G' i j s χ x ↔ IsTor G i j s χ x := by
    intro i j s χ x; unfold IsTor; rw [e_condF]; exact (Iff.refl (IsTor G i j s χ x))

  let hk1 : ∀ {N : ℕ}, Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) N → Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) N :=
    fun h => { f := ((h.f)), n := ((h.n)), unitary := ((h.unitary)), cont := ((h.cont)), aut := ((h.aut)), norm := ((h.norm)), par := ((h.par)), unr := ((h.unr)) }
  let wt1 : ∀ {δ : ℂ} {a d : ℕ} {e0 : Formalism.MainNotions.TaylorLogMetric.VC (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) a d → ℂ}, Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ a d e0 →
      Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ a d ((e0)) :=
    fun w => { chV := hk1 w.chV, chV' := hk1 w.chV', ep := w.ep, ep' := w.ep', ep_pm := w.ep_pm, nz := ((w.nz)), Om := ((w.Om)), maps := ((w.maps)), add := ((w.add)), smul := ((w.smul)), one := ((w.one)), mul := ((w.mul)), lift := ((w.lift)), inert := ((w.inert)), split := ((w.split)) }
  let pt1 : ∀ {δ t0 : ℂ} {Q : ℕ}, GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ t0 Q → GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ t0 Q :=
    fun P => { a := P.a, d := P.d, a_le := P.a_le, d_even := P.d_even, W := wt1 P.W, crv := ((P.crv)), pt0 := ((P.pt0)), e0 := ((P.e0)), vac := ((P.vac)), n := ((P.n)), wt := ((P.wt)), F := ((P.F)), pres := ((P.pres)), fix := ((P.fix)), J := ((P.J)), J_le := ((P.J_le)), idx_ne := ((P.idx_ne)), idx_le := ((P.idx_le)), eig := ((P.eig)) }

  let hk2 : ∀ {N : ℕ}, Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) N → Formalism.MainNotions.StandardLatticesGL3.HeckeU (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) N :=
    fun h => { f := ((h.f)), n := ((h.n)), unitary := ((h.unitary)), cont := ((h.cont)), aut := ((h.aut)), norm := ((h.norm)), par := ((h.par)), unr := ((h.unr)) }
  let wt2 : ∀ {δ : ℂ} {a d : ℕ} {e0 : Formalism.MainNotions.TaylorLogMetric.VC (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) a d → ℂ}, Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ a d e0 →
      Formalism.MainNotions.StandardLatticesGL3.WeilO (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ a d ((e0)) :=
    fun w => { chV := hk2 w.chV, chV' := hk2 w.chV', ep := w.ep, ep' := w.ep', ep_pm := w.ep_pm, nz := ((w.nz)), Om := ((w.Om)), maps := ((w.maps)), add := ((w.add)), smul := ((w.smul)), one := ((w.one)), mul := ((w.mul)), lift := ((w.lift)), inert := ((w.inert)), split := ((w.split)) }
  let pt2 : ∀ {δ t0 : ℂ} {Q : ℕ}, GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ t0 Q → GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ t0 Q :=
    fun P => { a := P.a, d := P.d, a_le := P.a_le, d_even := P.d_even, W := wt2 P.W, crv := ((P.crv)), pt0 := ((P.pt0)), e0 := ((P.e0)), vac := ((P.vac)), n := ((P.n)), wt := ((P.wt)), F := ((P.F)), pres := ((P.pres)), fix := ((P.fix)), J := ((P.J)), J_le := ((P.J_le)), idx_ne := ((P.idx_ne)), idx_le := ((P.idx_le)), eig := ((P.eig)) }

  have btr1 : ∀ {δ t0 : ℂ} {Q : ℕ} (i j : Fin (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩).R.m)
      (P P' : GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₁, W₁, V₁, S₁, N₁, G₁⟩) ⊤ δ t0 Q), IsBottom G μ₀ i j (SqNum.condE G.pl) P P' →
        IsBottom G' μ₀' i j (SqNum.condE G'.pl) (pt1 P) (pt1 P') := by
    intro δ t0 Q i j P P' h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨(h1), ?_, ?_, ?_, ?_, ?_⟩
    · rw [e_beta, e_nu]; exact (h2)
    · rw [e_alpha, e_nu]; exact (h3)
    · rw [e_condE]; exact (h4)
    · rw [e_condE]; exact (h5)
    · rw [e_condE]; exact (h6)

  have btr2 : ∀ {δ t0 : ℂ} {Q : ℕ} (i j : Fin (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩).R.m)
      (P P' : GlobalTheory.NormSum.Pair (Mem.Stages.toD7 ⟨_, C₂, W₂, V₂, S₂, N₂, G₂⟩) ⊤ δ t0 Q), IsBottom G' μ₀' i j (SqNum.condE G'.pl) P P' →
        IsBottom G μ₀ i j (SqNum.condE G.pl) (pt2 P) (pt2 P') := by
    intro δ t0 Q i j P P' h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    rw [e_beta, e_nu] at h2
    rw [e_alpha, e_nu] at h3
    rw [e_condE] at h4 h5 h6
    exact ⟨(h1), (h2), (h3), (h4), (h5), (h6)⟩
  refine ⟨fun hb => ?_, fun i j s c x y h1 h2 h3 h4 => ?_⟩
  · obtain ⟨δ, t0, hb⟩ := hb
    rw [e_levQ] at hb
    obtain ⟨δ', t0', hb'⟩ := hs.norms ⟨δ, t0, fun ij => by
      obtain ⟨P, P', hP, -, -⟩ := hb ((ij))
      exact ⟨pt2 P, pt2 P', btr2 ((ij.1)) ((ij.2)) P P' hP, trivial, trivial⟩⟩
    refine ⟨δ', t0', fun ij => ?_⟩
    rw [e_levQ]
    obtain ⟨P, P', hP, n1, n2⟩ := hb' ((ij))
    exact ⟨pt1 P, pt1 P', btr1 ij.1 ij.2 P P' hP, (n1), (n2)⟩
  · rw [eT, e_nu] at h3
    rw [eT, e_nu, e_del] at h4
    exact hs.toric ((i)) ((j)) s c x y h1 ((h2)) ((h3)) ((h4))

end GlobalTheory
